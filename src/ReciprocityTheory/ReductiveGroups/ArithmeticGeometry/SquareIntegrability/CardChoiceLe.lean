module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.IteratedDerivListBound

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.L2NormSqNonnegGaussianTorus
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.HfEqInner
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E]

def VP {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) : Submodule ℂ (Vsp dim) where
  carrier := {v | InPart σ v}
  add_mem' := fun {a b} ha hb j hj => by simp [ha j hj, hb j hj]
  zero_mem' := fun j _ => rfl
  smul_mem' := fun c v hv j hj => by simp [hv j hj]


open scoped Classical in
open Classical in
def prj {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (v : Vsp dim) : Vsp dim :=
  WithLp.toLp 2 fun j => if j.1 = σ then v j else 0

def mulc {dim : (E →+* ℂ) → ℕ} (c : (E →+* ℂ) → ℂ) (v : Vsp dim) : Vsp dim :=
  WithLp.toLp 2 fun j => c j.1 * v j

theorem emb_sep {σ τ : E →+* ℂ} (h : σ ≠ τ) : ∃ α : 𝓞 E, σ (α : E) ≠ τ (α : E) := by
  by_contra hc
  push Not at hc
  apply h
  exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun x => hc x)

theorem mulc_mem {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim))
    (hst : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I) (σ : E →+* ℂ) :
    ∀ v ∈ Submodule.span ℂ (I : Set (Vsp dim)), prj σ v ∈ Submodule.span ℂ (I : Set (Vsp dim)) := by
  classical
  set S := Submodule.span ℂ (I : Set (Vsp dim)) with hS

  have hact : ∀ (α : 𝓞 E), ∀ v ∈ S, act α v ∈ S := by
    intro α
    let A : Vsp dim →ₗ[ℂ] Vsp dim :=
      { toFun := act α
        map_add' := fun x y => by ext j; simp [act]; ring
        map_smul' := fun c x => by ext j; simp [act]; ring }
    have hle : S.map A ≤ S := by
      rw [hS, Submodule.map_span]
      apply Submodule.span_le.2
      rintro _ ⟨x, hx, rfl⟩
      exact Submodule.subset_span (hst α x hx)
    intro v hv
    exact hle ⟨v, hv, rfl⟩

  have hα : ∀ τ : E →+* ℂ, ∃ α : 𝓞 E, τ ≠ σ → σ (α : E) ≠ τ (α : E) := by
    intro τ
    by_cases h : τ = σ
    · exact ⟨0, fun h' => (h' h).elim⟩
    · obtain ⟨α, hα⟩ := emb_sep (Ne.symm h)
      exact ⟨α, fun _ => hα⟩
  choose α hα using hα
  let c : (E →+* ℂ) → (E →+* ℂ) → ℂ := fun τ τ' =>
    (τ' (α τ : E) - τ (α τ : E)) * (σ (α τ : E) - τ (α τ : E))⁻¹
  have hstep : ∀ τ, ∀ v ∈ S, mulc (c τ) v ∈ S := by
    intro τ v hv
    have : mulc (c τ) v = (σ (α τ : E) - τ (α τ : E))⁻¹ • (act (α τ) v - (τ (α τ : E)) • v) := by
      ext j; simp [mulc, act, c]; ring
    rw [this]
    exact S.smul_mem _ (S.sub_mem (hact _ v hv) (S.smul_mem _ hv))
  have hprod : ∀ T : Finset (E →+* ℂ), ∀ v ∈ S, mulc (fun τ' => ∏ τ ∈ T, c τ τ') v ∈ S := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro v hv
      have : mulc (fun τ' => ∏ τ ∈ (∅ : Finset (E →+* ℂ)), c τ τ') v = v := by ext j; simp [mulc]
      rw [this]; exact hv
    | insert τ T hτ ih =>
      intro v hv
      have : mulc (fun τ' => ∏ t ∈ insert τ T, c t τ') v = mulc (c τ) (mulc (fun τ' => ∏ t ∈ T, c t τ') v) := by
        ext j; simp [mulc, Finset.prod_insert hτ]; ring
      rw [this]
      exact hstep τ _ (ih v hv)
  intro v hv
  have : prj σ v = mulc (fun τ' => ∏ τ ∈ Finset.univ.erase σ, c τ τ') v := by
    ext j
    simp only [prj, mulc, PiLp.toLp_apply]
    by_cases hj : j.1 = σ
    · rw [if_pos hj, hj, Finset.prod_eq_one, one_mul]
      intro τ hτ
      have hne := hα τ (Finset.ne_of_mem_erase hτ)
      simp only [c]
      exact mul_inv_cancel₀ (sub_ne_zero.2 hne)
    · rw [if_neg hj, Finset.prod_eq_zero (i := j.1) (Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩), zero_mul]
      simp [c]
  rw [this]
  exact hprod _ v hv

theorem Hf_prj {dim : (E →+* ℂ) → ℕ} {σ : E →+* ℂ} {ξ : Vsp dim} (hξ : InPart σ ξ) (a : Vsp dim) :
    Hf ξ a = Hf ξ (prj σ a) := by
  unfold Hf
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [prj, PiLp.toLp_apply]
  by_cases hj : j.1 = σ
  · rw [if_pos hj]
  · rw [if_neg hj, hξ j hj]; simp

theorem Hf_eq_inner' {ι : Type} [Fintype ι] (w v : EuclideanSpace ℂ ι) : Hf w v = inner ℂ v w :=
  lemS_Hf_eq_inner w v

theorem prj_inpart {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (a : Vsp dim) : InPart σ (prj σ a) := by
  intro j hj; simp [prj, hj]

theorem onb_data (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (σ : E →+* ℂ) (ρ : ℕ)
    (hρ : Module.finrank ℂ (Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ VP σ : Submodule ℂ _) = ρ)
    (hst : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I)
    (w : Fin ρ → Vsp X.dim) (hw : ∀ s, InPart σ (w s) ∧ w s ∈ Submodule.span ℂ (I : Set (Vsp X.dim)))
    (hon : ∀ s s', Hf (w s) (w s') = if s = s' then 1 else 0) :
    ∃ (N : ℕ) (b : Fin N → Vsp X.dim), N ≤ X.r ∧ ρ ≤ N ∧
      (∀ k (h : k.val < ρ), b k = w ⟨k, h⟩) ∧
      (∀ k, InPart σ (b k)) ∧
      (∀ k, ρ ≤ k.val → ‖b k‖ = 1 ∧ ∀ a ∈ I, Hf (b k) a = 0) ∧
      (∀ x y : Vsp X.dim, InPart σ x → InPart σ y → ∑ k, Hf x (b k) * Hf (b k) y = Hf x y) := by
  classical
  set N := Module.finrank ℂ (VP (dim := X.dim) σ) with hN
  have hw_inner : ∀ s s', inner ℂ (w s) (w s') = if s = s' then (1 : ℂ) else 0 := by
    intro s s'
    rw [← Hf_eq_inner', hon s' s]
    by_cases h : s = s' <;> simp [h, eq_comm]
  have hwo : Orthonormal ℂ w := by
    rw [orthonormal_iff_ite]; exact hw_inner
  have hρN : ρ ≤ N := hρ ▸ Submodule.finrank_mono inf_le_right
  have hNr : N ≤ X.r := by
    let f : VP (dim := X.dim) σ →ₗ[ℂ] (Fin (X.dim σ) → ℂ) :=
      { toFun := fun v a => (v : Vsp X.dim) ⟨σ, a⟩
        map_add' := fun x y => by funext a; simp
        map_smul' := fun c x => by funext a; simp }
    have hinj : Function.Injective f := by
      intro v v' h
      apply Subtype.ext
      ext j
      obtain ⟨τ, a⟩ := j
      by_cases hτ : τ = σ
      · subst hτ; exact congrFun h a
      · rw [(v.2 : InPart σ (v : Vsp X.dim)) ⟨τ, a⟩ hτ, (v'.2 : InPart σ (v' : Vsp X.dim)) ⟨τ, a⟩ hτ]
    have h1 := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_fin_fun] at h1
    have h2 := X.dim_conj σ
    omega
  let vv : Fin N → VP (dim := X.dim) σ := fun k =>
    if h : k.val < ρ then ⟨w ⟨k, h⟩, (hw _).1⟩ else 0
  have hon' : Orthonormal ℂ (Set.domRestrict {k : Fin N | k.val < ρ} vv) := by
    rw [orthonormal_iff_ite]
    rintro ⟨k, hk⟩ ⟨k', hk'⟩
    have hk0 : k.val < ρ := hk
    have hk0' : k'.val < ρ := hk'
    show inner ℂ (vv k) (vv k') = if (⟨k, hk⟩ : {k : Fin N | k.val < ρ}) = ⟨k', hk'⟩ then 1 else 0
    simp only [vv, dif_pos hk0, dif_pos hk0', Submodule.coe_inner, hw_inner]
    simp [Fin.ext_iff, Subtype.ext_iff]
  obtain ⟨bb, hbb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℂ)
    (E := VP (dim := X.dim) σ) (ι := Fin N) (by simp [hN]) hon'
  have hbw : ∀ k (h : k.val < ρ), (bb k : Vsp X.dim) = w ⟨k, h⟩ := by
    intro k h
    rw [hbb k h]
    simp [vv, h]
  refine ⟨N, fun k => (bb k : Vsp X.dim), hNr, hρN, hbw, fun k => (bb k).2, ?_, ?_⟩
  · intro k hk
    constructor
    · exact bb.orthonormal.1 k
    · intro a ha
      rw [Hf_prj ((bb k).2 : InPart σ (bb k : Vsp X.dim)) a]
      have hpa : prj σ a ∈ (Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ VP σ : Submodule ℂ _) :=
        ⟨mulc_mem I hst σ a (Submodule.subset_span ha), prj_inpart σ a⟩
      have hspan : Submodule.span ℂ (Set.range w) =
          (Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ VP σ : Submodule ℂ _) := by
        apply Submodule.eq_of_le_of_finrank_eq
        · rw [Submodule.span_le]; rintro _ ⟨s, rfl⟩; exact ⟨(hw s).2, (hw s).1⟩
        · rw [finrank_span_eq_card hwo.linearIndependent, Fintype.card_fin, hρ]
      rw [← hspan] at hpa
      rw [Hf_eq_inner']
      refine Submodule.span_induction (p := fun z _ => inner ℂ z (bb k : Vsp X.dim) = 0) ?_ ?_ ?_ ?_ hpa
      · rintro _ ⟨s, rfl⟩
        have hs : (⟨s.val, lt_of_lt_of_le s.2 hρN⟩ : Fin N).val < ρ := s.2
        have e1 : w s = (bb ⟨s.val, lt_of_lt_of_le s.2 hρN⟩ : Vsp X.dim) := by
          rw [hbw _ hs]
        rw [e1, ← Submodule.coe_inner]
        refine bb.orthonormal.2 ?_
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      · simp
      · intro x y _ _ hx hy; rw [inner_add_left, hx, hy, add_zero]
      · intro c x _ hx; rw [inner_smul_left, hx, mul_zero]
  · intro x y hx hy
    have := bb.sum_inner_mul_inner (⟨y, hy⟩ : VP (dim := X.dim) σ) ⟨x, hx⟩
    simp only [Submodule.coe_inner] at this
    rw [Hf_eq_inner', ← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Hf_eq_inner', Hf_eq_inner', mul_comm]

end

end ReciprocityTheory.ChartRestriction.G.I2
end

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex

noncomputable section

theorem jof_Hf_smul_right {ι : Type} [Fintype ι] (x u : EuclideanSpace ℂ ι) (c : ℂ) :
    Hf x (c • u) = (starRingEnd ℂ) c * Hf x u := by
  simp only [Hf, PiLp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem jof_Hf_conj {ι : Type} [Fintype ι] (v w : EuclideanSpace ℂ ι) : star (Hf v w) = Hf w v := by
  simp only [Hf, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.star_def, mul_comm]

theorem Hf_single {ι : Type} [Fintype ι] [DecidableEq ι] (j j' : ι) :
    Hf (EuclideanSpace.single j (1 : ℂ)) (EuclideanSpace.single j' 1) = if j = j' then 1 else 0 := by
  simp only [Hf, PiLp.single_apply]
  by_cases h : j = j'
  · subst h
    simp [Finset.sum_ite_eq']
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h1 : i = j
    · subst h1
      simp [h]
    · simp [h1]

theorem sum_fin_le {M : Type*} [AddCommMonoid M] {ρ N : ℕ} (h : ρ ≤ N) (f : Fin ρ → M) :
    ∑ k : Fin N, (if h' : k.val < ρ then f ⟨k, h'⟩ else 0) = ∑ s, f s := by
  have key : ∀ M, ∑ k : Fin M, (if h' : k.val < ρ then f ⟨k, h'⟩ else 0) =
      ∑ k ∈ Finset.range M, (if h' : k < ρ then f ⟨k, h'⟩ else 0) :=
    fun M => Fin.sum_univ_eq_sum_range (fun k => if h' : k < ρ then f ⟨k, h'⟩ else 0) M
  rw [key N]
  have hρ : ∑ s, f s = ∑ k ∈ Finset.range ρ, (if h' : k < ρ then f ⟨k, h'⟩ else 0) := by
    rw [← key ρ]
    exact Finset.sum_congr rfl fun s _ => by simp [s.isLt]
  rw [hρ]
  symm
  apply Finset.sum_subset (Finset.range_mono h)
  intro k _ hk'
  simp only [Finset.mem_range] at hk'
  simp [hk']

variable {E : Type} [Field E] [NumberField E]

theorem l2NormSq_nonneg_gaussianTorus (X : PT E) (q : ℕ) {n : ℕ} (F : (Fin n → Vsp X.dim) → ℂ) : 0 ≤ X.l2 q F := by
  unfold PT.l2
  rw [MeasureTheory.setAverage_eq]
  exact smul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
    (MeasureTheory.integral_nonneg fun v => by unfold PT.ptN2; positivity)

theorem rd_nonneg : 0 ≤ PT.rd E := by
  unfold PT.rd
  positivity

theorem ph_nonneg {X : PT E} {DF : ℕ} (P : Par X DF) : 0 ≤ P.ph := by
  unfold Par.ph PT.ph
  have := rd_nonneg (E := E)
  split_ifs
  · positivity
  · exact le_rfl

theorem Cchi_nonneg (m : ℕ) : 0 ≤ Cchi (E := E) m := by
  unfold Cchi RR
  have := rd_nonneg (E := E)
  positivity

theorem inv_constant_nonneg {X : PT E} {DF : ℕ} (P : Par X DF) : 0 ≤ P.K6⁻¹ := by
  unfold Par.K6
  positivity

open Classical in
theorem block_data (hx : Ext.All) (hc : CharStatement) (ht : ColTorusStatement)
    (ha : ColAbelStatement) [IsCMField E] (X : PT E) {DF : ℕ} (P : Par X DF)
    (I : Submodule ℤ (Vsp X.dim)) (hI : IsSplit P I) (σ : E →+* ℂ) (i : ℕ) (hi : i ≤ X.dim σ)
    (c : ℕ) (hcD : c ≤ DF) :
    ∃ (y : Fin i → Vsp X.dim) (s : Fin i → (Fin 1 → Vsp X.dim) → ℂ) (μ : Fin i → ℂ),
      (∀ b, s b ∈ X.Sec P.q 1) ∧
      (∀ b (xs : Fin c → Vsp X.dim), (∀ k, InPart σ (xs k) ∧ ‖xs k‖ = 1) →
        ‖d1 (s b) c xs - μ b * ∏ k, Hf (xs k) (y b)‖ ≤ P.eps1 * ‖μ b‖) ∧
      (∀ b, P.K6⁻¹ * Real.exp (-(2 * Real.pi * Cchi (E := E) P.m * P.ph / P.q)) * X.l2 P.q (s b) ≤
        ‖μ b‖ ^ 2) ∧
      (∀ b, ‖y b‖ ≤ 2) ∧
      (2 : ℝ) ^ (-(X.r : ℝ) / 2) / 2 ≤
        ‖(Matrix.of fun a b => Hf (EuclideanSpace.single (⟨σ, Fin.castLE hi a⟩ : Idx X.dim) (1 : ℂ))
          (y b)).det‖ ∧
      (∀ b, μ b ≠ 0) := by
  classical
  obtain ⟨ρ, hρ⟩ : ∃ ρ, Module.finrank ℂ
      (Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ VP σ : Submodule ℂ (Vsp X.dim)) = ρ := ⟨_, rfl⟩
  obtain ⟨w, xx, u, R, ε, hw, hon, hxu, -, hεb, hc4, hc5, hc6, hc7⟩ := hc E X DF P I hI σ ρ hρ
  obtain ⟨N, bb, hNr, hρN, hbw, hin, hperp, hpars⟩ := onb_data X I σ ρ hρ hI.stable w hw hon
  set e : Fin i → Vsp X.dim := fun a => EuclideanSpace.single (⟨σ, Fin.castLE hi a⟩ : Idx X.dim) (1 : ℂ)
    with he
  have he_in : ∀ a, InPart σ (e a) := by
    intro a j hj
    simp only [he, PiLp.single_apply]
    rw [if_neg]
    rintro rfl
    exact hj rfl
  have hee : ∀ a a', Hf (e a) (e a') = if a = a' then 1 else 0 := by
    intro a a'
    simp only [he]
    rw [Hf_single]
    by_cases h : a = a'
    · simp [h]
    · rw [if_neg, if_neg h]
      intro h2
      rw [Sigma.mk.inj_iff] at h2
      exact h (Fin.castLE_injective hi (eq_of_heq h2.2))
  let M : Matrix (Fin i) (Fin N) ℂ := Matrix.of fun a k => Hf (e a) (bb k)
  have hMM : M * M.conjTranspose = 1 := by
    ext a a'
    simp only [M, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply, jof_Hf_conj]
    rw [hpars (e a) (e a') (he_in a) (he_in a'), hee]
  obtain ⟨s1, -, hs1⟩ := hx.2.2.2.2.2.1 i N X.r M hMM hNr
  haveI : Nonempty (Fin i → Fin N) := ⟨s1⟩
  obtain ⟨s0, hs0⟩ := Finite.exists_max (fun s : Fin i → Fin N => ‖(M.submatrix id s).det‖)
  set Δ := ‖(M.submatrix id s0).det‖ with hΔ
  have hΔr : (2 : ℝ) ^ (-(X.r : ℝ) / 2) ≤ Δ := hs1.trans (hs0 s1)
  have hΔpos : 0 < Δ := lt_of_lt_of_le (by positivity) hΔr
  have hinj : Function.Injective s0 := by
    intro j j' h
    by_contra hne
    have h0 : (M.submatrix id s0).det = 0 := Matrix.det_zero_of_column_eq hne (by intro a; simp [h])
    rw [hΔ, h0, norm_zero] at hΔpos
    exact lt_irrefl 0 hΔpos
  have hRpos : ∀ t, 0 < R t := by
    intro t
    have h1 := (hc5 t).2
    have hp := Real.pi_pos
    by_contra h
    push Not at h
    nlinarith
  have hT : ∀ t : Fin ρ, ∃ s' ∈ X.Sec P.q 1, ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
      (∀ xs : Fin c → Vsp X.dim, (∀ k, InPart σ (xs k) ∧ ‖xs k‖ = 1) →
        ‖d1 s' c xs - ζ * (2 * Real.pi) ^ c * ∏ k, Hf (xs k) (u t)‖ ≤ P.eps1 * (2 * Real.pi * R t) ^ c) ∧
      P.K6⁻¹ * Real.exp (-(2 * Real.pi * ‖u t‖ ^ 2 / P.q)) * X.l2 P.q s' ≤ (2 * Real.pi * R t) ^ (2 * c) :=
    fun t => ht E X DF P I hI c hcD σ (xx t) (u t) (hxu t).1 (hxu t).2 (2 * Real.pi * R t) (hc5 t).2
      (by have h1 := (hc5 t).1; have hp := Real.pi_pos; nlinarith) (hc6 t)
  choose sT hsT ζ hζ hζb hζl using hT
  have hA : ∀ k : Fin N, ρ ≤ k.val → ∃ s' ∈ X.Sec P.q 1,
      (∀ xs : Fin c → Vsp X.dim, (∀ k, InPart σ (xs k) ∧ ‖xs k‖ = 1) →
        ‖d1 s' c xs - (c.factorial : ℂ) * ∏ k', Hf (xs k') (bb k)‖ ≤ P.eps1 * c.factorial) ∧
      P.K6⁻¹ * X.l2 P.q s' ≤ (c.factorial : ℝ) ^ 2 :=
    fun k hk => ha E X DF P I hI c hcD σ (bb k) (hin k) (hperp k hk).1 (hperp k hk).2
  choose sA hsA hAb hAl using hA
  have hK6 := inv_constant_nonneg P
  have hexp1 : Real.exp (-(2 * Real.pi * Cchi (E := E) P.m * P.ph / P.q)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]
    have := Cchi_nonneg (E := E) P.m
    have := ph_nonneg P
    have := Real.pi_pos
    positivity
  have hexp : ∀ t, Real.exp (-(2 * Real.pi * Cchi (E := E) P.m * P.ph / P.q)) ≤
      Real.exp (-(2 * Real.pi * ‖u t‖ ^ 2 / P.q)) := by
    intro t
    rw [Real.exp_le_exp, neg_le_neg_iff]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have := hc7 t
    have := Real.pi_pos
    nlinarith
  let y : Fin i → Vsp X.dim := fun j =>
    if h : (s0 j).val < ρ then ((R ⟨_, h⟩ : ℂ))⁻¹ • u ⟨_, h⟩ else bb (s0 j)
  let s : Fin i → (Fin 1 → Vsp X.dim) → ℂ := fun j =>
    if h : (s0 j).val < ρ then sT ⟨_, h⟩ else sA (s0 j) (not_lt.1 h)
  let μ : Fin i → ℂ := fun j =>
    if h : (s0 j).val < ρ then ζ ⟨_, h⟩ * (((2 * Real.pi * R ⟨_, h⟩ : ℝ)) : ℂ) ^ c
    else (c.factorial : ℂ)
  have hnμ : ∀ t, ‖ζ t * (((2 * Real.pi * R t : ℝ)) : ℂ) ^ c‖ = (2 * Real.pi * R t) ^ c := by
    intro t
    have := hRpos t
    rw [norm_mul, hζ t, one_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  refine ⟨y, s, μ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases h : (s0 j).val < ρ
    · simp only [s, dif_pos h]; exact hsT _
    · simp only [s, dif_neg h]; exact hsA _ _
  · intro j xs hxs
    by_cases h : (s0 j).val < ρ
    · simp only [s, μ, y, dif_pos h]
      have hR := hRpos ⟨_, h⟩
      have e1 : ζ ⟨_, h⟩ * (((2 * Real.pi * R ⟨_, h⟩ : ℝ)) : ℂ) ^ c *
          ∏ k, Hf (xs k) (((R ⟨_, h⟩ : ℂ))⁻¹ • u ⟨_, h⟩) =
          ζ ⟨_, h⟩ * (2 * Real.pi) ^ c * ∏ k, Hf (xs k) (u ⟨_, h⟩) := by
        simp only [jof_Hf_smul_right, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, map_inv₀, Complex.conj_ofReal]
        have hR' : (R ⟨_, h⟩ : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
        push_cast
        have key : (2 * (Real.pi : ℂ) * (R ⟨_, h⟩ : ℂ)) ^ c * (1 / (R ⟨_, h⟩ : ℂ)) ^ c =
            (2 * Real.pi) ^ c := by
          rw [← mul_pow]; congr 1; field_simp
        linear_combination (ζ ⟨_, h⟩ * ∏ x, Hf (xs x) (u ⟨_, h⟩)) * key
      rw [e1, hnμ]
      exact hζb _ xs hxs
    · simp only [s, μ, y, dif_neg h]
      rw [Complex.norm_natCast]
      exact hAb _ _ xs hxs
  · intro j
    by_cases h : (s0 j).val < ρ
    · simp only [s, μ, dif_pos h]
      rw [hnμ]
      have hl := l2NormSq_nonneg_gaussianTorus X P.q (sT ⟨_, h⟩)
      calc P.K6⁻¹ * Real.exp (-(2 * Real.pi * Cchi (E := E) P.m * P.ph / P.q)) * X.l2 P.q (sT ⟨_, h⟩)
          ≤ P.K6⁻¹ * Real.exp (-(2 * Real.pi * ‖u ⟨_, h⟩‖ ^ 2 / P.q)) * X.l2 P.q (sT ⟨_, h⟩) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hexp _) hK6) hl
        _ ≤ (2 * Real.pi * R ⟨_, h⟩) ^ (2 * c) := hζl _
        _ = ((2 * Real.pi * R ⟨_, h⟩) ^ c) ^ 2 := by ring
    · simp only [s, μ, dif_neg h]
      rw [Complex.norm_natCast]
      have hl := l2NormSq_nonneg_gaussianTorus X P.q (sA (s0 j) (not_lt.1 h))
      calc P.K6⁻¹ * Real.exp (-(2 * Real.pi * Cchi (E := E) P.m * P.ph / P.q)) *
            X.l2 P.q (sA (s0 j) (not_lt.1 h))
          ≤ P.K6⁻¹ * X.l2 P.q (sA (s0 j) (not_lt.1 h)) :=
            mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hK6 hexp1) hl
        _ ≤ (c.factorial : ℝ) ^ 2 := hAl _ _
  · intro j
    by_cases h : (s0 j).val < ρ
    · simp only [y, dif_pos h]
      have hR := hRpos ⟨_, h⟩
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, inv_mul_le_iff₀ hR]
      have := (hc5 ⟨_, h⟩).1
      linarith
    · simp only [y, dif_neg h]
      rw [(hperp _ (not_lt.1 h)).1]
      norm_num
  ·
    have hDP := hx.2.2.2.2.2.2.1
    have hDN := hx.2.2.2.2.2.2.2.1
    let wv : Fin N → Fin i → ℂ := fun k a => Hf (e a) (bb k)
    let εc : Fin i → Fin N → ℂ := fun j k =>
      if h : (s0 j).val < ρ then (if hk : k.val < ρ then ε ⟨_, h⟩ ⟨_, hk⟩ else 0) else 0
    have hentry : ∀ a j, Hf (e a) (y j) = wv (s0 j) a + ∑ k, εc j k * wv k a := by
      intro a j
      by_cases h : (s0 j).val < ρ
      · simp only [y, dif_pos h, jof_Hf_smul_right, map_inv₀, Complex.conj_ofReal]
        have hR := hRpos ⟨_, h⟩
        have hR' : (R ⟨_, h⟩ : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
        have h4 := hc4 ⟨_, h⟩ (e a) (he_in a)
        have hws : w ⟨_, h⟩ = bb (s0 j) := (hbw (s0 j) h).symm
        have hsum : ∑ s', ε ⟨_, h⟩ s' * Hf (e a) (w s') = ∑ k, εc j k * wv k a := by
          rw [← sum_fin_le hρN (fun s' => ε ⟨_, h⟩ s' * Hf (e a) (w s'))]
          refine Finset.sum_congr rfl fun k _ => ?_
          by_cases hk : k.val < ρ
          · simp only [εc, wv, dif_pos h, dif_pos hk]
            rw [hbw k hk]
          · simp only [εc, dif_pos h, dif_neg hk, zero_mul]
        rw [← hsum]
        simp only [wv]
        rw [← hws, ← h4, div_eq_inv_mul]
      · simp only [y, dif_neg h, εc, wv, zero_mul, Finset.sum_const_zero, add_zero]
    have hmat : (Matrix.of fun a b => Hf (EuclideanSpace.single (⟨σ, Fin.castLE hi a⟩ : Idx X.dim) (1 : ℂ))
        (y b)) = Matrix.of fun a j => (wv (s0 j) + ∑ k, εc j k • wv k) a := by
      ext a j
      simp only [Matrix.of_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact hentry a j
    have hold : (Matrix.of fun a j => wv (s0 j) a).det = (M.submatrix id s0).det := rfl
    have hmax : ∀ σ' : Fin i → Fin N, ‖(Matrix.of fun a j => wv (σ' j) a).det‖ ≤ Δ :=
      fun σ' => hs0 σ'
    have hpert := hDP ℂ i (Fin N) wv s0 εc Δ hmax

    set B : ℝ := Real.sqrt ρ / (30 * ρ ^ 2) with hB
    have hB0 : 0 ≤ B := by positivity
    have hrow : ∀ j, ∑ k, ‖εc j k‖ ≤ if (s0 j).val < ρ then B else 0 := by
      intro j
      by_cases h : (s0 j).val < ρ
      · rw [if_pos h]
        have := (hεb ⟨_, h⟩).2
        rw [← sum_fin_le hρN (fun s' => ‖ε ⟨_, h⟩ s'‖)] at this
        refine le_of_eq_of_le ?_ this
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : k.val < ρ
        · simp [εc, dif_pos h, dif_pos hk]
        · simp [εc, dif_pos h, dif_neg hk]
      · rw [if_neg h]
        simp [εc, dif_neg h]
    have hprod : ∏ j, (1 + ∑ k, ‖εc j k‖) ≤ (1 + B) ^ ρ := by
      calc ∏ j, (1 + ∑ k, ‖εc j k‖)
          ≤ ∏ j, (if (s0 j).val < ρ then 1 + B else 1) := by
            refine Finset.prod_le_prod₀ (fun j _ => by positivity) fun j _ => ?_
            have := hrow j
            by_cases h : (s0 j).val < ρ
            · simp only [h, if_true] at this ⊢; linarith
            · simp only [h, if_false] at this ⊢; linarith
        _ = (1 + B) ^ (Finset.univ.filter fun j => (s0 j).val < ρ).card := by
            rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
        _ ≤ (1 + B) ^ ρ := by
            apply pow_le_pow_right₀ (by linarith)
            have : (Finset.univ.filter fun j => (s0 j).val < ρ).card ≤ (Finset.range ρ).card := by
              apply Finset.card_le_card_of_injOn (fun j => (s0 j).val)
              · intro j hj
                simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj
                simpa using hj
              · intro j _ j' _ hjj
                exact hinj (Fin.ext hjj)
            simpa using this
    have hhalf : (1 + B) ^ ρ - 1 ≤ 1 / 2 := by
      rcases Nat.eq_zero_or_pos ρ with h0 | hpos
      · subst h0; norm_num
      · have hρ1 : (1 : ℝ) ≤ ρ := by exact_mod_cast hpos
        have hnum := hDN ρ hpos
        have hBle : B ≤ (ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10 := by
          have hsq : Real.sqrt ρ * Real.sqrt ρ = ρ := Real.mul_self_sqrt (by positivity)
          have hsp : 0 < Real.sqrt ρ := Real.sqrt_pos.2 (by linarith)
          have hr : (ρ : ℝ) ^ (-(3 : ℝ) / 2) = 1 / (ρ * Real.sqrt ρ) := by
            rw [show (-(3 : ℝ) / 2) = -((1 : ℝ) + 1 / 2) by norm_num, Real.rpow_neg (by positivity),
              Real.rpow_add (by linarith), Real.rpow_one, ← Real.sqrt_eq_rpow, one_div]
          have hBeq : B = (ρ : ℝ) ^ (-(3 : ℝ) / 2) / 30 := by
            rw [hr, hB, div_div, div_eq_div_iff (by positivity) (by positivity)]
            linear_combination (30 * (ρ : ℝ)) * hsq
          have h0 : 0 ≤ (ρ : ℝ) ^ (-(3 : ℝ) / 2) := by positivity
          rw [hBeq]
          linarith
        have : (1 + B) ^ ρ ≤ (1 + (ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10) ^ ρ :=
          pow_le_pow_left₀ (by linarith) (by linarith) ρ
        linarith
    have hfac : ((∏ j, (1 + ∑ k, ‖εc j k‖)) - 1) * Δ ≤ Δ / 2 := by
      have := hΔpos.le
      nlinarith [hprod, hhalf]
    rw [hmat]
    have h2 : ‖(Matrix.of fun a j => wv (s0 j) a).det‖ = Δ := by rw [hold]
    have h4 : Δ - ‖(Matrix.of fun a j => (wv (s0 j) + ∑ k, εc j k • wv k) a).det -
        (Matrix.of fun a j => wv (s0 j) a).det‖ ≤
        ‖(Matrix.of fun a j => (wv (s0 j) + ∑ k, εc j k • wv k) a).det‖ := by
      have := norm_sub_norm_le (Matrix.of fun a j => wv (s0 j) a).det
        (Matrix.of fun a j => (wv (s0 j) + ∑ k, εc j k • wv k) a).det
      rw [h2, norm_sub_rev] at this
      linarith
    linarith [hpert, hfac, h4, hΔr]
  · intro j
    by_cases h : (s0 j).val < ρ
    · simp only [μ, dif_pos h]
      rw [← norm_ne_zero_iff, hnμ]
      have := hRpos ⟨_, h⟩
      positivity
    · simp only [μ, dif_neg h]
      exact_mod_cast Nat.factorial_ne_zero c

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.OneAddPowSubOneLe
namespace ReciprocityTheory.ChartRestriction.G.I2

theorem norm_prod_sub_prod_le {ι : Type*} (s : Finset ι) (x y : ι → ℂ) (β δ : ι → ℝ)
    (hy : ∀ i, ‖y i‖ ≤ β i) (hxy : ∀ i, ‖x i - y i‖ ≤ δ i) :
    ‖∏ i ∈ s, x i - ∏ i ∈ s, y i‖ ≤ ∏ i ∈ s, (β i + δ i) - ∏ i ∈ s, β i := by
  classical
  have hβ : ∀ i, 0 ≤ β i := fun i => (norm_nonneg _).trans (hy i)
  have hδ : ∀ i, 0 ≤ δ i := fun i => (norm_nonneg _).trans (hxy i)
  have hx : ∀ i, ‖x i‖ ≤ β i + δ i := fun i => by
    calc ‖x i‖ = ‖y i + (x i - y i)‖ := by ring_nf
      _ ≤ ‖y i‖ + ‖x i - y i‖ := norm_add_le _ _
      _ ≤ β i + δ i := add_le_add (hy i) (hxy i)
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha]
    have hX : ‖∏ i ∈ s, x i‖ ≤ ∏ i ∈ s, (β i + δ i) := by
      rw [norm_prod]
      exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hx i)
    have hP : ∏ i ∈ s, β i ≤ ∏ i ∈ s, (β i + δ i) :=
      Finset.prod_le_prod₀ (fun i _ => hβ i) (fun i _ => le_add_of_nonneg_right (hδ i))
    calc ‖x a * ∏ i ∈ s, x i - y a * ∏ i ∈ s, y i‖
        = ‖(x a - y a) * ∏ i ∈ s, x i + y a * (∏ i ∈ s, x i - ∏ i ∈ s, y i)‖ := by ring_nf
      _ ≤ ‖(x a - y a) * ∏ i ∈ s, x i‖ + ‖y a * (∏ i ∈ s, x i - ∏ i ∈ s, y i)‖ := norm_add_le _ _
      _ = ‖x a - y a‖ * ‖∏ i ∈ s, x i‖ + ‖y a‖ * ‖∏ i ∈ s, x i - ∏ i ∈ s, y i‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ δ a * ∏ i ∈ s, (β i + δ i) + β a * (∏ i ∈ s, (β i + δ i) - ∏ i ∈ s, β i) := by
          exact add_le_add (mul_le_mul (hxy a) hX (norm_nonneg _) (hδ a))
            (mul_le_mul (hy a) ih (norm_nonneg _) (hβ a))
      _ = (β a + δ a) * ∏ i ∈ s, (β i + δ i) - β a * ∏ i ∈ s, β i := by ring

theorem norm_sum_prod_sub_le {τ ι : Type*} [Fintype τ] [Fintype ι] (sg : τ → ℂ)
    (hsg : ∀ T, ‖sg T‖ ≤ 1) (D A : τ → ι → ℂ) (α δ : ι → ℝ) (hA : ∀ T k, ‖A T k‖ ≤ α k)
    (hD : ∀ T k, ‖D T k - A T k‖ ≤ δ k) :
    ‖∑ T, sg T * ∏ k, D T k - ∑ T, sg T * ∏ k, A T k‖ ≤
      Fintype.card τ * (∏ k, (α k + δ k) - ∏ k, α k) := by
  rw [← Finset.sum_sub_distrib]
  calc ‖∑ T, (sg T * ∏ k, D T k - sg T * ∏ k, A T k)‖
      ≤ ∑ T, ‖sg T * ∏ k, D T k - sg T * ∏ k, A T k‖ := norm_sum_le _ _
    _ ≤ ∑ _T : τ, (∏ k, (α k + δ k) - ∏ k, α k) := by
        refine Finset.sum_le_sum fun T _ => ?_
        rw [← mul_sub, norm_mul]
        have h := norm_prod_sub_prod_le Finset.univ (D T) (A T) α δ (hA T) (hD T)
        calc ‖sg T‖ * ‖∏ k, D T k - ∏ k, A T k‖ ≤ 1 * ‖∏ k, D T k - ∏ k, A T k‖ := by
              gcongr
              exact hsg T
          _ ≤ _ := by rw [one_mul]; exact h
    _ = Fintype.card τ * (∏ k, (α k + δ k) - ∏ k, α k) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem one_add_pow_sub_one_le (x : ℝ) (hx : 0 ≤ x) (m : ℕ) :
    (1 + x) ^ m - 1 ≤ m * x * (1 + x) ^ m := by
  induction m with
  | zero => simp
  | succ n ih =>
    have h1 : (1 : ℝ) ≤ (1 + x) ^ n := by
      have h : (1 : ℝ) ^ n ≤ (1 + x) ^ n := by gcongr; linarith
      simpa using h
    have h2 : (1 : ℝ) ≤ (1 + x) ^ n * (1 + x) := by nlinarith
    have h3 := mul_le_mul_of_nonneg_right ih (by linarith : (0 : ℝ) ≤ 1 + x)
    push_cast
    rw [pow_succ]
    nlinarith [mul_nonneg hx (sub_nonneg.2 h2)]

theorem num_bound (r D : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ε ≤ Real.exp (-((D + 1) * (r * Real.log r + 3 * r + 3)))) :
    2 * D * (4 * r) ^ D * Real.exp ((r / 2 + 1) * D) * ε ≤ 1 := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr1
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [h2]; nlinarith
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have h2D : 2 * (D : ℝ) ≤ Real.exp (2 * D) := by linarith [Real.add_one_le_exp (2 * (D : ℝ))]
  have hpow : ((4 : ℝ) * r) ^ D = Real.exp (D * Real.log (4 * r)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  have hlog : Real.log (4 * r) = Real.log 4 + Real.log r :=
    Real.log_mul (by norm_num) (by positivity)
  have hP : 2 * (D : ℝ) * (4 * r) ^ D * Real.exp ((r / 2 + 1) * D) ≤
      Real.exp ((D + 1) * (r * Real.log r + 3 * r + 3)) := by
    rw [hpow]
    calc 2 * (D : ℝ) * Real.exp (D * Real.log (4 * r)) * Real.exp ((r / 2 + 1) * D)
        ≤ Real.exp (2 * D) * Real.exp (D * Real.log (4 * r)) * Real.exp ((r / 2 + 1) * D) := by
          gcongr
      _ = Real.exp (2 * D + D * Real.log (4 * r) + (r / 2 + 1) * D) := by
          rw [Real.exp_add, Real.exp_add]
      _ ≤ Real.exp ((D + 1) * (r * Real.log r + 3 * r + 3)) := by
          apply Real.exp_le_exp.2
          rw [hlog]
          nlinarith [mul_nonneg hD0 (mul_nonneg (sub_nonneg.2 hr1) hlogr),
            mul_nonneg hD0 (sub_nonneg.2 hlog4), mul_nonneg hD0 (sub_nonneg.2 hr1),
            mul_nonneg hr0.le hlogr]
  calc 2 * (D : ℝ) * (4 * r) ^ D * Real.exp ((r / 2 + 1) * D) * ε
      ≤ Real.exp ((D + 1) * (r * Real.log r + 3 * r + 3)) *
          Real.exp (-((D + 1) * (r * Real.log r + 3 * r + 3))) :=
        mul_le_mul hP hε hε0 (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

theorem eps_bound (g d : ℕ) (t K : ℝ) (h : g * Real.log 2 + 2 * d + 3 + K ≤ t) :
    7 * 2 ^ g * (4.3 : ℝ) ^ d * Real.exp (-t) ≤ Real.exp (-K) := by
  have he1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h7 : (7 : ℝ) ≤ Real.exp 3 := by
    have e : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    calc (7 : ℝ) ≤ 2.7182818283 ^ 3 := by norm_num
      _ ≤ Real.exp 1 ^ 3 := by gcongr
  have h43 : (4.3 : ℝ) ≤ Real.exp 2 := by
    have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    calc (4.3 : ℝ) ≤ 2.7182818283 ^ 2 := by norm_num
      _ ≤ Real.exp 1 ^ 2 := by gcongr
  have h2g : (2 : ℝ) ^ g = Real.exp (g * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have h43d : (4.3 : ℝ) ^ d ≤ Real.exp (d * 2) := by
    rw [Real.exp_nat_mul]
    gcongr
  calc 7 * 2 ^ g * (4.3 : ℝ) ^ d * Real.exp (-t)
      ≤ Real.exp 3 * Real.exp (g * Real.log 2) * Real.exp (d * 2) * Real.exp (-t) := by
        rw [h2g]; gcongr
    _ = Real.exp (3 + g * Real.log 2 + d * 2 + -t) := by simp only [Real.exp_add]
    _ ≤ Real.exp (-K) := Real.exp_le_exp.2 (by linarith)

end ReciprocityTheory.ChartRestriction.G.I2
end

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField

noncomputable section

variable {E : Type} [Field E] [NumberField E] {n nb : ℕ}

section Count
variable {dim : (E →+* ℂ) → ℕ} (bs : Fin nb → Block E n dim)

theorem c_le_DF (j : Fin nb) (hi : 1 ≤ (bs j).i) : (bs j).c ≤ DF bs := by
  unfold DF
  exact le_trans (Nat.le_mul_of_pos_left _ hi)
    (Finset.single_le_sum (f := fun j => (bs j).i * (bs j).c) (fun j _ => Nat.zero_le _) (Finset.mem_univ j))

theorem card_choice_le (r : ℕ) (hr : ∀ j, (bs j).i ≤ r) :
    Fintype.card (Choice bs) ≤ r ^ DF bs := by
  unfold DF
  rw [Fintype.card_pi, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _)
  intro j _
  rw [Fintype.card_fun, Fintype.card_perm, Fintype.card_fin, Fintype.card_fin, pow_mul]
  exact Nat.pow_le_pow_left (le_trans (Nat.factorial_le_pow _) (Nat.pow_le_pow_left (hr j) _)) _

theorem prod_two_pow :
    ∏ p : (Σ j : Fin nb, Fin (bs j).i), (2 : ℝ) ^ (bs p.1).c = 2 ^ DF bs := by
  rw [Fintype.prod_sigma]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  unfold DF
  congr 1
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

theorem card_pos_le : Fintype.card (Σ j : Fin nb, Fin (bs j).i) ≤ DF bs := by
  rw [Fintype.card_sigma]
  unfold DF
  exact Finset.sum_le_sum (fun j _ => by rw [Fintype.card_fin]; exact Nat.le_mul_of_pos_right _ (bs j).hc)

theorem card_pos_pos (h : 1 ≤ DF bs) : 1 ≤ Fintype.card (Σ j : Fin nb, Fin (bs j).i) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  by_contra hc
  push_neg at hc
  have h0 : ∀ j, (bs j).i = 0 := by
    intro j
    have := Finset.single_le_sum (f := fun j => (bs j).i) (fun j _ => Nat.zero_le _) (Finset.mem_univ j)
    omega
  unfold DF at h
  simp [h0] at h

theorem prod_det_ge (d : ∀ j : Fin nb, ℝ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hd : ∀ j, 1 ≤ (bs j).i → δ ≤ d j) (hd1 : ∀ j, (bs j).i = 0 → d j = 1) :
    δ ^ DF bs ≤ ∏ j, d j ^ (bs j).c := by
  unfold DF
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod₀ (fun j _ => pow_nonneg hδ0 _)
  intro j _
  by_cases hi : (bs j).i = 0
  · rw [hi, zero_mul, pow_zero, hd1 j hi, one_pow]
  · have hi1 : 1 ≤ (bs j).i := Nat.one_le_iff_ne_zero.mpr hi
    calc δ ^ ((bs j).i * (bs j).c) ≤ δ ^ (bs j).c :=
          pow_le_pow_of_le_one hδ0 hδ1 (Nat.le_mul_of_pos_left _ hi1)
      _ ≤ d j ^ (bs j).c := pow_le_pow_left₀ hδ0 (hd j hi1) _

end Count

section Data
variable [IsCMField E] (X : PT E) (bs : Fin nb → Block E n X.dim)

open Classical in
theorem block_data_all (hx : Ext.All) (hc : CharStatement) (ht : ColTorusStatement)
    (ha : ColAbelStatement) (P : Par X (DF bs)) (I : Submodule ℤ (Vsp X.dim)) (hI : IsSplit P I)
    (j : Fin nb) :
    ∃ (y : Fin (bs j).i → Vsp X.dim) (s : Fin (bs j).i → (Fin 1 → Vsp X.dim) → ℂ)
      (μ : Fin (bs j).i → ℂ),
      (∀ b, s b ∈ X.Sec P.q 1) ∧
      (∀ b (xs : Fin (bs j).c → Vsp X.dim), (∀ k, InPart (bs j).τ (xs k) ∧ ‖xs k‖ = 1) →
        ‖d1 (s b) (bs j).c xs - μ b * ∏ k, Hf (xs k) (y b)‖ ≤ P.eps1 * ‖μ b‖) ∧
      (∀ b, P.K6⁻¹ * Real.exp (-(2 * Real.pi * Cchi (E := E) P.m * P.ph / P.q)) * X.l2 P.q (s b) ≤
        ‖μ b‖ ^ 2) ∧
      (∀ b, ‖y b‖ ≤ 2) ∧
      (2 : ℝ) ^ (-(X.r : ℝ) / 2) / 2 ≤
        ‖(Matrix.of fun a b => Hf (EuclideanSpace.single
          (⟨(bs j).τ, Fin.castLE (bs j).hi a⟩ : Idx X.dim) (1 : ℂ)) (y b)).det‖ ∧
      (∀ b, μ b ≠ 0) := by
  rcases Nat.eq_zero_or_pos (bs j).i with h0 | hpos
  · haveI : IsEmpty (Fin (bs j).i) := by rw [h0]; infer_instance
    refine ⟨isEmptyElim, isEmptyElim, isEmptyElim, isEmptyElim, fun b => isEmptyElim b,
      isEmptyElim, isEmptyElim, ?_, isEmptyElim⟩
    rw [Matrix.det_isEmpty, norm_one]
    have h1 : (2 : ℝ) ^ (-(X.r : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by
        have := Nat.cast_nonneg (α := ℝ) X.r; linarith)
    linarith
  · exact block_data hx hc ht ha X P I hI (bs j).τ (bs j).i (bs j).hi (bs j).c (c_le_DF bs j hpos)

end Data

end

end ReciprocityTheory.ChartRestriction.G.I2
