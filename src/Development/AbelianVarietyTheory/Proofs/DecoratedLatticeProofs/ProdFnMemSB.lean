module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LinearIndependentWave

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdFnMemSB
open GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.LocFlat.CFac

def prodFn {X Y : Type} (f : X → ℂ) (g : Y → ℂ) : X × Y → ℂ := fun p => f p.1 * g p.2

theorem prodFn_mem_SB {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {f : X → ℂ} {g : Y → ℂ}
    (hf : f ∈ SB X) (hg : g ∈ SB Y) : prodFn f g ∈ SB (X × Y) := by
  refine ⟨(hf.1.comp_continuous continuous_fst).mul (hg.1.comp_continuous continuous_snd), ?_⟩
  refine HasCompactSupport.intro' (IsCompact.prod hf.2 hg.2) ((isClosed_tsupport _).prod (isClosed_tsupport _)) ?_
  intro p hp
  simp only [Set.mem_prod, not_and_or] at hp
  rcases hp with h | h
  · simp [prodFn, image_eq_zero_of_notMem_tsupport h]
  · simp [prodFn, image_eq_zero_of_notMem_tsupport h]

def prodSB {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : SB X) (g : SB Y) : SB (X × Y) :=
  ⟨prodFn f.1 g.1, prodFn_mem_SB f.2 g.2⟩

@[simp] theorem prodSB_apply {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : SB X) (g : SB Y) (p : X × Y) :
    (prodSB f g).1 p = f.1 p.1 * g.1 p.2 := rfl

def comapH {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) : SB Y →ₗ[ℂ] SB X where
  toFun F := ⟨fun x => F.1 (e x), F.2.1.comp_continuous e.continuous, F.2.2.comp_homeomorph e⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem comapH_apply {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (F : SB Y) (x : X) :
    (comapH e F).1 x = F.1 (e x) := rfl

def mulLC {X : Type} [TopologicalSpace X] (φ : X → ℂ) (hφ : IsLocallyConstant φ) : SB X →ₗ[ℂ] SB X where
  toFun F := ⟨fun x => φ x * F.1 x, hφ.mul F.2.1, F.2.2.mul_left⟩
  map_add' F G := by ext x; simp [mul_add]
  map_smul' c F := by ext x; simp; ring

@[simp] theorem mulLC_apply {X : Type} [TopologicalSpace X] (φ : X → ℂ) (hφ : IsLocallyConstant φ) (F : SB X) (x : X) :
    (mulLC φ hφ F).1 x = φ x * F.1 x := rfl

end GlobalTheory.LocFlat.CFac
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixIntegralOfAddCharTraceDual
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixIntegralOfAddCharTraceDual
open ValuativeRel GlobalTheory.SplitWeil Matrix

noncomputable section
namespace GlobalTheory.CharDualMat

private lemma half_lt_re_of_norm_eq_one_of_norm_sub_one_lt {w : ℂ} (hw : ‖w‖ = 1) (h : ‖w - 1‖ < 1) :
    1 / 2 < w.re := by
  have h1 : w.re ^ 2 + w.im ^ 2 = 1 := by
    have := Complex.sq_norm w
    rw [hw, Complex.normSq_apply] at this
    nlinarith
  have h2 : (w.re - 1) ^ 2 + w.im ^ 2 < 1 := by
    have := Complex.sq_norm (w - 1)
    rw [Complex.normSq_apply] at this
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at this
    have h0 : ‖w - 1‖ ^ 2 < 1 := by
      have := norm_nonneg (w - 1)
      nlinarith
    nlinarith
  nlinarith

theorem _root_.GlobalTheory.CharDualMat.circle_eq_one_of_pow_near (z : Circle) (h : ∀ n : ℕ, ‖(z : ℂ) ^ n - 1‖ < 1) :
    z = 1 := by
  have hnorm : ∀ m : ℕ, ‖(z : ℂ) ^ (2 ^ m)‖ = 1 := fun m => by
    rw [norm_pow, Circle.norm_coe, one_pow]
  have hre : ∀ m : ℕ, 1 / 2 < ((z : ℂ) ^ (2 ^ m)).re := fun m =>
    half_lt_re_of_norm_eq_one_of_norm_sub_one_lt (hnorm m) (h _)
  have hsq : ∀ m : ℕ, ((z : ℂ) ^ (2 ^ m)).re ^ 2 + ((z : ℂ) ^ (2 ^ m)).im ^ 2 = 1 := fun m => by
    have := Complex.sq_norm ((z : ℂ) ^ (2 ^ m))
    rw [hnorm m, Complex.normSq_apply] at this
    nlinarith
  have hstep : ∀ m : ℕ, ((z : ℂ) ^ (2 ^ (m + 1))).re =
      ((z : ℂ) ^ (2 ^ m)).re ^ 2 - ((z : ℂ) ^ (2 ^ m)).im ^ 2 := fun m => by
    rw [pow_succ, pow_mul, sq, Complex.mul_re]
    ring
  have hgrow : ∀ m : ℕ, 3 ^ m * (1 - (z : ℂ).re) ≤ 1 - ((z : ℂ) ^ (2 ^ m)).re := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [hstep m, pow_succ]
      have hr := hre m
      have hs := hsq m
      have hle : ((z : ℂ) ^ (2 ^ m)).re ≤ 1 := by nlinarith [sq_nonneg ((z : ℂ) ^ (2 ^ m)).im]
      nlinarith
  have hd0 : (z : ℂ).re = 1 := by
    have hle : (z : ℂ).re ≤ 1 := by
      have := hsq 0
      simp only [pow_zero, pow_one] at this
      nlinarith [sq_nonneg (z : ℂ).im]
    by_contra hne
    have hpos : 0 < 1 - (z : ℂ).re := by
      rcases lt_or_eq_of_le hle with hlt | heq
      · linarith
      · exact absurd heq hne
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / (1 - (z : ℂ).re)) (by norm_num : (1 : ℝ) < 3)
    have h1 := hgrow n
    have h2 := hre n
    rw [div_lt_iff₀ hpos] at hn
    linarith
  have him : (z : ℂ).im = 0 := by
    have := hsq 0
    simp only [pow_zero, pow_one, hd0] at this
    nlinarith [sq_nonneg (z : ℂ).im]
  apply Circle.ext_iff.mpr
  apply Complex.ext <;> simp [hd0, him]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem _root_.GlobalTheory.CharDualMat.valuation_nsmul_le (t : k) (n : ℕ) : valuation k (n • t) ≤ valuation k t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul]
    exact ((valuation k).map_add _ _).trans (max_le ih le_rfl)

theorem _root_.GlobalTheory.CharDualMat.exists_ball_trivial (ψ : AddChar k Circle) (hψ : Continuous ψ) :
    ∃ γ : ValueGroupWithZero k, γ ≠ 0 ∧ ∀ t : k, valuation k t < γ → ψ t = 1 := by
  have hopen : IsOpen (ψ ⁻¹' {w : Circle | ‖(w : ℂ) - 1‖ < 1}) :=
    (isOpen_lt (by fun_prop) continuous_const).preimage hψ
  have hzero : (0 : k) ∈ ψ ⁻¹' {w : Circle | ‖(w : ℂ) - 1‖ < 1} := by
    simp [AddChar.map_zero_eq_one]
  obtain ⟨γ, hγ, hsub⟩ :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.1 (hopen.mem_nhds hzero)
  refine ⟨γ, hγ, fun t ht => ?_⟩
  apply _root_.GlobalTheory.CharDualMat.circle_eq_one_of_pow_near
  intro n
  have hmem : n • t ∈ ψ ⁻¹' {w : Circle | ‖(w : ℂ) - 1‖ < 1} :=
    hsub (lt_of_le_of_lt (_root_.GlobalTheory.CharDualMat.valuation_nsmul_le t n) ht)
  rw [Set.mem_preimage, AddChar.map_nsmul_eq_pow] at hmem
  simpa using hmem

theorem _root_.GlobalTheory.CharDualMat.mem_integer_of_dual (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (hne : ψ ≠ 1) (a : k)
    (h : ∀ s : k, (∀ u : k, u ∈ 𝒪[k] → ψ (s * u) = 1) → ψ (s * a) = 1) : a ∈ 𝒪[k] := by
  by_contra ha
  have hva : 1 < valuation k a := by
    rw [Valuation.mem_integer_iff] at ha
    exact not_le.1 ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hva
  obtain ⟨γ, hγ, hball⟩ := _root_.GlobalTheory.CharDualMat.exists_ball_trivial ψ hψ
  have hmul : ∀ s : k, (∀ u : k, u ∈ 𝒪[k] → ψ (s * u) = 1) →
      ∀ u : k, u ∈ 𝒪[k] → ψ (s * a * u) = 1 := by
    intro s hs u hu
    have := h (s * u) (fun u' hu' => by rw [mul_assoc]; exact hs _ (mul_mem hu hu'))
    rw [mul_right_comm]
    exact this
  have hpow : ∀ n : ℕ, ∀ s : k, (∀ u : k, u ∈ 𝒪[k] → ψ (s * u) = 1) →
      ∀ u : k, u ∈ 𝒪[k] → ψ (s * a ^ n * u) = 1 := by
    intro n
    induction n with
    | zero => intro s hs; simpa using hs
    | succ n ih => intro s hs; rw [pow_succ, ← mul_assoc]; exact hmul _ (ih s hs)
  apply hne
  ext t
  obtain ⟨n, hn⟩ := MulArchimedean.arch (valuation k t * γ⁻¹) hva
  have hlt : valuation k t * γ⁻¹ < valuation k a ^ (n + 1) :=
    lt_of_le_of_lt hn (pow_lt_pow_right₀ hva n.lt_succ_self)
  have hapos : valuation k a ^ (n + 1) ≠ 0 := pow_ne_zero _ (by simpa using ha0)
  have hlt' : valuation k t < γ * valuation k a ^ (n + 1) := by
    calc valuation k t = valuation k t * γ⁻¹ * γ := (inv_mul_cancel_right₀ hγ _).symm
      _ < valuation k a ^ (n + 1) * γ := mul_lt_mul_of_pos_right hlt (zero_lt_iff.2 hγ)
      _ = γ * valuation k a ^ (n + 1) := mul_comm _ _
  have hs : ∀ u : k, u ∈ 𝒪[k] → ψ (t * (a ^ (n + 1))⁻¹ * u) = 1 := by
    intro u hu
    apply hball
    rw [Valuation.mem_integer_iff] at hu
    rw [map_mul, map_mul, map_inv₀, map_pow]
    calc valuation k t * (valuation k a ^ (n + 1))⁻¹ * valuation k u
        ≤ valuation k t * (valuation k a ^ (n + 1))⁻¹ := mul_le_of_le_one_right' hu
      _ < γ := mul_inv_lt_of_lt_mul₀ hlt'
  have := hpow (n + 1) _ hs 1 (one_mem _)
  rw [mul_one, inv_mul_cancel_right₀ (pow_ne_zero _ ha0)] at this
  rw [this, AddChar.one_apply]

theorem _root_.GlobalTheory.CharDualMat.integral_of_dual (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (Y Y' : Type) [Fintype Y] [Fintype Y'] (ψk : AddChar k Circle)
    (hψ : Continuous ψk) (hne : ψk ≠ 1) (x : Matrix Y Y' k)
    (hx : ∀ b : Matrix Y Y' k, (∀ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) →
      ψk (∑ r, ∑ q, b r q * u r q) = 1) → ψk (∑ r, ∑ q, b r q * x r q) = 1)
    (r₀ : Y) (q₀ : Y') : x r₀ q₀ ∈ 𝒪[k] := by
  classical
  refine _root_.GlobalTheory.CharDualMat.mem_integer_of_dual ψk hψ hne (x r₀ q₀) (fun s hs => ?_)
  let b : Matrix Y Y' k := fun r q => if r = r₀ ∧ q = q₀ then s else 0
  have key : ∀ y : Matrix Y Y' k, ∑ r, ∑ q, b r q * y r q = s * y r₀ q₀ := by
    intro y
    rw [Finset.sum_eq_single r₀ (fun r _ hr => Finset.sum_eq_zero fun q _ => by simp [b, hr])
      (by simp), Finset.sum_eq_single q₀ (fun q _ hq => by simp [b, hq]) (by simp)]
    simp [b]
  have := hx b (fun u hu => by rw [key]; exact hs _ (hu r₀ q₀))
  rwa [key] at this

end GlobalTheory.CharDualMat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixIntegralOfAddCharTraceDualStatement
open ValuativeRel GlobalTheory.SplitWeil Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_integral_of_addChar_trace_dual : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Y Y' : Type) [Fintype Y] [Fintype Y'] (ψk : AddChar k Circle), Continuous ψk → ψk ≠ 1 → ∀ x : Matrix Y Y' k, (∀ b : Matrix Y Y' k, (∀ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) → ψk (∑ r, ∑ q, b r q * u r q) = 1) → ψk (∑ r, ∑ q, b r q * x r q) = 1) → ∀ r q, x r q ∈ 𝒪[k] := by
  first | exact @GlobalTheory.CharDualMat.integral_of_dual | exact GlobalTheory.CharDualMat.integral_of_dual | (intros; apply GlobalTheory.CharDualMat.integral_of_dual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNeZeroOfEventually
open ValuativeRel GlobalTheory.SplitWeil Matrix

noncomputable section
namespace GlobalTheory.SBUnif

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_nat_mem_mul_integer (c : k) (hc : c ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ c⁻¹ * (n : k) ∈ 𝒪[k] := by
  let S : AddSubgroup k := (𝒪[k].toAddSubgroup).comap (AddMonoidHom.mulLeft c⁻¹)
  let H : AddSubgroup 𝒪[k] := S.comap (𝒪[k].subtype.toAddMonoidHom)
  have hS : IsOpen (S : Set k) :=
    (Valuation.isOpen_integer (v := valuation k)).preimage (continuous_const.mul continuous_id)
  have hH : IsOpen (H : Set 𝒪[k]) := hS.preimage continuous_subtype_val
  let H' : OpenAddSubgroup 𝒪[k] := ⟨H, hH⟩
  have : Finite (𝒪[k] ⧸ H) := AddSubgroup.instFiniteQuotientOfSeparatelyContinuousAddOfCompactSpace H'
  have hne : H.index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
  refine ⟨H.index, Nat.pos_of_ne_zero hne, ?_⟩
  have hm := H.nsmul_index_mem (1 : 𝒪[k])
  simpa [H, S] using hm

theorem exists_ne_zero_of_eventually {P : k → Prop} (h : ∀ᶠ s in nhds (0 : k), P s) :
    ∃ c : k, c ≠ 0 ∧ P c := by
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).1 h
  obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero k)
  obtain ⟨w, hw0, hw1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp only [map_zero] at ha
    exact γ.ne_zero ha.symm
  refine ⟨a * w, mul_ne_zero ha0 hw0, hγ ?_⟩
  show valuation k (a * w) < γ
  rw [map_mul, ha]
  calc (γ : ValueGroupWithZero k) * valuation k w < γ * 1 :=
        mul_lt_mul_of_pos_left hw1 (zero_lt_iff.mpr γ.ne_zero)
    _ = γ := mul_one _

end GlobalTheory.SBUnif

namespace GlobalTheory.SBUnif

theorem sb_lattice_bounds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (Y Y' : Type) [Fintype Y] [Fintype Y'] (Φ : Matrix Y Y' k → ℂ), Φ ∈ SB (Matrix Y Y' k) → ∃ n : ℕ, 0 < n ∧ (∀ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) → ∀ t, Φ (t + n • u) = Φ t) ∧ ∀ t, Φ t ≠ 0 → ∀ r q, (n • t) r q ∈ 𝒪[k] := by
  intro k _ _ _ _ _ Y Y' _ _ Φ hΦ
  obtain ⟨hlc, hcs⟩ := hΦ
  set O : Set (Matrix Y Y' k) := {u | ∀ r q, u r q ∈ 𝒪[k]} with hOdef
  have hOpi : O = Set.univ.pi (fun _ : Y => Set.univ.pi (fun _ : Y' => (𝒪[k] : Set k))) := by
    ext u
    constructor
    · intro h r _ q _
      exact h r q
    · intro h r q
      exact h r (Set.mem_univ _) q (Set.mem_univ _)
  have hOc : IsCompact O := by
    rw [hOpi]
    exact isCompact_univ_pi (fun _ => isCompact_univ_pi
      (fun _ => (isCompact_iff_compactSpace (s := (𝒪[k] : Set k))).mpr
        (inferInstanceAs (CompactSpace 𝒪[k]))))
  have hOo : IsOpen O := by
    rw [hOpi]
    exact isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_set_pi Set.finite_univ
      (fun _ _ => Valuation.isOpen_integer (v := valuation k)))
  have hK : IsCompact (tsupport Φ) := hcs
  have h1 : ∀ᶠ s in nhds (0 : k), ∀ p ∈ tsupport Φ ×ˢ O, Φ (p.1 + s • p.2) = Φ p.1 := by
    apply (hK.prod hOc).eventually_forall_of_forall_eventually
    intro p _
    have hc : Continuous (fun z : k × (Matrix Y Y' k × Matrix Y Y' k) => z.2.1 + z.1 • z.2.2) := by
      fun_prop
    have e1 := (hlc.comp_continuous hc).eventually_eq (0, p)
    have e2 := (hlc.comp_continuous (continuous_fst.comp continuous_snd)).eventually_eq
      ((0 : k), p)
    filter_upwards [e1, e2] with z hz1 hz2
    simp only [Function.comp_apply, zero_smul, add_zero] at hz1 hz2
    rw [hz1, hz2]
  have h2 : ∀ᶠ s in nhds (0 : k), ∀ t ∈ tsupport Φ, s • t ∈ O := by
    apply hK.eventually_forall_of_forall_eventually
    intro t _
    have hc : Continuous (fun z : k × Matrix Y Y' k => z.1 • z.2) := by fun_prop
    have h0 : (fun z : k × Matrix Y Y' k => z.1 • z.2) ((0 : k), t) ∈ O := by
      simp only [zero_smul]
      intro r q
      simp
    exact hc.continuousAt.preimage_mem_nhds (hOo.mem_nhds h0)
  obtain ⟨c, hc0, hc1, hc2⟩ := exists_ne_zero_of_eventually (h1.and h2)
  obtain ⟨n, hn, hy⟩ := exists_nat_mem_mul_integer c hc0
  set y := c⁻¹ * (n : k) with hydef
  have hn' : (n : k) = c * y := by
    rw [hydef, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  have hsmul : ∀ u : Matrix Y Y' k, n • u = c • (y • u) := by
    intro u
    rw [smul_smul, ← hn', Nat.cast_smul_eq_nsmul]
  have hyO : ∀ u ∈ O, y • u ∈ O := fun u hu r q => by
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact mul_mem hy (hu r q)
  refine ⟨n, hn, ?_, ?_⟩
  · intro u hu t
    rw [hsmul]
    have hu' : y • u ∈ O := hyO u hu
    by_cases ht : t ∈ tsupport Φ
    · exact hc1 (t, y • u) ⟨ht, hu'⟩
    by_cases ht' : t + c • (y • u) ∈ tsupport Φ
    · have hneg : -(y • u) ∈ O := fun r q => by
        simp only [Matrix.neg_apply]
        exact neg_mem (hu' r q)
      have := hc1 (t + c • (y • u), -(y • u)) ⟨ht', hneg⟩
      simp only [smul_neg, add_neg_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport ht', image_eq_zero_of_notMem_tsupport ht]
  · intro t ht r q
    have htK : t ∈ tsupport Φ := subset_tsupport _ ht
    rw [hsmul, smul_comm]
    exact hyO _ (hc2 t htK) r q

end GlobalTheory.SBUnif
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DivisiblePontryaginAnnihilatorDuality
namespace GlobalTheory.DualTransfer

theorem exists_hom {A B : Type} [AddCommGroup A] [AddCommGroup B] (e : A → B → ℂ)
    (h1 : ∀ a a' b, e (a + a') b = e a b * e a' b) (h2 : ∀ a b b', e a (b + b') = e a b * e a b')
    (h3 : ∀ b, e 0 b = 1) (h4 : ∀ a, e a 0 = 1) (M : AddSubgroup A)
    (hM : ∀ a ∈ M, ∀ b, e a b = 1) :
    ∃ f : B →+ AddChar (A ⧸ M) ℂ, ∀ b (a : A), f b (a : A ⧸ M) = e a b := by
  have key : ∀ b (a a' : A), -a + a' ∈ M → e a b = e a' b := by
    intro b a a' h
    have ha : a' = a + (-a + a') := by abel
    rw [ha, h1, hM _ h b, mul_one]
  let ψ : B → AddChar (A ⧸ M) ℂ := fun b =>
    { toFun := fun q => Quotient.liftOn' q (fun a => e a b)
        (fun a a' h => key b a a' (QuotientAddGroup.leftRel_apply.mp h))
      map_zero_eq_one' := h3 b
      map_add_eq_mul' := by
        intro q q'
        obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
        obtain ⟨a', rfl⟩ := QuotientAddGroup.mk_surjective q'
        exact h1 a a' b }
  refine ⟨{ toFun := ψ, map_zero' := ?_, map_add' := ?_ }, ?_⟩
  · ext q
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact h4 a
  · intro b b'
    ext q
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact h2 a b b'
  · intro b a
    rfl

theorem card_range {A B : Type} [AddCommGroup A] [AddCommGroup B] (e : A → B → ℂ)
    (M : AddSubgroup A) (K : AddSubgroup B) (hK : ∀ b, b ∈ K ↔ ∀ a, e a b = 1)
    (f : B →+ AddChar (A ⧸ M) ℂ) (hf : ∀ b (a : A), f b (a : A ⧸ M) = e a b) :
    Nat.card f.range = Nat.card (B ⧸ K) := by
  have hker : f.ker = K := by
    ext b
    rw [AddMonoidHom.mem_ker, hK, AddChar.eq_zero_iff]
    constructor
    · intro h a
      rw [← hf]
      exact h _
    · intro h q
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
      rw [hf]
      exact h a
  rw [← hker]
  exact (Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv).symm

theorem exists_separating {A B : Type} [AddCommGroup A] [AddCommGroup B] (e : A → B → ℂ)
    (h1 : ∀ a a' b, e (a + a') b = e a b * e a' b) (h2 : ∀ a b b', e a (b + b') = e a b * e a b')
    (h3 : ∀ b, e 0 b = 1) (h4 : ∀ a, e a 0 = 1) (M : AddSubgroup A) (K : AddSubgroup B)
    [Finite (A ⧸ M)] [Finite (B ⧸ K)]
    (hM : ∀ a, a ∈ M ↔ ∀ b, e a b = 1) (hK : ∀ b, b ∈ K ↔ ∀ a, e a b = 1)
    (H : AddSubgroup A) (hMH : M ≤ H) (x : A) (hx : x ∉ H) :
    ∃ b, (∀ u ∈ H, e u b = 1) ∧ e x b ≠ 1 := by
  classical
  obtain ⟨f, hf⟩ := exists_hom e h1 h2 h3 h4 M (fun a ha b => (hM a).mp ha b)
  obtain ⟨f', hf'⟩ := exists_hom (fun b a => e a b) (fun b b' a => h2 a b b')
    (fun b a a' => h1 a a' b) (fun b => h4 b) (fun a => h3 a) K (fun b hb a => (hK b).mp hb a)
  have c1 := card_range e M K hK f hf
  have c2 := card_range (fun b a => e a b) K M hM f' hf'
  have : Fintype (A ⧸ M) := Fintype.ofFinite _
  have : Fintype (B ⧸ K) := Fintype.ofFinite _
  have cA : Nat.card (AddChar (A ⧸ M) ℂ) = Nat.card (A ⧸ M) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]
  have cB : Nat.card (AddChar (B ⧸ K) ℂ) = Nat.card (B ⧸ K) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]
  have le1 : Nat.card f.range ≤ Nat.card (AddChar (A ⧸ M) ℂ) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  have le2 : Nat.card f'.range ≤ Nat.card (AddChar (B ⧸ K) ℂ) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  have htop : f.range = ⊤ := AddSubgroup.eq_top_of_card_eq _ (by omega)
  set r := QuotientAddGroup.map M H (AddMonoidHom.id A) (fun a ha => hMH ha) with hr
  have : Finite (A ⧸ H) := Finite.of_surjective r (fun q => by
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact ⟨(a : A ⧸ M), rfl⟩)
  have hx0 : (x : A ⧸ H) ≠ 0 := by
    rwa [Ne, QuotientAddGroup.eq_zero_iff]
  obtain ⟨ψ0, hψ0⟩ := AddChar.exists_apply_ne_zero.mpr hx0
  have hmem : ψ0.compAddMonoidHom r ∈ f.range := by
    rw [htop]
    exact AddSubgroup.mem_top _
  obtain ⟨b, hb⟩ := hmem
  refine ⟨b, fun u hu => ?_, ?_⟩
  · rw [← hf b u, hb, AddChar.compAddMonoidHom_apply]
    have hu0 : (u : A ⧸ H) = 0 := (QuotientAddGroup.eq_zero_iff u).mpr hu
    show ψ0 (u : A ⧸ H) = 1
    rw [hu0]
    exact ψ0.map_zero_eq_one
  · rw [← hf b x, hb, AddChar.compAddMonoidHom_apply]
    exact hψ0

theorem finite_quot {G : Type} [AddCommGroup G] (A L₀ : AddSubgroup G) (N : ℕ) (hN : 0 < N)
    (tf : Function.Injective fun t : G => N • t)
    (hA : ∀ t ∈ A, N • t ∈ L₀)
    (fin : ∀ k : ℕ, 0 < k → ∃ R : Set G, R.Finite ∧ ∀ t ∈ L₀, ∃ r ∈ R, ∃ u ∈ L₀, t = r + k • u) :
    Finite (A ⧸ (L₀.map (nsmulAddMonoidHom N)).addSubgroupOf A) := by
  classical
  obtain ⟨R, hR, hcov⟩ := fin (N * N) (Nat.mul_pos hN hN)
  set S := (L₀.map (nsmulAddMonoidHom N)).addSubgroupOf A with hS
  let c : G → A ⧸ S := fun r =>
    if h : ∃ t : A, ∃ u ∈ L₀, N • (t : G) = r + (N * N) • u then
      ((Classical.choose h : A) : A ⧸ S) else 0
  have key : ∀ t : A, ∃ r ∈ R, c r = (t : A ⧸ S) := by
    intro t
    obtain ⟨r, hr, u, hu, htu⟩ := hcov _ (hA t t.2)
    have h : ∃ t : A, ∃ u ∈ L₀, N • (t : G) = r + (N * N) • u := ⟨t, u, hu, htu⟩
    refine ⟨r, hr, ?_⟩
    simp only [c, dif_pos h]
    obtain ⟨u', hu', ht'⟩ := Classical.choose_spec h
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map]
    refine ⟨u - u', L₀.sub_mem hu hu', ?_⟩
    apply tf
    show N • (N • (u - u')) = N • (((-Classical.choose h + t : A)) : G)
    rw [AddSubgroup.coe_add, AddSubgroup.coe_neg, smul_add, smul_neg, htu, ht', smul_smul, smul_sub]
    abel
  have hfin : Set.Finite (Set.univ : Set (A ⧸ S)) := by
    refine (hR.image c).subset ?_
    intro q _
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨r, hr, hc⟩ := key t
    exact ⟨r, hr, hc⟩
  exact Set.finite_univ_iff.mp hfin

theorem mem_of_double_annihilator : ∀ {G : Type} [AddCommGroup G] (χ : G → G → ℂ), GlobalTheory.PlaceModel.IsBichar χ → ∀ (X Y L₀ L₀' L : AddSubgroup G), L₀ ≤ X → L₀' ≤ Y → L ≤ X → (∀ u ∈ L₀, ∀ y ∈ L₀', χ u y = 1) → (∀ x ∈ X, (∀ y ∈ L₀', χ x y = 1) → x ∈ L₀) → (∀ y ∈ Y, (∀ u ∈ L₀, χ u y = 1) → y ∈ L₀') → (∀ k : ℕ, 0 < k → ∀ x ∈ X, ∃ x' ∈ X, k • x' = x) → (∀ k : ℕ, 0 < k → ∀ y ∈ Y, ∃ y' ∈ Y, k • y' = y) → (∀ k : ℕ, 0 < k → Function.Injective fun t : G => k • t) → (∀ k : ℕ, 0 < k → ∃ R : Set G, R.Finite ∧ ∀ t ∈ L₀, ∃ r ∈ R, ∃ u ∈ L₀, t = r + k • u) → (∀ k : ℕ, 0 < k → ∃ R : Set G, R.Finite ∧ ∀ t ∈ L₀', ∃ r ∈ R, ∃ u ∈ L₀', t = r + k • u) → ∀ N : ℕ, 0 < N → (∀ u ∈ L₀, N • u ∈ L) → (∀ u ∈ L, N • u ∈ L₀) → ∀ x ∈ X, N • x ∈ L₀ → (∀ y ∈ Y, (∀ u ∈ L, χ u y = 1) → χ x y = 1) → x ∈ L := by
  intro G _ χ hχ X Y L₀ L₀' L hL₀ hL₀' hL hortho hX hY dX dY tf fin0 fin0' N hN hNL hLN x hx hNx hxY
  by_contra hxL
  set P : AddSubgroup G := X ⊓ L₀.comap (nsmulAddMonoidHom N) with hP
  set Q : AddSubgroup G := Y ⊓ L₀'.comap (nsmulAddMonoidHom N) with hQ
  have memP : ∀ t, t ∈ P ↔ t ∈ X ∧ N • t ∈ L₀ := fun t => Iff.rfl
  have memQ : ∀ t, t ∈ Q ↔ t ∈ Y ∧ N • t ∈ L₀' := fun t => Iff.rfl
  set M := (L₀.map (nsmulAddMonoidHom N)).addSubgroupOf P with hM
  set K := (L₀'.map (nsmulAddMonoidHom N)).addSubgroupOf Q with hK
  have fM : Finite (P ⧸ M) :=
    finite_quot P L₀ N hN (tf N hN) (fun t ht => ((memP t).mp ht).2) fin0
  have fK : Finite (Q ⧸ K) :=
    finite_quot Q L₀' N hN (tf N hN) (fun t ht => ((memQ t).mp ht).2) fin0'
  have memM : ∀ a : P, a ∈ M ↔ ∃ u ∈ L₀, N • u = (a : G) := by
    intro a
    simp only [M, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map, nsmulAddMonoidHom_apply]
  have memK : ∀ b : Q, b ∈ K ↔ ∃ v ∈ L₀', N • v = (b : G) := by
    intro b
    simp only [K, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map, nsmulAddMonoidHom_apply]
  have eM : ∀ a : P, a ∈ M ↔ ∀ b : Q, χ a b = 1 := by
    intro a
    rw [memM]
    constructor
    · rintro ⟨u, hu, hua⟩ b
      rw [← hua, hχ.nsmul]
      exact hortho u hu _ ((memQ b).mp b.2).2
    · intro h
      obtain ⟨x', hx'X, hx'a⟩ := dX N hN a ((memP a).mp a.2).1
      refine ⟨x', hX x' hx'X (fun y hy => ?_), hx'a⟩
      obtain ⟨y', hy'Y, hy'y⟩ := dY N hN y (hL₀' hy)
      have hy'Q : y' ∈ Q := (memQ y').mpr ⟨hy'Y, hy'y ▸ hy⟩
      rw [← hy'y, ← hχ.nsmul, hx'a]
      exact h ⟨y', hy'Q⟩
  have eK : ∀ b : Q, b ∈ K ↔ ∀ a : P, χ a b = 1 := by
    intro b
    rw [memK]
    constructor
    · rintro ⟨v, hv, hvb⟩ a
      rw [← hvb, ← hχ.nsmul]
      exact hortho _ ((memP a).mp a.2).2 v hv
    · intro h
      obtain ⟨y', hy'Y, hy'b⟩ := dY N hN b ((memQ b).mp b.2).1
      refine ⟨y', hY y' hy'Y (fun u hu => ?_), hy'b⟩
      obtain ⟨x', hx'X, hx'u⟩ := dX N hN u (hL₀ hu)
      have hx'P : x' ∈ P := (memP x').mpr ⟨hx'X, hx'u ▸ hu⟩
      rw [← hx'u, hχ.nsmul, hy'b]
      exact h ⟨x', hx'P⟩
  have hMH : M ≤ L.addSubgroupOf P := by
    intro a ha
    obtain ⟨u, hu, hua⟩ := (memM a).mp ha
    rw [AddSubgroup.mem_addSubgroupOf, ← hua]
    exact hNL u hu
  have hxP : x ∈ P := (memP x).mpr ⟨hx, hNx⟩
  have hxH : (⟨x, hxP⟩ : P) ∉ L.addSubgroupOf P := by
    rw [AddSubgroup.mem_addSubgroupOf]
    exact hxL
  obtain ⟨b, hb1, hb2⟩ := exists_separating (fun (a : P) (b : Q) => χ a b)
    (fun a a' b => hχ.left a a' b) (fun a b b' => hχ.right a b b')
    (fun b => hχ.zero_left b) (fun a => hχ.zero_right a) M K eM eK
    (L.addSubgroupOf P) hMH ⟨x, hxP⟩ hxH
  apply hb2
  refine hxY b ((memQ b).mp b.2).1 (fun u hu => ?_)
  have huP : u ∈ P := (memP u).mpr ⟨hL hu, hLN u hu⟩
  exact hb1 ⟨u, huP⟩ ((AddSubgroup.mem_addSubgroupOf).mpr hu)

end GlobalTheory.DualTransfer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixIntegersModNatFinite
open ValuativeRel GlobalTheory.SplitWeil Matrix

namespace GlobalTheory

theorem exists_finite_integer_residues (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [CharZero k] (n : ℕ) (hn : 0 < n) :
    ∃ (ι : Type) (_ : Finite ι) (x : ι → k), (∀ i, x i ∈ 𝒪[k]) ∧
      ∀ y ∈ 𝒪[k], ∃ i, ∃ u ∈ 𝒪[k], y = x i + (n : k) * u := by
  let U : Set k := ((𝒪[k] : Subring k) : Set k)
  have hUo : IsOpen U := Valuation.isOpen_integer
  have hUc : IsCompact U := isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace 𝒪[k])
  have hc : (n : k) ≠ 0 := by exact_mod_cast hn.ne'
  let V : U → Set k := fun x => (fun y => (y - (x : k)) * (n : k)⁻¹) ⁻¹' U
  have hVo : ∀ x, IsOpen (V x) := fun x =>
    hUo.preimage ((continuous_id.sub continuous_const).mul continuous_const)
  have hcov : U ⊆ ⋃ x, V x := by
    intro y hy
    refine Set.mem_iUnion.2 ⟨⟨y, hy⟩, ?_⟩
    show (y - y) * (n : k)⁻¹ ∈ U
    rw [sub_self, zero_mul]
    exact (𝒪[k]).zero_mem
  obtain ⟨t, ht⟩ := hUc.elim_finite_subcover V hVo hcov
  refine ⟨t, inferInstance, fun i => ((i : U) : k), fun i => (i : U).2, ?_⟩
  intro y hy
  have := ht hy
  simp only [Set.mem_iUnion] at this
  obtain ⟨x, hxt, hyx⟩ := this
  refine ⟨⟨x, hxt⟩, (y - (x : k)) * (n : k)⁻¹, hyx, ?_⟩
  field_simp
  ring

theorem matrix_integers_mod_nat_finite : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [CharZero k] (Y Y' : Type) [Fintype Y] [Fintype Y'] (n : ℕ), 0 < n →
    ∃ R : Set (Matrix Y Y' k), R.Finite ∧ ∀ t : Matrix Y Y' k, (∀ r q, t r q ∈ 𝒪[k]) →
      ∃ s ∈ R, ∃ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) ∧ t = s + n • u := by
  intro k _ _ _ _ _ Y Y' _ _ n hn
  obtain ⟨ι, hι, x, -, hx⟩ := exists_finite_integer_residues k n hn
  refine ⟨Set.range (fun f : Y → Y' → ι => Matrix.of fun r q => x (f r q)), Set.finite_range _, ?_⟩
  intro t ht
  have key := fun r q => hx (t r q) (ht r q)
  choose f u hu hf using key
  refine ⟨Matrix.of fun r q => x (f r q), ⟨f, rfl⟩, Matrix.of fun r q => u r q, hu, ?_⟩
  ext r q
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul]
  exact hf r q

end GlobalTheory
end
