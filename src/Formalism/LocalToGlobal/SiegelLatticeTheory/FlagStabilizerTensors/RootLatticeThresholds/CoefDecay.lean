module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSecondOrder.HasDerivAtDOf
public import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.BetaCut
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundOfCompact

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSecondOrder.SmoothClassInFiniteOrder
open Matrix Finset

noncomputable section

namespace PI.ComplexConjugateDerivative

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Good (Φ : (B.Mat k r → E) → (B.Mat k r → E)) : Prop :=
  (∀ f₁ f₂ : B.Mat k r → E, (∀ h ∈ B.GV k r, f₁ h = f₂ h) → ∀ g ∈ B.GV k r, Φ f₁ g = Φ f₂ g) ∧
  (∀ f₁ f₂ : B.Mat k r → E, SS k r f₁ → SS k r f₂ → ∀ g ∈ B.GV k r, Φ (f₁ + f₂) g = Φ f₁ g + Φ f₂ g) ∧
  (∀ (c : ℝ) (f : B.Mat k r → E), SS k r f → ∀ g ∈ B.GV k r, Φ (c • f) g = c • Φ f g)

theorem good_id : Good (k := k) (r := r) (E := E) id :=
  ⟨fun _ _ h g hg => h g hg, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

theorem good_comp {Φ : (B.Mat k r → E) → (B.Mat k r → E)} (hΦ : Good Φ) {b : Bool} {X : B.Mat k r}
    (hX : B.inLie k r X) : Good (fun f => Φ (D b X f)) := by
  refine ⟨fun f₁ f₂ h g hg => hΦ.1 _ _ (fun y hy => D_congr h hy hX) g hg, fun f₁ f₂ h₁ h₂ g hg => ?_,
    fun c f hf g hg => ?_⟩
  · show Φ (D b X (f₁ + f₂)) g = Φ (D b X f₁) g + Φ (D b X f₂) g
    rw [hΦ.1 _ (D b X f₁ + D b X f₂) (fun y hy => D_add h₁ h₂ hy hX) g hg]
    exact hΦ.2.1 _ _ (ss_D h₁ hX) (ss_D h₂ hX) g hg
  · show Φ (D b X (c • f)) g = c • Φ (D b X f) g
    rw [hΦ.1 _ (c • D b X f) (fun y hy => D_smul c hf hy hX) g hg]
    exact hΦ.2.2 c _ (ss_D hf hX) g hg

theorem good_sum {Φ : (B.Mat k r → E) → (B.Mat k r → E)} (hΦ : Good Φ) {N : ℕ} (c : Fin N → ℝ)
    (h : Fin N → B.Mat k r → E) (hh : ∀ i, SS k r (h i)) {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    Φ (∑ i, c i • h i) g = ∑ i, c i • Φ (h i) g := by
  have h0 : Φ 0 g = 0 := by
    have := hΦ.2.2 0 0 ss_zero g hg
    simpa only [zero_smul] using this
  have key : ∀ s : Finset (Fin N),
      SS k r (∑ i ∈ s, c i • h i) ∧ Φ (∑ i ∈ s, c i • h i) g = ∑ i ∈ s, c i • Φ (h i) g := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; exact ⟨ss_zero, h0⟩
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      refine ⟨ss_add (ss_smul _ (hh a)) ih.1, ?_⟩
      rw [hΦ.2.1 _ _ (ss_smul _ (hh a)) ih.1 g hg, hΦ.2.2 _ _ (hh a) g hg, ih.2]
  exact (key univ).2

def ev : List Bool → List (B.Mat k r) → (B.Mat k r → E) → (B.Mat k r → E)
  | b :: ks, X :: xs, f => D b X (ev ks xs f)
  | _, _, f => f

theorem ss_ev : ∀ (ks : List Bool) (xs : List (B.Mat k r)) {f : B.Mat k r → E},
    (∀ X ∈ xs, B.inLie k r X) → SS k r f → SS k r (ev ks xs f)
  | [], _, _, _, hf => by simpa [ev] using hf
  | _ :: _, [], _, _, hf => by simpa [ev] using hf
  | b :: ks, X :: xs, f, hxs, hf => by
    show SS k r (D b X (ev ks xs f))
    exact ss_D (ss_ev ks xs (fun Y hY => hxs Y (List.mem_cons_of_mem _ hY)) hf) (hxs X List.mem_cons_self)

theorem rw_eq_ev (v : List (B.Mat k r)) (F : B.Mat k r → E) :
    B.Rw v F = ev (List.replicate v.length false) v F := by
  induction v with
  | nil => rfl
  | cons X v ih =>
    show Formalism.REAL.RdV X (B.Rw v F) = D false X (ev (List.replicate v.length false) v F)
    rw [ih]; rfl

theorem dLR_eq_ev (u v : List (B.Mat k r)) (F : B.Mat k r → E) :
    B.dLR u v F = ev (List.replicate u.length true ++ List.replicate v.length false) (u ++ v) F := by
  induction u with
  | nil => exact rw_eq_ev v F
  | cons X u ih =>
    show B.LdV X (B.dLR u v F) = D true X (ev (List.replicate u.length true ++ List.replicate v.length false) (u ++ v) F)
    rw [ih]; rfl

def bsum {N : ℕ} (e : Fin N → B.Mat k r) : List Bool → (List (B.Mat k r) → ℝ) → ℝ
  | [], Ψ => Ψ []
  | _ :: ks, Ψ => ∑ i, bsum e ks (fun β => Ψ (e i :: β))

theorem bsum_mul {N : ℕ} (e : Fin N → B.Mat k r) (a : ℝ) :
    ∀ (ks : List Bool) (Ψ : List (B.Mat k r) → ℝ), bsum e ks (fun β => a * Ψ β) = a * bsum e ks Ψ
  | [], _ => rfl
  | _ :: ks, Ψ => by
    simp only [bsum]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => bsum_mul e a ks _

theorem bsum_mono {N : ℕ} (e : Fin N → B.Mat k r) :
    ∀ (ks : List Bool) (Ψ₁ Ψ₂ : List (B.Mat k r) → ℝ),
      (∀ β : List (B.Mat k r), β.length = ks.length → (∀ x ∈ β, ∃ i, x = e i) → Ψ₁ β ≤ Ψ₂ β) →
      bsum e ks Ψ₁ ≤ bsum e ks Ψ₂
  | [], _, _, h => h [] rfl (by simp)
  | _ :: ks, Ψ₁, Ψ₂, h => by
    simp only [bsum]
    refine Finset.sum_le_sum fun i _ => bsum_mono e ks _ _ fun β hβ hβe => h (e i :: β) (by simp [hβ]) ?_
    intro x hx
    rcases List.mem_cons.1 hx with hx | hx
    · exact ⟨i, hx⟩
    · exact hβe x hx

theorem bsum_nonneg {N : ℕ} (e : Fin N → B.Mat k r) :
    ∀ (ks : List Bool) (Ψ : List (B.Mat k r) → ℝ), (∀ β, 0 ≤ Ψ β) → 0 ≤ bsum e ks Ψ
  | [], _, h => h []
  | _ :: ks, Ψ, h => by
    simp only [bsum]
    exact Finset.sum_nonneg fun i _ => bsum_nonneg e ks _ fun β => h _

theorem expand {N : ℕ} (e : Fin N → B.Mat k r) (c : Fin N → B.Mat k r → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (he : ∀ i, B.inLie k r (e i)) (hc : ∀ X, B.inLie k r X → X = ∑ i, c i X • e i) :
    ∀ (ks : List Bool) (xs : List (B.Mat k r)), xs.length = ks.length →
      (∀ X ∈ xs, B.inLie k r X ∧ ∀ i, |c i X| ≤ K) →
      ∀ (Φ : (B.Mat k r → E) → (B.Mat k r → E)), Good Φ → ∀ f, SS k r f → ∀ g ∈ B.GV k r,
        ‖Φ (ev ks xs f) g‖ ≤ K ^ xs.length * bsum e ks (fun β => ‖Φ (ev ks β f) g‖) := by
  intro ks
  induction ks with
  | nil =>
    intro xs hlen _ Φ _ f _ g _
    have : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst this
    simp [ev, bsum]
  | cons b ks ih =>
    intro xs hlen hxs Φ hΦ f hf g hg
    cases xs with
    | nil => simp at hlen
    | cons X xs =>
      have hlen' : xs.length = ks.length := by simpa using hlen
      have hX := hxs X List.mem_cons_self
      have hxs' : ∀ Y ∈ xs, B.inLie k r Y ∧ ∀ i, |c i Y| ≤ K :=
        fun Y hY => hxs Y (List.mem_cons_of_mem _ hY)
      have hh : SS k r (ev ks xs f) := ss_ev ks xs (fun Y hY => (hxs' Y hY).1) hf
      have hexp : ∀ g' ∈ B.GV k r,
          D b X (ev ks xs f) g' = (∑ i, c i X • D b (e i) (ev ks xs f)) g' := by
        intro g' hg'
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply]
        exact D_letter hh hg' he hX.1 (hc X hX.1)
      have step1 : Φ (ev (b :: ks) (X :: xs) f) g = ∑ i, c i X • Φ (D b (e i) (ev ks xs f)) g := by
        show Φ (D b X (ev ks xs f)) g = _
        rw [hΦ.1 _ _ hexp g hg]
        exact good_sum hΦ _ _ (fun i => ss_D hh (he i)) hg
      rw [step1]
      calc ‖∑ i, c i X • Φ (D b (e i) (ev ks xs f)) g‖
          ≤ ∑ i, ‖c i X • Φ (D b (e i) (ev ks xs f)) g‖ := norm_sum_le _ _
        _ ≤ ∑ i, K * (K ^ xs.length * bsum e ks (fun β => ‖Φ (D b (e i) (ev ks β f)) g‖)) := by
          apply Finset.sum_le_sum
          intro i _
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul (hX.2 i)
            (ih xs hlen' hxs' (fun f' => Φ (D b (e i) f')) (good_comp hΦ (he i)) f hf g hg)
            (norm_nonneg _) hK
        _ = K ^ (X :: xs).length * bsum e (b :: ks) (fun β => ‖Φ (ev (b :: ks) β f) g‖) := by
          rw [List.length_cons]
          simp only [bsum, ev]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring

def lieSub (k r : ℕ) : Submodule ℝ (B.Mat k r) where
  carrier := {X | B.inLie k r X}
  add_mem' := fun {X Y} hX hY => by
    have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
    have hY' : Yᴴ * Hpk k r + Hpk k r * Y = 0 := hY
    show (X + Y)ᴴ * Hpk k r + Hpk k r * (X + Y) = 0
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    calc _ = (Xᴴ * Hpk k r + Hpk k r * X) + (Yᴴ * Hpk k r + Hpk k r * Y) := by abel
      _ = 0 := by rw [hX', hY', add_zero]
  zero_mem' := by
    show (0 : B.Mat k r)ᴴ * Hpk k r + Hpk k r * 0 = 0
    simp
  smul_mem' := fun a X hX => by
    have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
    show (a • X)ᴴ * Hpk k r + Hpk k r * (a • X) = 0
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX',
      smul_zero]

theorem basis_exists (k r : ℕ) : ∃ (N : ℕ) (e : Fin N → B.Mat k r) (c : Fin N → B.Mat k r → ℝ) (K : ℝ),
    0 ≤ K ∧ (∀ i, B.unitLie k r (e i)) ∧ (∀ X, B.inLie k r X → X = ∑ i, c i X • e i) ∧
    (∀ X, B.unitLie k r X → ∀ i, |c i X| ≤ K) := by
  classical
  have : FiniteDimensional ℝ (B.Mat k r) :=
    inferInstanceAs (FiniteDimensional ℝ (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))
  let bs := Module.finBasis ℝ (lieSub k r)
  let N := Module.finrank ℝ (lieSub k r)
  let s : Fin N → ℝ := fun i => max 1 ‖((bs i : lieSub k r) : B.Mat k r)‖
  have hs1 : ∀ i, 1 ≤ s i := fun i => le_max_left _ _
  have hs0 : ∀ i, 0 < s i := fun i => lt_of_lt_of_le one_pos (hs1 i)
  have hb : ∀ i : Fin N, ∃ C, 0 < C ∧ ∀ x : lieSub k r, ‖bs.coord i x‖ ≤ C * ‖x‖ :=
    fun i => (LinearMap.toContinuousLinearMap (bs.coord i)).bound
  choose C hC0 hC using hb
  let K : ℝ := ∑ i, C i * s i
  refine ⟨N, fun i => (s i)⁻¹ • ((bs i : lieSub k r) : B.Mat k r),
    fun i X => if h : B.inLie k r X then bs.repr ⟨X, h⟩ i * s i else 0, K, ?_, ?_, ?_, ?_⟩
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (hC0 i).le (hs0 i).le
  · intro i
    refine ⟨(lieSub k r).smul_mem (s i)⁻¹ (bs i).2, fun p q => ?_⟩
    show ‖((s i)⁻¹ • ((bs i : lieSub k r) : B.Mat k r)) p q‖ ≤ 1
    rw [Matrix.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hs0 i)),
      inv_mul_le_iff₀ (hs0 i), mul_one]
    exact le_trans (Matrix.norm_entry_le_entrywise_sup_norm _) (le_max_right _ _)
  · intro X hX
    have h1 := congrArg Subtype.val (bs.sum_repr ⟨X, hX⟩)
    rw [Submodule.coe_sum] at h1
    simp only [Submodule.coe_smul] at h1
    conv_lhs => rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    show _ = (if h : B.inLie k r X then bs.repr ⟨X, h⟩ i * s i else 0) • ((s i)⁻¹ • ((bs i : lieSub k r) : B.Mat k r))
    rw [dite_eq_left hX, smul_smul, mul_assoc, mul_inv_cancel₀ (hs0 i).ne', mul_one]
  · intro X hX i
    show |(if h : B.inLie k r X then bs.repr ⟨X, h⟩ i * s i else 0)| ≤ K
    rw [dite_eq_left hX.1, abs_mul, abs_of_pos (hs0 i)]
    have hXn : ‖(⟨X, hX.1⟩ : lieSub k r)‖ ≤ 1 := by
      show ‖X‖ ≤ 1
      exact (Matrix.norm_le_iff zero_le_one).2 hX.2
    have hrep : |bs.repr ⟨X, hX.1⟩ i| ≤ C i := by
      rw [← Module.Basis.coord_apply, ← Real.norm_eq_abs]
      calc ‖bs.coord i ⟨X, hX.1⟩‖ ≤ C i * ‖(⟨X, hX.1⟩ : lieSub k r)‖ := hC i _
        _ ≤ C i * 1 := mul_le_mul_of_nonneg_left hXn (hC0 i).le
        _ = C i := mul_one _
    calc |bs.repr ⟨X, hX.1⟩ i| * s i ≤ C i * s i := mul_le_mul_of_nonneg_right hrep (hs0 i).le
      _ ≤ K := Finset.single_le_sum (f := fun j => C j * s j)
          (fun j _ => mul_nonneg (hC0 j).le (hs0 j).le) (Finset.mem_univ i)


end PI.ComplexConjugateDerivative
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CoefDecayA
open Matrix Finset

noncomputable section

namespace Formalism.L2.SG.Pf.CoefDecay

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt PI.ComplexConjugateDerivative

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def CCw (k r : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (A : ℝ) (F : B.Mat k r → E) : Prop :=
  SS k r F ∧ ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
    ∃ C : ℝ, ∀ g ∈ B.GV k r, B.gN g ^ A * ‖B.dLR u v F g‖ ≤ C


open Classical in
def cstW {A : ℝ} {F : B.Mat k r → E} (hF : CCw k r A F) (u v : List (B.Mat k r)) : ℝ :=
  if h : (∀ X ∈ u, B.unitLie k r X) ∧ (∀ X ∈ v, B.unitLie k r X) then Classical.choose (hF.2 u v h.1 h.2) else 0

theorem cstW_spec {A : ℝ} {F : B.Mat k r → E} (hF : CCw k r A F) (u v : List (B.Mat k r))
    (hu : ∀ X ∈ u, B.unitLie k r X) (hv : ∀ X ∈ v, B.unitLie k r X) {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    B.gN g ^ A * ‖B.dLR u v F g‖ ≤ cstW hF u v := by
  unfold cstW
  rw [dite_eq_left ⟨hu, hv⟩]
  exact Classical.choose_spec (hF.2 u v hu hv) g hg

def termW {N : ℕ} (e : Fin N → B.Mat k r) (K : ℝ) {A : ℝ} {F : B.Mat k r → E} (hF : CCw k r A F)
    (a b : ℕ) : ℝ :=
  K ^ (a + b) * bsum e (List.replicate a true ++ List.replicate b false)
    (fun β => max (cstW hF (β.take a) (β.drop a)) 0)

theorem inCC_of_CCw {A : ℝ} {F : B.Mat k r → E} (hF : CCw k r A F) (m : ℕ) :
    B.InCC (k := k) (r := r) A m F := by
  obtain ⟨N, e, c, K, hK, he, hc, hcK⟩ := basis_exists k r
  have he' : ∀ i, B.inLie k r (e i) := fun i => (he i).1
  have hgN : ∀ g : B.Mat k r, 0 ≤ B.gN g ^ A := fun g => Real.rpow_nonneg (Real.sqrt_nonneg _) A
  have hterm : ∀ a b, 0 ≤ termW e K hF a b := fun a b =>
    mul_nonneg (pow_nonneg hK _) (bsum_nonneg e _ _ fun β => le_max_right _ _)

  have hword : ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
      ∀ g ∈ B.GV k r, B.gN g ^ A * ‖B.dLR u v F g‖ ≤ termW e K hF u.length v.length := by
    intro u v hu hv g hg
    set ks := List.replicate u.length true ++ List.replicate v.length false with hks
    have hlen : (u ++ v).length = ks.length := by simp [hks]
    have hxs : ∀ X ∈ u ++ v, B.inLie k r X ∧ ∀ i, |c i X| ≤ K := by
      intro X hX
      have hX' : B.unitLie k r X := by
        rcases List.mem_append.1 hX with h | h
        · exact hu X h
        · exact hv X h
      exact ⟨hX'.1, hcK X hX'⟩
    have hexp := expand e c hK he' hc ks (u ++ v) hlen hxs id good_id F hF.1 g hg
    rw [B.dLR, ← B.dLR, dLR_eq_ev]
    have hl : (u ++ v).length = u.length + v.length := List.length_append
    rw [hl] at hexp
    calc B.gN g ^ A * ‖ev ks (u ++ v) F g‖
        ≤ B.gN g ^ A * (K ^ (u.length + v.length) * bsum e ks (fun β => ‖id (ev ks β F) g‖)) :=
          mul_le_mul_of_nonneg_left hexp (hgN g)
      _ = K ^ (u.length + v.length) * bsum e ks (fun β => B.gN g ^ A * ‖ev ks β F g‖) := by
          rw [bsum_mul]; simp only [id]; ring
      _ ≤ termW e K hF u.length v.length := by
          unfold termW
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hK _)
          refine bsum_mono e ks _ _ ?_
          intro β hβ hβe
          have hβl : β.length = u.length + v.length := by rw [hβ]; simp [hks]
          have h1 : (β.take u.length).length = u.length := by simp [List.length_take, hβl]
          have h2 : (β.drop u.length).length = v.length := by simp [List.length_drop, hβl]
          have hev : ev ks β F = B.dLR (β.take u.length) (β.drop u.length) F := by
            rw [dLR_eq_ev, h1, h2, List.take_append_drop]
          have hunit : ∀ X ∈ β, B.unitLie k r X := by
            intro X hX
            obtain ⟨i, rfl⟩ := hβe X hX
            exact he i
          rw [hev]
          exact (cstW_spec hF _ _ (fun X hX => hunit X (List.mem_of_mem_take hX))
            (fun X hX => hunit X (List.mem_of_mem_drop hX)) hg).trans (le_max_left _ _)
  refine ⟨∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1), termW e K hF a b, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', hff'⟩ := hF.1 g₀ hg₀
    exact ⟨U, f', hU, hgU, hf'.of_le (by exact_mod_cast le_top), hff'⟩
  · intro u v hu hv hl g hg
    refine (hword u v hu hv g hg).trans ?_
    have ha : u.length ∈ Finset.range (m + 1) := Finset.mem_range.2 (by omega)
    have hb : v.length ∈ Finset.range (m + 1) := Finset.mem_range.2 (by omega)
    calc termW e K hF u.length v.length
        ≤ ∑ b ∈ Finset.range (m + 1), termW e K hF u.length b :=
          Finset.single_le_sum (fun b _ => hterm _ b) hb
      _ ≤ ∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1), termW e K hF a b :=
          Finset.single_le_sum (f := fun a => ∑ b ∈ Finset.range (m + 1), termW e K hF a b)
            (fun a _ => Finset.sum_nonneg fun b _ => hterm a b) ha

end Formalism.L2.SG.Pf.CoefDecay
end
end

open Matrix Filter Topology
open scoped InnerProductSpace ContDiff

noncomputable section

namespace Formalism.L2.SG.Pf.CoefDecay

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def rk1 (ξ : Wp) (ξ' : Wq) : Wq →L[ℂ] Wp := (innerSL ℂ ξ').smulRight ξ

def cf (σ : B.Mat k r → (H →L[ℂ] H)) (a b : H) (T : Wq →L[ℂ] Wp) : B.Mat k r → (Wq →L[ℂ] Wp) :=
  fun g => ⟪a, σ g b⟫_ℂ • T

theorem coefM_eq (σ : B.Mat k r → (H →L[ℂ] H)) (v v' : H) (ξ : Wp) (ξ' : Wq) :
    Formalism.MainNotions.S.Pv.BetaCut.coefM σ v v' ξ ξ' = cf σ v v' (rk1 ξ ξ') := by
  funext g
  ext x
  simp only [Formalism.MainNotions.S.Pv.BetaCut.coefM, cf, rk1, ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply]
  rw [smul_comm]

variable {σ : B.Mat k r → (H →L[ℂ] H)}

theorem dsigW_smooth (hσ : Formalism.MainNotions.S.IsURepOn (B.GV k r) σ) {v : H}
    (hv : Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ v) (D : List (B.Mat k r))
    (hD : ∀ X ∈ D, Formalism.MainNotions.S.InLieHpk k r X) :
    Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ (Formalism.MainNotions.S.dsigW σ D v) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, h0, hF, hE⟩ :=
    Formalism.MainNotions.LowestKTypeMultiplicity.psiD_smooth hσ hv D hD ((1 : B.Mat k r), g₀) (Formalism.MainNotions.LowestKTypeMultiplicity.UH_one k r) hg₀
  have hc : ContDiff ℝ ∞ (fun g : B.Mat k r => ((1 : B.Mat k r), g)) := contDiff_const.prodMk contDiff_id
  refine ⟨(fun g : B.Mat k r => ((1 : B.Mat k r), g)) ⁻¹' U, fun g => F (1, g), hU.preimage hc.continuous, h0,
    hF.comp hc.contDiffOn (fun x hx => hx), ?_⟩
  intro g hgU hgH
  have := hE (1, g) hgU (Formalism.MainNotions.LowestKTypeMultiplicity.UH_one k r) hgH
  simp only [hσ.1.1, one_apply_eq_self] at this
  exact this

theorem ss_cf {b : H} (hb : Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ b) (a : H) (T : Wq →L[ℂ] Wp) :
    PI.ComplexConjugateDerivative.SS k r (cf σ a b T) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, h0, hF, hE⟩ := hb g₀ hg₀
  let L : H →L[ℝ] (Wq →L[ℂ] Wp) := ((innerSL ℂ a).smulRight T).restrictScalars ℝ
  refine ⟨U, fun g => L (F g), hU, h0, L.contDiff.comp_contDiffOn hF, fun g hgU hgG => ?_⟩
  show ⟪a, σ g b⟫_ℂ • T = L (F g)
  have e := hE g hgU hgG
  simp only at e
  rw [e]
  rfl

theorem hasDeriv_R (hσ : Formalism.MainNotions.S.IsURepOn (B.GV k r) σ) {v' : H}
    (hv' : Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ v') (w : List (B.Mat k r))
    (hw : ∀ X ∈ w, Formalism.MainNotions.S.InLieHpk k r X) {Y : B.Mat k r} (hY : Formalism.MainNotions.S.InLieHpk k r Y) (a : H)
    {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    HasDerivAt (fun t : ℝ => ⟪a, σ (g * NormedSpace.exp ((t : ℂ) • Y)) (Formalism.MainNotions.S.dsigW σ w v')⟫_ℂ)
      ⟪a, σ g (Formalism.MainNotions.S.dsigW σ (Y :: w) v')⟫_ℂ 0 := by
  have h1 := Formalism.MainNotions.LowestKTypeMultiplicity.dsigW_hasDeriv hσ hv' w hw hY
  have h2 := (((innerSL ℂ a).comp (σ g)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  show ⟪a, σ (g * NormedSpace.exp ((t : ℂ) • Y)) (Formalism.MainNotions.S.dsigW σ w v')⟫_ℂ =
    ⟪a, σ g (σ (NormedSpace.exp ((t : ℂ) • Y)) (Formalism.MainNotions.S.dsigW σ w v'))⟫_ℂ
  rw [hσ.1.2 g hg _ (Formalism.MainNotions.LowestKTypeMultiplicity.exp_mem_UH hY t)]
  rfl

theorem inner_exp_move (hσ : Formalism.MainNotions.S.IsURepOn (B.GV k r) σ) {X : B.Mat k r}
    (hX : Formalism.MainNotions.S.InLieHpk k r X) (t : ℝ) (x y : H) :
    ⟪x, σ (NormedSpace.exp (-((t : ℂ) • X))) y⟫_ℂ = ⟪σ (NormedSpace.exp ((t : ℂ) • X)) x, y⟫_ℂ := by
  have he : NormedSpace.exp ((t : ℂ) • X) ∈ B.GV k r := Formalism.MainNotions.LowestKTypeMultiplicity.exp_mem_UH hX t
  have hX' : Formalism.MainNotions.S.InLieHpk k r (-X) := by
    have h : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
    show (-X)ᴴ * Hpk k r + Hpk k r * (-X) = 0
    rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, h, neg_zero]
  have he' : NormedSpace.exp (-((t : ℂ) • X)) ∈ B.GV k r := by
    rw [← smul_neg]; exact Formalism.MainNotions.LowestKTypeMultiplicity.exp_mem_UH hX' t
  have e1 : NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp (-((t : ℂ) • X)) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl ((t : ℂ) • X)).neg_right)]
    simp
  let L : H →ₗᵢ[ℂ] H := ⟨(σ (NormedSpace.exp ((t : ℂ) • X)) : H →ₗ[ℂ] H), fun v => hσ.2.1 _ he v⟩
  have h1 : ⟪x, σ (NormedSpace.exp (-((t : ℂ) • X))) y⟫_ℂ =
      ⟪L x, L (σ (NormedSpace.exp (-((t : ℂ) • X))) y)⟫_ℂ := (L.inner_map_map _ _).symm
  rw [h1]
  show ⟪σ (NormedSpace.exp ((t : ℂ) • X)) x,
    σ (NormedSpace.exp ((t : ℂ) • X)) (σ (NormedSpace.exp (-((t : ℂ) • X))) y)⟫_ℂ = _
  have h2 : σ (NormedSpace.exp ((t : ℂ) • X)) (σ (NormedSpace.exp (-((t : ℂ) • X))) y) = y := by
    have := hσ.1.2 _ he _ he'
    rw [e1, hσ.1.1] at this
    have h3 := congrArg (fun T : H →L[ℂ] H => T y) this
    simpa using h3.symm
  rw [h2]

theorem hasDeriv_L (hσ : Formalism.MainNotions.S.IsURepOn (B.GV k r) σ) {v : H}
    (hv : Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ v) (u : List (B.Mat k r))
    (hu : ∀ X ∈ u, Formalism.MainNotions.S.InLieHpk k r X) {X : B.Mat k r} (hX : Formalism.MainNotions.S.InLieHpk k r X) (y : H)
    {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    HasDerivAt (fun t : ℝ => ⟪Formalism.MainNotions.S.dsigW σ u v, σ (NormedSpace.exp (-((t : ℂ) • X)) * g) y⟫_ℂ)
      ⟪Formalism.MainNotions.S.dsigW σ (X :: u) v, σ g y⟫_ℂ 0 := by
  have hX' : Formalism.MainNotions.S.InLieHpk k r (-X) := by
    have h : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
    show (-X)ᴴ * Hpk k r + Hpk k r * (-X) = 0
    rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, h, neg_zero]
  have h1 := Formalism.MainNotions.LowestKTypeMultiplicity.dsigW_hasDeriv hσ hv u hu hX
  have h2 := h1.inner ℂ (hasDerivAt_const (0 : ℝ) (σ g y))
  rw [inner_zero_right, zero_add] at h2
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  have he' : NormedSpace.exp (-((t : ℂ) • X)) ∈ B.GV k r := by
    rw [← smul_neg]; exact Formalism.MainNotions.LowestKTypeMultiplicity.exp_mem_UH hX' t
  show ⟪Formalism.MainNotions.S.dsigW σ u v, σ (NormedSpace.exp (-((t : ℂ) • X)) * g) y⟫_ℂ =
    ⟪σ (NormedSpace.exp ((t : ℂ) • X)) (Formalism.MainNotions.S.dsigW σ u v), σ g y⟫_ℂ
  rw [hσ.1.2 _ he' g hg]
  exact inner_exp_move hσ hX t _ _

theorem Rw_cf (hσ : Formalism.MainNotions.S.IsURepOn (B.GV k r) σ) {v' : H}
    (hv' : Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ v') (a : H) (T : Wq →L[ℂ] Wp) :
    ∀ w : List (B.Mat k r), (∀ X ∈ w, Formalism.MainNotions.S.InLieHpk k r X) → ∀ g ∈ B.GV k r,
      B.Rw w (cf σ a v' T) g = cf σ a (Formalism.MainNotions.S.dsigW σ w v') T g
  | [], _, _, _ => rfl
  | Y :: w, hw, g, hg => by
    have hw' : ∀ X ∈ w, Formalism.MainNotions.S.InLieHpk k r X := fun X hX => hw X (List.mem_cons_of_mem _ hX)
    have hY : Formalism.MainNotions.S.InLieHpk k r Y := hw Y List.mem_cons_self
    have hc := PI.ComplexConjugateDerivative.D_congr (E := Wq →L[ℂ] Wp) (b := false) (X := Y)
      (fun y hy => Rw_cf hσ hv' a T w hw' y hy) hg hY
    refine (hc : Formalism.REAL.RdV Y (B.Rw w (cf σ a v' T)) g = Formalism.REAL.RdV Y (cf σ a (Formalism.MainNotions.S.dsigW σ w v') T) g).trans ?_
    have hd := hasDeriv_R hσ hv' w hw' hY a hg
    show deriv (fun t : ℝ => ⟪a, σ (g * NormedSpace.exp ((t : ℂ) • Y)) (Formalism.MainNotions.S.dsigW σ w v')⟫_ℂ • T) 0 =
      ⟪a, σ g (Formalism.MainNotions.S.dsigW σ (Y :: w) v')⟫_ℂ • T
    rw [deriv_smul_const hd.differentiableAt, hd.deriv]

theorem dLR_cf (hσ : Formalism.MainNotions.S.IsURepOn (B.GV k r) σ) {v v' : H}
    (hv : Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ v) (hv' : Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ v')
    (T : Wq →L[ℂ] Wp) :
    ∀ u w : List (B.Mat k r), (∀ X ∈ u, Formalism.MainNotions.S.InLieHpk k r X) → (∀ X ∈ w, Formalism.MainNotions.S.InLieHpk k r X) →
      ∀ g ∈ B.GV k r, B.dLR u w (cf σ v v' T) g = cf σ (Formalism.MainNotions.S.dsigW σ u v) (Formalism.MainNotions.S.dsigW σ w v') T g
  | [], w, _, hw, g, hg => Rw_cf hσ hv' v T w hw g hg
  | X :: u, w, hu, hw, g, hg => by
    have hu' : ∀ Y ∈ u, Formalism.MainNotions.S.InLieHpk k r Y := fun Y hY => hu Y (List.mem_cons_of_mem _ hY)
    have hX : Formalism.MainNotions.S.InLieHpk k r X := hu X List.mem_cons_self
    have hc := PI.ComplexConjugateDerivative.D_congr (E := Wq →L[ℂ] Wp) (b := true) (X := X)
      (fun y hy => dLR_cf hσ hv hv' T u w hu' hw y hy) hg hX
    refine (hc : B.LdV X (B.dLR u w (cf σ v v' T)) g =
      B.LdV X (cf σ (Formalism.MainNotions.S.dsigW σ u v) (Formalism.MainNotions.S.dsigW σ w v') T) g).trans ?_
    have hd := hasDeriv_L hσ hv u hu' hX (Formalism.MainNotions.S.dsigW σ w v') hg
    show deriv (fun t : ℝ => ⟪Formalism.MainNotions.S.dsigW σ u v,
      σ (NormedSpace.exp (-((t : ℂ) • X)) * g) (Formalism.MainNotions.S.dsigW σ w v')⟫_ℂ • T) 0 =
      ⟪Formalism.MainNotions.S.dsigW σ (X :: u) v, σ g (Formalism.MainNotions.S.dsigW σ w v')⟫_ℂ • T
    rw [deriv_smul_const hd.differentiableAt, hd.deriv]

theorem coefM_inCC_of_dec (hσ : Formalism.MainNotions.S.IsURepOn (B.GV k r) σ) {A : ℝ}
    (hdec : ∀ a ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ, ∀ b ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ,
      ∃ C : ℝ, ∀ g ∈ B.GV k r, B.gN g ^ A * ‖⟪a, σ g b⟫_ℂ‖ ≤ C)
    {v v' : H} (hv : v ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ)
    (hv' : v' ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ) (ξ : Wp) (ξ' : Wq) (m : ℕ) :
    B.InCC (k := k) (r := r) A m (Formalism.MainNotions.S.Pv.BetaCut.coefM σ v v' ξ ξ') := by
  rw [coefM_eq]
  refine inCC_of_CCw ⟨ss_cf hv' v _, fun u w hu hw => ?_⟩ m
  have hu' : ∀ X ∈ u, Formalism.MainNotions.S.InLieHpk k r X := fun X hX => (hu X hX).1
  have hw' : ∀ X ∈ w, Formalism.MainNotions.S.InLieHpk k r X := fun X hX => (hw X hX).1
  obtain ⟨C, hC⟩ := hdec _ (dsigW_smooth hσ hv u hu') _ (dsigW_smooth hσ hv' w hw')
  refine ⟨C * ‖rk1 ξ ξ'‖, fun g hg => ?_⟩
  rw [dLR_cf hσ hv hv' _ u w hu' hw' g hg]
  show B.gN g ^ A * ‖⟪Formalism.MainNotions.S.dsigW σ u v, σ g (Formalism.MainNotions.S.dsigW σ w v')⟫_ℂ • rk1 ξ ξ'‖ ≤ _
  rw [norm_smul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hC g hg) (norm_nonneg _)

theorem coefM_inCC {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    (hlam : Formalism.QuantumDeterminants.IsHCParam lam) {h : ℝ} (hgap : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (m' : ℕ)
    (hm' : ReciprocityTheory.ChartRestriction.DS.thrStar ε + m' < h) {A : ℝ} (hA : A ≤ m')
    [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsDSHpk k r ε lam σ) {v v' : H}
    (hv : v ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ) (hv' : v' ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ)
    (ξ : Wp) (ξ' : Wq) (m : ℕ) :
    B.InCC (k := k) (r := r) A m (Formalism.MainNotions.S.Pv.BetaCut.coefM σ v v' ξ ξ') := by
  obtain ⟨C, Ws, -, hC⟩ := ReciprocityTheory.ChartRestriction.DS.DecInf.decSm hlam hgap m' hm' hσ
  refine coefM_inCC_of_dec (Formalism.MainNotions.LowestKTypeMultiplicity.urep_of_DS hσ) (fun a ha b hb =>
    ⟨C * (Ws.map fun w => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w b‖).sum *
      (Ws.map fun w => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w a‖).sum, fun g hg => ?_⟩) hv hv' ξ ξ' m
  have h1 := PI.ComplexConjugateDerivative.one_le_gN hg
  calc B.gN g ^ A * ‖⟪a, σ g b⟫_ℂ‖ ≤ B.gN g ^ (m' : ℝ) * ‖⟪a, σ g b⟫_ℂ‖ :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le h1 hA) (norm_nonneg _)
    _ = B.gN g ^ m' * ‖⟪a, σ g b⟫_ℂ‖ := by rw [Real.rpow_natCast]
    _ ≤ _ := hC b hb a ha g hg

end Formalism.L2.SG.Pf.CoefDecay
