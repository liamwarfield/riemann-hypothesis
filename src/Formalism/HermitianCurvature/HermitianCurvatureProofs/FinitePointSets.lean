module

public import Formalism.HermitianCurvature.StatementTB
public import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.FinitePointSets
namespace Formalism.FourierDecayAlt.P.FinitePointSets

open Formalism.FourierDecayAlt.TB Finset Filter Topology
open scoped ComplexInnerProductSpace ComplexConjugate

theorem finite_pts {E : Type} [Field E] (S : Finset E) (i : ℕ) :
    {p : Pt E | level p = i ∧
      ∀ k (hk : k < p.length), 1 ≤ (p[k]'hk).1 ∧ (p[k]'hk).2 ∈ S}.Finite := by
  classical
  set F : Finset (ℕ × E) := (range (i + 1)) ×ˢ S with hFdef
  refine ((List.finite_length_le F i).image (List.map Subtype.val)).subset ?_
  rintro p ⟨hl, hp⟩
  have hmem : ∀ x ∈ p, 1 ≤ x.1 ∧ x.2 ∈ S := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
    exact hp k hk
  unfold level at hl
  have hF : ∀ x ∈ p, x ∈ F := by
    intro x hx
    simp only [hFdef, mem_product, mem_range]
    refine ⟨?_, (hmem x hx).2⟩
    have : x.1 ≤ (p.map Prod.fst).sum := List.le_sum_of_mem (List.mem_map_of_mem hx)
    omega
  refine ⟨p.pmap Subtype.mk hF, ?_, ?_⟩
  · have h1 : (p.map Prod.fst).length ≤ (p.map Prod.fst).sum := by
      refine List.length_le_sum_of_one_le _ fun n hn => ?_
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hn
      exact (hmem x hx).1
    change (p.pmap Subtype.mk hF).length ≤ i
    simpa [hl] using h1
  · simp [List.map_pmap]

noncomputable def tw {E : Type} [Field E] (S : Finset E) (h0 : (0 : E) ∉ S) : Tower E where
  Sg := fun _ _ => S
  X := fun i => (finite_pts S i).toFinset
  isTower := by
    intro i p
    simp
  zero_not_mem := fun _ _ => h0

theorem form_nonneg {α H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Y : Finset α) (k : α → α → ℂ) (hk : PSDOn Y k) (V : α → H) :
    0 ≤ (∑ p ∈ Y, ∑ q ∈ Y, k p q * ⟪V q, V p⟫).re := by
  classical
  obtain ⟨B, hB⟩ : ∃ B : Matrix Y Y ℂ, Matrix.gram ℂ (fun p : Y => V p.1) = star B * B := by
    open scoped MatrixOrder Matrix.Norms.L2Operator in
    exact CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
      (Matrix.posSemidef_gram ℂ (fun p : Y => V p.1)).nonneg
  have hG : ∀ p q : Y, ⟪V p.1, V q.1⟫ = ∑ j, conj (B j p) * B j q := by
    intro p q
    have := congrFun (congrFun hB p) q
    simpa [Matrix.gram, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply] using this
  have e1 : ∑ p ∈ Y, ∑ q ∈ Y, k p q * ⟪V q, V p⟫
      = ∑ p : Y, ∑ q : Y, k p.1 q.1 * ⟪V q.1, V p.1⟫ := by
    rw [← Finset.sum_coe_sort Y]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_coe_sort Y]
  have e2 : ∑ p : Y, ∑ q : Y, k p.1 q.1 * ⟪V q.1, V p.1⟫
      = ∑ j : Y, star (fun p : Y => conj (B j p)) ⬝ᵥ
          (Matrix.of fun x y : Y => k x y).mulVec (fun p : Y => conj (B j p)) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, RCLike.star_def,
      Complex.conj_conj, Finset.mul_sum]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hG q p, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e1, e2, Complex.re_sum]
  exact Finset.sum_nonneg fun j _ => Matrix.PosSemidef.re_dotProduct_nonneg hk _

theorem norm_sq_comb {α H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Y : Finset α) (c : α → ℂ) (V : α → H) :
    ((‖∑ p ∈ Y, c p • V p‖ ^ 2 : ℝ) : ℂ)
      = ∑ p ∈ Y, ∑ q ∈ Y, (c p * conj (c q)) * ⟪V q, V p⟫ := by
  have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (∑ p ∈ Y, c p • V p)
  rw [Complex.ofReal_pow]
  refine this.symm.trans ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [sum_inner]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [inner_smul_left, inner_smul_right]
  ring

theorem rows_le_form {α H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Y : Finset α) (k : α → α → ℂ) (V : α → H) (c : ℕ → α → ℂ) (R : Finset ℕ)
    (h : PSDOn Y (fun p q => k p q - ∑ ρ ∈ R, c ρ p * starRingEnd ℂ (c ρ q))) :
    ∑ ρ ∈ R, ‖∑ p ∈ Y, c ρ p • V p‖ ^ 2 ≤ (∑ p ∈ Y, ∑ q ∈ Y, k p q * ⟪V q, V p⟫).re := by
  have h0 := form_nonneg Y _ h V
  have e : ∑ p ∈ Y, ∑ q ∈ Y, (k p q - ∑ ρ ∈ R, c ρ p * starRingEnd ℂ (c ρ q)) * ⟪V q, V p⟫
      = ∑ p ∈ Y, ∑ q ∈ Y, k p q * ⟪V q, V p⟫
        - ((∑ ρ ∈ R, ‖∑ p ∈ Y, c ρ p • V p‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    simp_rw [norm_sq_comb]
    rw [Finset.sum_comm (s := R), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm (s := R), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [sub_mul, Finset.sum_mul]
  rw [e, Complex.sub_re, Complex.ofReal_re] at h0
  linarith

end Formalism.FourierDecayAlt.P.FinitePointSets

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.TB Finset Filter Topology
open scoped ComplexInnerProductSpace ComplexConjugate

theorem limitStep : Formalism.FourierDecayAlt.TB.LimitStep := by
  intro E W _ D jn H _ _ _ Vt c _ _ hE hC hA B hB R
  classical
  obtain ⟨hA1, hA2, hA3⟩ := hA
  have hsum : ∀ ρ, Summable (fun p : Pt E => c ρ p • Vt p) := by
    intro ρ
    refine Summable.of_norm ?_
    simpa [norm_smul] using hA3 ρ
  have hlim : Tendsto (fun F : Finset (Pt E) => ∑ ρ ∈ R, ‖∑ p ∈ F, c ρ p • Vt p‖ ^ 2) atTop
      (𝓝 (∑ ρ ∈ R, ‖∑' p, c ρ p • Vt p‖ ^ 2)) := by
    refine tendsto_finsetSum _ fun ρ _ => ?_
    exact ((hsum ρ).hasSum.norm).pow 2
  refine le_of_tendsto_of_frequently hlim ?_
  rw [Filter.frequently_atTop]
  intro F

  set F0 : Finset (Pt E) := F.filter (fun p => IsPt p (D.r + 1)) with hF0
  set S : Finset E := F0.biUnion fun p => (p.map Prod.snd).toFinset with hS
  have hS0 : (0 : E) ∉ S := by
    intro h
    simp only [hS, mem_biUnion, List.mem_toFinset, List.mem_map] at h
    obtain ⟨p, hp, b, hb, hb0⟩ := h
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hb
    exact ((Finset.mem_filter.1 hp).2.2 k hk).2 hb0
  set T : Tower E := FinitePointSets.tw S hS0 with hT
  set Y : Finset (Pt E) := T.X (D.r + 1) with hY
  have hYpt : ∀ p ∈ Y, IsPt p (D.r + 1) := by
    intro p hp
    obtain ⟨h1, h2⟩ := (T.isTower (D.r + 1) p).1 hp
    refine ⟨h1, fun k hk => ⟨(h2 k hk).1, fun h => ?_⟩⟩
    have := (h2 k hk).2
    rw [h] at this
    exact T.zero_not_mem _ _ this
  have hF0Y : ∀ p ∈ F0, p ∈ Y := by
    intro p hp
    have hp' := (Finset.mem_filter.1 hp).2
    refine (T.isTower (D.r + 1) p).2 ⟨hp'.1, fun k hk => ⟨(hp'.2 k hk).1, ?_⟩⟩
    change (p[k]'hk).2 ∈ S
    simp only [hS, mem_biUnion, List.mem_toFinset, List.mem_map]
    exact ⟨p, hp, p[k]'hk, List.getElem_mem hk, rfl⟩
  refine ⟨F ∪ Y, Finset.subset_union_left, ?_⟩
  have e : ∀ ρ, ∑ p ∈ F ∪ Y, c ρ p • Vt p = ∑ p ∈ Y, c ρ p • Vt p := by
    intro ρ
    symm
    refine Finset.sum_subset Finset.subset_union_right fun p hp hnp => ?_
    have hc : c ρ p = 0 := by
      by_contra h
      have hpF : p ∈ F := by
        rcases Finset.mem_union.1 hp with h' | h'
        · exact h'
        · exact absurd h' hnp
      exact hnp (hF0Y p (Finset.mem_filter.2 ⟨hpF, hA1 ρ p h⟩))
    rw [hc, zero_smul]
  simp_rw [e]
  refine (FinitePointSets.rows_le_form Y (D.Kr (D.r + 1)) Vt c R (hA2 Y hYpt R)).trans ?_

  have key : ∀ δ : ℝ, 0 < δ →
      (∑ p ∈ Y, ∑ q ∈ Y, D.Kr (D.r + 1) p q * ⟪Vt q, Vt p⟫).re ≤ B * (jn + δ) := by
    intro δ hδ
    have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ w ∈ D.Wb D.Ntop,
        (D.gram ε 0 w [] []).re / D.wt w ≤ jn + δ :=
      (Filter.eventually_all_finset _).2 fun w hw =>
        (hE w hw).eventually_le_const (by linarith)
    obtain ⟨ε, h1ε, h2ε, hε⟩ := (h1.and ((hC Y hYpt).and self_mem_nhdsWithin)).exists
    have h3 := hB T ε hε (jn + δ) h1ε
    have e2 : D.Sf ε (D.r + 1) D.emp (T.X (D.r + 1))
        = (∑ p ∈ Y, ∑ q ∈ Y, D.Kr (D.r + 1) p q * ⟪Vt q, Vt p⟫).re := by
      unfold Data.Sf
      congr 1
      refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
      by_cases hK : D.Kr (D.r + 1) p q = 0
      · rw [hK, zero_mul, zero_mul]
      · rw [h2ε p hp q hq hK]
    rwa [e2] at h3
  have ht : Tendsto (fun δ : ℝ => B * (jn + δ)) (𝓝[>] 0) (𝓝 (B * (jn + 0))) :=
    (Continuous.tendsto (by fun_prop) 0).mono_left nhdsWithin_le_nhds
  rw [add_zero] at ht
  exact ge_of_tendsto ht (by filter_upwards [self_mem_nhdsWithin] with δ hδ using key δ hδ)

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.FormDomination
namespace Formalism.FourierDecayAlt.P.FormDomination

open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data

open scoped ComplexOrder

theorem form_nonneg {α : Type} (Y : Finset α) (k g : α → α → ℂ) (hk : PSDOn Y k)
    (hg : PSDOn Y g) : 0 ≤ (∑ a ∈ Y, ∑ b ∈ Y, k a b * g a b).re := by
  have H := (Matrix.PosSemidef.hadamard hk hg).dotProduct_mulVec_nonneg (fun _ => (1 : ℂ))
  have e : star (fun _ : Y => (1 : ℂ)) ⬝ᵥ
      ((Matrix.hadamard (Matrix.of fun x y : Y => k x y) (Matrix.of fun x y : Y => g x y)).mulVec
        (fun _ => (1 : ℂ))) = ∑ a ∈ Y, ∑ b ∈ Y, k a b * g a b := by
    simp only [dotProduct, Matrix.mulVec, Matrix.hadamard_apply, Matrix.of_apply, Pi.star_apply,
      star_one, one_mul, mul_one]
    rw [← Finset.sum_coe_sort Y]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_coe_sort Y]
  rw [e] at H
  exact (Complex.le_def.1 H).1

theorem form_dom {α ι : Type} (Y : Finset α) (R : Finset ι) (c : ℝ) (k g : α → α → ℂ)
    (Th : ι → α → α → ℂ)
    (h : PSDOn Y (fun a b => (c : ℂ) * k a b - ∑ t ∈ R, Th t a b)) (hg : PSDOn Y g) :
    ∑ t ∈ R, (∑ a ∈ Y, ∑ b ∈ Y, Th t a b * g a b).re ≤
      c * (∑ a ∈ Y, ∑ b ∈ Y, k a b * g a b).re := by
  have H := form_nonneg Y _ g h hg
  have e : ∑ a ∈ Y, ∑ b ∈ Y, ((c : ℂ) * k a b - ∑ t ∈ R, Th t a b) * g a b =
      (c : ℂ) * ∑ a ∈ Y, ∑ b ∈ Y, k a b * g a b -
        ∑ t ∈ R, ∑ a ∈ Y, ∑ b ∈ Y, Th t a b * g a b := by
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    congr 1
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
  rw [e, Complex.sub_re, Complex.re_ofReal_mul] at H
  rw [← Complex.re_sum]
  linarith

theorem prob_le {α : Type} (S : Finset α) (θ g : α → ℝ) (hθ : IsProb S θ) (M : ℝ)
    (hg : ∀ a ∈ S, g a ≤ M) : ∑ a ∈ S, θ a * g a ≤ M := by
  calc ∑ a ∈ S, θ a * g a ≤ ∑ a ∈ S, θ a * M :=
        Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left (hg a ha) (hθ.1 a)
    _ = M := by rw [← Finset.sum_mul, hθ.2.2, one_mul]

theorem prob_nonneg {α : Type} (S : Finset α) (θ g : α → ℝ) (hθ : IsProb S θ)
    (hg : ∀ a ∈ S, 0 ≤ g a) : 0 ≤ ∑ a ∈ S, θ a * g a :=
  Finset.sum_nonneg fun a ha => mul_nonneg (hθ.1 a) (hg a ha)

variable {E W : Type} [Field E] (D : Data E W)

theorem baseGram_nonneg (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ} (hε : 0 < ε) (k : ℕ) (w : W)
    (Y : Finset (Pt E)) (κ : Pt E → Pt E → ℂ) (hκ : PSDOn Y κ) : 0 ≤ D.N0 ε k w Y κ :=
  div_nonneg (form_nonneg Y κ _ hκ (hG ε hε k w Y)) (hW w).le

theorem sum_baseGram_le (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ} (hε : 0 < ε) (k : ℕ) (w : W)
    (Y : Finset (Pt E)) (R : Finset E) (c : ℝ) (κ : Pt E → Pt E → ℂ)
    (Th : E → Pt E → Pt E → ℂ)
    (h : PSDOn Y (fun a b => (c : ℂ) * κ a b - ∑ t ∈ R, Th t a b)) :
    ∑ t ∈ R, D.N0 ε k w Y (Th t) ≤ c * D.N0 ε k w Y κ := by
  unfold Data.N0
  rw [← Finset.sum_div, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (form_dom Y R c κ _ Th h (hG ε hε k w Y)) (hW w).le

theorem mean_dom (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ} (hε : 0 < ε) (k : ℕ)
    (S : Finset W) (θ : W → ℝ) (hθ : IsProb S θ)
    (Y : Finset (Pt E)) (R : Finset E) (c : ℝ) (hc : 0 ≤ c) (κ : Pt E → Pt E → ℂ)
    (Th : E → Pt E → Pt E → ℂ)
    (h : PSDOn Y (fun a b => (c : ℂ) * κ a b - ∑ t ∈ R, Th t a b)) (M : ℝ)
    (hM : ∀ w' ∈ S, D.N0 ε k w' Y κ ≤ M) :
    ∑ t ∈ R, ∑ w' ∈ S, θ w' * D.N0 ε k w' Y (Th t) ≤ c * M := by
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  refine prob_le S θ _ hθ _ fun w' hw' => ?_
  exact (sum_baseGram_le D hG hW hε k w' Y R c κ Th h).trans (mul_le_mul_of_nonneg_left (hM w' hw') hc)

end Formalism.FourierDecayAlt.P.FormDomination

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.P.FormDomination

open Classical

theorem longBlockStep : Formalism.FourierDecayAlt.TB.MultiStep := by
  intro E W _ D C₄ hG hK hW hA hB hC hv T ε hε i s hs hsi hi w hw hcnt hvol R hR M hM
  obtain ⟨θ, hθ, hest⟩ := hB ε hε i s hs hsi hi w hw hcnt hvol
  obtain ⟨⟨he0, he1⟩, -, -, hdom⟩ := hA i s (by omega) hsi hi
  have hY : ∀ h ∈ T.X (i - s), level h = i - s := fun h hh => ((T.isTower _ _).1 hh).1
  have hc : 0 ≤ C₄ ^ (D.f * s) * (∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') :=
    mul_nonneg (pow_nonneg (by linarith) _) (Finset.prod_nonneg fun s' _ => hv _ _)
  have hd := hdom R hR (T.X (i - s)) hY
  have hd' : PSDOn (T.X (i - s)) (fun a b => (((1 + D.e i : ℝ)) : ℂ) * D.Kr (i - s) a b -
      ∑ t ∈ R, D.Th i s t a b) := by
    push_cast; exact hd
  calc ∑ t₀ ∈ R, ∑ t ∈ (T.Sg (i - s + 1) s).filter (fun t => t - t₀ ∈ D.La (i - s + 1) s),
            (D.Nst ε i s w (T.X (i - s)) (D.Th i s t₀) t t).re
      ≤ ∑ t₀ ∈ R, C₄ ^ (D.f * s) * (∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') *
          ∑ w' ∈ D.Wb (D.cnt w + (s + 1) * D.K),
            θ w' * D.N0 ε (i - s) w' (T.X (i - s)) (D.Th i s t₀) := by
        refine Finset.sum_le_sum fun t₀ _ => ?_
        refine hest (T.X (i - s)) hY _ (hK.2 i s t₀ _) t₀ _ fun t ht => ?_
        rw [Finset.mem_filter] at ht
        exact ⟨fun h0 => T.zero_not_mem _ _ (h0 ▸ ht.1), ht.2⟩
    _ = C₄ ^ (D.f * s) * (∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') *
          ∑ t₀ ∈ R, ∑ w' ∈ D.Wb (D.cnt w + (s + 1) * D.K),
            θ w' * D.N0 ε (i - s) w' (T.X (i - s)) (D.Th i s t₀) := by
        rw [Finset.mul_sum]
    _ ≤ C₄ ^ (D.f * s) * (∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') * ((1 + D.e i) * M) :=
        mul_le_mul_of_nonneg_left
          (mean_dom D hG hW hε (i - s) _ θ hθ _ R (1 + D.e i) (by linarith) _ _ hd' M hM) hc

theorem singleBlockStep : Formalism.FourierDecayAlt.TB.OneStep := by
  intro E W _ D ep hG hK hW hA hWv hP hL T ε hε i hi1 hi w hw hcnt R hR M hM
  obtain ⟨θ, hθ, hest⟩ := hWv ε hε i hi1 hi w hw hcnt
  obtain ⟨⟨he0, he1⟩, -, -, hdom⟩ := hA i 1 le_rfl hi1 hi
  have hii : i - 1 + 1 = i := Nat.sub_add_cancel hi1
  rw [hii] at hdom
  have hY : ∀ h ∈ T.X (i - 1), level h = i - 1 := fun h hh => ((T.isTower _ _).1 hh).1
  have hep : 0 ≤ ep := by simpa using hL.1 i hi1 hi ∅ (by simp)
  have hd := hdom R hR (T.X (i - 1)) hY
  have hd' : PSDOn (T.X (i - 1)) (fun a b => (((1 + D.e i : ℝ)) : ℂ) * D.Kr (i - 1) a b -
      ∑ t ∈ R, D.Th i 1 t a b) := by
    push_cast; exact hd
  have h1e : 0 ≤ 1 + D.e i := by linarith

  set g : Finset (Fin D.f) → E → ℝ := fun A t₀ => ∑ w' ∈ D.Wb (D.cnt w + D.K),
    θ A w' * D.N0 ε (i - 1) w' (T.X (i - 1)) (D.Th i 1 t₀) with hg
  have hg0 : ∀ A t₀, 0 ≤ g A t₀ := fun A t₀ =>
    prob_nonneg _ _ _ (hθ A) fun w' _ => baseGram_nonneg D hG hW hε _ _ _ _ (hK.2 i 1 t₀ _)
  have hstep : ∀ t₀ ∈ R, ∑ t ∈ (T.Sg i 1).filter (fun t => t - t₀ ∈ D.La i 1),
      (D.Nst ε i 1 w (T.X (i - 1)) (D.Th i 1 t₀) t t).re ≤
        D.N0 ε (i - 1) w (T.X (i - 1)) (D.Th i 1 t₀) + ep * ∑ A, g A t₀ := by
    intro t₀ _
    have hpsd := hK.2 i 1 t₀ (T.X (i - 1))
    obtain ⟨h0, hl⟩ := hest (T.X (i - 1)) hY _ hpsd
    have hbound : ∀ L : Finset E, (∀ l ∈ L, l ∈ D.Lad i ∧ l ≠ 0) →
        ∑ l ∈ L, ‖D.Nhat ε i w (T.X (i - 1)) (D.Th i 1 t₀) l‖ ≤ ep * ∑ A, g A t₀ := by
      intro L hLm
      have hG0 : 0 ≤ ∑ A, g A t₀ := Finset.sum_nonneg fun A _ => hg0 A t₀
      have h1 : ∀ l ∈ L, ‖D.Nhat ε i w (T.X (i - 1)) (D.Th i 1 t₀) l‖ ≤
          max (D.maj (D.szD i) l) 0 * ∑ A, g A t₀ := by
        intro l hl'
        obtain ⟨A, hA'⟩ := hl l (hLm l hl').1 (hLm l hl').2
        calc ‖D.Nhat ε i w (T.X (i - 1)) (D.Th i 1 t₀) l‖ ≤ D.maj (D.szD i) l * g A t₀ := hA'
          _ ≤ max (D.maj (D.szD i) l) 0 * g A t₀ :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (hg0 A t₀)
          _ ≤ max (D.maj (D.szD i) l) 0 * ∑ A, g A t₀ :=
              mul_le_mul_of_nonneg_left
                (Finset.single_le_sum (f := fun A => g A t₀) (fun A _ => hg0 A t₀)
                  (Finset.mem_univ A)) (le_max_right _ _)
      have h2 : ∑ l ∈ L, max (D.maj (D.szD i) l) 0 ≤ ep := by
        have h3 := hL.1 i hi1 hi (L.filter fun l => 0 ≤ D.maj (D.szD i) l)
          (fun l hl' => hLm l (Finset.mem_filter.1 hl').1)
        rw [Finset.sum_filter] at h3
        refine le_trans (le_of_eq (Finset.sum_congr rfl fun l _ => ?_)) h3
        split_ifs with hh
        · exact max_eq_left hh
        · exact max_eq_right (not_le.1 hh).le
      calc ∑ l ∈ L, ‖D.Nhat ε i w (T.X (i - 1)) (D.Th i 1 t₀) l‖
          ≤ ∑ l ∈ L, max (D.maj (D.szD i) l) 0 * ∑ A, g A t₀ := Finset.sum_le_sum h1
        _ = (∑ l ∈ L, max (D.maj (D.szD i) l) 0) * ∑ A, g A t₀ := by rw [Finset.sum_mul]
        _ ≤ ep * ∑ A, g A t₀ := mul_le_mul_of_nonneg_right h2 hG0
    have hp := hP ε hε i hi1 hi w (T.X (i - 1)) hY _ hpsd t₀ _ hbound
      ((T.Sg i 1).filter (fun t => t - t₀ ∈ D.La i 1)) (fun t ht => by
        rw [Finset.mem_filter] at ht
        exact ⟨fun h0 => T.zero_not_mem _ _ (h0 ▸ ht.1), ht.2⟩)
    rw [h0, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (baseGram_nonneg D hG hW hε _ _ _ _ hpsd)] at hp
    exact hp
  have hsumG : ∑ t₀ ∈ R, ∑ A, g A t₀ ≤ 2 ^ D.f * ((1 + D.e i) * M) := by
    rw [Finset.sum_comm]
    calc ∑ A : Finset (Fin D.f), ∑ t₀ ∈ R, g A t₀
        ≤ ∑ _A : Finset (Fin D.f), (1 + D.e i) * M :=
          Finset.sum_le_sum fun A _ =>
            mean_dom D hG hW hε (i - 1) _ (θ A) (hθ A) _ R (1 + D.e i) h1e _ _ hd' M hM
      _ = 2 ^ D.f * ((1 + D.e i) * M) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast; ring
  calc ∑ t₀ ∈ R, ∑ t ∈ (T.Sg i 1).filter (fun t => t - t₀ ∈ D.La i 1),
            (D.Nst ε i 1 w (T.X (i - 1)) (D.Th i 1 t₀) t t).re
      ≤ ∑ t₀ ∈ R, (D.N0 ε (i - 1) w (T.X (i - 1)) (D.Th i 1 t₀) + ep * ∑ A, g A t₀) :=
        Finset.sum_le_sum hstep
    _ = ∑ t₀ ∈ R, D.N0 ε (i - 1) w (T.X (i - 1)) (D.Th i 1 t₀) +
          ep * ∑ t₀ ∈ R, ∑ A, g A t₀ := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (1 + D.e i) * D.N0 ε (i - 1) w (T.X (i - 1)) (D.Kr (i - 1)) +
          ep * (2 ^ D.f * ((1 + D.e i) * M)) :=
        add_le_add (sum_baseGram_le D hG hW hε (i - 1) w _ R (1 + D.e i) _ _ hd')
          (mul_le_mul_of_nonneg_left hsumG hep)
    _ = (1 + D.e i) * (D.N0 ε (i - 1) w (T.X (i - 1)) (D.Kr (i - 1)) + 2 ^ D.f * ep * M) := by
        ring

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.MeanPositiveSemidefinite
noncomputable section

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite

section PSD

variable {X : Type}

theorem psd_congr {F : Finset X} {k k' : X → X → ℂ} (h : ∀ x ∈ F, ∀ y ∈ F, k x y = k' x y)
    (hk : IsPSD F k) : IsPSD F k' := by
  intro a
  have : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k' x y =
      ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y :=
    Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => by rw [h x hx y hy]
  rw [this]; exact hk a

theorem psd_zero (F : Finset X) : IsPSD F (fun _ _ => (0 : ℂ)) := by
  intro a; simp

theorem psd_add {F : Finset X} {k k' : X → X → ℂ} (hk : IsPSD F k) (hk' : IsPSD F k') :
    IsPSD F (fun x y => k x y + k' x y) := by
  intro a
  have : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * (k x y + k' x y) =
      (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y) +
        ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k' x y := by
    simp only [mul_add, Finset.sum_add_distrib]
  rw [this, Complex.add_im, Complex.add_re, (hk a).1, (hk' a).1]
  exact ⟨by simp, add_nonneg (hk a).2 (hk' a).2⟩

theorem psd_sum {ι : Type} (S : Finset ι) {F : Finset X} {k : ι → X → X → ℂ}
    (hk : ∀ i ∈ S, IsPSD F (k i)) : IsPSD F (fun x y => ∑ i ∈ S, k i x y) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using psd_zero F
  | insert i S hi ih =>
    have := psd_add (hk i (Finset.mem_insert_self _ _))
      (ih fun j hj => hk j (Finset.mem_insert_of_mem hj))
    refine psd_congr ?_ this
    intro x _ y _; rw [Finset.sum_insert hi]

theorem psd_smul {F : Finset X} {k : X → X → ℂ} (c : ℝ) (hc : 0 ≤ c) (hk : IsPSD F k) :
    IsPSD F (fun x y => (c : ℂ) * k x y) := by
  intro a
  have : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * ((c : ℂ) * k x y) =
      (c : ℂ) * ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  rw [this, Complex.re_ofReal_mul, Complex.im_ofReal_mul, (hk a).1]
  exact ⟨by simp, mul_nonneg hc (hk a).2⟩

end PSD

theorem finite_classes {K : Type} [AddCommGroup K] (R P : AddSubgroup K) (h : R.relIndex P ≠ 0) :
    {x : K ⧸ R | (Quotient.out x : K) ∈ P}.Finite := by
  have hfi : (R.addSubgroupOf P).FiniteIndex := ⟨h⟩
  have : Finite (P ⧸ R.addSubgroupOf P) := inferInstance
  refine (Set.finite_range
    (fun q : P ⧸ R.addSubgroupOf P => (((Quotient.out q : P) : K) : K ⧸ R))).subset ?_
  intro x hx
  refine ⟨((⟨Quotient.out x, hx⟩ : P) : P ⧸ R.addSubgroupOf P), ?_⟩
  have h1 : ((Quotient.out ((⟨Quotient.out x, hx⟩ : P) : P ⧸ R.addSubgroupOf P) : P) :
      P ⧸ R.addSubgroupOf P) = ((⟨Quotient.out x, hx⟩ : P) : P ⧸ R.addSubgroupOf P) :=
    QuotientAddGroup.out_eq' _
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h1
  have h2 : (((Quotient.out ((⟨Quotient.out x, hx⟩ : P) : P ⧸ R.addSubgroupOf P) : P) : K) :
      K ⧸ R) = ((Quotient.out x : K) : K ⧸ R) := by
    rw [QuotientAddGroup.eq]; simpa using h1
  exact h2.trans (QuotientAddGroup.out_eq' x)

theorem finsum_ite_eq {α : Type} (S : Finset α) (p : α → Prop) [DecidablePred p] (f : α → ℂ)
    (hS : ∀ x, p x → x ∈ S) :
    ∑ᶠ x, (if p x then f x else 0) = ∑ x ∈ S, if p x then f x else 0 := by
  refine finsum_eq_sum_of_support_subset _ ?_
  intro x hx
  by_cases hp : p x
  · exact hS x hp
  · simp [hp] at hx

theorem mean_sub {K : Type} (A B : Finset K) (hA : A.card ≠ 0) (hB : B.card ≠ 0) (Y : ℂ)
    (u : K → K → ℂ) :
    Y - ((A.card : ℂ) * (B.card : ℂ))⁻¹ * ∑ ρ ∈ A, ∑ b ∈ B, u ρ b =
      ∑ ρ ∈ A, ∑ b ∈ B, ((((A.card : ℝ) * (B.card : ℝ))⁻¹ : ℝ) : ℂ) * (Y - u ρ b) := by
  have hA' : (A.card : ℂ) ≠ 0 := by exact_mod_cast hA
  have hB' : (B.card : ℂ) ≠ 0 := by exact_mod_cast hB
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  push_cast
  field_simp

theorem reps_card_ne_zero {K : Type} [CommRing K] {S : Finset K} {L M : AddSubgroup K}
    (h : IsReps S L M) : S.card ≠ 0 := by
  obtain ⟨a, ha, _⟩ := h.2 0 L.zero_mem
  exact Finset.card_ne_zero_of_mem ha.1

end Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite

open Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite in
theorem Formalism.FourierDecayAlt.P.thetaOnDomainOfSteps : Formalism.FourierDecayAlt.A6.ThOmAssemble := by
  intro hGI hADE hLC hKH hMLC hLCh hLF hSU hSmU hUG hUNB hCP hUB hCSA hMM hKG hKBD hGRC hAB hPG hPD
    hPL hCM hCNE hTL hTB hTS hA2 hN1 K _ _ _ R ψ hD hch m hm hA13 n₀ F Lc Om hF hCut hOm
  classical
  obtain ⟨hLo, hLcpt, hRL, hNs0⟩ := hCut
  obtain ⟨D⟩ := hADE hLC hKH hMLC hLCh hLF K R ψ hD hch (m + 1) F Om (Lc : Set K) (by omega) hOm
    hLcpt
  obtain ⟨V₁, hV₁, hLow⟩ := hTL hGI hA2.2 hUG hN1 hCSA hMM hCP hKG hGRC hAB hCNE hCM hPL K R ψ hD hch
    m hm n₀ F Om (Lc : Set K) hF hOm D
  obtain ⟨V₂, hV₂, hSh⟩ := hSU K R ψ hD hch ((D.A ×ˢ D.B).image (fun p => p.1 + p.2))
  obtain ⟨t, ht⟩ := hSmU K R ψ hD hch (V₁ ∩ V₂) (Filter.inter_mem hV₁ hV₂)

  let τ : K → Kˣ := fun σ =>
    if h : IsUnit (((t⁻¹ : Kˣ) : K) + σ) then h.unit⁻¹ else 1
  have hmem : ∀ ρ ∈ D.A, ∀ b ∈ D.B, ρ + b ∈ (D.A ×ˢ D.B).image (fun p => p.1 + p.2) := by
    intro ρ hρ b hb
    exact Finset.mem_image.2 ⟨(ρ, b), Finset.mem_product.2 ⟨hρ, hb⟩, rfl⟩
  have hτ : ∀ ρ ∈ D.A, ∀ b ∈ D.B, IsShift t (τ (ρ + b)) (ρ + b) := by
    intro ρ hρ b hb
    have hu := (hSh t ht.2 _ (hmem ρ hρ b hb)).1
    simp only [IsShift, τ, dif_pos hu, inv_inv, IsUnit.unit_spec]
  have hτmod : ∀ ρ ∈ D.A, ∀ b ∈ D.B,
      modK R (τ (ρ + b) : K) * modK R ((t⁻¹ : Kˣ) : K) = modK R 1 := by
    intro ρ hρ b hb
    have h1 := (hSh t ht.2 _ (hmem ρ hρ b hb)).2
    have h2 := (hMM K R ψ hD (τ (ρ + b)) (τ (ρ + b))⁻¹).2
    rw [hτ ρ hρ b hb] at h2
    rw [← h1, ← h2, ← hτ ρ hρ b hb, Units.mul_inv]
  have htpos : 0 < modK R ((t⁻¹ : Kˣ) : K) := (hMM K R ψ hD t⁻¹ 1).1

  have hcrex : ∀ x : K ⧸ R.toAddSubgroup, ∃ u : Kˣ, ((u : K) : K ⧸ R.toAddSubgroup) = x := by
    intro x
    obtain ⟨r, hr, hu⟩ := hD.unitRep (Quotient.out x)
    refine ⟨hu.unit, ?_⟩
    rw [IsUnit.unit_spec, QuotientAddGroup.mk_add, QuotientAddGroup.out_eq',
      (QuotientAddGroup.eq_zero_iff r).2 hr, add_zero]
  choose cr hcr using hcrex
  have hcr' : IsCr R cr := hcr
  have hBR : ∀ b ∈ D.B, b ∈ R := fun b hb => D.repsB.1 b hb
  obtain ⟨hper, hpsd⟩ := hTB hCP hKG hN1 hMM K R ψ hD m n₀ F D.A D.B τ cr hF hcr' hBR
  obtain ⟨Θm, hΘm⟩ := hA13 n₀ F hF
  refine ⟨fun z h h' => if z ∈ Lc then thx R ψ m cr D.A D.B τ z h h' else 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x r hr
    have hiff : x + r ∈ Lc ↔ x ∈ Lc := by
      constructor
      · intro h
        have := Lc.sub_mem h (hRL r hr)
        simpa using this
      · intro h; exact Lc.add_mem h (hRL r hr)
    funext h h'
    simp only [hiff, hper x r hr]
  ·
    intro x
    by_cases hx : x ∈ Lc
    · simpa only [hx, if_true] using hpsd x
    · simpa only [hx, if_false] using psd_zero F
  ·
    intro x hx h _ h' _
    simp only [hx, if_false]
  ·
    intro t' ht'
    by_cases hx : (t' : K) ∈ Lc
    · have := hLow t τ cr ht.1 hcr' hτ (t' : K) ht'
      refine psd_congr ?_ this
      intro h _ h' _
      have hu : IsUnit (t' : K) := t'.isUnit
      have hu' : hu.unit = t' := Units.ext rfl
      simp only [hx, if_true, NsK, dif_pos hu, hu']
    · refine psd_congr ?_ (psd_zero F)
      intro h hh h' hh'
      simp only [hx, if_false, hNs0 t' hx h hh h' hh', sub_zero]
  ·
    have hPlat := (hPL K R ψ hD hch D.L₁ D.lat₁).1
    have hRlat : IsLat R.toAddSubgroup := ⟨hD.isOpen, hD.isCompact⟩
    have hfin := finite_classes R.toAddSubgroup (perp ψ D.L₁)
      (hLF K (perp ψ D.L₁) R.toAddSubgroup hPlat hRlat)
    have hS : ∀ x : K ⧸ R.toAddSubgroup, (Quotient.out x : K) ∈ perp ψ D.L₁ → x ∈ hfin.toFinset :=
      fun x hx => hfin.mem_toFinset.2 hx
    have hAc := reps_card_ne_zero D.repsA
    have hBc := reps_card_ne_zero D.repsB
    have hp1 : IsPSD F (fun h h' => ∑ ρ ∈ D.A, ∑ b ∈ D.B,
        ((((D.A.card : ℝ) * (D.B.card : ℝ))⁻¹ : ℝ) : ℂ) *
          (((cSize R h ^ (m + 1) * cSize R h' ^ (m + 1) : ℝ) : ℂ) * N0 R ψ h h' -
            uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b)))) := by
      refine psd_sum D.A fun ρ _ => psd_sum D.B fun b _ => psd_smul _ (by positivity) ?_
      exact hUNB hUG hN1 hCSA hMM hLF K R ψ hD m n₀ F Θm hF hΘm (τ (ρ + b)) cr hcr'
    have hp2 : IsPSD F (fun h h' => ∑ x ∈ hfin.toFinset,
        if (Quotient.out x : K) ∈ Lc then 0 else thx R ψ m cr D.A D.B τ (Quotient.out x) h h') := by
      refine psd_sum _ fun x _ => ?_
      by_cases hx : (Quotient.out x : K) ∈ Lc
      · simpa only [hx, if_true] using psd_zero F
      · simpa only [hx, if_false] using hpsd _
    refine psd_congr ?_ (psd_add hp1 hp2)
    intro h hh h' hh'
    have hsum := hTS hPG hPD hPL hLF hGRC hCP hKG hN1 hMM K R ψ hD hch m (m + 1) n₀ F Om (Lc : Set K) D
      τ cr hF hcr' h hh h' hh'
    rw [← mean_sub D.A D.B hAc hBc, ← hsum]
    rw [finsum_ite_eq hfin.toFinset (fun x : K ⧸ R.toAddSubgroup => (Quotient.out x : K) ∈ perp ψ D.L₁)
      (fun x => thx R ψ m cr D.A D.B τ (Quotient.out x) h h') hS]
    rw [finsum_ite_eq hfin.toFinset (fun x : K ⧸ R.toAddSubgroup => (Quotient.out x : K) ∈ Lc)
      (fun x => thx R ψ m cr D.A D.B τ (Quotient.out x) h h')
      (fun x hx => hS x (D.cutPerp _ hx))]
    rw [sub_add, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxP : (Quotient.out x : K) ∈ perp ψ D.L₁ := hfin.mem_toFinset.1 hx
    by_cases hxL : (Quotient.out x : K) ∈ Lc
    · simp only [hxP, hxL, if_true, sub_zero]
    · simp only [hxP, hxL, if_true, if_false, sub_self]
  ·
    intro x h _ h' _ hne
    by_cases hx : x ∈ Lc
    · simp only [hx, if_true, thx]
      have hz : ∀ ρ ∈ D.A, ∀ b ∈ D.B, ∀ b' ∈ D.B,
          uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b')) = 0 := by
        intro ρ hρ b hb b' hb'
        refine hUB hKBD hCSA hMM K R ψ hD m cr Set.univ h h' _ _ ?_ hne
        exact mul_right_cancel₀ htpos.ne' ((hτmod ρ hρ b hb).trans (hτmod ρ hρ b' hb').symm)
      have : ∑ ρ ∈ D.A, ((D.B.card : ℂ)⁻¹) ^ 2 * ∑ b ∈ D.B, ∑ b' ∈ D.B,
          ψ (-(x * b)) * conj (ψ (-(x * b'))) *
            uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b')) = 0 := by
        refine Finset.sum_eq_zero fun ρ hρ => ?_
        rw [Finset.sum_eq_zero fun b hb => Finset.sum_eq_zero fun b' hb' => by
          rw [hz ρ hρ b hb b' hb', mul_zero], mul_zero]
      rw [this, mul_zero]
    · simp only [hx, if_false]
end
end
