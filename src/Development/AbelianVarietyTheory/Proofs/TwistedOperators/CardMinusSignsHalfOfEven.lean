module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SupportParahoricBiTransformingLeviDoubleCoset
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivedAdjoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardMinusSignsHalfOfEven
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardMinusSignsHalfOfEven
open Formalism.L2.Theta

namespace GlobalTheory.SignedHC

open Finset

theorem card_minus_of_isEnum {n : ℕ} {S : Finset (ℚ × Bool)} {lam : Fin n → ℝ} {ε : Fin n → Bool} (h : IsEnum S lam ε) :
    (univ.filter fun a => ε a = false).card = nMinus S := by
  obtain ⟨hanti, f, hf, rfl⟩ := h
  have hinj : Function.Injective f := fun a b h => hanti.injective (by rw [hf, hf, h])
  rw [nMinus, filter_image, card_image_of_injective _ fun a b h => hinj (congrArg Prod.fst h)]

namespace GridData

theorem nMinus_lam_of_even (G : GridData) (hm : Even G.m) (hg : 0 < G.ga) : nMinus G.lam = G.m / 2 := by
  obtain ⟨k, hk⟩ := hm
  have hS : G.lam.filter (fun x => x.2 = false) = (range k).image fun j => (G.a (2 * j + 1), false) := by
    ext x
    simp only [mem_filter, mem_lam, mem_image, mem_range]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩ | ⟨-, h⟩, h2⟩
      · simp only [decide_eq_false_iff_not, Nat.not_even_iff] at h2
        refine ⟨i / 2, by omega, ?_⟩
        have e : 2 * (i / 2) + 1 = i := by omega
        have : ¬ Even (G.m - i) := by rw [Nat.not_even_iff]; exact h2
        simp [e, this]
      · simp [h] at h2
    · rintro ⟨j, hj, rfl⟩
      have : ¬ Even (G.m - (2 * j + 1)) := by rw [Nat.not_even_iff]; omega
      exact ⟨Or.inl ⟨2 * j + 1, by omega, by simp [this]⟩, rfl⟩
  rw [nMinus, hS, card_image_of_injective, card_range]
  · omega
  · intro i j h
    have h1 : G.a (2 * i + 1) = G.a (2 * j + 1) := congrArg Prod.fst h
    have h2 := G.a_sub_a (2 * i + 1) (2 * j + 1)
    rw [h1, sub_self] at h2
    have hg' : (G.ga : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
    have h3 := sub_eq_zero.1 ((mul_eq_zero.1 h2.symm).resolve_right hg')
    have h4 : 2 * j + 1 = 2 * i + 1 := by exact_mod_cast h3
    omega

theorem minus_signs_of_D0_eq_half (G : GridData) : nMinus G.parD0 = G.m / 2 := by
  have hS : G.parD0.filter (fun x => x.2 = false) =
      (range (G.m / 2)).image fun j => (-(G.b (2 * j + 2) : ℚ), false) := by
    ext x
    simp only [mem_filter, mem_discrete_parameter_iff, mem_image, mem_range]
    constructor
    · rintro ⟨⟨-, h⟩ | ⟨i, hi, hi', rfl⟩, h2⟩
      · simp [h] at h2
      · simp only [decide_eq_false_iff_not, Nat.not_even_iff] at h2
        refine ⟨i / 2 - 1, by omega, ?_⟩
        have e : 2 * (i / 2 - 1) + 2 = i := by omega
        have : ¬ Even (i - 1) := by rw [Nat.not_even_iff]; exact h2
        simp [e, this]
    · rintro ⟨j, hj, rfl⟩
      have : ¬ Even (2 * j + 2 - 1) := by rw [Nat.not_even_iff]; omega
      exact ⟨Or.inr ⟨2 * j + 2, by omega, by omega, by rw [decide_eq_false this]⟩, rfl⟩
  rw [nMinus, hS, card_image_of_injOn, card_range]
  intro i hi j hj h
  have h1 : -(G.b (2 * i + 2) : ℚ) = -(G.b (2 * j + 2) : ℚ) := congrArg Prod.fst h
  have h2 : G.b (2 * i + 2) = G.b (2 * j + 2) := by exact_mod_cast neg_injective h1
  have hi' : i < G.m / 2 := by simpa using hi
  have hj' : j < G.m / 2 := by simpa using hj
  rcases lt_trichotomy i j with hl | hl | hl
  · have := G.b_mono (2 * i + 2) (2 * j + 2) (by omega) (by omega) (by omega); omega
  · exact hl
  · have := G.b_mono (2 * j + 2) (2 * i + 2) (by omega) (by omega) (by omega); omega

theorem card_minus_signs_interlacing_parameters {G : GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool}
    {mu : Fin n → ℝ} {ε' : Fin n → Bool} (hm : Even G.m) (hg : 0 < G.ga) (h1 : IsEnum (G.parPi 0) lam ε)
    (h2 : IsEnum G.parD0 mu ε') :
    (Finset.univ.filter fun a => ε a = false).card = G.m / 2 ∧
      (Finset.univ.filter fun i => ε' i = false).card = G.m / 2 :=
  ⟨by rw [card_minus_of_isEnum h1, G.parPi_zero, G.nMinus_lam_of_even hm hg],
    by rw [card_minus_of_isEnum h2, G.minus_signs_of_D0_eq_half]⟩

end GridData

end GlobalTheory.SignedHC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardMinusSignsHalfOfEvenStatement
open Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_minus_signs_half_of_even : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool} {mu : Fin n → ℝ} {ε' : Fin n → Bool}, Even G.m → 0 < G.ga → IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' → (Finset.univ.filter fun a => ε a = false).card = G.m / 2 ∧ (Finset.univ.filter fun i => ε' i = false).card = G.m / 2 := by
  first | exact @GlobalTheory.SignedHC.GridData.card_minus_signs_interlacing_parameters | exact GlobalTheory.SignedHC.GridData.card_minus_signs_interlacing_parameters | (intros; apply GlobalTheory.SignedHC.GridData.card_minus_signs_interlacing_parameters <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParametersSeparatedByOne
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParametersSeparatedByOne
open Formalism.L2.Theta

namespace GlobalTheory.WordSep

open GlobalTheory.SignedHC

private theorem v_le {G : GridData} {i j : ℕ} (hi : 2 ≤ i) (hij : i ≤ j) (hj : j ≤ G.k) : G.v j ≤ G.v i := by
  rcases hij.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (G.v_anti i j hi h hj).le

private theorem b_ge {G : GridData} {l : ℕ} (hl : 1 ≤ l) (hlm : l ≤ G.m) : G.b 1 ≤ G.b l := by
  rcases hl.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (G.b_mono 1 l le_rfl h hlm).le

theorem sep_rat {G : GridData} (hga : 0 < G.ga)
    (hgap : ∀ i, 2 ≤ i → i < G.k → G.v (i + 1) + 2 ≤ G.v i) (hb : 2 ≤ G.v G.k + G.b 1)
    {x y : ℚ} (hx : (∃ l, l ≤ G.m ∧ x = G.a l) ∨ ∃ j, 2 ≤ j ∧ j ≤ G.k ∧ x = G.vHalf j)
    (hy : (∃ j, 2 ≤ j ∧ j ≤ G.k ∧ y = G.v j) ∨ ∃ l, 1 ≤ l ∧ l ≤ G.m ∧ y = -(G.b l : ℚ)) :
    (y < x → y + 1 < x) ∧ x ≠ y := by
  have hk := G.two_le_k
  rcases hx with ⟨l, hl, rfl⟩ | ⟨j, hj2, hjk, rfl⟩
  · have hal : (G.v 2 : ℚ) + 3 / 2 ≤ G.a l := by
      unfold GridData.a
      have h1 : (1 : ℚ) ≤ (G.m : ℚ) + 1 - l := by
        have : (l : ℚ) ≤ G.m := by exact_mod_cast hl
        linarith
      have h2 : (1 : ℚ) ≤ G.ga := by exact_mod_cast hga
      nlinarith
    obtain ⟨z, hz, hzle⟩ : ∃ z : ℤ, y = z ∧ z ≤ G.v 2 := by
      rcases hy with ⟨j, hj2, hjk, rfl⟩ | ⟨l', hl1, hlm, rfl⟩
      · exact ⟨_, rfl, v_le le_rfl hj2 hjk⟩
      · refine ⟨-G.b l', by push_cast; ring, ?_⟩
        have := b_ge (G := G) hl1 hlm
        have := v_le (G := G) le_rfl hk le_rfl
        linarith
    have : (z : ℚ) ≤ G.v 2 := by exact_mod_cast hzle
    subst hz
    constructor
    · intro _; linarith
    · intro h; linarith
  · obtain ⟨z, hz, hzc⟩ : ∃ z : ℤ, y = z ∧ (G.v j ≤ z ∨ z ≤ G.v j - 2) := by
      rcases hy with ⟨j', hj2', hjk', rfl⟩ | ⟨l', hl1, hlm, rfl⟩
      · refine ⟨_, rfl, ?_⟩
        rcases le_or_gt j' j with h | h
        · exact Or.inl (v_le hj2' h hjk)
        · right
          have h1 := v_le (G := G) (by omega : 2 ≤ j + 1) (by omega : j + 1 ≤ j') hjk'
          have h2 := hgap j hj2 (by omega)
          linarith
      · refine ⟨-G.b l', by push_cast; ring, Or.inr ?_⟩
        have := b_ge (G := G) hl1 hlm
        have := v_le (G := G) hj2 hjk le_rfl
        linarith
    subst hz
    unfold GridData.vHalf
    rcases hzc with h | h
    · have : (G.v j : ℚ) ≤ z := by exact_mod_cast h
      constructor
      · intro h'; linarith
      · intro h'; linarith
    · have : (z : ℚ) ≤ G.v j - 2 := by exact_mod_cast h
      constructor
      · intro _; linarith
      · intro h'; linarith

theorem word_sep : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool}
    {mu : Fin n → ℝ} {ε' : Fin n → Bool}, 0 < G.ga → (∀ i, 2 ≤ i → i < G.k → G.v (i + 1) + 2 ≤ G.v i) →
    2 ≤ G.v G.k + G.b 1 → IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' →
    (∀ a i, mu i < lam a → mu i + 1 < lam a) ∧ ∀ a i, lam a ≠ mu i := by
  rintro G n lam ε mu ε' hga hgap hb ⟨-, q, hq, hS⟩ ⟨-, q', hq', hT⟩
  have key : ∀ a i, (q' i < q a → q' i + 1 < q a) ∧ q a ≠ q' i := by
    intro a i
    have ha : (q a, ε a) ∈ G.lam := by
      rw [← G.parPi_zero, hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    have hi : (q' i, ε' i) ∈ G.parD0 := by
      rw [hT]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    refine sep_rat hga hgap hb ?_ ?_
    · rcases GridData.mem_lam.1 ha with ⟨l, hl, e⟩ | ⟨h, -⟩
      · exact Or.inl ⟨l, hl, (Prod.ext_iff.1 e).1⟩
      · exact Or.inr (GridData.mem_cloudHalf.1 h)
    · rcases GridData.mem_discrete_parameter_iff.1 hi with ⟨h, -⟩ | ⟨l, h1, h2, e⟩
      · exact Or.inl (GridData.mem_cloud.1 h)
      · exact Or.inr ⟨l, h1, h2, (Prod.ext_iff.1 e).1⟩
  refine ⟨fun a i h => ?_, fun a i h => ?_⟩
  · rw [hq, hq'] at h ⊢
    have := (key a i).1 (by exact_mod_cast h)
    exact_mod_cast this
  · rw [hq, hq'] at h
    exact (key a i).2 (by exact_mod_cast h)

end GlobalTheory.WordSep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParametersSeparatedByOneStatement
open Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parameters_separated_by_one : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool} {mu : Fin n → ℝ} {ε' : Fin n → Bool}, 0 < G.ga → (∀ i, 2 ≤ i → i < G.k → G.v (i + 1) + 2 ≤ G.v i) → 2 ≤ G.v G.k + G.b 1 → IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' → (∀ a i, mu i < lam a → mu i + 1 < lam a) ∧ ∀ a i, lam a ≠ mu i := by
  first | exact @GlobalTheory.WordSep.word_sep | exact GlobalTheory.WordSep.word_sep | (intros; apply GlobalTheory.WordSep.word_sep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupportParahoricBiTransformingDoubleCosets
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupportParahoricBiTransformingDoubleCosets
noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
  GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

namespace GlobalTheory.ChainStepSupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem _root_.GlobalTheory.ChainStepSupp.det_lower_ne_zero {A D : Type} [Fintype A] [DecidableEq A]
    [Fintype D] [DecidableEq D]
    {j : GL (A ⊕ D) k} (hj : j ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k A D) : j.1.toBlocks₂₂.det ≠ 0 :=
  (_root_.GlobalTheory.ParahoricLowerBlock.lower_block_tame k A D 1 (fun _ _ => rfl) j hj).1

variable (k) in
def reGL {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n) : GL m k ≃* GL n k :=
  Units.mapEquiv (Matrix.reindexAlgEquiv k k e).toMulEquiv

theorem val_reGL {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n) (g : GL m k) :
    (reGL k e g).1 = reindex e e g.1 := rfl

theorem _root_.GlobalTheory.ChainStepSupp.reGL_mem_KO {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (e : m ≃ n)
    {g : GL m k} (hg : g ∈ _root_.GlobalTheory.SplitWeil.KO k m) :
    _root_.GlobalTheory.ChainStepSupp.reGL k e g ∈ _root_.GlobalTheory.SplitWeil.KO k n := by
  rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff] at hg ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · simpa [_root_.GlobalTheory.ChainStepSupp.val_reGL, Matrix.reindex_apply] using hg.1 (e.symm i) (e.symm j)
  · rw [← map_inv]
    simpa [_root_.GlobalTheory.ChainStepSupp.val_reGL, Matrix.reindex_apply] using hg.2 (e.symm i) (e.symm j)

theorem _root_.GlobalTheory.ChainStepSupp.reGL_torusElt {m n : Type} [Fintype m]
    [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    (ϖ : kˣ) (f : m → ℤ) :
    _root_.GlobalTheory.ChainStepSupp.reGL k e (_root_.GlobalTheory.GLDoubling.torusElt k m ϖ f) =
      _root_.GlobalTheory.GLDoubling.torusElt k n ϖ (f ∘ e.symm) := by
  ext i j
  simp [_root_.GlobalTheory.ChainStepSupp.val_reGL, _root_.GlobalTheory.GLDoubling.val_torusElt, Matrix.reindex_apply,
    Matrix.diagonal_apply]

theorem _root_.GlobalTheory.ChainStepSupp.reGL_reGL_symm {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (e : m ≃ n)
    (g : GL n k) : _root_.GlobalTheory.ChainStepSupp.reGL k e (_root_.GlobalTheory.ChainStepSupp.reGL k e.symm g) = g := by
  ext i j
  simp [_root_.GlobalTheory.ChainStepSupp.val_reGL, Matrix.reindex_apply]

theorem _root_.GlobalTheory.ChainStepSupp.emb₂_mem_parahoric {A D : Type} [Fintype A] [DecidableEq A]
    [Fintype D] [DecidableEq D]
    {x : GL A k} {y : GL D k} (hx : x ∈ _root_.GlobalTheory.SplitWeil.KO k A)
    (hy : y ∈ _root_.GlobalTheory.SplitWeil.KO k D) :
    _root_.GlobalTheory.SmGL.emb₂ k (Equiv.refl (A ⊕ D)) (x, y) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k A D := by
  have hb (g : GL A k × GL D k) :
      (SmGL.emb₂ k (Equiv.refl (A ⊕ D)) g : Matrix (A ⊕ D) (A ⊕ D) k) =
        Matrix.fromBlocks g.1.val 0 0 g.2.val := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [SmGL.emb₂, SmGL.leviEmb, SmGL.leviTwo, SmGL.two,
        Matrix.blockDiagonal'_apply_eq, Matrix.blockDiagonal'_apply_ne]
  rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff] at hx hy
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.mem_parahoric, _root_.GlobalTheory.SplitFlip.mem_KO_iff]
  refine ⟨⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩
  · change ((_: GL (A ⊕ D) k) : Matrix (A ⊕ D) (A ⊕ D) k) i j ∈ _
    rw [hb]
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.reindex_apply, hx.1, hy.1]
  · have hx₂ := hx.2
    have hy₂ := hy.2
    simp only [Matrix.coe_units_inv] at hx₂ hy₂
    rw [← map_inv, Prod.inv_mk]
    change ((_: GL (A ⊕ D) k) : Matrix (A ⊕ D) (A ⊕ D) k) i j ∈ _
    rw [hb]
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.reindex_apply, hx₂, hy₂]
  · rw [hb]
    simp [Matrix.reindex_apply]

theorem _root_.GlobalTheory.ChainStepSupp.emb₂_one_torusElt {A D : Type} [Fintype A] [DecidableEq A]
    [Fintype D] [DecidableEq D] (ϖ : kˣ)
    (f : D → ℤ) :
    _root_.GlobalTheory.SmGL.emb₂ k (Equiv.refl (A ⊕ D)) (1, _root_.GlobalTheory.GLDoubling.torusElt k D ϖ f) =
      (_root_.GlobalTheory.ZonalCellDecomposition.mtor ϖ f : GL (A ⊕ D) k) := by
  have hb (g : GL A k × GL D k) :
      (SmGL.emb₂ k (Equiv.refl (A ⊕ D)) g : Matrix (A ⊕ D) (A ⊕ D) k) =
        Matrix.fromBlocks g.1.val 0 0 g.2.val := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [SmGL.emb₂, SmGL.leviEmb, SmGL.leviTwo, SmGL.two,
        Matrix.blockDiagonal'_apply_eq, Matrix.blockDiagonal'_apply_ne]
  have h : (_root_.GlobalTheory.ZonalCellDecomposition.mtor ϖ f : GL (A ⊕ D) k) =
      _root_.GlobalTheory.GLDoubling.torusElt k (A ⊕ D) ϖ (0 ⊕ᵥ f) := rfl
  rw [h]
  ext i j
  change ((_: GL (A ⊕ D) k) : Matrix (A ⊕ D) (A ⊕ D) k) i j = _
  rw [hb]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.reindex_apply, _root_.GlobalTheory.GLDoubling.val_torusElt, Matrix.diagonal_apply,
      Matrix.one_apply]

theorem _root_.GlobalTheory.ChainStepSupp.support_dcell : ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k →
  ∀ (r l t : ℕ) (ξ : kˣ →* ℂˣ), _root_.GlobalTheory.SplitWeil.IsTame ξ → ¬ _root_.GlobalTheory.SplitWeil.IsUnram ξ →
  ∀ φ : GL (Fin r ⊕ _root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.Blocks l t) k → ℂ, _root_.GlobalTheory.ZonalCellDecomposition.IsBiType ξ φ →
    (∀ x y, φ (_root_.GlobalTheory.SmGL.emb₂ k (Equiv.refl (Fin r ⊕ _root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.Blocks l t)) (x, y)) ≠ 0 →
      x ∈ _root_.GlobalTheory.SplitWeil.KO k (Fin r)) →
    ∀ g, φ g ≠ 0 → ∃ e : Fin (l * t) → ℤ, Antitone e ∧
      g ∈ _root_.GlobalTheory.ZonalCellDecomposition.dcell ϖ (e ∘ (_root_.GlobalTheory.ZonalCellDecomposition.blkEquiv l t).symm) := by
  intro k _ _ _ _ ϖ hϖ r l t ξ hT hU φ hφ hL g hg
  obtain ⟨x, y, j, hj, j', hj', rfl⟩ :=
    _root_.GlobalTheory.ParHeckeSupp.support_levi k (Fin r) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.Blocks l t) ξ hT hU φ hφ
      g hg
  have hne : φ (_root_.GlobalTheory.SmGL.emb₂ k (Equiv.refl _) (x, y)) ≠ 0 := by
    intro h0
    apply hg
    have hd := _root_.GlobalTheory.ChainStepSupp.det_lower_ne_zero hj
    have hd' := _root_.GlobalTheory.ChainStepSupp.det_lower_ne_zero hj'
    rw [mul_assoc, (hφ j hj (Units.mk0 _ hd) rfl _).1, (hφ j' hj' (Units.mk0 _ hd') rfl _).2, h0,
      mul_zero, mul_zero]
  have hx := hL x y hne
  set E := _root_.GlobalTheory.ZonalCellDecomposition.blkEquiv l t
  obtain ⟨⟨e, he⟩, hy⟩ := Set.mem_iUnion.1 ((Set.eq_univ_iff_forall.1
    (_root_.GlobalTheory.GLDoubling.iUnion_cell (N := l * t) hϖ)) (_root_.GlobalTheory.ChainStepSupp.reGL k E.symm y))
  unfold _root_.GlobalTheory.GLDoubling.cell at hy
  rw [DoubleCoset.mem_doubleCoset] at hy
  obtain ⟨κ₁, hκ₁, κ₂, hκ₂, hyeq⟩ := hy
  refine ⟨e, he, ?_⟩
  unfold _root_.GlobalTheory.ZonalCellDecomposition.dcell
  rw [DoubleCoset.mem_doubleCoset]
  have hy' : y = _root_.GlobalTheory.ChainStepSupp.reGL k E κ₁ *
      _root_.GlobalTheory.GLDoubling.torusElt k _ ϖ (e ∘ E.symm) * _root_.GlobalTheory.ChainStepSupp.reGL k E κ₂ := by
    rw [← _root_.GlobalTheory.ChainStepSupp.reGL_torusElt, ← map_mul, ← map_mul, ← hyeq]
    exact (_root_.GlobalTheory.ChainStepSupp.reGL_reGL_symm E y).symm
  refine ⟨j * _root_.GlobalTheory.SmGL.emb₂ k (Equiv.refl _) (x, _root_.GlobalTheory.ChainStepSupp.reGL k E κ₁),
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k _ _).mul_mem hj
      (_root_.GlobalTheory.ChainStepSupp.emb₂_mem_parahoric hx
        (_root_.GlobalTheory.ChainStepSupp.reGL_mem_KO E hκ₁)),
    _root_.GlobalTheory.SmGL.emb₂ k (Equiv.refl _) (1, _root_.GlobalTheory.ChainStepSupp.reGL k E κ₂) * j',
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k _ _).mul_mem
      (_root_.GlobalTheory.ChainStepSupp.emb₂_mem_parahoric (Subgroup.one_mem _)
        (_root_.GlobalTheory.ChainStepSupp.reGL_mem_KO E hκ₂)) hj', ?_⟩
  rw [← _root_.GlobalTheory.ChainStepSupp.emb₂_one_torusElt, hy']
  have hprod : ((x, _root_.GlobalTheory.ChainStepSupp.reGL k E κ₁ *
      _root_.GlobalTheory.GLDoubling.torusElt k _ ϖ (e ∘ E.symm) * _root_.GlobalTheory.ChainStepSupp.reGL k E κ₂) :
        GL (Fin r) k × GL (_root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.Blocks l t) k) =
      (x, _root_.GlobalTheory.ChainStepSupp.reGL k E κ₁) * (1, _root_.GlobalTheory.GLDoubling.torusElt k _ ϖ (e ∘ E.symm)) *
        (1, _root_.GlobalTheory.ChainStepSupp.reGL k E κ₂) := by
    simp [Prod.mk_mul_mk]
  rw [hprod, map_mul, map_mul]
  simp only [mul_assoc]

end GlobalTheory.ChainStepSupp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupportParahoricBiTransformingDoubleCosetsStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.support_parahoricBiTransforming_doubleCosets : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
  ∀ (r l t : ℕ) (ξ : kˣ →* ℂˣ), IsTame ξ → ¬ IsUnram ξ →
  ∀ φ : GL (Fin r ⊕ Blocks l t) k → ℂ, IsBiType ξ φ →
    (∀ x y, φ (emb₂ k (Equiv.refl (Fin r ⊕ Blocks l t)) (x, y)) ≠ 0 → x ∈ KO k (Fin r)) →
    ∀ g, φ g ≠ 0 → ∃ e : Fin (l * t) → ℤ, Antitone e ∧ g ∈ dcell ϖ (e ∘ (blkEquiv l t).symm) := by
  first | exact @GlobalTheory.ChainStepSupp.support_dcell | exact GlobalTheory.ChainStepSupp.support_dcell | (intros; apply GlobalTheory.ChainStepSupp.support_dcell <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymmetrisationEquivariant
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.InducedPBW

noncomputable section

namespace GlobalTheory.InducedPBW.Equivariant

attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

variable {p q : ℕ}

abbrev unitP (ab : PIx p q) : Mat p q := Eab ab.1.1 ab.1.2

theorem pLin_unitP (ab : PIx p q) : pLin (unitP ab) = MvPolynomial.X ab := by
  unfold pLin
  rw [Finset.sum_eq_single ab]
  · simp [unitP, Eab]
  · intro c _ hc
    have hne : ¬ (ab.1.1 = c.1.1 ∧ ab.1.2 = c.1.2) := fun hh =>
      hc (Subtype.ext (Prod.ext hh.1.symm hh.2.symm))
    simp [unitP, Eab, Matrix.single_apply, hne]
  · intro hab
    exact absurd (Finset.mem_univ ab) hab

theorem ug_comm (Y Z : Mat p q) :
    ugι p q (Y * Z - Z * Y) = ugι p q Y * ugι p q Z - ugι p q Z * ugι p q Y := by
  have hl := (UniversalEnvelopingAlgebra.ι ℂ : Mat p q →ₗ⁅ℂ⁆ Ug p q).map_lie Y Z
  rw [Ring.lie_def, Ring.lie_def] at hl
  simpa [ugι] using hl

theorem kOnS_X (Y : Mat p q) (ab : PIx p q) :
    kOnS Y (MvPolynomial.X ab) = pLin (Y * unitP ab - unitP ab * Y) := by
  change MvPolynomial.mkDerivation ℂ (fun c : PIx p q => pLin (Y * Eab c.1.1 c.1.2 - Eab c.1.1 c.1.2 * Y))
    (MvPolynomial.X ab) = _
  rw [MvPolynomial.mkDerivation_X]

theorem kOnS_one (Y : Mat p q) : kOnS Y 1 = 0 := by
  exact (MvPolynomial.mkDerivation ℂ fun c : PIx p q =>
    pLin (Y * Eab c.1.1 c.1.2 - Eab c.1.1 c.1.2 * Y)).map_one_eq_zero

theorem kOnS_mul (Y : Mat p q) (P Q : MvPolynomial (PIx p q) ℂ) :
    kOnS Y (P * Q) = P * kOnS Y Q + Q * kOnS Y P := by
  exact (MvPolynomial.mkDerivation ℂ fun c : PIx p q =>
    pLin (Y * Eab c.1.1 c.1.2 - Eab c.1.1 c.1.2 * Y)).leibniz P Q

variable {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)

def cls (v : V) : Ug p q →ₗ[ℂ] Ind act :=
  (indRel act).mkQ ∘ₗ (TensorProduct.mk ℂ (Ug p q) V).flip v

theorem cls_apply (v : V) (u : Ug p q) :
    cls act v u = (indRel act).mkQ (TensorProduct.tmul ℂ u v) := rfl

theorem cls_mul (v : V) (u : Ug p q) {Y : Mat p q} (hY : IsKC Y) :
    cls act v (u * ugι p q Y) = cls act (act Y v) u := by
  rw [cls_apply, cls_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  exact Submodule.subset_span ⟨u, Y, v, hY, rfl⟩

theorem map_pLin (a : List (PIx p q)) :
    (a.map unitP).map pLin = a.map MvPolynomial.X := by
  induction a with
  | nil => rfl
  | cons c a ih => simp only [List.map_cons, pLin_unitP, ih]

private theorem mul_commutator_mul_expand {R : Type*} [Ring R] (B y x P : R) :
    B * (y * (x * P) - x * P * y) = B * ((y * x - x * y) * P) + B * x * (y * P - P * y) := by
  noncomm_ring

private theorem mul_leibniz_comm {R : Type*} [CommRing R] (B x Q dx dQ : R) :
    B * (x * dQ + Q * dx) = B * (dx * Q) + B * x * dQ := by
  ring

theorem comm_mem (h : SymbolCongr act) (Y : Mat p q) (v : V) (a : List (PIx p q)) :
    ∀ b : List (Mat p q),
      cls act v ((b.map (ugι p q)).prod *
        (ugι p q Y * ((a.map unitP).map (ugι p q)).prod -
          ((a.map unitP).map (ugι p q)).prod * ugι p q Y)) -
      cls act v (symU p q ((b.map pLin).prod * kOnS Y (a.map MvPolynomial.X).prod)) ∈
        indFlt act (b.length + a.length) := by
  induction a with
  | nil =>
    intro b
    simp [kOnS_one]
  | cons e a ih =>
    intro b
    have h1 := h (b ++ (Y * unitP e - unitP e * Y) :: a.map unitP) v
    have h2 := ih (b ++ [unitP e])
    rw [← cls_apply, ← cls_apply] at h1
    simp only [List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons,
      List.prod_nil, mul_one, List.length_append, List.length_cons, List.length_nil, zero_add,
      List.length_map, ug_comm, map_pLin, pLin_unitP] at h1 h2 ⊢
    rw [← kOnS_X] at h1
    rw [show b.length + 1 + a.length = b.length + (a.length + 1) by omega] at h2
    rw [kOnS_mul, mul_commutator_mul_expand, mul_leibniz_comm, map_add (f := _), map_add (f := _), map_add (f := _)]
    have hs := Submodule.add_mem _ h1 h2
    convert hs using 1
    abel

theorem list_mem (h : SymbolCongr act) {Y : Mat p q} (hY : IsKC Y) (v : V) (a : List (PIx p q)) :
    cls act v (symU p q (kOnS Y (a.map MvPolynomial.X).prod)) +
      cls act (act Y v) (symU p q (a.map MvPolynomial.X).prod) -
      cls act v (ugι p q Y * ((a.map unitP).map (ugι p q)).prod) ∈ indFlt act a.length := by
  have h1 := comm_mem act h Y v a []
  have h2 := h (a.map unitP) (act Y v)
  rw [← cls_apply, ← cls_apply, map_pLin, List.length_map] at h2
  simp only [List.map_nil, List.prod_nil, one_mul, List.length_nil, zero_add, map_sub] at h1
  rw [cls_mul act v _ hY] at h1
  have hs := Submodule.neg_mem _ (Submodule.add_mem _ h1 h2)
  convert hs using 1
  abel

theorem toList_prod (α : PIx p q →₀ ℕ) :
    ((Finsupp.toMultiset α).toList.map (MvPolynomial.X (R := ℂ))).prod =
      MvPolynomial.monomial α 1 := by
  rw [← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList, Finset.prod_multiset_map_count,
    Finsupp.toFinset_toMultiset, MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, Finsupp.prod]
  simp [Finsupp.count_toMultiset]

private theorem mul_symU_monomial_eq_avg_perm (α : PIx p q →₀ ℕ) (y : Ug p q) :
    y * symU p q (MvPolynomial.monomial α 1) =
      (((Finsupp.toMultiset α).toList.length.factorial : ℂ)⁻¹) •
        ∑ σ : Equiv.Perm (Fin (Finsupp.toMultiset α).toList.length),
          y * (((List.ofFn fun i => (Finsupp.toMultiset α).toList.get (σ i)).map unitP).map
            (ugι p q)).prod := by
  rw [show MvPolynomial.monomial α (1 : ℂ) = MvPolynomial.basisMonomials (PIx p q) ℂ α by
    rw [MvPolynomial.coe_basisMonomials]]
  unfold symU
  rw [Module.Basis.constr_basis]
  unfold symProd
  rw [mul_smul_comm, Finset.mul_sum]
  simp only [List.map_ofFn]
  rfl

private theorem prod_ofFn_perm_map_X_eq_prod (l : List (PIx p q)) (σ : Equiv.Perm (Fin l.length)) :
    ((List.ofFn fun i => l.get (σ i)).map (MvPolynomial.X (R := ℂ))).prod =
      (l.map MvPolynomial.X).prod := by
  rw [List.map_ofFn, List.prod_ofFn]
  conv_rhs => rw [← List.ofFn_get l, List.map_ofFn, List.prod_ofFn]
  exact Equiv.prod_comp σ (fun i => MvPolynomial.X (l.get i))

private theorem sub_inv_factorial_smul_sum_mem {M : Type*} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M)
    (n : ℕ) (x : M) (f : Equiv.Perm (Fin n) → M) (hf : ∀ σ, x - f σ ∈ S) :
    x - ((n.factorial : ℂ)⁻¹) • ∑ σ, f σ ∈ S := by
  have hx : x = ((n.factorial : ℂ)⁻¹) • ∑ _σ : Equiv.Perm (Fin n), x := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), one_smul]
  rw [hx, ← smul_sub, ← Finset.sum_sub_distrib]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun σ _ => hf σ)

theorem monomial_mem (h : SymbolCongr act) {Y : Mat p q} (hY : IsKC Y) (v : V)
    (α : PIx p q →₀ ℕ) :
    cls act v (symU p q (kOnS Y (MvPolynomial.monomial α 1))) +
      cls act (act Y v) (symU p q (MvPolynomial.monomial α 1)) -
      cls act v (ugι p q Y * symU p q (MvPolynomial.monomial α 1)) ∈
        indFlt act (Finsupp.toMultiset α).toList.length := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [mul_symU_monomial_eq_avg_perm, map_smul, map_sum]
  apply sub_inv_factorial_smul_sum_mem
  intro σ
  have hσ := list_mem act h hY v (List.ofFn fun i => (Finsupp.toMultiset α).toList.get (σ i))
  rw [prod_ofFn_perm_map_X_eq_prod, toList_prod, List.length_ofFn] at hσ
  exact hσ

theorem homog_mem (h : SymbolCongr act) {Y : Mat p q} (hY : IsKC Y) (v : V) (k : ℕ)
    (P : MvPolynomial (PIx p q) ℂ) (hP : P.IsHomogeneous k) :
    cls act v (symU p q (kOnS Y P)) + cls act (act Y v) (symU p q P) -
      cls act v (ugι p q Y * symU p q P) ∈ indFlt act k := by
  have hlin : ∀ Q : MvPolynomial (PIx p q) ℂ,
      cls act v (symU p q (kOnS Y Q)) + cls act (act Y v) (symU p q Q) -
        cls act v (ugι p q Y * symU p q Q) =
      (cls act v ∘ₗ symU p q ∘ₗ kOnS Y + cls act (act Y v) ∘ₗ symU p q -
        cls act v ∘ₗ LinearMap.mulLeft ℂ (ugι p q Y) ∘ₗ symU p q) Q := fun Q => by
    simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hlin, MvPolynomial.as_sum P, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [show MvPolynomial.monomial d (P.coeff d) = P.coeff d • MvPolynomial.monomial d 1 by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], map_smul]
  refine Submodule.smul_mem _ _ ?_
  rw [← hlin]
  have hk : (Finsupp.toMultiset d).toList.length = k := by
    have hw := hP (MvPolynomial.mem_support_iff.mp hd)
    simpa [Multiset.length_toList, Finsupp.card_toMultiset, Finsupp.weight_apply, Finsupp.sum] using hw
  have hm := monomial_mem act h hY v d
  rw [hk] at hm
  exact hm

end GlobalTheory.InducedPBW.Equivariant

namespace GlobalTheory.InducedPBW

open Equivariant in
theorem symmetrisation_equivariant : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), SymbolCongr act → ∀ (k : ℕ) (Y : Mat p q), IsKC Y → ∀ z ∈ symTens p q V k, (indRel act).mkQ (LinearMap.rTensor V (symU p q) (LinearMap.rTensor V (kOnS Y) z + LinearMap.lTensor _ (act Y) z)) - (indRel act).mkQ (LinearMap.rTensor V (LinearMap.mulLeft ℂ (ugι p q Y)) (LinearMap.rTensor V (symU p q) z)) ∈ indFlt act k := by
  intro p q V _ _ act h k Y hY z hz
  unfold symTens at hz
  rw [LinearMap.mem_range] at hz
  obtain ⟨w, rfl⟩ := hz
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul P v =>
    simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, Submodule.coe_subtype, map_add (f := _),
      LinearMap.mulLeft_apply, ← cls_apply]
    exact homog_mem act h hY v k P ((MvPolynomial.mem_homogeneousSubmodule k _).mp P.2)
  | add x y hx hy =>
    have hs := Submodule.add_mem _ hx hy
    convert hs using 1
    simp only [map_add (f := _)]
    abel

end GlobalTheory.InducedPBW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdXEqMonomial
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.InducedPBW

noncomputable section

namespace GlobalTheory.InducedPBW.Symbol

variable {p q : ℕ}

def prodU (l : List (Mat p q)) : Ug p q := (l.map (ugι p q)).prod

theorem prodU_cons (x : Mat p q) (l : List (Mat p q)) : prodU (x :: l) = ugι p q x * prodU l := by
  simp only [prodU, List.map_cons, List.prod_cons]

theorem prodU_append (l l' : List (Mat p q)) : prodU (l ++ l') = prodU l * prodU l' := by
  simp only [prodU, List.map_append, List.prod_append]

def below (p q k : ℕ) : Submodule ℂ (Ug p q) :=
  Submodule.span ℂ {u | ∃ l : List (Mat p q), l.length < k ∧ u = prodU l}

section
attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

theorem ug_bracket (x y : Mat p q) :
    ugι p q (x * y - y * x) = ugι p q x * ugι p q y - ugι p q y * ugι p q x := by
  have h := LieHom.map_lie (UniversalEnvelopingAlgebra.ι ℂ : Mat p q →ₗ⁅ℂ⁆ Ug p q) x y
  simpa only [ugι, LieHom.coe_toLinearMap, Ring.lie_def] using h
end

theorem mul_mem_below (x : Mat p q) {k : ℕ} {u : Ug p q} (hu : u ∈ below p q k) :
    ugι p q x * u ∈ below p q (k + 1) := by
  induction hu using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨l, hl, rfl⟩ := hw
    refine Submodule.subset_span ⟨x :: l, ?_, (prodU_cons x l).symm⟩
    simp only [List.length_cons]
    omega
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add w w' _ _ hw hw' => rw [mul_add]; exact Submodule.add_mem _ hw hw'
  | smul c w _ hw => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hw

theorem perm_sub_mem_below {l l' : List (Mat p q)} (h : l.Perm l') :
    prodU l - prodU l' ∈ below p q l.length := by
  induction h with
  | nil => rw [sub_self]; exact Submodule.zero_mem _
  | cons x _ ih =>
    rw [prodU_cons, prodU_cons, ← mul_sub, List.length_cons]
    exact mul_mem_below x ih
  | swap x y l =>
    have e : prodU (y :: x :: l) - prodU (x :: y :: l) = prodU ((y * x - x * y) :: l) := by
      simp only [prodU_cons, ug_bracket, sub_mul, mul_assoc]
    rw [e]
    exact Submodule.subset_span ⟨(y * x - x * y) :: l, by simp, rfl⟩
  | @trans l₁ l₂ l₃ h₁ _ ih₁ ih₂ =>
    rw [← sub_add_sub_cancel (prodU l₁) (prodU l₂) (prodU l₃)]
    exact Submodule.add_mem _ ih₁ (h₁.length_eq ▸ ih₂)

variable {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)

def cls (v : V) : Ug p q →ₗ[ℂ] Ind act :=
  (indRel act).mkQ ∘ₗ (TensorProduct.mk ℂ (Ug p q) V).flip v

theorem cls_apply (v : V) (u : Ug p q) :
    cls act v u = (indRel act).mkQ (TensorProduct.tmul ℂ u v) := rfl

private lemma indF_le_indFlt_of_lt {j k : ℕ} (h : j < k) : indF act j ≤ indFlt act k := by
  unfold indFlt
  exact le_iSup₂_of_le (f := fun i (_ : i < k) => indF act i) j h le_rfl

private lemma cls_prodU_mem_indF (v : V) (l : List (Mat p q)) :
    cls act v (prodU l) ∈ indF act l.length :=
  Submodule.subset_span ⟨prodU l, Submodule.subset_span ⟨l, le_rfl, rfl⟩, v, cls_apply act v _⟩

theorem cls_mem_of_below (v : V) {k : ℕ} {u : Ug p q} (hu : u ∈ below p q k) :
    cls act v u ∈ indFlt act k := by
  have hle : below p q k ≤ (indFlt act k).comap (cls act v) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨l, hl, rfl⟩
    exact indF_le_indFlt_of_lt act hl (cls_prodU_mem_indF act v l)
  exact hle hu

theorem cls_mul_kc (v : V) (u : Ug p q) {Y : Mat p q} (hY : IsKC Y) :
    cls act v (u * ugι p q Y) = cls act (act Y v) u := by
  rw [cls_apply, cls_apply, Submodule.mkQ_apply, Submodule.mkQ_apply]
  exact (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨u, Y, v, hY, rfl⟩)

theorem cls_mem_of_kc (v : V) (l l' : List (Mat p q)) {Y : Mat p q} (hY : IsKC Y) :
    cls act v (prodU (l ++ Y :: l')) ∈ indFlt act (l.length + (l'.length + 1)) := by
  have hperm : (l ++ Y :: l').Perm ((l ++ l') ++ [Y]) :=
    List.perm_middle.trans (List.perm_append_singleton Y (l ++ l')).symm
  have hlen : (l ++ Y :: l').length = l.length + (l'.length + 1) := by simp
  have h₁ := cls_mem_of_below act v (perm_sub_mem_below hperm)
  rw [hlen] at h₁
  have h₂ : cls act v (prodU ((l ++ l') ++ [Y])) ∈ indFlt act (l.length + (l'.length + 1)) := by
    have e : prodU ((l ++ l') ++ [Y]) = prodU (l ++ l') * ugι p q Y := by
      rw [prodU_append, prodU_cons]
      simp [prodU]
    rw [e, cls_mul_kc act v _ hY]
    refine indF_le_indFlt_of_lt act (j := (l ++ l').length) ?_ (cls_prodU_mem_indF act _ _)
    simp only [List.length_append]
    omega
  have e : cls act v (prodU (l ++ Y :: l')) =
      cls act v (prodU (l ++ Y :: l') - prodU ((l ++ l') ++ [Y])) + cls act v (prodU ((l ++ l') ++ [Y])) := by
    rw [map_sub, sub_add_cancel]
  rw [e]
  exact Submodule.add_mem _ h₁ h₂

def unitP (ab : PIx p q) : Mat p q := Eab ab.1.1 ab.1.2

theorem prod_X_eq_monomial (a : List (PIx p q)) :
    (a.map (MvPolynomial.X : PIx p q → MvPolynomial (PIx p q) ℂ)).prod =
      MvPolynomial.monomial (Multiset.toFinsupp (a : Multiset (PIx p q))) 1 := by
  induction a with
  | nil => simp
  | cons x a ih =>
    rw [List.map_cons, List.prod_cons, ih, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul,
      ← Multiset.cons_coe, ← Multiset.singleton_add, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]

theorem symProd_sub_mem (b : List (Mat p q)) {k : ℕ} (x : Fin k → Mat p q)
    (h : b.Perm (List.ofFn x)) :
    prodU b - symProd (fun i => ugι p q (x i)) ∈ below p q b.length := by
  have hk : ((k.factorial : ℂ)⁻¹) • ∑ _σ : Equiv.Perm (Fin k), prodU b = prodU b := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k), one_smul]
  have e : prodU b - symProd (fun i => ugι p q (x i)) =
      ((k.factorial : ℂ)⁻¹) • ∑ σ : Equiv.Perm (Fin k), (prodU b - prodU (List.ofFn fun i => x (σ i))) := by
    rw [Finset.sum_sub_distrib, smul_sub, hk]
    simp only [symProd, prodU, List.map_ofFn]
    rfl
  rw [e]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun σ _ => perm_sub_mem_below ?_)
  exact h.trans (Equiv.Perm.ofFn_comp_perm σ x).symm

theorem units_sub_mem (a : List (PIx p q)) :
    prodU (a.map unitP) - symU p q (a.map MvPolynomial.X).prod ∈ below p q a.length := by
  rw [prod_X_eq_monomial]
  have hb : MvPolynomial.monomial (Multiset.toFinsupp (a : Multiset (PIx p q))) (1 : ℂ) =
      MvPolynomial.basisMonomials (PIx p q) ℂ (Multiset.toFinsupp (a : Multiset (PIx p q))) := by
    rw [MvPolynomial.coe_basisMonomials]
  rw [hb, symU, Module.Basis.constr_basis, Multiset.toFinsupp_toMultiset]
  have hlen : (a.map unitP).length = a.length := List.length_map _
  rw [← hlen]
  refine symProd_sub_mem (a.map unitP) (fun i => unitP ((a : Multiset (PIx p q)).toList.get i)) ?_
  have hL : ((a : Multiset (PIx p q)).toList).Perm a :=
    Multiset.coe_eq_coe.mp (by rw [Multiset.coe_toList])
  have hf : List.ofFn (fun i => unitP ((a : Multiset (PIx p q)).toList.get i)) =
      ((a : Multiset (PIx p q)).toList).map unitP :=
    List.ext_get (by simp) (by simp)
  rw [hf]
  exact (hL.map unitP).symm

private lemma sum_unitP_apply (x : Mat p q) (c d : Ix p q) :
    (∑ ab : PIx p q, x ab.1.1 ab.1.2 • unitP ab) c d = if sameBlock c d then 0 else x c d := by
  rw [Matrix.sum_apply]
  split_ifs with h
  · refine Finset.sum_eq_zero fun ab _ => ?_
    have hne : ¬ (ab.1.1 = c ∧ ab.1.2 = d) := by
      rintro ⟨h₁, h₂⟩
      exact ab.2 (h₁ ▸ h₂ ▸ h)
    simp [unitP, Eab, Matrix.single_apply_of_ne (h := hne)]
  · rw [Finset.sum_eq_single (⟨(c, d), h⟩ : PIx p q)]
    · simp [unitP, Eab]
    · intro ab _ hab
      have hne : ¬ (ab.1.1 = c ∧ ab.1.2 = d) := fun e => hab (Subtype.ext (Prod.ext e.1 e.2))
      simp [unitP, Eab, Matrix.single_apply_of_ne (h := hne)]
    · intro hn
      exact absurd (Finset.mem_univ _) hn

private lemma isKC_sub_sum_unitP (x : Mat p q) : IsKC (x - ∑ ab : PIx p q, x ab.1.1 ab.1.2 • unitP ab) := by
  intro c d h
  rw [Matrix.sub_apply, sum_unitP_apply, if_neg h, sub_self]

theorem mixed_mem (v : V) (l : List (Mat p q)) : ∀ a : List (PIx p q),
    cls act v (prodU (a.map unitP) * prodU l) -
      cls act v (symU p q ((a.map MvPolynomial.X).prod * (l.map pLin).prod)) ∈
      indFlt act (a.length + l.length) := by
  induction l with
  | nil =>
    intro a
    have h1 : prodU ([] : List (Mat p q)) = 1 := by simp [prodU]
    simp only [h1, mul_one, List.map_nil, List.prod_nil, List.length_nil, add_zero]
    rw [← map_sub]
    exact cls_mem_of_below act v (units_sub_mem a)
  | cons x l ih =>
    intro a
    set P : Mat p q := ∑ ab : PIx p q, x ab.1.1 ab.1.2 • unitP ab with hP
    have hY : IsKC (x - P) := isKC_sub_sum_unitP x
    have hx : ugι p q x = ∑ ab : PIx p q, x ab.1.1 ab.1.2 • ugι p q (unitP ab) + ugι p q (x - P) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, hP, map_sum]
      simp only [map_smul]
      abel
    have hpl : pLin x = ∑ ab : PIx p q, x ab.1.1 ab.1.2 • MvPolynomial.X ab := by
      simp only [pLin, MvPolynomial.smul_eq_C_mul]
    have hL : prodU (a.map unitP) * prodU (x :: l) =
        ∑ ab : PIx p q, x ab.1.1 ab.1.2 • (prodU ((a ++ [ab]).map unitP) * prodU l) +
          prodU (a.map unitP ++ (x - P) :: l) := by
      rw [prodU_cons, hx, add_mul, Finset.sum_mul, mul_add, Finset.mul_sum, prodU_append, prodU_cons]
      congr 1
      refine Finset.sum_congr rfl fun ab _ => ?_
      rw [List.map_append, prodU_append, List.map_singleton, prodU_cons]
      simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]
      simp [prodU]
    have hR : (a.map MvPolynomial.X).prod * ((x :: l).map pLin).prod =
        ∑ ab : PIx p q, x ab.1.1 ab.1.2 •
          (((a ++ [ab]).map MvPolynomial.X).prod * (l.map pLin).prod) := by
      rw [List.map_cons, List.prod_cons, hpl, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ab _ => ?_
      simp only [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton,
        smul_mul_assoc, mul_smul_comm, mul_assoc]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hL, hR, map_add (f := _), map_sum, map_sum, map_sum]
    simp only [map_smul]
    rw [add_sub_right_comm, ← Finset.sum_sub_distrib]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun ab _ => ?_) ?_
    · rw [← smul_sub]
      refine Submodule.smul_mem _ _ ?_
      have h := ih (a ++ [ab])
      have e : (a ++ [ab]).length + l.length = a.length + (x :: l).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rwa [e] at h
    · have h := cls_mem_of_kc act v (a.map unitP) l hY
      have e : a.length + (l.length + 1) = a.length + (x :: l).length := by simp
      rw [List.length_map, e] at h
      exact h

end GlobalTheory.InducedPBW.Symbol

namespace GlobalTheory.InducedPBW

theorem symbolCongr (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) : SymbolCongr act := by
  intro l v
  have h := Symbol.mixed_mem act v l []
  simp only [Symbol.prodU, List.map_nil, List.prod_nil, one_mul, List.length_nil, zero_add,
    Symbol.cls_apply] at h
  exact h

end GlobalTheory.InducedPBW
end
end
