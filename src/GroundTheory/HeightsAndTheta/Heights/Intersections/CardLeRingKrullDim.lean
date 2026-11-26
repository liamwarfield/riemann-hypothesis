module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherFurther
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationLength
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteMapOpen

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.CardLeRingKrullDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace RegularityRelativeClosedPoint

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] [DecidableEq K]

def killBlocks (S : Finset K) : MRing ι →ₐ[ℤ] MRing ι :=
  aeval fun p => if p.1 ∈ S then 0 else X p

theorem killBlocks_form (S : Finset K) {g : MRing ι} {a : K → ℕ} (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a) :
    killBlocks S g = (∏ k, (if k ∈ S then (0 : MRing ι) else 1) ^ a k) * g := by
  have e : (fun p : (Σ k, ι k) => if p.1 ∈ S then (0 : MRing ι) else X p) =
      fun p => (if p.1 ∈ S then (0 : MRing ι) else 1) * X p := by
    funext p
    split_ifs <;> simp
  have h := regularityLocalResidue_holds.aeval_blockScale_int hg (fun k => if k ∈ S then (0 : MRing ι) else 1) X
  rw [aeval_X_left_apply] at h
  rw [killBlocks, e]
  exact h

theorem le_comap_killBlocks (S : Finset K) {W : Ideal (MRing ι)} (hW : IsMultiHomogIdeal W) :
    W ≤ W.comap (killBlocks S) := by
  obtain ⟨T, hT, rfl⟩ := hW
  rw [Ideal.span_le]
  intro g hg
  obtain ⟨a, ha⟩ := hT g hg
  rw [SetLike.mem_coe, Ideal.mem_comap, killBlocks_form S ha]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span hg)


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem killBlocks_comp {S T : Finset K} (hST : S ⊆ T) :
    (killBlocks T).comp (killBlocks S) = (killBlocks T : MRing ι →ₐ[ℤ] MRing ι) := by
  refine MvPolynomial.algHom_ext fun p => ?_
  simp only [AlgHom.comp_apply, killBlocks, aeval_X]
  by_cases h : p.1 ∈ S
  · simp [h, hST h]
  · simp [h]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem killBlocks_empty : (killBlocks ∅ : MRing ι →ₐ[ℤ] MRing ι) = AlgHom.id ℤ (MRing ι) :=
  MvPolynomial.algHom_ext fun p => by simp [killBlocks]

theorem card_le_ringKrullDim (W : Ideal (MRing ι)) [W.IsPrime] (hWh : IsMultiHomogIdeal W)
    (hWr : ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W) : ((Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι ⧸ W) := by
  choose j hj using hWr
  let Q : Finset K → Ideal (MRing ι) := fun S => W.comap (killBlocks S)
  have hQp : ∀ S, (Q S).IsPrime := fun S => Ideal.comap_isPrime _ _
  have hstep : ∀ S k, k ∉ S → Q S < Q (insert k S) := by
    intro S k hk
    refine SetLike.lt_iff_le_and_exists.mpr ⟨fun g hg => ?_, X ⟨k, j k⟩, ?_, ?_⟩
    · have h1 := Ideal.mem_comap.mp (le_comap_killBlocks (insert k S) hWh (Ideal.mem_comap.mp hg))
      rw [← AlgHom.comp_apply, killBlocks_comp (Finset.subset_insert k S)] at h1
      exact Ideal.mem_comap.mpr h1
    · rw [Ideal.mem_comap]
      simp [killBlocks]
    · intro h
      rw [Ideal.mem_comap] at h
      simp only [killBlocks, aeval_X, if_neg hk] at h
      exact hj k h
  have chain : ∀ S : Finset K, (S.card : WithBot ℕ∞) + ringKrullDim (MRing ι ⧸ Q S) ≤
      ringKrullDim (MRing ι ⧸ Q ∅) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert k S hk ih =>
      have : (Q S).IsPrime := hQp S
      have : (Q (insert k S)).IsPrime := hQp _
      have h1 := HorizNotMem.ringKrullDim_quotient_add_one_le (hstep S k hk)
      rw [Finset.card_insert_of_notMem hk]
      calc (((S.card + 1 : ℕ)) : WithBot ℕ∞) + ringKrullDim (MRing ι ⧸ Q (insert k S))
          = (S.card : WithBot ℕ∞) + (ringKrullDim (MRing ι ⧸ Q (insert k S)) + 1) := by
            push_cast; abel
        _ ≤ (S.card : WithBot ℕ∞) + ringKrullDim (MRing ι ⧸ Q S) := by gcongr
        _ ≤ _ := ih
  have hQ0 : Q ∅ = W := by
    ext g
    simp [Q, killBlocks_empty]
  have : (Q Finset.univ).IsPrime := hQp _
  have : IsDomain (MRing ι ⧸ Q Finset.univ) := Ideal.Quotient.isDomain _
  have h3 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MRing ι ⧸ Q Finset.univ) := ringKrullDim_nonneg_of_nontrivial
  have hc := chain Finset.univ
  rw [Finset.card_univ, hQ0] at hc
  calc ((Fintype.card K : ℕ) : WithBot ℕ∞) = (Fintype.card K : WithBot ℕ∞) + 0 := (add_zero _).symm
    _ ≤ (Fintype.card K : WithBot ℕ∞) + ringKrullDim (MRing ι ⧸ Q Finset.univ) := by gcongr
    _ ≤ _ := hc

end RegularityRelativeClosedPoint

theorem RegularityRelativeClosedPoint.proof : RegularityRelativeClosedPoint.Statement := by
  intro K _ ι _ P W hP hW hPW hne
  classical
  refine ⟨hW, ?_⟩
  obtain ⟨-, ⟨hPp, -, -⟩, -, hPdim⟩ := hP
  obtain ⟨hWp, hWh, hWr⟩ := hW
  have := hPp
  have := hWp
  have e := mvPolynomialInt_dimFormula P W hPW
  rw [hPdim] at e
  have hh : (W.map (Ideal.Quotient.mk P)).height ≠ 0 := fun h0 =>
    hne (le_antisymm (RegularityDivisorSupportClosed.le_of_height_map_eq_zero h0) hPW)
  have hlow := RegularityRelativeClosedPoint.card_le_ringKrullDim W hWh hWr
  generalize ringKrullDim (MRing ι ⧸ W) = m at e hlow ⊢
  generalize (W.map (Ideal.Quotient.mk P)).height = h at e hh
  induction m using WithBot.recBotCoe with
  | bot => exact absurd hlow (by simp)
  | coe m =>
    have e' : m + h = ((1 + Fintype.card K : ℕ) : ℕ∞) := by exact_mod_cast e
    have hlow' : ((Fintype.card K : ℕ) : ℕ∞) ≤ m := by exact_mod_cast hlow
    induction m using ENat.recTopCoe with
    | top => simp at e'; exact absurd e'.symm (ENat.natCast_ne_top _)
    | coe m =>
      induction h using ENat.recTopCoe with
      | top => simp at e'; exact absurd e'.symm (ENat.natCast_ne_top _)
      | coe h =>
        have h1 : m + h = 1 + Fintype.card K := by exact_mod_cast e'
        have h2 : Fintype.card K ≤ m := by exact_mod_cast hlow'
        have h3 : h ≠ 0 := by exact_mod_cast hh
        have h4 : m = Fintype.card K := by omega
        rw [h4]
        rfl

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherTer
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def PullbackVanishingOfNullCycle.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' J' : Ideal (MRing ι')) (n : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    IsGoodProj (imageZ v P') Ψ → IsMultiHomogIdeal J' → ¬ J' ≤ P' →
    volume {y : Fin n → ℂ | ∃ z' ∈ mcPts P', z' ∈ mcPts J' ∧
      (Ψ (segre fun p => z' (v p)) 0)⁻¹ • segre (fun p => z' (v p)) ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre (imageZ v P') Ψ y} = 0

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsBlockRatioAlg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def BlockRatioAlg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    ∀ q c : Σ k', ι' k', q.1 = c.1 → (X c : MRing ι') ∉ P' →
      ∃ (m : ℕ) (A : Fin (m + 1) → MRing ι) (a : K → ℕ), (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (A j) a) ∧
        A (Fin.last m) ∉ imageZ v P' ∧
        ∑ j : Fin (m + 1), rename v (A j) * X q ^ (j : ℕ) * X c ^ (m - j : ℕ) ∈ P'

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOver
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section Over

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {n : ℕ}

def ptsOver (P' : Ideal (MRing ι')) (v : (Σ k, ι k) → (Σ k', ι' k'))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (w : ((k : K) → ι k) → ℂ) :
    Set (Set ((Σ k', ι' k') → ℂ)) :=
  {O | ∃ z' ∈ mcPts P', O = {z'' | SameOrbit z'' z'} ∧
    (Ψ (segre fun p => z' (v p)) 0)⁻¹ • segre (fun p => z' (v p)) = w}

end Over

def GenericPointsCount.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (i : ∀ k : FibreBlock κ, ι' k.1)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    IsGoodProj (imageZ v P') Ψ → (∀ k : FibreBlock κ, G.x' ⟨k.1, i k⟩ ≠ 0) →
    ∀ᵐ y : Fin n → ℂ, ∀ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre (imageZ v P') Ψ y,
      (ptsOver P' v Ψ w).ncard = Module.finrank G.Φ (IntermediateField.adjoin G.Φ
        (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩))

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PFibreIsolFinite
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

namespace FibreIsolFinite

theorem isolated_finite (N : ℕ) (S : Set (MvPolynomial (Fin N) ℂ)) :
    {x : Fin N → ℂ | (∀ s ∈ S, eval x s = 0) ∧
      ∀ᶠ y in 𝓝 x, (∀ s ∈ S, eval y s = 0) → y = x}.Finite := by
  classical
  let m : (Fin N → ℂ) → Ideal (MvPolynomial (Fin N) ℂ) := fun x => RingHom.ker (eval x)
  have hinj : Function.Injective m := by
    intro x y hxy
    funext i
    have h1 : X i - C (x i) ∈ m y := by
      rw [← hxy]
      exact RingHom.mem_ker.mpr (by simp)
    have h2 : y i - x i = 0 := by simpa using RingHom.mem_ker.mp h1
    exact (sub_eq_zero.mp h2).symm
  refine ((Ideal.finite_minimalPrimes_of_isNoetherianRing _ (Ideal.span S)).preimage
    (fun a _ b _ h => hinj h)).subset ?_
  rintro x ⟨hx, hiso⟩
  have hIm : Ideal.span S ≤ m x := by
    rw [Ideal.span_le]
    exact fun s hs => RingHom.mem_ker.mpr (hx s hs)
  have : (m x).IsPrime := RingHom.ker_isPrime _
  obtain ⟨q, hq, hqm⟩ := Ideal.exists_minimalPrimes_le hIm
  have hmq : m x ≤ q := by
    intro f hf
    refine IndefiniteRowSideFullHecke.ComplexSets.VanishNearPoint.proof IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.proof N q f x hq.1.1
      (fun g hg => RingHom.mem_ker.mp (hqm hg)) ?_
    filter_upwards [hiso] with y hy hyq
    rw [hy fun s hs => hyq s (hq.1.2 (Ideal.subset_span hs))]
    exact RingHom.mem_ker.mp hf
  show m x ∈ (Ideal.span S).minimalPrimes
  rwa [le_antisymm hqm hmq] at hq

variable {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}

theorem sameOrbit_comp_smul {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hvb : ∀ p, (v p).1 = κ p.1) {z' : (Σ k', ι' k') → ℂ} {u : (Σ k, ι k) → ℂ}
    (h : SameOrbit (fun p => z' (v p)) u) (c : K' → ℂ) (hc : ∀ k', c k' ≠ 0) :
    SameOrbit (fun p => c (v p).1 * z' (v p)) u := by
  obtain ⟨c₀, hc₀, hz⟩ := h
  refine ⟨fun k => c (κ k) * c₀ k, fun k => mul_ne_zero (hc _) (hc₀ k), funext fun p => ?_⟩
  have h1 : z' (v p) = c₀ p.1 * u p := congrFun hz p
  show c (v p).1 * z' (v p) = c (κ p.1) * c₀ p.1 * u p
  rw [hvb p, h1, mul_assoc]

theorem minor_of_sameOrbit {w u : (Σ k, ι k) → ℂ} (h : SameOrbit w u) (j : ∀ k, ι k)
    (p : Σ k, ι k) : w p * u ⟨p.1, j p.1⟩ = w ⟨p.1, j p.1⟩ * u p := by
  obtain ⟨c, -, rfl⟩ := h
  show c p.1 * u p * u ⟨p.1, j p.1⟩ = c p.1 * u ⟨p.1, j p.1⟩ * u p
  ring

theorem sameOrbit_of_minor {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hκ : Function.Injective κ) (hvb : ∀ p, (v p).1 = κ p.1)
    (hvr : ∀ q : Σ k', ι' k', q.1 ∈ Set.range κ → q ∈ Set.range v)
    {b : (Σ k', ι' k') → ℂ} (i' : ∀ k', ι' k') (hb : ∀ k', b ⟨k', i' k'⟩ = 1)
    {u : (Σ k, ι k) → ℂ} (j : ∀ k, ι k) (hj : ∀ k, u ⟨k, j k⟩ ≠ 0)
    (hm : ∀ p, b (v p) * u ⟨p.1, j p.1⟩ = b (v ⟨p.1, j p.1⟩) * u p) :
    SameOrbit (fun p => b (v p)) u := by
  have hne : ∀ k, b (v ⟨k, j k⟩) ≠ 0 := by
    intro k h0
    obtain ⟨⟨k₀, i₀⟩, hp⟩ := hvr ⟨κ k, i' (κ k)⟩ ⟨k, rfl⟩
    have hk : k₀ = k := hκ (by simpa [hp] using (hvb ⟨k₀, i₀⟩).symm)
    subst hk
    have h1 := hm ⟨k₀, i₀⟩
    dsimp only at h1
    rw [hp, hb, h0, zero_mul, one_mul] at h1
    exact hj k₀ h1
  refine ⟨fun k => b (v ⟨k, j k⟩) / u ⟨k, j k⟩, fun k => div_ne_zero (hne k) (hj k),
    funext fun p => ?_⟩
  show b (v p) = b (v ⟨p.1, j p.1⟩) / u ⟨p.1, j p.1⟩ * u p
  rw [div_mul_eq_mul_div, ← hm p, mul_div_assoc, div_self (hj _), mul_one]

theorem proof : FibreIsolFinite.Statement := by
  classical
  intro K _ ι _ K' _ ι' _ κ v P' n hB hA u
  obtain ⟨hκ, -, hvb, hvr⟩ := hB
  have hP' : IsMultiHomogIdeal P' := hA.2.1.2.1
  by_cases hu : ∀ k, ∃ i, u ⟨k, i⟩ ≠ 0
  swap
  · refine ⟨∅, fun z' hz' ho _ => absurd ?_ hu⟩
    intro k
    obtain ⟨i', hi'⟩ := hz'.1 (κ k)
    obtain ⟨⟨k₀, i₀⟩, hp⟩ := hvr ⟨κ k, i'⟩ ⟨k, rfl⟩
    have hk : k₀ = k := hκ (by simpa [hp] using (hvb ⟨k₀, i₀⟩).symm)
    subst hk
    obtain ⟨c, -, hc⟩ := ho
    refine ⟨i₀, fun h0 => hi' ?_⟩
    have h1 : z' (v ⟨k₀, i₀⟩) = c k₀ * u ⟨k₀, i₀⟩ := congrFun hc ⟨k₀, i₀⟩
    rw [hp, h0, mul_zero] at h1
    exact h1
  choose j hj using hu
  obtain ⟨N, ⟨e⟩⟩ : ∃ N, Nonempty ((Σ k', ι' k') ≃ Fin N) := ⟨_, ⟨Fintype.equivFin _⟩⟩

  let S : (∀ k', ι' k') → Set (MvPolynomial (Fin N) ℂ) := fun i' =>
    {s | (∃ f ∈ P', s = rename e (map (Int.castRingHom ℂ) f)) ∨
      (∃ k', s = X (e ⟨k', i' k'⟩) - 1) ∨
      ∃ p : Σ k, ι k, s = X (e (v p)) * C (u ⟨p.1, j p.1⟩) - X (e (v ⟨p.1, j p.1⟩)) * C (u p)}
  have hS : ∀ i' (y : Fin N → ℂ), (∀ s ∈ S i', eval y s = 0) ↔
      ((∀ f ∈ P', eval (y ∘ e) (map (Int.castRingHom ℂ) f) = 0) ∧ (∀ k', y (e ⟨k', i' k'⟩) = 1) ∧
        ∀ p, y (e (v p)) * u ⟨p.1, j p.1⟩ = y (e (v ⟨p.1, j p.1⟩)) * u p) := by
    intro i' y
    constructor
    · intro h
      refine ⟨fun f hf => ?_, fun k' => ?_, fun p => ?_⟩
      · have h1 := h _ (Or.inl ⟨f, hf, rfl⟩)
        rwa [eval_rename] at h1
      · have h1 := h _ (Or.inr (Or.inl ⟨k', rfl⟩))
        simp only [map_sub, map_one, eval_X] at h1
        exact sub_eq_zero.mp h1
      · have h1 := h _ (Or.inr (Or.inr ⟨p, rfl⟩))
        simp only [map_sub, map_mul, eval_X, eval_C] at h1
        exact sub_eq_zero.mp h1
    · rintro ⟨h1, h2, h3⟩ s (⟨f, hf, rfl⟩ | ⟨k', rfl⟩ | ⟨p, rfl⟩)
      · rw [eval_rename]
        exact h1 f hf
      · simp only [map_sub, map_one, eval_X]
        rw [h2 k', sub_self]
      · simp only [map_sub, map_mul, eval_X, eval_C]
        rw [h3 p, sub_self]
  have hfin := fun i' => isolated_finite N (S i')
  let T : Finset ((Σ k', ι' k') → ℂ) :=
    Finset.univ.biUnion fun i' : (∀ k', ι' k') => (hfin i').toFinset.image fun y => y ∘ e
  refine ⟨T, fun z' hz' ho hiso => ?_⟩
  choose i' hi' using hz'.1
  obtain ⟨ε, hε, hball⟩ := hiso

  let d : K' → ℂ := fun k' => (z' ⟨k', i' k'⟩)⁻¹
  have hd : ∀ k', d k' ≠ 0 := fun k' => inv_ne_zero (hi' k')
  let a : (Σ k', ι' k') → ℂ := fun q => d q.1 * z' q
  have ha1 : ∀ k', a ⟨k', i' k'⟩ = 1 := fun k' => inv_mul_cancel₀ (hi' k')
  have haP : a ∈ mcPts P' := mcPts_smul hP' d hd hz'
  have hao : SameOrbit (fun p => a (v p)) u := sameOrbit_comp_smul hvb ho d hd
  let w₀ : Fin N → ℂ := a ∘ e.symm
  have hw₀ : w₀ ∘ e = a := funext fun q => by simp [w₀]
  have hw₀Z : ∀ s ∈ S i', eval w₀ s = 0 := by
    refine (hS i' w₀).mpr ⟨by rw [hw₀]; exact haP.2, fun k' => ?_, fun p => ?_⟩
    · simpa [w₀] using ha1 k'
    · simpa [w₀] using minor_of_sameOrbit hao j p
  have hw₀iso : ∀ᶠ y in 𝓝 w₀, (∀ s ∈ S i', eval y s = 0) → y = w₀ := by
    let g : (Fin N → ℂ) → (Σ k', ι' k') → ℂ := fun y q => z' ⟨q.1, i' q.1⟩ * y (e q)
    have hg : Continuous g := continuous_pi fun q => continuous_const.mul (continuous_apply _)
    have hgw : g w₀ = z' := funext fun q => by
      show z' ⟨q.1, i' q.1⟩ * (d (e.symm (e q)).1 * z' (e.symm (e q))) = z' q
      rw [Equiv.symm_apply_apply]
      exact mul_inv_cancel_left₀ (hi' q.1) (z' q)
    have hmem : g ⁻¹' Metric.ball z' ε ∈ 𝓝 w₀ :=
      hg.continuousAt.preimage_mem_nhds (by rw [hgw]; exact Metric.ball_mem_nhds _ hε)
    filter_upwards [hmem] with y hy hyS
    obtain ⟨h1, h2, h3⟩ := (hS i' y).mp hyS
    have hbP : y ∘ e ∈ mcPts P' := ⟨fun k' => ⟨i' k', by simp [h2 k']⟩, h1⟩
    have hbo : SameOrbit (fun p => (y ∘ e) (v p)) u :=
      sameOrbit_of_minor (b := y ∘ e) hκ hvb hvr i' (fun k' => h2 k') j hj h3
    have hgP : g y ∈ mcPts P' := mcPts_smul hP' (fun k' => z' ⟨k', i' k'⟩) hi' hbP
    have hgo : SameOrbit (fun p => g y (v p)) u :=
      sameOrbit_comp_smul hvb hbo (fun k' => z' ⟨k', i' k'⟩) hi'
    obtain ⟨c₁, -, hgz⟩ := hball (g y) hgP hgo hy
    have hc1 : ∀ k', c₁ k' = 1 := fun k' => by
      have h : z' ⟨k', i' k'⟩ * y (e ⟨k', i' k'⟩) = c₁ k' * z' ⟨k', i' k'⟩ := congrFun hgz ⟨k', i' k'⟩
      rw [h2 k', mul_one] at h
      exact mul_right_cancel₀ (hi' k') (h.symm.trans (one_mul _).symm)
    funext x
    have h : z' ⟨(e.symm x).1, i' (e.symm x).1⟩ * y (e (e.symm x)) = c₁ (e.symm x).1 * z' (e.symm x) :=
      congrFun hgz (e.symm x)
    rw [hc1, one_mul, Equiv.apply_symm_apply] at h
    show y x = (z' ⟨(e.symm x).1, i' (e.symm x).1⟩)⁻¹ * z' (e.symm x)
    rw [← h, ← mul_assoc, inv_mul_cancel₀ (hi' _), one_mul]
  refine ⟨w₀ ∘ e, Finset.mem_biUnion.mpr ⟨i', Finset.mem_univ _,
    Finset.mem_image.mpr ⟨w₀, (hfin i').mem_toFinset.mpr ⟨hw₀Z, hw₀iso⟩, rfl⟩⟩, ?_⟩
  rw [hw₀]
  exact ⟨fun k' => z' ⟨k', i' k'⟩, hi', funext fun q => (mul_inv_cancel_left₀ (hi' q.1) (z' q)).symm⟩

end FibreIsolFinite

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.KerIsMultiHomogIdeal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

attribute [local instance] MvPolynomial.weightedGradedAlgebra

namespace RegularityValuationCentre

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ltIdeal_one_isPrime {R Γ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ] (v : Valuation R Γ) :
    (v.ltIdeal 1).IsPrime := by
  refine ⟨fun h => ?_, fun {x y} hxy => ?_⟩
  · have h1 : (1 : v.integer) ∈ v.ltIdeal 1 := h ▸ Submodule.mem_top
    simp [Valuation.mem_ltIdeal_iff] at h1
  · simp only [Valuation.mem_ltIdeal_iff, Units.val_one] at hxy ⊢
    by_contra hc
    push Not at hc
    have hx : v x = 1 := le_antisymm x.2 hc.1
    have hy : v y = 1 := le_antisymm y.2 hc.2
    simp [Subring.coe_mul, map_mul, hx, hy] at hxy

def tWeight [DecidableEq K] (k : K) : K → ℕ := fun k' => if k' = k then 1 else 0


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem specMap_component [DecidableEq K] {E : Type*} [Field E] (ψ : MRing ι →+* E) (k : K) (d : ℕ)
    (g : MRing ι) :
    RegularityFunctionFieldNumber.specMap ψ ∅ (weightedHomogeneousComponent (blockWeight k) d g) =
      weightedHomogeneousComponent (tWeight k) d (RegularityFunctionFieldNumber.specMap ψ ∅ g) := by
  induction g using MvPolynomial.induction_on' with
  | monomial m c =>
    have hX : ∀ p : Σ k, ι k, IsWeightedHomogeneous (tWeight k)
        (RegularityFunctionFieldNumber.cS E ∅ p.1 * MvPolynomial.C (ψ (X p))) (tWeight k p.1) := by
      intro p
      simp only [RegularityFunctionFieldNumber.cS, Finset.notMem_empty, ite_false]
      rw [mul_comm]
      exact (isWeightedHomogeneous_X E (tWeight k) p.1).C_mul _
    have hh : IsWeightedHomogeneous (tWeight k) (RegularityFunctionFieldNumber.specMap ψ ∅ (monomial m c))
        (Finsupp.weight (blockWeight k) m) := by
      rw [RegularityFunctionFieldNumber.specMap, aeval_monomial, Finsupp.weight_apply, Finsupp.prod, Finsupp.sum,
        show algebraMap ℤ (MvPolynomial K E) c = MvPolynomial.C (c : E) by simp]
      exact (IsWeightedHomogeneous.prod _ _ _ fun p _ => (hX p).pow (m p)).C_mul _
    have hm : IsWeightedHomogeneous (blockWeight k) (monomial m c) (Finsupp.weight (blockWeight k) m) :=
      isWeightedHomogeneous_monomial _ _ _ rfl
    by_cases h : d = Finsupp.weight (blockWeight k) m
    · rw [h, hm.weightedHomogeneousComponent_same, hh.weightedHomogeneousComponent_same]
    · rw [hm.weightedHomogeneousComponent_ne d h, hh.weightedHomogeneousComponent_ne d h, map_zero]
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _), hp, hq, map_add (RegularityFunctionFieldNumber.specMap ψ ∅) p q]
    exact ((weightedHomogeneousComponent (R := E) (tWeight k) d).map_add _ _).symm


set_option backward.isDefEq.respectTransparency.types false in
theorem ker_isMultiHomogIdeal [DecidableEq K] {E : Type*} [Field E] (ψ : MRing ι →+* E) :
    IsMultiHomogIdeal (RingHom.ker (RegularityFunctionFieldNumber.specMap ψ ∅)) := by
  refine isMultiHomogIdeal_of_isHomogeneous fun k d g hg => ?_
  have hc : weightedHomogeneousComponent (blockWeight k) d g ∈ RingHom.ker (RegularityFunctionFieldNumber.specMap ψ ∅) := by
    rw [RingHom.mem_ker] at hg ⊢
    rw [specMap_component, hg, map_zero]
  rw [← weightedDecomposition.decompose'_apply] at hc
  exact hc

end RegularityValuationCentre


set_option maxHeartbeats 400000 in
open regularityEmbedding_holds in
theorem RegularityValuationCentre.proof : RegularityValuationCentre.Statement := by
  intro K _ ι _ P hP Γ _ v n hn
  classical
  obtain ⟨hPp, hPh, hPr⟩ := hP
  have := hPp
  have hX0 : ∀ {f : MRing ι}, f ∉ P → toFrac P f ≠ 0 := fun hf h => hf (toFrac_eq_zero.mp h)

  have hratio : ∀ (p : Σ k, ι k) (i : ι p.1), (X ⟨p.1, i⟩ : MRing ι) ∉ P → ∃ x : funField P,
      (x : FractionRing (MRing ι ⧸ P)) * toFrac P (X ⟨p.1, i⟩) = toFrac P (X p) := fun p i hi =>
    exists_funField_mul_eq (isMultiHomog_X_single p.1 p.2) (isMultiHomog_X_single p.1 i) hi
  choose j0 hj0 using hPr
  choose s hs using fun p : Σ k, ι k => hratio p (j0 p.1) (hj0 p.1)

  have hj : ∀ k, ∃ i, (X ⟨k, i⟩ : MRing ι) ∉ P ∧
      ∀ i', (X ⟨k, i'⟩ : MRing ι) ∉ P → v (s ⟨k, i'⟩) ≤ v (s ⟨k, i⟩) := by
    intro k
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun i => (X ⟨k, i⟩ : MRing ι) ∉ P)
      (fun i => v (s ⟨k, i⟩)) ⟨j0 k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj0 k⟩⟩
    exact ⟨i, (Finset.mem_filter.mp hi).2,
      fun i' hi' => hmax i' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'⟩)⟩
  choose j hjP hjmax using hj
  choose r hr using fun p : Σ k, ι k => hratio p (j p.1) (hjP p.1)

  have hrle : ∀ p, v (r p) ≤ 1 := by
    intro p
    by_cases hp : (X p : MRing ι) ∈ P
    · have h0 : r p = 0 := Subtype.ext <|
        (mul_eq_zero.mp ((hr p).trans (toFrac_eq_zero.mpr hp))).resolve_right (hX0 (hjP p.1))
      simp [h0]
    · obtain ⟨t, ht⟩ := hratio ⟨p.1, j0 p.1⟩ (j p.1) (hjP p.1)
      have hs' := hs ⟨p.1, j p.1⟩
      dsimp only at ht hs'
      have hst : s ⟨p.1, j p.1⟩ * t = 1 := Subtype.ext <| mul_right_cancel₀ (hX0 (hjP p.1)) <| by
        rw [Subring.coe_mul, Subring.coe_one, mul_assoc, ht, hs', one_mul]
      have hrs : r p * s ⟨p.1, j p.1⟩ = s p := Subtype.ext <| mul_right_cancel₀ (hX0 (hj0 p.1)) <| by
        rw [Subring.coe_mul, mul_assoc, hs', hr, hs]
      have hvs : v (s ⟨p.1, j p.1⟩) ≠ 0 := fun h => by
        have h1 := congrArg v hst
        rw [map_mul, h, zero_mul, map_one] at h1
        exact zero_ne_one h1
      have hle : v (r p) * v (s ⟨p.1, j p.1⟩) ≤ 1 * v (s ⟨p.1, j p.1⟩) := by
        rw [← map_mul, hrs, one_mul]
        exact hjmax p.1 p.2 hp
      exact le_of_mul_le_mul_right hle (zero_lt_iff.mpr hvs)

  have hψle : ∀ g, chartHom r g ∈ v.integer := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp [chartHom]
    | add f g hf hg => rw [map_add]; exact add_mem hf hg
    | mul_X f p hf =>
      rw [map_mul]
      exact mul_mem hf (by simpa [chartHom] using (Valuation.mem_integer_iff v (r p)).mpr (hrle p))
  have : (v.ltIdeal 1).IsPrime := RegularityValuationCentre.ltIdeal_one_isPrime v

  obtain ⟨E, _, ψE, hψE⟩ : ∃ (E : Type) (_ : Field E) (ψE : MRing ι →+* E),
      ∀ g, ψE g = 0 ↔ v (chartHom r g) < 1 := by
    refine ⟨FractionRing (v.integer ⧸ v.ltIdeal 1), inferInstance, (algebraMap (v.integer ⧸ v.ltIdeal 1) _).comp
      ((Ideal.Quotient.mk (v.ltIdeal 1)).comp ((chartHom r).codRestrict v.integer hψle)), fun g => ?_⟩
    rw [RingHom.comp_apply, RingHom.comp_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _),
      Ideal.Quotient.eq_zero_iff_mem, Valuation.mem_ltIdeal_iff, Units.val_one]
    rfl

  have hform : ∀ (g : MRing ι) (a : K → ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a →
      (g ∈ RingHom.ker (RegularityFunctionFieldNumber.specMap ψE ∅) ↔ v (chartHom r g) < 1) := by
    intro g a hg
    rw [RingHom.mem_ker, RegularityFunctionFieldNumber.specMap_form ψE ∅ hg, ← hψE, mul_eq_zero, MvPolynomial.C_eq_zero]
    refine or_iff_right (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ ?_)
    simp [RegularityFunctionFieldNumber.cS, MvPolynomial.X_ne_zero]
  have hWp : (RingHom.ker (RegularityFunctionFieldNumber.specMap ψE ∅)).IsPrime := RingHom.ker_isPrime _
  have hPW : P ≤ RingHom.ker (RegularityFunctionFieldNumber.specMap ψE ∅) := by
    obtain ⟨S, hS, hPS⟩ := hPh
    refine hPS.le.trans (Ideal.span_le.mpr fun g hg => ?_)
    obtain ⟨a, ha⟩ := hS g hg
    have hgP : g ∈ P := hPS ▸ Ideal.subset_span hg
    rw [SetLike.mem_coe, hform g a ha]
    have h1 := chartHom_mul j r hr ha
    rw [toFrac_eq_zero.mpr hgP] at h1
    have hφ : chartHom r g = 0 :=
      Subtype.ext ((mul_eq_zero.mp h1).resolve_right (toFrac_prod_ne_zero j hjP a))
    rw [hφ, map_zero]
    exact zero_lt_one
  have hC : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (C n : MRing ι) 0 := fun μ hμ k => by
    rw [mem_support_iff, coeff_C] at hμ
    split_ifs at hμ with h
    · subst h
      simp
    · exact absurd rfl hμ
  refine ⟨RingHom.ker (RegularityFunctionFieldNumber.specMap ψE ∅),
    ⟨hWp, RegularityValuationCentre.ker_isMultiHomogIdeal ψE, fun k => ⟨j k, ?_⟩⟩, hPW, ?_, fun z hz => ?_⟩
  ·
    have hrj : r ⟨k, j k⟩ = 1 :=
      Subtype.ext (mul_right_cancel₀ (hX0 (hjP k)) ((hr ⟨k, j k⟩).trans (one_mul _).symm))
    rw [hform _ _ (isMultiHomog_X_single k (j k))]
    have hXr : chartHom r (X ⟨k, j k⟩) = r ⟨k, j k⟩ := eval₂Hom_X' _ _ _
    rw [hXr, hrj, Valuation.map_one]
    exact lt_irrefl 1
  · rw [hform _ 0 hC]
    have hCn : chartHom r (C n) = (n : funField P) := eval₂Hom_C _ _ _
    rw [hCn]
    exact hn
  ·
    obtain ⟨u, w, a, hu, hw, hwW, e⟩ := LocRingFrac.proof K ι P _ hPp hWp hPW z hz
    have hzw : z * chartHom r w = chartHom r u :=
      Subtype.ext <| mul_right_cancel₀ (toFrac_prod_ne_zero j hjP a) <| by
        rw [Subring.coe_mul, mul_assoc, chartHom_mul j r hr hw, chartHom_mul j r hr hu]
        exact e
    have hvw : v (chartHom r w) = 1 :=
      le_antisymm (hψle w) (not_lt.mp fun h => hwW ((hform w a hw).mpr h))
    have h1 := congrArg v hzw
    rw [map_mul, hvw, mul_one] at h1
    exact h1 ▸ hψle u

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisMore
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem RegularityIntegral.proof (hC : RegularityValuationCentre.Statement) (hB : RegularityRelativeClosedPoint.Statement) :
    RegularityIntegral.Statement := by
  intro K _ ι _ P hP x
  obtain ⟨hF, hNF⟩ := RegularityFunctionFieldNumber.proof K ι P hP
  let _ := hF.toField
  have hv : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers (funField P)),
      v.valuation (funField P) (x : funField P) ≤ 1 := by
    intro v
    obtain ⟨n, hn0, hn⟩ := RegularityValuationCentre.exists_int_valuation_lt_one v
    obtain ⟨W, hW, hPW, hnW, hsub⟩ := hC K ι P hP.2.1 _ (v.valuation (funField P)) n hn
    have hWP : W ≠ P := by
      rintro rfl
      have h0 : n ∈ W.comap (C : ℤ →+* MRing ι) := hnW
      rw [show W.comap (C : ℤ →+* MRing ι) = ⊥ from hP.2.2.1, Ideal.mem_bot] at h0
      exact hn0 h0
    exact hsub x (x.2 W (hB K ι P W hP hW hPW hWP) hPW)
  obtain ⟨y, hy⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (funField P)
    (x : funField P) hv
  have hint : IsIntegral ℤ (x : funField P) := hy ▸ (Algebra.IsIntegral.isIntegral y).algebraMap
  let f : funField P →ₐ[ℤ] FractionRing (MRing ι ⧸ P) :=
    { (funField P).subtype with commutes' := fun n => by simp }
  exact hint.map f

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisFurther
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem RegularityLocalPrime.proof (h₁ : RegularityOrder.Statement) : RegularityLocalPrime.Statement := by
  intro K _ ι _ P p y hP hp hy
  have hPp : P.IsPrime := hP.2.1.1
  obtain ⟨c, hc0, hc⟩ := RegularityDenominator.proof RegularityDivisorSupportClosed.proof LocRingPow.proof K ι P y hP
  have hcR : c ∈ regRing P := fun W h1 h2 => (hc W h1 h2).1
  have : Module.Finite ℤ (regRing P) := (h₁ K ι P hP).2.1
  have hci : IsIntegral ℤ (⟨c, hcR⟩ : regRing P) := Algebra.IsIntegral.isIntegral _
  have hne := Ideal.comap_ne_bot_of_integral_mem (I := Ideal.span {(⟨c, hcR⟩ : regRing P)})
    (fun h => hc0 (congrArg Subtype.val h)) (Ideal.mem_span_singleton_self _) hci
  obtain ⟨N, hN, hN0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hN)
  have hNF : ((N : funField P) : FractionRing (MRing ι ⧸ P)) =
      ((d : funField P) : FractionRing (MRing ι ⧸ P)) * (c : FractionRing (MRing ι ⧸ P)) := by
    have h := congrArg (fun z : regRing P => ((z : funField P) : FractionRing (MRing ι ⧸ P))) hd
    simp only [Subring.coe_mul, algebraMap_int_eq, eq_intCast, SubringClass.coe_intCast] at h
    simp only [SubringClass.coe_intCast]
    exact h.symm
  have hpu : p.natAbs ≠ 1 := fun h => hp.not_isUnit (Int.isUnit_iff_natAbs_eq.mpr h)
  obtain ⟨m, hNm, hpm⟩ := (Int.finiteMultiplicity_iff.mpr ⟨hpu, hN0⟩).exists_eq_pow_mul_and_not_dvd
  generalize multiplicity p N = e at hNm
  refine ⟨m, hpm, fun W h1 h2 => ?_⟩
  rw [Subring.coe_mul, SubringClass.coe_intCast]
  by_cases hpW : C p ∈ W
  · exact mul_mem (intCast_mem _ m) (hy W h1 h2 hpW)
  have hCp : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (C p)) = (p : _) := by
    rw [eq_intCast C p, map_intCast, map_intCast]
  have hp0 : (p : FractionRing (MRing ι ⧸ P)) ≠ 0 := by
    intro h
    apply hpW
    apply h2
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← IsFractionRing.to_map_eq_zero_iff (K := FractionRing (MRing ι ⧸ P)),
      hCp, h]
  have hq : (p : FractionRing (MRing ι ⧸ P))⁻¹ ∈ locRing P W :=
    frac_mem_locRing h2 (RegularityDenominator.isMultiHomog_C 1) (RegularityDenominator.isMultiHomog_C p) hpW
      (by rw [hCp, map_one, map_one, map_one, inv_mul_cancel₀ hp0])
  have hyc : (y : FractionRing (MRing ι ⧸ P)) * (c : FractionRing (MRing ι ⧸ P)) ∈ locRing P W := by
    have := (hc W h1 h2).2
    rwa [Subring.coe_mul] at this
  have hdW : ((d : funField P) : FractionRing (MRing ι ⧸ P)) ∈ locRing P W := d.2 W h1 h2
  have key : (m : FractionRing (MRing ι ⧸ P)) * (y : FractionRing (MRing ι ⧸ P)) =
      (p : FractionRing (MRing ι ⧸ P))⁻¹ ^ e *
        (((d : funField P) : FractionRing (MRing ι ⧸ P)) * ((y : FractionRing (MRing ι ⧸ P)) * c)) := by
    have hN' : ((d : funField P) : FractionRing (MRing ι ⧸ P)) * ((y : FractionRing (MRing ι ⧸ P)) * c) =
        (p : FractionRing (MRing ι ⧸ P)) ^ e * m * y := by
      rw [show ((d : funField P) : FractionRing (MRing ι ⧸ P)) * ((y : FractionRing (MRing ι ⧸ P)) * c) =
        ((N : funField P) : FractionRing (MRing ι ⧸ P)) * y by rw [hNF]; ring, SubringClass.coe_intCast,
        hNm, Int.cast_mul, Int.cast_pow]
    rw [hN', inv_pow, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hp0), one_mul]
  rw [key]
  exact mul_mem (pow_mem hq _) (mul_mem hdW hyc)

end

end GroundTheory.Heights₂.Heights.Inter
end
