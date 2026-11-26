module

public import Development.WeilBound.CoreStatements.FlagImmersions.IntersectionMultilinearExpansion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HermitianCombinationSmoothConj
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FiniteVerticalRecursion

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionMultilinearAll
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionMultilinearAll
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem intersection_combLine_expansion : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (J : Type) [Fintype J] [DecidableEq J] (ℓ : J → HermLine ι) (n : Fin d → J → ℤ), IsArithVar P d → (∀ j, IsSmoothHerm (ℓ j)) → II K ι P d (fun k => combLine ℓ (n k)) = ∑ w : Fin d → J, (∏ k, (n k (w k) : ℝ)) * II K ι P d (fun k => ℓ (w k)) :=
  @RootFieldNumerics.intersection_multilinear_expansion

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionMultilinearAllStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_intersection_multilinear_all : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (J : Type) [Fintype J] [DecidableEq J] (ℓ : J → HermLine ι) (n : Fin d → J → ℤ), IsArithVar P d → (∀ j, IsSmoothHerm (ℓ j)) → II K ι P d (fun k => combLine ℓ (n k)) = ∑ w : Fin d → J, (∏ k, (n k (w k) : ℝ)) * II K ι P d (fun k => ℓ (w k)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.intersection_combLine_expansion | exact GlobalTheory.CompanionTheory.Ar.Top.intersection_combLine_expansion | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.intersection_combLine_expansion <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelArithIntersectionFormula
section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.RootModelArithmeticIntersection
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

namespace Ii

theorem lin_prod_expand {J : Type} [Fintype J] [DecidableEq J] (d : ℕ) (Φ : MvPolynomial J ℝ →ₗ[ℝ] ℝ)
    (c : J → ℝ) :
    Φ ((∑ j, C (c j) * X j) ^ d) =
      ∑ w : Fin d → J, (∏ k, c (w k)) * Φ (monomial (∑ k, Finsupp.single (w k) 1) 1) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Fin.prod_const, Fintype.prod_sum, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hm : ∏ k, C (c (w k)) * X (w k) = C (∏ k, c (w k)) * monomial (∑ k, Finsupp.single (w k) 1) (1 : ℝ) := by
    rw [Finset.prod_mul_distrib, map_prod, monomial_sum_one]
    rfl
  rw [hm, C_mul', map_smul, smul_eq_mul]

theorem prod_weight {α : Type} [DecidableEq α] {d : ℕ} (w : Fin d → Option α) (x : ℝ) :
    ∏ k, (if w k = none then x else 1) = x ^ (∑ k, Finsupp.single (w k) 1 : Option α →₀ ℕ) none := by
  rw [Finsupp.finsetSum_apply, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finsupp.single_apply]
  split_ifs <;> simp

end Ii

open Ii in
theorem root_model_arithmetic_intersection : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), (∀ j, (n j : ℝ) = q * M.coef lam s j) → II M.K M.ι M.P (dimFl Ψ N + 1) (fun _ => combLine (M.line t) n) = M.δ * (q : ℝ) ^ (dimFl Ψ N + 1) * M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) := by
  intro II hII Ψ _ N M t lam s q n hn
  classical
  have hsm : ∀ j, IsSmoothHerm (M.line t j) := by
    intro j
    cases j with
    | none => exact M.A_smooth
    | some r => exact M.x_smooth t r
  rw [RootFieldNumerics.intersection_multilinear_expansion II hII M.K M.ι M.P (dimFl Ψ N + 1) _ (M.line t) (fun _ => n) M.arith hsm]
  let cc : Option (Ψ × Fin N) → ℝ := fun j => Option.elim j s (fun r => -lam r.1 r.2)
  have hlin : linA lam s = ∑ j, C (cc j) * X j := by
    rw [Fintype.sum_option]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [cc, linA, toA, linRoot, map_sum, map_neg, rename_X, Finset.sum_neg_distrib, add_comm]
  rw [hlin, lin_prod_expand, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  obtain ⟨hdeg, σ, _, hII2⟩ := RootFieldNumerics.intersection_monomial_lines II hII.1 M.K M.ι M.P (dimFl Ψ N + 1) _ (M.line t) w M.arith hsm
  have hmono : M.arFun II t (monomial (∑ k, Finsupp.single (w k) 1) 1) =
      II M.K M.ι M.P (dimFl Ψ N + 1) (fun k => M.line t (w k)) /
        (M.δ * (M.kA : ℝ) ^ (∑ k, Finsupp.single (w k) 1 : Option (Ψ × Fin N) →₀ ℕ) none) := by
    have hb : (monomial (∑ k, Finsupp.single (w k) 1) (1 : ℝ) : RPA Ψ N) =
        basisMonomials (Option (Ψ × Fin N)) ℝ (∑ k, Finsupp.single (w k) 1) := by
      rw [coe_basisMonomials]
    rw [RootModel.arFun, hb, Module.Basis.constr_basis, RootModel.arMono, if_pos hdeg, hII2]
  have hc : ∏ k, cc (w k) = (∏ k, M.coef lam s (w k)) *
      (M.kA : ℝ) ^ (∑ k, Finsupp.single (w k) 1 : Option (Ψ × Fin N) →₀ ℕ) none := by
    rw [← prod_weight w (M.kA : ℝ), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    have hk : (M.kA : ℝ) ≠ 0 := by exact_mod_cast M.kA_pos.ne'
    cases w k with
    | none =>
      simp [cc, RootModel.coef]
      field_simp
    | some r => simp [cc, RootModel.coef]
  have hnp : ∏ k, (n (w k) : ℝ) = (q : ℝ) ^ (dimFl Ψ N + 1) * ∏ k, M.coef lam s (w k) := by
    simp_rw [hn]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hδ : (M.δ : ℝ) ≠ 0 := by exact_mod_cast M.δ_pos.ne'
  have hk : (M.kA : ℝ) ≠ 0 := by exact_mod_cast M.kA_pos.ne'
  rw [hmono, hc, hnp]
  field_simp

end RootFieldNumerics
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelArithIntersectionFormula
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem top_comb_eq_arFun : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), (∀ j, (n j : ℝ) = q * M.coef lam s j) → II M.K M.ι M.P (dimFl Ψ N + 1) (fun _ => combLine (M.line t) n) = M.δ * (q : ℝ) ^ (dimFl Ψ N + 1) * M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) :=
  RootFieldNumerics.root_model_arithmetic_intersection

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelArithIntersectionFormulaStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_model_arith_intersection_formula : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), (∀ j, (n j : ℝ) = q * M.coef lam s j) → II M.K M.ι M.P (dimFl Ψ N + 1) (fun _ => combLine (M.line t) n) = M.δ * (q : ℝ) ^ (dimFl Ψ N + 1) * M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.top_comb_eq_arFun | exact GlobalTheory.CompanionTheory.Ar.Top.top_comb_eq_arFun | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.top_comb_eq_arFun <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsometricVerticalIntersectionEq
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsometricVerticalIntersectionEq
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.Link

theorem divCycle_eq_off {K : Type} {ι : K → Type} {P : Ideal (MRing ι ℤ)} {f g : MRing ι ℤ} {S : Finset Nat.Primes}
    (h : ∀ W : Ideal (MvPolynomial (Σ k, ι k) ℤ), W.IsPrime → P ≤ W → IsRelevant W →
      (∀ p ∈ S, (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ W) →
      ∃ u v : MvPolynomial (Σ k, ι k) ℤ, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ P)
    {W : Ideal (MRing ι ℤ)}
    (hW : W.IsPrime → ∀ p ∈ S, (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ W) :
    divCycle P f W = divCycle P g W := by
  by_cases hc : W.IsPrime ∧ P ≤ W ∧ IsRelevant W
  · obtain ⟨u, v, hu, hv, huv⟩ := h W hc.1 hc.2.1 hc.2.2 (hW hc.1)
    exact divCycle_eq_of_mul_sub_mem hu hv huv
  · have h0 : ∀ s : MRing ι ℤ, divCycle P s W = 0 := fun s => by
      by_contra hne
      exact hc (le_and_isRelevant_of_divCycle_ne_zero hne)
    rw [h0, h0]

theorem not_mem_of_mem {K : Type} {ι : K → Type} {W : Ideal (MRing ι ℤ)} (hW : W.IsPrime) {p q : Nat.Primes}
    (hpq : p ≠ q) (hp : (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∈ W) :
    (C ((q : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ W := by
  intro hq
  have hcop : IsCoprime ((p : ℕ) : ℤ) ((q : ℕ) : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact (Nat.coprime_primes p.2 q.2).2 fun h => hpq (Subtype.ext h)
  obtain ⟨a, b, hab⟩ := hcop
  apply hW.ne_top
  rw [Ideal.eq_top_iff_one]
  have e : (1 : MvPolynomial (Σ k, ι k) ℤ) =
      C a * C ((p : ℕ) : ℤ) + C b * C ((q : ℕ) : ℤ) := by
    rw [← C_mul, ← C_mul, ← C_add, hab, C_1]
  rw [e]
  exact W.add_mem (W.mul_mem_left _ hp) (W.mul_mem_left _ hq)

theorem not_mem_of_horizontal {K : Type} {ι : K → Type} {W : Ideal (MRing ι ℤ)} (hW : IsHorizontal W)
    (p : Nat.Primes) : (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ W := by
  intro hp
  have h1 : ((p : ℕ) : ℤ) ∈ W.comap (C : ℤ →+* MvPolynomial (Σ k, ι k) ℤ) := hp
  rw [show W.comap (C : ℤ →+* MvPolynomial (Σ k, ι k) ℤ) = ⊥ from hW, Ideal.mem_bot] at h1
  exact p.2.ne_zero (by exact_mod_cast h1)

theorem change_line : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ (S : Finset Nat.Primes) (T : LocPair ι ℤ Unit), T.IsVertOff P S → ∀ A A' : HermLine ι, IsSmoothHerm A → IsSmoothHerm A' → T.IsIsometric P (fun _ => A) (fun _ => A') → ∀ L : Fin D → HermLine ι, (∀ j, IsSmoothHerm (L j)) → I P (D + 1) (Fin.snoc L A) - I P (D + 1) (Fin.snoc L A') = ∑ p ∈ S, Real.log (p : ℕ) * ((vertAt p P (T.f ()) (List.ofFn fun j => (L j).a) : ℝ) - (vertAt p P (T.g ()) (List.ofFn fun j => (L j).a) : ℝ)) := by
  intro K _ _ ι _ P D hP I hI S T hT A A' hA hA' hiso L hL
  obtain ⟨⟨bf, bg, hf, hg, hdeg⟩, hfP, hgP, hunit⟩ := hT ()
  obtain ⟨hAa, hA'a, hnorm⟩ := hiso ()
  let B : HermLine ι := (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric bf).tensor A.inv
  have hB : IsSmoothHerm B := ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor
    (ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_sqMetric bf) (ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_inv hA)
  have hAB : IsSmoothHerm (A.tensor B) := ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor hA hB
  have hAB' : IsSmoothHerm (A'.tensor B) := ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor hA' hB
  have dF : ∀ k, (A.tensor B).a k = bf k := fun k => by
    simp [B, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.inv,
      ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric]
  have dG : ∀ k, (A'.tensor B).a k = bg k := fun k => by
    have h1 := congrFun hdeg k
    have h2 := congrFun hAa k
    have h3 := congrFun hA'a k
    simp only [Pi.sub_apply] at h1
    simp only [B, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.inv,
      ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric, Pi.add_apply, Pi.neg_apply]
    linarith
  have e1 := hI.2.1 P D L A B hP hL hA hB
  have e2 := hI.2.1 P D L A' B hP hL hA' hB
  have r1 := hI.2.2 P D L (A.tensor B) (T.f ()) bf hP hL hAB dF
    ((GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff _ _).1 hf) hfP
  have r2 := hI.2.2 P D L (A'.tensor B) (T.g ()) bg hP hL hAB' dG
    ((GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff _ _).1 hg) hgP
  obtain ⟨fin1, s1⟩ := GlobalTheory.T.finite_vertical_recursion K ι P D hP I bf (T.f ()) hf hfP L (A.tensor B)
  obtain ⟨fin2, s2⟩ := GlobalTheory.T.finite_vertical_recursion K ι P D hP I bg (T.g ()) hg hgP L (A'.tensor B)
  have hor : (∑ᶠ W, (divCycle P (T.f ()) W : ℝ) * Set.indicator {W | IsHorizontal W} (fun W => I W D L) W) =
      ∑ᶠ W, (divCycle P (T.g ()) W : ℝ) * Set.indicator {W | IsHorizontal W} (fun W => I W D L) W := by
    refine finsum_congr fun W => ?_
    by_cases hW : IsHorizontal W
    · rw [divCycle_eq_off hunit (fun _ p _ => not_mem_of_horizontal hW p)]
    · have : W ∉ {W | IsHorizontal W} := hW
      simp [Set.indicator_of_notMem this]
  have ar : arInt P (T.f ()) (A.tensor B) L = arInt P (T.g ()) (A'.tensor B) L := by
    refine (GlobalTheory.T.log_integral_congr_smul K ι P D _).1 _ _ fun z hz => ?_
    have h1 := hnorm z hz
    have pA := A.pos z hz.1
    have pA' := A'.pos z hz.1
    have pB := B.pos z hz.1
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.logNorm, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor]
    congr 1
    rw [div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (B.h z) * h1
  have hv : ∀ p : Nat.Primes, p ∉ S → vertAt p P (T.f ()) (List.ofFn fun j => (L j).a) =
      vertAt p P (T.g ()) (List.ofFn fun j => (L j).a) := by
    intro p hp
    unfold vertAt cycEval
    refine finsum_congr fun W => ?_
    by_cases hpW : (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∈ W
    · rw [divCycle_eq_off hunit (fun hWp q hq => not_mem_of_mem hWp
        (fun h : p = q => hp (by rw [h]; exact hq)) hpW)]
    · simp only [if_neg hpW, mul_zero]
  have vert : (∑ᶠ p : Nat.Primes, Real.log (p : ℕ) * (vertAt p P (T.f ()) (List.ofFn fun j => (L j).a) : ℝ)) -
      (∑ᶠ p : Nat.Primes, Real.log (p : ℕ) * (vertAt p P (T.g ()) (List.ofFn fun j => (L j).a) : ℝ)) =
      ∑ p ∈ S, Real.log (p : ℕ) * ((vertAt p P (T.f ()) (List.ofFn fun j => (L j).a) : ℝ) -
        (vertAt p P (T.g ()) (List.ofFn fun j => (L j).a) : ℝ)) := by
    have hF : (Function.support fun p : Nat.Primes =>
        Real.log (p : ℕ) * (vertAt p P (T.f ()) (List.ofFn fun j => (L j).a) : ℝ)).Finite :=
      fin1.subset fun p hp h0 => hp (by simp [h0])
    have hG : (Function.support fun p : Nat.Primes =>
        Real.log (p : ℕ) * (vertAt p P (T.g ()) (List.ofFn fun j => (L j).a) : ℝ)).Finite :=
      fin2.subset fun p hp h0 => hp (by simp [h0])
    rw [← finsum_sub_distrib hF hG,
      finsum_eq_sum_of_support_subset (s := S) _ fun p hp => ?_]
    · exact Finset.sum_congr rfl fun p _ => by ring
    · by_contra hpS
      exact hp (by simp [hv p (by simpa using hpS)])
  have e3 : I P (D + 1) (Fin.snoc L A) - I P (D + 1) (Fin.snoc L A') =
      I P (D + 1) (Fin.snoc L (A.tensor B)) - I P (D + 1) (Fin.snoc L (A'.tensor B)) := by
    rw [e1, e2]; ring
  rw [e3, r1, r2, s1, s2, hor, ar, ← vert]
  ring

end GlobalTheory.CompanionTheory.Ar.Num.Link
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsometricVerticalIntersectionEqStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometric_vertical_intersection_eq : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ (S : Finset Nat.Primes) (T : LocPair ι ℤ Unit), T.IsVertOff P S → ∀ A A' : HermLine ι, IsSmoothHerm A → IsSmoothHerm A' → T.IsIsometric P (fun _ => A) (fun _ => A') → ∀ L : Fin D → HermLine ι, (∀ j, IsSmoothHerm (L j)) → I P (D + 1) (Fin.snoc L A) - I P (D + 1) (Fin.snoc L A') = ∑ p ∈ S, Real.log (p : ℕ) * ((vertAt p P (T.f ()) (List.ofFn fun j => (L j).a) : ℝ) - (vertAt p P (T.g ()) (List.ofFn fun j => (L j).a) : ℝ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.Link.change_line | exact GlobalTheory.CompanionTheory.Ar.Num.Link.change_line | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.Link.change_line <;> assumption)
end
end
