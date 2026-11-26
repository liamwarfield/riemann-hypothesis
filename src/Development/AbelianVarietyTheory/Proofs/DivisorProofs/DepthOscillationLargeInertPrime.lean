module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumEigenInertPlaceLatticeStabiliser
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDeterminantPowDepthBasisChangeInvaria
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypicalCurvesTangentAndBases
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupRootsOfUnityTypedLieRanks
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorDepthBoundsInertPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerContentDetPowDependsOnPIK
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerContentDetPowDependsOnPIK
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

namespace GlobalTheory.DetPowContent

open GlobalTheory.DetPowShape

noncomputable def intCoeff (i k : ℕ) (α : (Σ _ : Fin i, Fin i) →₀ ℕ) : ℤ :=
  (detZ i ^ k).coeff α * α.prod fun _ n => ((n.factorial : ℕ) : ℤ)

theorem cast_intCoeff (C : Type) [Field C] (i k : ℕ) (α : (Σ _ : Fin i, Fin i) →₀ ℕ) :
    ((intCoeff i k α : ℤ) : C) = (detPow C i k).coeff α * GlobalTheory.FGDepth.mfact α := by
  rw [intCoeff, detPow_eq_map, MvPolynomial.coeff_map, Int.cast_mul, GlobalTheory.FGDepth.mfact]
  congr 1 <;> simp [Finsupp.prod]

theorem mem_support_iff' (C : Type) [Field C] [CharZero C] (i k : ℕ) (α) :
    α ∈ (detPow C i k).support ↔ α ∈ (detZ i ^ k).support := by
  rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff, detPow_eq_map,
    MvPolynomial.coeff_map]
  simp

theorem intCoeff_ne_zero (i k : ℕ) (α) (h : α ∈ (detZ i ^ k).support) : intCoeff i k α ≠ 0 := by
  rw [intCoeff]
  refine mul_ne_zero (MvPolynomial.mem_support_iff.1 h) ?_
  rw [Finsupp.prod]
  refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
  exact_mod_cast Nat.factorial_ne_zero _

theorem v_intCast (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ)
    (hp : p.Prime) (hv : v (p : C) = 1) (m : ℤ) (hm : m ≠ 0) :
    v (m : C) = (((padicValNat p m.natAbs : ℕ) : ℝ) : WithTop ℝ) := by
  have h := GlobalTheory.addValuation_natCast_eq_padicValNat C v p hp hv m.natAbs (Int.natAbs_ne_zero.2 hm)
  rcases Int.natAbs_eq m with h1 | h1
  · conv_lhs => rw [h1]
    simpa using h
  · conv_lhs => rw [h1, Int.cast_neg, v.map_neg]
    simpa using h

end GlobalTheory.DetPowContent

namespace GlobalTheory


open GlobalTheory.DetPowShape GlobalTheory.DetPowContent in
theorem detPow_content_const : ∀ (p : ℕ), p.Prime → ∀ i k : ℕ, ∃ κ : ℝ, ∀ (C : Type) [Field C]
    [CharZero C] (v : AddValuation C (WithTop ℝ)), v (p : C) = 1 →
      content v (detPow C i k) = (κ : EReal) := by
  intro p hp i k
  set S := (detZ i ^ k).support with hS
  have hne : S.Nonempty := by
    refine ⟨∑ a : Fin i, Finsupp.single ⟨a, a⟩ k, ?_⟩
    rw [← mem_support_iff' ℚ]
    rw [MvPolynomial.mem_support_iff, (detPow_shape ℚ i k).2.2.1]
    exact one_ne_zero
  let f : ((Σ _ : Fin i, Fin i) →₀ ℕ) → ℕ := fun α => padicValNat p (intCoeff i k α).natAbs
  obtain ⟨α0, hα0, hmin⟩ := S.exists_min_image f hne
  refine ⟨(f α0 : ℝ), fun C _ _ v hv => ?_⟩
  have hval : ∀ α ∈ S, GlobalTheory.FGDepth.toE (v ((detPow C i k).coeff α * GlobalTheory.FGDepth.mfact α)) =
      ((f α : ℝ) : EReal) := by
    intro α hα
    rw [← cast_intCoeff, v_intCast C v p hp hv _ (intCoeff_ne_zero i k α hα)]
    rfl
  unfold GlobalTheory.FGDepth.content
  apply le_antisymm
  · refine iInf₂_le_of_le α0 ((mem_support_iff' C i k α0).2 hα0) ?_
    rw [hval α0 hα0]
  · refine le_iInf₂ fun α hα => ?_
    have hα' := (mem_support_iff' C i k α).1 hα
    rw [hval α hα']
    exact_mod_cast hmin α hα'

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerContentDetPowDependsOnPIKStatement
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividedPowerContent_detPow_depends_on_p_i_k : ∀ (p : ℕ), p.Prime → ∀ i k : ℕ, ∃ κ : ℝ, ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)), v (p : C) = 1 → content v (detPow C i k) = (κ : EReal) := by
  first | exact @GlobalTheory.detPow_content_const | exact GlobalTheory.detPow_content_const | (intros; apply GlobalTheory.detPow_content_const <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContentLeDetDepthAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTypicalCurveBasisAdaptedToSaturatedFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTypicalCurveBasisAdaptedToSaturatedFrame
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem det_eq_det_minor_of_unit_rows {K : Type} [CommRing K] {i d : ℕ} (r : Fin i → Fin d)
    (hr : Function.Injective r) (M : Matrix (Fin d) (Fin d) K)
    (hM : ∀ e, e ∉ Set.range r → ∀ c, M e c = if c = e then 1 else 0) :
    M.det = (M.submatrix r r).det := by
  classical
  let E : Fin i ⊕ {e // e ∉ Set.range r} ≃ Fin d :=
    (Equiv.sumCongr (Equiv.ofInjective r hr) (Equiv.refl _)).trans
      (Equiv.sumCompl (fun e => e ∈ Set.range r))
  have hEl : ∀ a, E (Sum.inl a) = r a := fun a => rfl
  have hEr : ∀ e, E (Sum.inr e) = e.1 := fun e => rfl
  rw [← Matrix.det_submatrix_equiv_self E M, ← Matrix.fromBlocks_toBlocks (M.submatrix E E)]
  have h21 : (M.submatrix E E).toBlocks₂₁ = 0 := by
    ext e b
    simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.submatrix_apply, Matrix.zero_apply, hEl, hEr]
    rw [hM e.1 e.2, if_neg]
    rintro h
    exact e.2 ⟨b, h⟩
  have h22 : (M.submatrix E E).toBlocks₂₂ = 1 := by
    ext e e'
    simp only [Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.submatrix_apply, hEr, Matrix.one_apply]
    rw [hM e.1 e.2]
    by_cases hee : e = e'
    · subst hee; simp
    · rw [if_neg (fun h => hee (Subtype.ext h).symm), if_neg hee]
  have h11 : (M.submatrix E E).toBlocks₁₁ = M.submatrix r r := by
    ext a b
    simp only [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.submatrix_apply, hEl]
  rw [h21, Matrix.det_fromBlocks_zero₂₁, h22, Matrix.det_one, mul_one, h11]

end GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem exists_basis_adapted_frame : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (d h : ℕ), 0 < h →
    ∀ (ty : Fin d → ZMod h) (G : LogFGL v d), MuAction G p h ty → ∀ (τ : ZMod h) (j i : ℕ),
    (Finset.univ.filter fun a => ty a = τ + 1).card ≤ j → ∀ u : Fin i → Fin d → C,
    IsSatFrame v u → (∀ a e, ty e ≠ τ → u a e = 0) →
    ∃ (γ : Fin d → Fin d → PowerSeries C) (r : Fin i ↪ Fin d) (g : Matrix (Fin i) (Fin i) C),
      IsBasis G p ty γ ∧ (∀ a b, IsIntV v (g a b)) ∧ v g.det = 0 ∧
      (∀ a, tangent (γ (r a)) = ∑ a', g a a' • u a') ∧
      ∀ a : Fin i, j ≤ a.val → G.lc p (γ (r a)) 1 = 0 := by
  intro C _ _ _ v p hp hv d h hh ty G hmu τ j i hj u hu hut
  classical
  obtain ⟨hPT2, -⟩ := GlobalTheory.T.typicalCurveEigenspace_and_basisExists
  choose η hηc hηt hηtan using fun a : Fin i =>
    hPT2 C v p hp hv d h hh ty G hmu τ (u a) (hu.1 a) (hut a)
  have hspan : Module.finrank C (Submodule.span C (Set.range fun a =>
      (LinearMap.id : (Fin d → C) →ₗ[C] (Fin d → C)) (G.lc p (η a) 1))) ≤ j := by
    let W := Submodule.span C
      (Set.range fun e : {e : Fin d // ty e = τ + 1} => (Pi.single e.1 (1 : C) : Fin d → C))
    have hle : Submodule.span C (Set.range fun a =>
        (LinearMap.id : (Fin d → C) →ₗ[C] (Fin d → C)) (G.lc p (η a) 1)) ≤ W := by
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      show G.lc p (η a) 1 ∈ W
      rw [← Finset.univ_sum_single (G.lc p (η a) 1)]
      refine Submodule.sum_mem _ fun e _ => ?_
      by_cases he : ty e = τ + 1
      · have : (Pi.single e (G.lc p (η a) 1 e) : Fin d → C) =
            G.lc p (η a) 1 e • (Pi.single e (1 : C) : Fin d → C) := by
          ext c; simp [Pi.single_apply]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨e, he⟩, rfl⟩)
      · rw [(hηt a).2 1 e (by simpa using he), Pi.single_zero]
        exact Submodule.zero_mem _
    calc _ ≤ Module.finrank C W := Submodule.finrank_mono hle
      _ ≤ Fintype.card {e : Fin d // ty e = τ + 1} := finrank_range_le_card _
      _ = _ := Fintype.card_subtype _
      _ ≤ j := hj
  obtain ⟨x, hxi, hxd, hxt, hxty, hxl⟩ := GlobalTheory.T.root_extraction_lemma_sheaf C v p hp hv d h i ty τ G η
    (fun a => hηc a) (fun a => hηt a) 1 j le_rfl (Fin d → C) LinearMap.id hspan
  set γ' : Fin i → Fin d → PowerSeries C :=
    fun w => G.sumF fun u => rescaleCurve (x w u) (η u) with hγ'
  have hγ'c : ∀ w, IsCurve v (γ' w) := fun w =>
    (pt6' C v p hp hv d i G η (x w) (fun a => hηc a) (fun a => hxi w a)).1
  obtain ⟨r0, hr0⟩ := hu.2
  set U : Matrix (Fin i) (Fin i) C := Matrix.of fun a b => u a (r0 b) with hU
  have hUne : U.det ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hr0
    exact WithTop.top_ne_zero hr0
  have hinj : Function.Injective r0 := by
    intro b1 b2 heq
    by_contra hne
    exact hUne (Matrix.det_zero_of_column_eq hne (fun a => by simp [hU, heq]))
  have hty0 : ∀ b, ty (r0 b) = τ := by
    intro b
    by_contra hne
    exact hUne (Matrix.det_eq_zero_of_column_eq_zero b (fun a => by simp [hU, hut a _ hne]))
  choose ζ hζc hζt hζtan using fun e : Fin d =>
    hPT2 C v p hp hv d h hh ty G hmu (ty e) (Pi.single e 1)
      (fun c => by
        unfold IsIntV
        by_cases hc : c = e
        · subst hc; simp
        · simp [Pi.single_apply, hc])
      (fun c hc => by
        have : c ≠ e := fun h' => hc (h' ▸ rfl)
        simp [Pi.single_apply, this])
  let γ : Fin d → Fin d → PowerSeries C := fun e =>
    if hm : e ∈ Set.range r0 then γ' ((Equiv.ofInjective r0 hinj).symm ⟨e, hm⟩) else ζ e
  have hγr : ∀ a, γ (r0 a) = γ' a := by
    intro a
    simp only [γ, dif_pos (Set.mem_range_self a)]
    rw [Equiv.ofInjective_symm_apply]
  have hγn : ∀ e, e ∉ Set.range r0 → γ e = ζ e := fun e he => by simp only [γ, dif_neg he]
  have htan : ∀ a, tangent (γ (r0 a)) = ∑ a', x a a' • u a' := by
    intro a
    rw [hγr, hxt a]
    simp only [hηtan]
  refine ⟨γ, ⟨r0, hinj⟩, x, ⟨fun e => ?_, fun e => ?_, ?_⟩, hxi, hxd, htan, fun a ha => ?_⟩
  · by_cases he : e ∈ Set.range r0
    · obtain ⟨b, rfl⟩ := he
      rw [hγr]; exact hγ'c b
    · rw [hγn e he]; exact hζc e
  · by_cases he : e ∈ Set.range r0
    · obtain ⟨b, rfl⟩ := he
      rw [hγr, hty0]; exact hxty b
    · rw [hγn e he]; exact hζt e
  · rw [det_eq_det_minor_of_unit_rows r0 hinj]
    · have hsub : (Matrix.of fun a b => tangent (γ a) b).submatrix r0 r0 = x * U := by
        ext a b
        simp only [Matrix.submatrix_apply, Matrix.of_apply, htan, Matrix.mul_apply, hU,
          Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [hsub, Matrix.det_mul, AddValuation.map_mul, hxd, hr0, add_zero]
    · intro e he c
      simp only [Matrix.of_apply, hγn e he, hζtan, Pi.single_apply]
  · show G.lc p (γ (r0 a)) 1 = 0
    rw [hγr]
    simpa using hxl a ha

end GlobalTheory.FGDepth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTypicalCurveBasisAdaptedToSaturatedFrameStatement
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_typicalCurve_basis_adapted_to_saturated_frame : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (d h : ℕ), 0 < h → ∀ (ty : Fin d → ZMod h) (G : LogFGL v d), MuAction G p h ty → ∀ (τ : ZMod h) (j i : ℕ), (Finset.univ.filter fun a => ty a = τ + 1).card ≤ j → ∀ u : Fin i → Fin d → C, IsSatFrame v u → (∀ a e, ty e ≠ τ → u a e = 0) → ∃ (γ : Fin d → Fin d → PowerSeries C) (r : Fin i ↪ Fin d) (g : Matrix (Fin i) (Fin i) C), IsBasis G p ty γ ∧ (∀ a b, IsIntV v (g a b)) ∧ v g.det = 0 ∧ (∀ a, tangent (γ (r a)) = ∑ a', g a a' • u a') ∧ ∀ a : Fin i, j ≤ a.val → G.lc p (γ (r a)) 1 = 0 := by
  first | exact @GlobalTheory.FGDepth.exists_basis_adapted_frame | exact GlobalTheory.FGDepth.exists_basis_adapted_frame | (intros; apply GlobalTheory.FGDepth.exists_basis_adapted_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdGeExpOfLogSumTwoRadii
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdGeExpOfLogSumTwoRadii
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.ExpWeightTwoRadii

variable {C : Type} [Field C] {M : ℕ}

def WtBelow (v : AddValuation C (WithTop ℝ)) (ρ : Fin M → ℝ) (D : ℕ)
    (g : MvPowerSeries (Fin M) C) (r : ℝ) : Prop :=
  ∀ α : Fin M →₀ ℕ, Finsupp.degree α < D →
    (((r - ∑ m, ρ m * (α m : ℝ) : ℝ)) : WithTop ℝ) ≤ v (coeff α g)

theorem wt_add_index (ρ : Fin M → ℝ) (β γ : Fin M →₀ ℕ) :
    ∑ m, ρ m * ((β + γ) m : ℝ) = (∑ m, ρ m * (β m : ℝ)) + ∑ m, ρ m * (γ m : ℝ) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finsupp.add_apply, Nat.cast_add, mul_add]

theorem WtBelow.mul {v : AddValuation C (WithTop ℝ)} {ρ : Fin M → ℝ} {D : ℕ}
    {g h : MvPowerSeries (Fin M) C} {r s : ℝ} (hg0 : constantCoeff g = 0)
    (hh0 : constantCoeff h = 0) (hg : WtBelow v ρ D g r) (hh : WtBelow v ρ D h s) :
    WtBelow v ρ (D + 1) (g * h) (r + s) := by
  classical
  intro α hα
  rw [coeff_mul]
  refine v.map_le_sum fun q hq => ?_
  have hq' : q.1 + q.2 = α := by simpa using hq
  by_cases h1 : q.1 = 0
  · rw [h1, coeff_zero_eq_constantCoeff_apply, hg0, zero_mul, v.map_zero]; exact le_top
  by_cases h2 : q.2 = 0
  · rw [h2, coeff_zero_eq_constantCoeff_apply, hh0, mul_zero, v.map_zero]; exact le_top
  have hd : Finsupp.degree q.1 + Finsupp.degree q.2 = Finsupp.degree α := by
    rw [← hq', map_add (f := _)]
  have d1 : Finsupp.degree q.1 ≠ 0 := fun e => h1 ((Finsupp.degree_eq_zero_iff _).1 e)
  have d2 : Finsupp.degree q.2 ≠ 0 := fun e => h2 ((Finsupp.degree_eq_zero_iff _).1 e)
  rw [v.map_mul]
  refine le_trans (le_of_eq ?_) (add_le_add (hg q.1 (by omega)) (hh q.2 (by omega)))
  rw [← WithTop.coe_add, ← hq', wt_add_index]
  congr 1
  ring

theorem WtBelow.pow_succ {v : AddValuation C (WithTop ℝ)} {ρ : Fin M → ℝ} {D : ℕ}
    {g : MvPowerSeries (Fin M) C} {r : ℝ} (hg0 : constantCoeff g = 0)
    (hg : WtBelow v ρ D g r) (k : ℕ) :
    WtBelow v ρ D (g ^ (k + 1)) (((k + 1 : ℕ) : ℝ) * r) := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
    have h := WtBelow.mul (by simp [hg0]) hg0 ih hg
    intro α hα
    have h' := h α (by omega)
    rw [_root_.pow_succ g (k + 1)]
    refine le_trans (le_of_eq ?_) h'
    congr 1
    push_cast
    ring

theorem WtBelow.pow {v : AddValuation C (WithTop ℝ)} {ρ : Fin M → ℝ} {D : ℕ}
    {g : MvPowerSeries (Fin M) C} {r : ℝ} (hg0 : constantCoeff g = 0)
    (hg : WtBelow v ρ D g r) {N : ℕ} (hN : 2 ≤ N) :
    WtBelow v ρ (D + 1) (g ^ N) ((N : ℝ) * r) := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 + 1 := ⟨N - 2, by omega⟩
  have h := WtBelow.mul (by simp [hg0]) hg0 (hg.pow_succ hg0 k) hg
  rw [_root_.pow_succ g (k + 1)]
  convert h using 1
  push_cast
  ring

theorem ordGe_of_lgSum_radii (v : AddValuation C (WithTop ℝ)) (p : ℕ) (hp : p.Prime)
    {d : ℕ} (good : Fin d → Prop) [DecidablePred good] (c : Fin d → ℕ → Fin d → C)
    (h0 : ∀ a, c a 0 = Pi.single a 1)
    (hc : ∀ a (n : ℕ) b, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b))
    (hgood : ∀ a, good a → ∀ (n : ℕ) b, 1 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b))
    (ρ : Fin M → ℝ) (z t : Fin d → MvPowerSeries (Fin M) C) (r : Fin d → ℝ)
    (hr : ∀ b, r b = if good b then 2 / ((p : ℝ) * (p - 1)) else 2 / ((p : ℝ) - 1))
    (hz : ∀ b, OrdGe v ρ (z b) (r b)) (ht : ∀ b, constantCoeff (t b) = 0)
    (hlg : ∀ b, lgSum p c t b = z b) : ∀ b, OrdGe v ρ (t b) (r b) := by
  classical
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  set g' : ℝ := 2 / ((p : ℝ) - 1) with hg'
  have hg'1 : g' * ((p : ℝ) - 1) = 2 := by rw [hg']; field_simp
  have hg'0 : 0 < g' := by rw [hg']; apply div_pos <;> linarith
  have hgp : 2 / ((p : ℝ) * (p - 1)) * p = g' := by rw [hg']; field_simp
  have hγ0 : 0 ≤ 2 / ((p : ℝ) * (p - 1)) := by
    apply div_nonneg (by norm_num); apply mul_nonneg <;> linarith
  have hγg : 2 / ((p : ℝ) * (p - 1)) ≤ g' := by
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ p by linarith) hγ0
    linarith
  have hre : ∀ e, r e ≤ g' := by
    intro e; rw [hr e]; split_ifs <;> linarith

  have hnum : ∀ (a e : Fin d) (n : ℕ) (L : ℝ), (good a → -(n : ℝ) ≤ L) →
      (-((n : ℝ) + 1) ≤ L) → r e ≤ L + (p : ℝ) ^ (n + 1) * r a := by
    intro a e n L hLg hL
    have hb := one_add_mul_sub_le_pow (a := (p : ℝ)) (by linarith) n
    have hb' := mul_le_mul_of_nonneg_left hb hg'0.le
    have hb1 := one_add_mul_sub_le_pow (a := (p : ℝ)) (by linarith) (n + 1)
    have hb1' := mul_le_mul_of_nonneg_left hb1 hg'0.le
    have e1 : g' * (1 + (n : ℝ) * ((p : ℝ) - 1)) = g' + 2 * n := by
      linear_combination (n : ℝ) * hg'1
    have e2 : g' * (1 + ((n + 1 : ℕ) : ℝ) * ((p : ℝ) - 1)) = g' + 2 * ((n : ℝ) + 1) := by
      push_cast; linear_combination ((n : ℝ) + 1) * hg'1
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hre' := hre e
    rw [hr a]
    split_ifs with hga
    · have hL' := hLg hga
      have e3 : (p : ℝ) ^ (n + 1) * (2 / ((p : ℝ) * (p - 1))) = g' * (p : ℝ) ^ n := by
        rw [_root_.pow_succ, ← hgp]; ring
      rw [e3]; linarith
    · have e4 : (p : ℝ) ^ (n + 1) * g' = g' * (p : ℝ) ^ (n + 1) := by ring
      rw [e4]; linarith
  have step : ∀ D : ℕ, ∀ a, WtBelow v ρ D (t a) (r a) := by
    intro D
    induction D with
    | zero => intro a α hα; omega
    | succ D ih =>
      intro e α hα
      have h1 : coeff α (lgSum p c t e) = coeff α (z e) := by rw [hlg e]
      have h2 : coeff α (lgSum p c t e) =
          ∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a, c a n e * coeff α (t a ^ (p ^ n)) :=
        rfl
      rw [h2, Finset.sum_range_succ'] at h1
      have h3 : ∑ a, c a 0 e * coeff α (t a ^ (p ^ 0)) = coeff α (t e) := by
        simp [h0, Pi.single_apply]
      rw [h3] at h1
      rw [eq_sub_of_add_eq' h1]
      refine v.map_le_sub (hz e α) ?_
      refine v.map_le_sum fun n _ => v.map_le_sum fun a _ => ?_
      have hN : 2 ≤ p ^ (n + 1) := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
      have h4 := (ih a).pow (ht a) hN α hα
      rw [v.map_mul]
      by_cases hga : good a
      · have hc1 := hgood a hga (n + 1) e (by omega)
        refine le_trans ?_ (add_le_add hc1 h4)
        rw [← WithTop.coe_add, WithTop.coe_le_coe]
        have := hnum a e n (1 - ((n + 1 : ℕ) : ℝ)) (fun _ => by push_cast; linarith)
          (by push_cast; linarith)
        push_cast at this ⊢
        linarith
      · have hc1 := hc a (n + 1) e
        refine le_trans ?_ (add_le_add hc1 h4)
        rw [← WithTop.coe_add, WithTop.coe_le_coe]
        have := hnum a e n (-((n + 1 : ℕ) : ℝ)) (fun h => absurd h hga) (by push_cast; linarith)
        push_cast at this ⊢
        linarith
  intro b α
  exact step (Finsupp.degree α + 1) b α (by omega)

theorem ordGe_of_lgSum_twoRadii :
    ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (d M : ℕ) (good : Fin d → Prop) [DecidablePred good] (c : Fin d → ℕ → Fin d → C), (∀ a, c a 0 = Pi.single a 1) → (∀ a (n : ℕ) b, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b)) → (∀ a, good a → ∀ (n : ℕ) b, 1 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b)) → ∀ (ρ : Fin M → ℝ) (z t : Fin d → MvPowerSeries (Fin M) C), (∀ b, OrdGe v ρ (z b) (if good b then 2 / ((p : ℝ) * (p - 1)) else 2 / ((p : ℝ) - 1))) → (∀ b, constantCoeff (t b) = 0) → (∀ b, lgSum p c t b = z b) → ∀ b, OrdGe v ρ (t b) (if good b then 2 / ((p : ℝ) * (p - 1)) else 2 / ((p : ℝ) - 1)) := by
  intro C _ _ v p hp _ d M good _ c h0 hc hgood ρ z t hz ht hlg
  exact ordGe_of_lgSum_radii v p hp good c h0 hc hgood ρ z t
    (fun b => if good b then 2 / ((p : ℝ) * (p - 1)) else 2 / ((p : ℝ) - 1)) (fun _ => rfl)
    hz ht hlg

end GlobalTheory.ExpWeightTwoRadii
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdGeExpOfLogSumTwoRadiiStatement
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordGe_exp_of_logSum_two_radii : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (d M : ℕ) (good : Fin d → Prop) [DecidablePred good] (c : Fin d → ℕ → Fin d → C), (∀ a, c a 0 = Pi.single a 1) → (∀ a (n : ℕ) b, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b)) → (∀ a, good a → ∀ (n : ℕ) b, 1 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b)) → ∀ (ρ : Fin M → ℝ) (z t : Fin d → MvPowerSeries (Fin M) C), (∀ b, OrdGe v ρ (z b) (if good b then 2 / ((p : ℝ) * (p - 1)) else 2 / ((p : ℝ) - 1))) → (∀ b, constantCoeff (t b) = 0) → (∀ b, lgSum p c t b = z b) → ∀ b, OrdGe v ρ (t b) (if good b then 2 / ((p : ℝ) * (p - 1)) else 2 / ((p : ℝ) - 1)) := by
  first | exact @GlobalTheory.ExpWeightTwoRadii.ordGe_of_lgSum_twoRadii | exact GlobalTheory.ExpWeightTwoRadii.ordGe_of_lgSum_twoRadii | (intros; apply GlobalTheory.ExpWeightTwoRadii.ordGe_of_lgSum_twoRadii <;> assumption)
end
end

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth.InertBound

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

theorem exists_chart_coords {d M : ℕ} (G : LogFGL v d) (Φ Ψ : Fin d → MvPowerSeries (Fin d) C)
    (hΦ0 : ∀ a, constantCoeff (Φ a) = 0) (hΨ0 : ∀ a, constantCoeff (Ψ a) = 0)
    (hΨΦ : ∀ a, subst Ψ (Φ a) = X a) (L : Fin d → MvPowerSeries (Fin M) C)
    (hL : ∀ k, constantCoeff (L k) = 0) :
    ∃ t : Fin d → MvPowerSeries (Fin M) C, (∀ a, constantCoeff (t a) = 0) ∧
      ∀ e, subst t (subst Φ (G.lg e)) = L e := by
  have hex := isExp_expOf G
  have hL' : HasSubst L := hasSubst_of_constantCoeff_zero hL
  have hexs : HasSubst (expOf G) := hasSubst_of_constantCoeff_zero hex.1
  set E : Fin d → MvPowerSeries (Fin M) C := fun k => subst L (expOf G k) with hE
  have hE0 : ∀ k, constantCoeff (E k) = 0 := fun k =>
    constantCoeff_subst_eq_zero hL' hL (hex.1 k)
  have hEs : HasSubst E := hasSubst_of_constantCoeff_zero hE0
  refine ⟨fun a => subst E (Ψ a), fun a => constantCoeff_subst_eq_zero hEs hE0 (hΨ0 a), ?_⟩
  intro e
  have hΨs : HasSubst Ψ := hasSubst_of_constantCoeff_zero hΨ0
  have hΦs : HasSubst Φ := hasSubst_of_constantCoeff_zero hΦ0
  have h1 : ∀ k, subst (fun a => subst E (Ψ a)) (Φ k) = E k := by
    intro k
    rw [← subst_comp_subst_apply hΨs hEs, hΨΦ, subst_X hEs]
  rw [subst_comp_subst_apply hΦs (hasSubst_of_constantCoeff_zero
    (fun a => constantCoeff_subst_eq_zero hEs hE0 (hΨ0 a)))]
  simp only [h1]
  rw [hE, ← subst_comp_subst_apply hexs hL', hex.2 e, subst_X hL']

theorem lgSum_mulMatrix {d M : ℕ} (p : ℕ) (c : Fin d → ℕ → Fin d → C)
    (t : Fin d → MvPowerSeries (Fin M) C) (N : Matrix (Fin d) (Fin d) C) (b : Fin d) :
    lgSum p (fun a n b => ∑ e, c a n e * N e b) t b = ∑ e, N e b • lgSum p c t e := by
  ext α
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lgSum, map_sum, coeff_smul, smul_eq_mul]
  show (∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a, (∑ e, c a n e * N e b) * coeff α (t a ^ p ^ n))
    = ∑ e, N e b * (∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a, c a n e * coeff α (t a ^ p ^ n))
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => by ring

end

end GlobalTheory.FGDepth.InertBound

namespace GlobalTheory.FGDepth.InertBound

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

theorem coeff_subst_typical {M p : ℕ} (hp : 2 ≤ p) (f : PowerSeries C)
    (hf : ∀ m, (∀ n, m ≠ p ^ n) → PowerSeries.coeff m f = 0)
    (s : MvPowerSeries (Fin M) C) (hs : constantCoeff s = 0) (α : Fin M →₀ ℕ) :
    coeff α (PowerSeries.subst s f) = ∑ n ∈ Finset.range (Finsupp.degree α + 1),
      PowerSeries.coeff (p ^ n) f * coeff α (s ^ (p ^ n)) := by
  classical
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hs),
    finsum_eq_sum_of_support_subset
      (s := (Finset.range (Finsupp.degree α + 1)).image fun n => p ^ n),
    Finset.sum_image fun x _ y _ hxy => Nat.pow_right_injective hp hxy]
  · rfl
  · intro m hm
    rw [Function.mem_support, smul_eq_mul] at hm
    obtain ⟨n, rfl⟩ : ∃ n, m = p ^ n := by
      by_contra hne
      exact hm (by rw [hf m (fun n e => hne ⟨n, e⟩), zero_mul])
    have hle : p ^ n ≤ Finsupp.degree α := by
      by_contra hlt
      exact hm (by rw [GlobalTheory.ChainCoord.coeff_pow_eq_zero hs α (not_le.1 hlt), mul_zero])
    have hn : n < p ^ n := Nat.lt_pow_self hp
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨n, Finset.mem_range.2 (by omega), rfl⟩)

theorem subst_sum_lgCurve {d M : ℕ} (G : LogFGL v d) {p : ℕ} (hp : 2 ≤ p)
    (γ : Fin d → Fin d → PowerSeries C) (hγ : ∀ a, G.IsPTypical p (γ a))
    (t : Fin d → MvPowerSeries (Fin M) C) (ht : ∀ a, constantCoeff (t a) = 0) (b : Fin d) :
    subst t (∑ a, PowerSeries.subst (X a : MvPowerSeries (Fin d) C) (G.lgCurve (γ a) b)) =
      lgSum p (fun a n e => G.lc p (γ a) n e) t b := by
  have hts : HasSubst t := hasSubst_of_constantCoeff_zero ht
  have h1 : ∀ a (f : PowerSeries C),
      subst t (PowerSeries.subst (X a : MvPowerSeries (Fin d) C) f) = PowerSeries.subst (t a) f := by
    intro a f
    rw [PowerSeries.subst_def, PowerSeries.subst_def, subst_comp_subst_apply (ptOn_hs a) hts]
    simp only [subst_X hts]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← coe_substAlgHom hts, map_sum]
  simp only [coe_substAlgHom, h1]
  ext α
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  show _ = ∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a,
    G.lc p (γ a) n b * coeff α (t a ^ (p ^ n))
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => coeff_subst_typical hp _ (hγ a b) (t a) (ht a) α

theorem sum_radii_le {i d j : ℕ} (p : ℕ) (hp : 2 ≤ p) (r : Fin i → Fin d) (good : Fin d → Prop)
    [DecidablePred good] (hgood : ∀ a : Fin i, j ≤ a.val → good (r a)) :
    (∑ a, (if good (r a) then 2 / ((p : ℝ) * (p - 1)) else 2 / ((p : ℝ) - 1))) ≤
      i * (2 / ((p : ℝ) * (p - 1))) + j * (2 / ((p : ℝ) - 1)) := by
  have hp1 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hA : 0 ≤ 2 / ((p : ℝ) * (p - 1)) :=
    div_nonneg zero_le_two (mul_nonneg (by linarith) (by linarith))
  have hB : 0 ≤ 2 / ((p : ℝ) - 1) := div_nonneg zero_le_two (by linarith)
  generalize 2 / ((p : ℝ) * (p - 1)) = A at hA ⊢
  generalize 2 / ((p : ℝ) - 1) = B at hB ⊢
  have hcard : (Finset.univ.filter fun a : Fin i => a.val < j).card ≤ j := by
    calc _ = ((Finset.univ.filter fun a : Fin i => a.val < j).map Fin.valEmbedding).card :=
          (Finset.card_map _).symm
      _ ≤ (Finset.range j).card := Finset.card_le_card fun x hx => by
          obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hx
          exact Finset.mem_range.2 (Finset.mem_filter.1 ha).2
      _ = j := Finset.card_range j
  calc _ ≤ ∑ a : Fin i, (A + if a.val < j then B else 0) := Finset.sum_le_sum fun a _ => by
        by_cases hj : a.val < j
        · rw [if_pos hj]
          split_ifs <;> linarith
        · rw [if_neg hj, if_pos (hgood a (not_lt.1 hj)), add_zero]
    _ = i * A + (Finset.univ.filter fun a : Fin i => a.val < j).card * B := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter]
        simp
    _ ≤ _ := by
        have : ((Finset.univ.filter fun a : Fin i => a.val < j).card : ℝ) ≤ j := by
          exact_mod_cast hcard
        nlinarith [mul_le_mul_of_nonneg_right this hB]

end

end GlobalTheory.FGDepth.InertBound

namespace GlobalTheory.FGDepth.InertBound


open GlobalTheory.ChainCoord in
theorem content_le_detDepth_add :
    ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
      p.Prime → v (p : C) = 1 → ∀ (d h : ℕ), 0 < h → ∀ (ty : Fin d → ZMod h) (G : LogFGL v d),
        MuAction G p h ty → ∀ (τ : ZMod h) (j i c : ℕ),
          (Finset.univ.filter fun a => ty a = τ + 1).card ≤ j →
          ∀ u : Fin i → Fin d → C, IsSatFrame v u → (∀ a e, ty e ≠ τ → u a e = 0) →
            content v (detPow C i c) ≤ detDepth G u c +
              ((2 * i * c / ((p : ℝ) * (p - 1)) + 2 * j * c / ((p : ℝ) - 1) : ℝ) : EReal) := by
  intro C _ _ _ v p hp hv d h hh ty G μ τ j i c hcard u hu hsupp
  classical
  obtain ⟨γ, r, g, hB, -, hgdet, htan, hgood⟩ :=
    GlobalTheory.T.exists_typicalCurve_basis_adapted_to_saturated_frame C v p hp hv d h hh ty G μ τ j i hcard u hu hsupp
  obtain ⟨hγ, hγty, hdet⟩ := hB
  have e1 : detDepth G u c = detDepth G (fun a => tangent (γ (r a))) c := by
    rw [← GlobalTheory.T.formalGroupDeterminantPowDepth_basis_change_invariant C v i d c G u g hgdet]
    congr 1
    funext a
    exact (htan a).symm
  obtain ⟨Ψ, hΨi, hΨ0, hΨΦ, hΦΨ⟩ := ptBasisMap_inv G hγ hdet
  have hΦg := ptBasisMap_good G hγ
  set T : Matrix (Fin d) (Fin d) C := Matrix.of fun a b => tangent (γ a) b with hT
  obtain ⟨hTu, hTinv⟩ := pt_inv_int (M := T) (fun a b => (hγ a b).2 1) hdet
  set L : Fin d → MvPowerSeries (Fin i) C := fun e => ∑ a, tangent (γ (r a)) e • X a with hLdef
  have hL0 : ∀ e, constantCoeff (L e) = 0 := by intro e; simp [L]
  obtain ⟨t, ht0, htL⟩ :=
    exists_chart_coords G (ptBasisMap G γ) Ψ (fun a => (hΦg a).1) hΨ0 hΨΦ L hL0
  have hp2 : 2 ≤ p := hp.two_le
  have hlg : ∀ b, lgSum p (fun a n e => G.lc p (γ a) n e) t b = L b := by
    intro b
    rw [← htL b, ptBasisMap_lg G hγ b,
      subst_sum_lgCurve G hp2 γ (fun a => (hγty a).1) t ht0 b]
  set c' : Fin d → ℕ → Fin d → C := fun a n b => ∑ e, G.lc p (γ a) n e * T⁻¹ e b with hc'
  set z' : Fin d → MvPowerSeries (Fin i) C := fun b => ∑ e, T⁻¹ e b • L e with hz'
  have hlg' : ∀ b, lgSum p c' t b = z' b := by
    intro b
    rw [hc', lgSum_mulMatrix]
    simp only [hlg, hz']
  set good : Fin d → Prop := fun b => G.lc p (γ b) 1 = 0 with hgoodDef
  set rad : Fin d → ℝ := fun b => if good b then 2 / ((p : ℝ) * (p - 1)) else 2 / ((p : ℝ) - 1)
    with hrad
  set ρ : Fin i → ℝ := fun a => rad (r a) with hρ
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hrad0 : ∀ b, 0 ≤ rad b := by
    intro b
    simp only [hrad]
    split_ifs
    · exact div_nonneg zero_le_two (mul_nonneg (by linarith) (by linarith))
    · exact div_nonneg zero_le_two (by linarith)
  have hTT : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv T hTu
  have hc0 : ∀ a, c' a 0 = Pi.single a 1 := by
    intro a
    funext b
    have hte : ∀ e, G.lc p (γ a) 0 e = T a e := fun e => by
      simp only [hT, Matrix.of_apply]
      exact (congrFun (ReciprocityTheory.ChartRestriction.G.Sh.PTb.tangent_eq_lc_zero G p (fun e => (hγ a e).1)) e).symm
    simp only [hc', hte]
    rw [← Matrix.mul_apply, hTT, Matrix.one_apply, Pi.single_apply]
    by_cases hab : b = a
    · simp [hab]
    · simp [hab, Ne.symm hab]
  have hcn : ∀ a (n : ℕ) b, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c' a n b) := by
    intro a n b
    refine v.map_le_sum fun e _ => ?_
    rw [v.map_mul]
    exact le_add_of_le_of_nonneg ((pt5v' C v p hp hv d h ty G γ ⟨hγ, hγty, hdet⟩ a).1 n e)
      (hTinv e b)
  have hcg : ∀ a, good a → ∀ (n : ℕ) b, 1 ≤ n →
      ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c' a n b) := by
    intro a ha n b hn
    refine v.map_le_sum fun e _ => ?_
    rw [v.map_mul]
    exact le_add_of_le_of_nonneg
      ((pt5v' C v p hp hv d h ty G γ ⟨hγ, hγty, hdet⟩ a).2 ha n e hn) (hTinv e b)
  have hzeq : ∀ b, z' b = ∑ a, ((1 : Matrix (Fin d) (Fin d) C) (r a) b) • (X a : MvPowerSeries (Fin i) C) := by
    intro b
    rw [← hTT]
    simp only [hz', hLdef, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    simp only [hT, Matrix.of_apply]
    ring_nf
  have hz : ∀ b, OrdGe v ρ (z' b) (rad b) := by
    intro b
    rw [hzeq b]
    refine ord_sum _ fun a _ => ?_
    rw [Matrix.one_apply]
    split_ifs with hab
    · rw [one_smul]
      intro α
      rw [coeff_X]
      split_ifs with hα
      · subst hα
        have hs : ∑ m, ρ m * ((Finsupp.single a 1 : Fin i →₀ ℕ) m : ℝ) = ρ a := by
          simp [Finsupp.single_apply]
        rw [hs, v.map_one, ← hab]
        show ((rad (r a) - rad (r a) : ℝ) : WithTop ℝ) ≤ 0
        simp
      · simp
    · rw [zero_smul]
      exact ord_zero _
  have hD := GlobalTheory.T.ordGe_exp_of_logSum_two_radii C v p hp hv d i good c' hc0 hcn hcg ρ z' t hz ht0 hlg'
  have htord : ∀ b, OrdGe v ρ (t b) 0 := fun b => ord_mono (hD b) (hrad0 b)
  have e2 := GlobalTheory.T.differentialOperatorDepth_integral_coordinates C v i d c G (fun a => tangent (γ (r a))) (basisMap G γ) Ψ
    (fun a => by
      rw [basisMap_eq_ptBasisMap]
      exact ⟨(hΦg a).2, (hΦg a).1, hΨi a, hΨ0 a⟩)
    (fun a => by rw [basisMap_eq_ptBasisMap]; exact ⟨hΨΦ a, hΦΨ a⟩) t ht0
    (fun e => by rw [basisMap_eq_ptBasisMap]; exact htL e)
  rw [e1]
  have hS : (c : ℝ) * ∑ a, ρ a ≤ 2 * i * c / ((p : ℝ) * (p - 1)) + 2 * j * c / ((p : ℝ) - 1) := by
    have := sum_radii_le (d := d) p hp2 r good hgood
    have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    calc (c : ℝ) * ∑ a, ρ a ≤ c * (i * (2 / ((p : ℝ) * (p - 1))) + j * (2 / ((p : ℝ) - 1))) :=
          mul_le_mul_of_nonneg_left this hc
      _ = _ := by ring
  have hlowAll : ∀ B : ℝ, (∀ α ∈ (detPow C i c).support, ((B + (c : ℝ) * ∑ a, ρ a : ℝ) : WithTop ℝ) ≤
      v ((detPow C i c).coeff α * mfact α)) →
      (B : EReal) ≤ detDepth G (fun a => tangent (γ (r a))) c := by
    intro B hB
    rw [e2]
    refine le_iInf fun f => ?_
    have := GlobalTheory.T.le_formalGroupDeterminantPowDepth_of_radii C v i d c ρ t B ht0 htord hB f.1 f.2
    exact WithBot.coe_le_coe.2 this
  by_cases hfin : ∃ α ∈ (detPow C i c).support, v ((detPow C i c).coeff α * mfact α) ≠ ⊤
  · obtain ⟨α1, hα1, hne⟩ := hfin
    obtain ⟨α0, hα0, hmin⟩ := (detPow C i c).support.exists_min_image
      (fun α => v ((detPow C i c).coeff α * mfact α)) ⟨α1, hα1⟩
    have hne0 : v ((detPow C i c).coeff α0 * mfact α0) ≠ ⊤ := ne_top_of_le_ne_top hne (hmin α1 hα1)
    obtain ⟨κ, hκ⟩ := WithTop.ne_top_iff_exists.1 hne0
    have hlow := hlowAll (κ - (c : ℝ) * ∑ a, ρ a) (fun α hα => by
      rw [sub_add_cancel, hκ]; exact hmin α hα)
    have hcont : content v (detPow C i c) ≤ (κ : EReal) := by
      unfold content
      refine (iInf₂_le α0 hα0).trans (le_of_eq ?_)
      rw [← hκ]
      rfl
    refine hcont.trans ?_
    have e3 : (κ : EReal) = ((κ - (c : ℝ) * ∑ a, ρ a : ℝ) : EReal) + (((c : ℝ) * ∑ a, ρ a : ℝ) : EReal) := by
      rw [← EReal.coe_add]; congr 1; ring
    rw [e3]
    exact add_le_add hlow (EReal.coe_le_coe_iff.2 hS)
  · push_neg at hfin
    have htop : detDepth G (fun a => tangent (γ (r a))) c = ⊤ := by
      refine (EReal.eq_top_iff_forall_lt _).2 fun y => ?_
      refine lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (lt_add_one y)) (hlowAll (y + 1) fun α hα => ?_)
      rw [hfin α hα]
      exact le_top
    rw [htop, EReal.top_add_coe]
    exact le_top

end GlobalTheory.FGDepth.InertBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorDepthBoundsInertPrime
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

namespace GlobalTheory.RefSum

theorem facBetween_inert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c), ¬ (p : ℤ) ∣ discr E → InertInK H p → ∀ (f : Lt1 Dw) (k : ℕ), InPsi H f.1 → ∃ A B : ℝ, FacBetween Xo la f k A B ∧ B - A ≤ boundInert p Dw.q (rk f) k := by
  intro E _ _ _ H Dw l Xo c p _ la hdisc hinert f k hpsi
  letI := H.starRing
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.dividedPowerContent_detPow_depends_on_p_i_k p Fact.out (rk f) k
  have hFGT := GlobalTheory.T.formalGroup_rootsOfUnity_typed_lieRanks E H Dw l Xo c (fun _ => rfl) p hdisc
  have hch : ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), Nonempty (IntegralChartA3 Xo c T io y) :=
    fun T io y => by
      obtain ⟨C, -⟩ := (@GlobalTheory.IntChartExists.intChart_exists E _ _ _ H Dw l Xo c H.starRing).2.2 (fun _ => rfl) T io y
      exact ⟨C⟩
  have hbd : boundInert p Dw.q (rk f) k =
      2 * ((rk f : ℕ) : ℝ) * (k : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) + 2 * ((Dw.q : ℕ) : ℝ) * (k : ℝ) / ((p : ℝ) - 1) := rfl
  refine ⟨κ - boundInert p Dw.q (rk f) k, κ, fun T io e ho y => ⟨le_nuFac fun Ch X => ?_, fun _ => ?_⟩, by linarith⟩
  · obtain ⟨hfrob, htyp⟩ := hFGT T io X
    obtain ⟨h, hh, -, lab, hlab, d', G', ty, I, P, -, ⟨mu⟩, -, hcard, hfr⟩ := htyp y Ch f.1
    have hf0 : f.1 = lab 0 := hlab.1.symm
    obtain ⟨hsat, hsupp, hnu⟩ := hfr 0 f hf0
    have hiff := (hfrob (lab 0) (lab (0 + 1)) (hlab.2.1 0)).2 hinert
    have hnot : ¬ InPsi H (lab (0 + 1)) := fun h1 =>
      ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.not_inPsi_both H f.1 ⟨hpsi, by rw [hf0]; exact hiff.1 h1⟩
    have hc1 : (Finset.univ.filter fun a => ty a = (0 : ZMod h) + 1).card ≤ Dw.q := by
      have := hcard (0 + 1)
      rw [if_neg hnot, Fintype.card_subtype] at this
      exact this.le
    have hd2 := GlobalTheory.FGDepth.InertBound.content_le_detDepth_add X.C (vX_vp X) p Fact.out (vX_vp_p X) d' h hh ty G' mu
      0 Dw.q (rk f) k hc1 _ hsat hsupp
    rw [hκ X.C (vX_vp X) (vX_vp_p X), ← hbd] at hd2
    rw [hnu k, EReal.coe_sub]
    exact EReal.sub_le_of_le_add hd2
  · obtain ⟨Ch⟩ := hch T io y
    obtain ⟨X⟩ := nonempty_valExt_of_overLa la ho
    have h1 := GlobalTheory.T.formalGroupDeterminantPowDepth_bounds X.C (vX_vp X) p Fact.out (vX_vp_p X) (rk f) _ k (fgl Ch X) (frame Ch X f)
      (isSatFrame_frame Ch X f)
    refine (nuFac_le Ch X f k).trans ?_
    rw [← hκ X.C (vX_vp X) (vX_vp_p X)]
    exact h1.2.1

end GlobalTheory.RefSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorDepthBoundsInertPrimeStatement
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factorDepth_bounds_inert_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c), ¬ (p : ℤ) ∣ discr E → InertInK H p → ∀ (f : Lt1 Dw) (k : ℕ), InPsi H f.1 → ∃ A B : ℝ, FacBetween Xo la f k A B ∧ B - A ≤ boundInert p Dw.q (rk f) k := by
  first | exact @GlobalTheory.RefSum.facBetween_inert | exact GlobalTheory.RefSum.facBetween_inert | (intros; apply GlobalTheory.RefSum.facBetween_inert <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLargeInertPrime
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RefSum.InertOsc

open GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification (IsBig IsSmall IsSpread sumSmallSpread not_isBig_iff)

theorem card_filter_inPsi {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    [DecidablePred (fun τ : E →+* ℂ => InPsi H τ)] :
    (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card = Module.finrank ℚ E / 2 := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact GlobalTheory.LamF.card_psiSet H

theorem nuBetween_mono {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {p : ℕ} [Fact p.Prime] {la : PointsOfFlagModel.abelian₂ p c}
    {cx : Lt1 Dw → ℕ} {A B B' : ℝ} (h : NuBetween Xo la cx A B) (hB : B ≤ B') : NuBetween Xo la cx A B' :=
  fun T io e ho y => ⟨(h T io e ho y).1, fun ha => ((h T io e ho y).2 ha).trans (EReal.coe_le_coe_iff.2 hB)⟩

theorem big_arith {i q k m p : ℕ} (hi : i + 1 ≤ k + m) (hk : k ≤ m * p) (hq : q ≤ m) (hp : 2 ≤ p) :
    2 * i + 2 * q * p ≤ 5 * m * p := by
  have h1 : 2 * m ≤ m * p := by nlinarith
  have h2 : q * p ≤ m * p := Nat.mul_le_mul_right _ hq
  nlinarith

theorem big_bound {i q k m p c : ℕ} (hi : i + 1 ≤ k + m) (hk : k ≤ m * p) (hq : q ≤ m) (hp : 2 ≤ p) :
    boundInert p q i c ≤ 5 * (m : ℝ) * c / ((p : ℝ) - 1) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hn : ((2 * i + 2 * q * p : ℕ) : ℝ) ≤ ((5 * m * p : ℕ) : ℝ) := by exact_mod_cast big_arith hi hk hq hp
  push_cast at hn
  unfold boundInert
  rw [div_add_div _ _ (by positivity) hp1.ne', div_le_div_iff₀ (by positivity) hp1]
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have : (2 * (i : ℝ) * c * ((p : ℝ) - 1) + (p * ((p : ℝ) - 1)) * (2 * q * c)) * ((p : ℝ) - 1)
      = ((2 * i + 2 * q * p) * c) * ((p : ℝ) - 1) ^ 2 := by ring
  rw [this]
  have : 5 * (m : ℝ) * c * (p * ((p : ℝ) - 1) * ((p : ℝ) - 1)) = ((5 * m * p) * c) * ((p : ℝ) - 1) ^ 2 := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn hc) (sq_nonneg _)

theorem rk_add_one_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (f : Lt1 Dw) : rk f + 1 ≤ Dw.p + Dw.q + 1 := by
  have h := rk_le f
  unfold Datum.mult at h
  split_ifs at h <;> omega

theorem oscLe_inert_large : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime], ¬ (p : ℤ) ∣ discr E → InertInK H p → k ≤ m * p → OscLe Xo c p cx ((6 * F * m * Mb + Sm) / ((p : ℝ) - 1) + 1) := by
  classical
  intro E _ _ _ H Dw l Xo c F k m M Mb Sm cx hS hE p _ hdisc hin hkp
  obtain ⟨hS1, hSq, hmk, hm1, hk2, hF⟩ := hS
  obtain ⟨hMb, hbig, hsm, -⟩ := hE
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    linarith
  intro la
  set w : Lt1 Dw → ℝ := fun f => if GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f then 5 * (m : ℝ) * cx f / ((p : ℝ) - 1)
    else (rk f : ℝ) * cx f / ((p : ℝ) - 1) with hw
  have key : ∀ f, ∃ ab : ℝ × ℝ, FacBetween Xo la f (cx f) ab.1 ab.2 ∧ ab.2 - ab.1 ≤ w f := by
    intro f
    by_cases hb : GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f
    · obtain ⟨A, B, hAB, hBA⟩ := GlobalTheory.T.factorDepth_bounds_inert_prime E H Dw l Xo c p la hdisc hin f (cx f) hb.1
      refine ⟨(A, B), hAB, ?_⟩
      simp only [hw, if_pos hb]
      exact hBA.trans (big_bound (by have := rk_add_one_le f; omega) hkp hSq hp2)
    · refine ⟨(0, boundAll p (rk f) (cx f)), (GlobalTheory.T.factorDepth_between_zero_and_bound E H Dw l Xo c p la f (cx f)).1, ?_⟩
      simp only [hw, if_neg hb, boundAll, sub_zero, le_refl]
  choose g hg using key
  obtain ⟨n, hn⟩ := ((GlobalTheory.T.productDepth_sum_rounding_oscillation E H Dw l Xo c p la cx).1 (fun f => (g f).1) (fun f => (g f).2) fun f => (hg f).1).2
  refine ⟨n, nuBetween_mono hn ?_⟩
  have hsum : ∑ f, ((g f).2 - (g f).1) ≤ ∑ f, w f := Finset.sum_le_sum fun f _ => (hg f).2
  suffices hw2 : ∑ f, w f ≤ (6 * F * m * Mb + Sm) / ((p : ℝ) - 1) by linarith

  have hcard : (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card = F := by
    rw [card_filter_inPsi H, hF]; omega
  have hB : ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f), (cx f : ℝ) ≤ F * Mb := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun f : Lt1 Dw => GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f))
      (t := Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)) (g := fun f : Lt1 Dw => f.1)
      (fun f hf => by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢; exact hf.1)]
    calc _ ≤ ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ), Mb := by
          refine Finset.sum_le_sum fun τ _ => ?_
          have h := hbig τ
          push_cast at h
          rw [Finset.filter_filter]
          convert h using 2
      _ = F * Mb := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
  have hSS : ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => ¬ GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f), (rk f : ℝ) * cx f = (sumSmallSpread k cx : ℝ) := by
    unfold sumSmallSpread
    push_cast
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_isBig_iff]
  simp only [hw]
  rw [Finset.sum_ite, ← Finset.sum_div, ← Finset.sum_div, ← add_div, ← Finset.mul_sum, hSS]
  refine div_le_div_of_nonneg_right ?_ hp1.le
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have h5 : 5 * (m : ℝ) * ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f), (cx f : ℝ) ≤ 5 * m * (F * Mb) :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have h6 : 5 * (m : ℝ) * (F * Mb) ≤ 6 * F * m * Mb := by
    have : (0 : ℝ) ≤ F * m * Mb := by positivity
    nlinarith
  linarith

end GlobalTheory.RefSum.InertOsc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLargeInertPrimeStatement
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthOscillation_large_inertPrime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime], ¬ (p : ℤ) ∣ discr E → InertInK H p → k ≤ m * p → OscLe Xo c p cx ((6 * F * m * Mb + Sm) / ((p : ℝ) - 1) + 1) := by
  first | exact @GlobalTheory.RefSum.InertOsc.oscLe_inert_large | exact GlobalTheory.RefSum.InertOsc.oscLe_inert_large | (intros; apply GlobalTheory.RefSum.InertOsc.oscLe_inert_large <;> assumption)
end
