module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.NilpotentOfPowerTraces

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.C3C
namespace PositivityTheory.CW

theorem c3c : KStableHighestWeightVector := by
  intro n ε V _ _ E hgl hun S hfd hS hne
  obtain ⟨w, hw, hw0, μ, hμ⟩ := ReciprocityTheory.ChartRestriction.DS.exists_khw hgl (ReciprocityTheory.ChartRestriction.DS.isKUnitary_of_isInfUnitary hun) hfd hS hne
  exact ⟨w, μ, hw, hw0, hμ⟩

end PositivityTheory.CW
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.D5
namespace PositivityTheory.CW

theorem d5 : D5 := by
  intro n ε g hg
  have hu : ReciprocityTheory.ChartRestriction.DS.inUJ ε g := hg
  refine ⟨g * NormedSpace.exp (-ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_L g),
    ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_k_mem hu,
    ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_L g,
    (ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_L_inP hu).1,
    ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.eq_mul_exp_neg_polar_L_mul_exp_polar_L⟩

end PositivityTheory.CW
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CasimirNonnegative
open Matrix Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum

namespace PositivityTheory.CW.DerivativeRepresentation

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem dS_eq_dRep (X : Matrix (Fin n) (Fin n) ℂ) (w : H) : ReciprocityTheory.ChartRestriction.DS.dS σ X w = dRep σ X w := by
  unfold ReciprocityTheory.ChartRestriction.DS.dS dRep
  simp only [Complex.coe_smul]

theorem bridge (hσ : IsURepOn (UJset ε) σ) {E : Fin n → Fin n → Module.End ℂ (kfin ε σ)} (hE : PositivityTheory.CW.KDer ε σ E)
    (v : kfin ε σ) (hv : (v : H) ∈ ReciprocityTheory.ChartRestriction.DS.smD ε σ) (a b : Fin n) :
    ((E a b v : kfin ε σ) : H) = ((ReciprocityTheory.ChartRestriction.DS.smE ε σ a b ⟨v, hv⟩ : ReciprocityTheory.ChartRestriction.DS.smD ε σ) : H) := by
  rw [ReciprocityTheory.ChartRestriction.DS.smE_apply hσ]
  set Z : Matrix (Fin n) (Fin n) ℂ := Matrix.single a b 1
  have h1 := ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart1 ε Z
  have h2 := ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart2 ε Z
  have hd : E a b = ReciprocityTheory.ChartRestriction.DS.actM E (ReciprocityTheory.ChartRestriction.DS.S7.cpart1 ε Z) +
      Complex.I • ReciprocityTheory.ChartRestriction.DS.actM E (ReciprocityTheory.ChartRestriction.DS.S7.cpart2 ε Z) := by
    rw [← ReciprocityTheory.ChartRestriction.DS.SmDerA.actM_smul, ← ReciprocityTheory.ChartRestriction.DS.SmDerA.actM_add,
      ← ReciprocityTheory.ChartRestriction.DS.SmDerA.cpart_decomp, ReciprocityTheory.ChartRestriction.DS.SmDerA.actM_single]
  rw [hd, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul,
    hE _ h1 v, hE _ h2 v, dS_eq_dRep, dS_eq_dRep]

end PositivityTheory.CW.DerivativeRepresentation

namespace PositivityTheory.CW

open DerivativeRepresentation in
theorem c2a : CardSubmodulesOfIndexLePow := by
  intro n ε H _ _ _ σ hσ hirr E hE v
  have hsm := (CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H σ hσ hirr).1
  obtain ⟨S0, hS0f, hvS0, hS0K⟩ := v.2
  have hS0k : ∀ x ∈ S0, IsKFin ε σ x := fun x hx => ⟨S0, hS0f, hx, hS0K⟩
  let S : Submodule ℂ (kfin ε σ) := S0.comap (kfin ε σ).subtype
  let f : S →ₗ[ℂ] S0 :=
    { toFun := fun x => ⟨((x : kfin ε σ) : H), x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun x y h => by
    apply Subtype.ext; apply Subtype.ext
    have h' := congrArg Subtype.val h
    exact h'
  refine ⟨S, Module.Finite.of_injective f hf, hvS0, fun a b hab w hw => ?_⟩
  show ((E a b w : kfin ε σ) : H) ∈ S0
  rw [bridge hσ hE w (hsm _ w.2)]
  exact CompanionTheory.D.gk.HC.smE_mem_of_compact_A hσ hS0K hab _ hw

end PositivityTheory.CW
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.ExponentialKSet
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.LowTypeDetermined

namespace PositivityTheory.CW

namespace ExistsFunctional

theorem exists_functional {E : Type} [AddCommGroup E] [Module ℂ E] (q : Seminorm ℂ E) {x₀ : E} (hx : q x₀ ≠ 0) :
    ∃ φ : Module.Dual ℂ E, φ x₀ ≠ 0 ∧ ∀ x, ‖φ x‖ ≤ q x := by
  have h0 : x₀ ≠ 0 := by
    rintro rfl
    exact hx (map_zero q)
  let e := LinearEquiv.toSpanNonzeroSingleton ℂ E x₀ h0
  let f : Module.Dual ℂ (Submodule.span ℂ {x₀}) := (q x₀ : ℂ) • (e.symm : _ →ₗ[ℂ] ℂ)
  have hfe : ∀ t : ℂ, f (e t) = t * q x₀ := by
    intro t
    simp [f, mul_comm]
  obtain ⟨g, hg, hgp⟩ := Module.Dual.exists_extension_of_le_seminorm (Submodule.span ℂ {x₀}) f
    (p := q) (by
      intro y
      obtain ⟨t, rfl⟩ := e.surjective y
      rw [hfe, norm_mul, Complex.norm_real, Real.norm_of_nonneg (apply_nonneg q x₀)]
      rw [LinearEquiv.toSpanNonzeroSingleton_apply]
      simp [map_smul_eq_mul])
  refine ⟨g, ?_, hgp⟩
  have h1 := hg (e 1)
  rw [hfe, one_mul] at h1
  have : ((e 1 : Submodule.span ℂ {x₀}) : E) = x₀ := by
    rw [LinearEquiv.toSpanNonzeroSingleton_one]
  rw [this] at h1
  rw [h1]
  exact_mod_cast hx

end ExistsFunctional

theorem e1b : faceMap_comp_succAbove_castSucc := by
  unfold faceMap_comp_succAbove_castSucc AllTgt
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hrep T hT i w₀ hw₀ hp u hu hu0
  by_contra hall
  push_neg at hall
  obtain ⟨φ, hφ0, hφ⟩ := ExistsFunctional.exists_functional (p i) hp
  let ℓ : H →ₗ[ℂ] ℂ := φ ∘ₗ T
  have hlie : ((GlobalTheory.LowTypeDetermined.lie (Jm ε) : Set (Mx n))) = lieSet ε := rfl
  have hsm : ∀ w, Sm ε σ w →
      w ∈ GlobalTheory.LowTypeDetermined.smooth (Jm ε) (fun g => σ (1 * g * (1 : Mx n)⁻¹)) := by
    intro w hw
    change SmoothVec ((GlobalTheory.LowTypeDetermined.lie (Jm ε) : Set (Mx n)))
      (fun g => σ (1 * g * (1 : Mx n)⁻¹)) w
    simp only [inv_one, mul_one, one_mul]
    rw [hlie]
    exact hw
  have key := GlobalTheory.LowTypeDetermined.eq_zero_of_translates (G := Jm ε) (P := 1) hU hI isUnit_one
    (by simp) (ℓ := ℓ) ?_ (hsm u hu) hu0 ?_ (hsm w₀ hw₀)
  · exact hφ0 key
  · obtain ⟨S, C, hS, hb⟩ := hT.2 i
    refine ⟨S, C, ?_, ?_⟩
    · rw [hlie]
      exact hS
    · simp only [inv_one, mul_one, one_mul]
      rw [hlie]
      intro w hw
      exact (hφ (T w)).trans (hb w hw)
  · intro g hg
    show φ (T (σ g u)) = 0
    rw [hT.1 g hg u hu]
    exact norm_le_zero_iff.mp ((hφ _).trans (hall g hg).le)

end PositivityTheory.CW
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.MatrixActionLinear
open ReciprocityTheory.ChartRestriction.DS (casimirK IsGlRep IsInfUnitary IsKStableSub adjSign)
open scoped InnerProductSpace

namespace PositivityTheory.CW.CasimirNonnegativeSymmetric

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}

theorem casK_symm (hU : IsInfUnitary ε E) (x y : V) :
    ⟪casimirK ε E x, y⟫_ℂ = ⟪x, casimirK ε E y⟫_ℂ := by
  simp only [casimirK, LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  have hab : ε b = ε a := (Finset.mem_filter.1 hb).2
  rw [hU a b (E b a x) y, hU b a x (E b a y)]
  simp [adjSign, hab]

theorem re_inner_casK_nonneg (hU : IsInfUnitary ε E) (x : V) : 0 ≤ (⟪x, casimirK ε E x⟫_ℂ).re := by
  simp only [ReciprocityTheory.ChartRestriction.DS.casimirK, LinearMap.sum_apply, Module.End.mul_apply,
    inner_sum, Complex.re_sum]
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b hb => ?_
  have hb' : ε b = ε a := (Finset.mem_filter.1 hb).2
  have h := hU b a x (E b a x)
  simp only [ReciprocityTheory.ChartRestriction.DS.adjSign, hb', if_true, one_mul] at h
  rw [← h]
  simpa using (inner_self_nonneg (𝕜 := ℂ) (x := E b a x))

theorem eig_nonneg (hU : IsInfUnitary ε E) {μ : ℝ} {v : V} (hv : v ≠ 0) (h : Eig ε E μ v) : 0 ≤ μ := by
  have h2 := re_inner_casK_nonneg hU v
  rw [show casimirK ε E v = (μ : ℂ) • v from h, inner_smul_right, inner_self_eq_norm_sq_to_K] at h2
  have h3 : 0 ≤ μ * ‖v‖ ^ 2 := by simpa [← Complex.ofReal_pow] using h2
  have hn : 0 < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.2 hv) 2
  by_contra hμ
  push_neg at hμ
  nlinarith [mul_neg_of_neg_of_pos hμ hn]

end PositivityTheory.CW.CasimirNonnegativeSymmetric

namespace PositivityTheory.CW

open CasimirNonnegativeSymmetric in
theorem e3a : CasimirPowerSurjectiveSymmetric := by
  intro k ε V _ _ E _ hU hM m
  set a := 1 + casimirK ε E with ha_def
  have ha : ∀ x y : V, ⟪a x, y⟫_ℂ = ⟪x, a y⟫_ℂ := by
    intro x y
    simp only [ha_def, LinearMap.add_apply, Module.End.one_apply, inner_add_left, inner_add_right,
      casK_symm hU]
  have hsymm : ∀ j : ℕ, ∀ x y : V, ⟪(a ^ j) x, y⟫_ℂ = ⟪x, (a ^ j) y⟫_ℂ := by
    intro j
    induction j with
    | zero => intro x y; simp
    | succ j ih =>
      intro x y
      calc ⟪(a ^ (j + 1)) x, y⟫_ℂ = ⟪(a ^ j) (a x), y⟫_ℂ := by rw [pow_succ, Module.End.mul_apply]
        _ = ⟪a x, (a ^ j) y⟫_ℂ := ih _ _
        _ = ⟪x, a ((a ^ j) y)⟫_ℂ := ha _ _
        _ = ⟪x, (a ^ (j + 1)) y⟫_ℂ := by rw [pow_succ', Module.End.mul_apply]
  refine ⟨?_, hsymm m⟩
  have hrange : LinearMap.range (a ^ m) = ⊤ := by
    rw [eq_top_iff, ← hM.span, Submodule.span_le]
    rintro v ⟨μ, hv⟩
    show v ∈ LinearMap.range (a ^ m)
    by_cases h0 : v = 0
    · rw [h0]; exact Submodule.zero_mem _
    have hμ : 0 ≤ μ := eig_nonneg hU h0 hv
    have h1 : a v = (1 + (μ : ℂ)) • v := by
      simp [ha_def, add_smul, show casimirK ε E v = (μ : ℂ) • v from hv]
    have hav : ∀ j : ℕ, (a ^ j) v = ((1 + (μ : ℂ)) ^ j) • v := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ, Module.End.mul_apply, h1, map_smul, ih, smul_smul, ← pow_succ']
    have hne1 : (1 + (μ : ℂ)) ≠ 0 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_add]
      exact_mod_cast (by linarith : (0 : ℝ) < 1 + μ).ne'
    have hne : (1 + (μ : ℂ)) ^ m ≠ 0 := pow_ne_zero _ hne1
    refine LinearMap.mem_range.2 ⟨((1 + (μ : ℂ)) ^ m)⁻¹ • v, ?_⟩
    rw [map_smul, hav, smul_smul, inv_mul_cancel₀ hne, one_smul]
  exact LinearMap.range_eq_top.1 hrange

end PositivityTheory.CW
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CasimirNonnegativeSymmetric
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

namespace PositivityTheory.CW.SeminormApproximation

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)} {E : Type} [AddCommGroup E] [Module ℂ E]

theorem sup_bound {p : ℕ → Seminorm ℂ E} {T : H →ₗ[ℂ] E} (hT : SobBdOn ε σ (Sm ε σ) p T) (s : Finset ℕ) :
    ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧
      ∀ x, Sm ε σ x → s.sup p (T x) ≤ C * sobNorm σ S x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · refine ⟨[], 0, fun l hl => by simp at hl, le_refl _, fun x _ => ?_⟩
    simp [Seminorm.bot_eq_zero]
  · intro i s _ ih
    obtain ⟨S, C, hS, hC, h⟩ := ih
    obtain ⟨S', C', hS', h'⟩ := hT i
    refine ⟨S' ++ S, |C'| + C, words_append hS' hS, by positivity, fun x hx => ?_⟩
    rw [Finset.sup_insert, Seminorm.sup_apply, sobNorm_append]
    have e1 := h x hx
    have e2 := h' x hx
    have a := sobNorm_nonneg σ S x
    have b := sobNorm_nonneg σ S' x
    have c1 := mul_nonneg (abs_nonneg C') a
    have c2 := mul_nonneg hC b
    have c3 := mul_nonneg hC a
    have c4 := mul_nonneg (abs_nonneg C') b
    have c5 := mul_le_mul_of_nonneg_right (le_abs_self C') b
    refine max_le ?_ ?_
    · nlinarith
    · nlinarith

theorem q_bound {p : ℕ → Seminorm ℂ E} [TopologicalSpace E] (hp : WithSeminorms p) {T : H →ₗ[ℂ] E}
    (hT : SobBdOn ε σ (Sm ε σ) p T) (Q : Seminorm ℂ E) (hQ : Continuous Q) :
    ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧
      ∀ x, Sm ε σ x → Q (T x) ≤ C * sobNorm σ S x := by
  obtain ⟨s, C', -, hle⟩ := Seminorm.bound_of_continuous hp Q hQ
  obtain ⟨S, C, hS, hC, h⟩ := sup_bound hT s
  refine ⟨S, C' * C, hS, mul_nonneg (NNReal.coe_nonneg C') hC, fun x hx => ?_⟩
  have h1 : Q (T x) ≤ (C' • s.sup p) (T x) := hle (T x)
  rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul] at h1
  calc Q (T x) ≤ C' * s.sup p (T x) := h1
    _ ≤ C' * (C * sobNorm σ S x) := mul_le_mul_of_nonneg_left (h x hx) (NNReal.coe_nonneg C')
    _ = _ := by ring

theorem approx (hD : Dens ε σ) {p : ℕ → Seminorm ℂ E} [TopologicalSpace E] (hp : WithSeminorms p)
    {T : H →ₗ[ℂ] E} (hT : SobBdOn ε σ (Sm ε σ) p T) (Q : Seminorm ℂ E) (hQ : Continuous Q) (l : List (Mx n))
    (hl : ∀ X ∈ l, X ∈ lieSet ε) (y : H) (hy : Sm ε σ y) (δ : ℝ) (hδ : 0 < δ) :
    ∃ v, IsKFin ε σ v ∧ Q (T (y - v)) ≤ δ ∧ ‖y - v‖ ≤ δ ∧ ‖Dw σ l (y - v)‖ ≤ δ := by
  obtain ⟨S, C, hS, hC, h⟩ := q_bound hp hT Q hQ
  have hW : Words (lieSet ε) (S ++ [l, []]) := by
    intro m hm X hX
    rcases List.mem_append.1 hm with hm | hm
    · exact hS m hm X hX
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact hl X hX
      · simp at hX
  have hC1 : 0 < C + 1 := by linarith
  obtain ⟨v, hv, hlt⟩ := hD.2.2 y hy (S ++ [l, []]) hW (δ / (C + 1)) (div_pos hδ hC1)
  have hsm : Sm ε σ (y - v) := sm_iff.2 ((smooth (Jm ε) σ).sub_mem (sm_iff.1 hy) (sm_iff.1 (hD.1 v hv)))
  have e : sobNorm σ (S ++ [l, []]) (y - v) = sobNorm σ S (y - v) + (‖Dw σ l (y - v)‖ + ‖y - v‖) := by
    rw [sobNorm_append]
    congr 1
    simp [sobNorm]
  rw [e] at hlt
  have a := sobNorm_nonneg σ S (y - v)
  have n1 := norm_nonneg (Dw σ l (y - v))
  have n2 := norm_nonneg (y - v)
  have hρ : δ / (C + 1) ≤ δ := div_le_self hδ.le (by linarith)
  have hCρ : C * (δ / (C + 1)) ≤ δ := by
    have : (C + 1) * (δ / (C + 1)) = δ := by field_simp
    nlinarith [div_pos hδ hC1]
  refine ⟨v, hv, ?_, by linarith, by linarith⟩
  calc Q (T (y - v)) ≤ C * sobNorm σ S (y - v) := h _ hsm
    _ ≤ C * (δ / (C + 1)) := mul_le_mul_of_nonneg_left (by linarith) hC
    _ ≤ δ := hCρ

end PositivityTheory.CW.SeminormApproximation

namespace PositivityTheory.CW

open SeminormApproximation in
theorem e2d : SobolevBoundedPairing := by
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ hD T hT Q hQ l η C hl
  have hp := hπ.withSeminorms
  refine ⟨fun h y hy => ?_, fun h y hy => ?_⟩
  · refine le_of_forall_pos_le_add fun e he => ?_
    have hK : 0 < |C| + ‖η‖ + 1 := by positivity
    obtain ⟨v, hv, h1, h2, -⟩ := approx hD hp hT Q hQ l hl y hy (e / (|C| + ‖η‖ + 1)) (div_pos he hK)
    have hv' := h v hv
    have i1 : ‖⟪η, y⟫_ℂ‖ ≤ ‖⟪η, v⟫_ℂ‖ + ‖η‖ * ‖y - v‖ := by
      have : ⟪η, y⟫_ℂ = ⟪η, v⟫_ℂ + ⟪η, y - v⟫_ℂ := by rw [inner_sub_right]; ring
      rw [this]
      exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_inner_le_norm _ _))
    have i2 : |Q (T v) - Q (T y)| ≤ Q (T (y - v)) := by
      rw [show T (y - v) = T y - T v from map_sub T y v, abs_sub_comm]
      exact abs_sub_map_le_sub Q (T y) (T v)
    have i3 : C * (Q (T v) - Q (T y)) ≤ |C| * Q (T (y - v)) := by
      have := le_abs_self (C * (Q (T v) - Q (T y)))
      rw [abs_mul] at this
      exact this.trans (mul_le_mul_of_nonneg_left i2 (abs_nonneg C))
    have i4 : C * Q (T v) = C * Q (T y) + C * (Q (T v) - Q (T y)) := by ring
    have i5 : |C| * Q (T (y - v)) + ‖η‖ * ‖y - v‖ ≤ e := by
      calc |C| * Q (T (y - v)) + ‖η‖ * ‖y - v‖
          ≤ |C| * (e / (|C| + ‖η‖ + 1)) + ‖η‖ * (e / (|C| + ‖η‖ + 1)) :=
            add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg C)) (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
        _ = (|C| + ‖η‖) * (e / (|C| + ‖η‖ + 1)) := by ring
        _ ≤ (|C| + ‖η‖ + 1) * (e / (|C| + ‖η‖ + 1)) :=
            mul_le_mul_of_nonneg_right (by linarith) (div_pos he hK).le
        _ = e := by field_simp
    linarith
  · refine le_of_forall_pos_le_add fun e he => ?_
    obtain ⟨v, hv, h1, -, h3⟩ := approx hD hp hT Q hQ l hl y hy (e / 2) (by positivity)
    have hv' := h v hv
    have hsm : Sm ε σ (y - v) := sm_iff.2 ((smooth (Jm ε) σ).sub_mem (sm_iff.1 hy) (sm_iff.1 (hD.1 v hv)))
    have hsplit : Dw σ l y = Dw σ l (y - v) + Dw σ l v := by
      have := Dw_add hU hl hsm (hD.1 v hv)
      rwa [sub_add_cancel] at this
    have i1 : ‖Dw σ l y‖ ≤ ‖Dw σ l (y - v)‖ + ‖Dw σ l v‖ := by
      rw [hsplit]; exact norm_add_le _ _
    have i2 : Q (T v) ≤ Q (T y) + Q (T (y - v)) := by
      have := map_sub_le_add Q (T y) (T (y - v))
      have e2 : T y - T (y - v) = T v := by rw [map_sub T y v, sub_sub_cancel]
      rwa [e2] at this
    linarith

end PositivityTheory.CW

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EigenOrthogonalForm
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum MeasureTheory
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.CW

namespace BilinearFormCasimir

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

def tr (k : KG ε) (v : kfin ε σ) : kfin ε σ :=
  ⟨σ (toMK k⁻¹) v, isKFin_translate (mem_kfin.1 v.2) (toMK_mem_K _)⟩

theorem tr_add (k : KG ε) (v v' : kfin ε σ) : tr k (v + v') = tr k v + tr k v' :=
  Subtype.ext (map_add (σ (toMK k⁻¹)) (v : H) v')

theorem tr_smul (k : KG ε) (c : ℂ) (v : kfin ε σ) : tr k (c • v) = c • tr k v :=
  Subtype.ext (map_smul (σ (toMK k⁻¹)) c (v : H))

theorem continuous_tr (hU : IsURepOn (UJset ε) σ) (l : kfin ε σ →ₗ[ℂ] ℂ) (v : kfin ε σ) :
    Continuous fun k : KG ε => l (tr k v) := by
  obtain ⟨S, hSf, hvS, hSK⟩ := mem_kfin.1 v.2
  haveI := hSf
  have hSk : ∀ x ∈ S, x ∈ kfin ε σ := fun x hx => mem_kfin.2 ⟨S, hSf, hx, hSK⟩
  let ι : S →ₗ[ℂ] kfin ε σ :=
    { toFun := fun x => ⟨x, hSk x x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hc : Continuous (l ∘ₗ ι) := LinearMap.continuous_of_finiteDimensional _
  have hmem : ∀ k : KG ε, σ (toMK k⁻¹) v ∈ S := fun k => hSK _ (toMK_mem_K _) _ hvS
  have h1 : Continuous fun k : KG ε => σ (toMK k⁻¹) (v : H) :=
    (hU.2.2 v).comp_continuous ((continuous_toMK ε).comp continuous_inv) fun k => K_le_UJ (toMK_mem_K _)
  have h2 : Continuous fun k : KG ε => (⟨σ (toMK k⁻¹) v, hmem k⟩ : S) := h1.subtype_mk _
  exact (hc.comp h2).congr fun k => rfl

def fm (l : kfin ε σ →ₗ[ℂ] ℂ) (v y : kfin ε σ) : ℂ := ∫ k, conj (l (tr k v)) * l (tr k y) ∂(muK ε)

theorem integrable_fm (hU : IsURepOn (UJset ε) σ) (l : kfin ε σ →ₗ[ℂ] ℂ) (v y : kfin ε σ) :
    Integrable (fun k : KG ε => conj (l (tr k v)) * l (tr k y)) (muK ε) := by
  haveI : CompactSpace (KG ε) := instCompactKG n ε
  have hc : Continuous fun k : KG ε => conj (l (tr k v)) * l (tr k y) :=
    ((continuous_tr hU l v).star).mul (continuous_tr hU l y)
  exact hc.integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact

def bf (hU : IsURepOn (UJset ε) σ) (l : kfin ε σ →ₗ[ℂ] ℂ) : kfin ε σ →ₗ⋆[ℂ] kfin ε σ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fm l)
    (fun v v' y => by
      unfold fm
      rw [← integral_add (integrable_fm hU l v y) (integrable_fm hU l v' y)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [tr_add, map_add (f := _), add_mul])
    (fun c v y => by
      unfold fm
      rw [smul_eq_mul, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [tr_smul, map_smul, smul_eq_mul, map_mul]
      ring)
    (fun v y y' => by
      unfold fm
      rw [← integral_add (integrable_fm hU l v y) (integrable_fm hU l v y')]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [tr_add, map_add (f := _), mul_add])
    (fun c v y => by
      unfold fm
      rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [tr_smul, map_smul, smul_eq_mul]
      ring)

theorem bf_apply (hU : IsURepOn (UJset ε) σ) (l : kfin ε σ →ₗ[ℂ] ℂ) (v y : kfin ε σ) :
    bf hU l v y = fm l v y := rfl

end BilinearFormCasimir

open BilinearFormCasimir in
theorem e2b : E2b := by
  intro n ε H _ _ _ σ hU hI Q hQ v₀ hv₀
  have hv0 : v₀ ≠ 0 := fun h => hv₀ (by rw [h, map_zero])

  let f0 : (ℂ ∙ v₀) →ₗ[ℂ] ℂ := (LinearPMap.mkSpanSingleton v₀ ((Q v₀ : ℝ) : ℂ) hv0).toFun
  have hf0 : ∀ x : (ℂ ∙ v₀), ‖f0 x‖ ≤ Q x := by
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    have e : f0 ⟨c • v₀, hx⟩ = c • ((Q v₀ : ℝ) : ℂ) :=
      LinearPMap.mkSpanSingleton'_apply v₀ ((Q v₀ : ℝ) : ℂ) _ c hx
    rw [e, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (apply_nonneg Q v₀)]
    exact (map_smul_eq_mul Q c v₀).symm.le
  obtain ⟨l, hl, hlQ⟩ := Module.Dual.exists_extension_of_le_seminorm (ℂ ∙ v₀) f0 hf0
  have hlv : l v₀ = ((Q v₀ : ℝ) : ℂ) := by
    have h1 : v₀ ∈ (ℂ ∙ v₀) := Submodule.mem_span_singleton_self v₀
    have h1' : (1 : ℂ) • v₀ ∈ (ℂ ∙ v₀) := by rw [one_smul]; exact h1
    rw [hl ⟨v₀, h1⟩]
    have e : f0 ⟨(1 : ℂ) • v₀, h1'⟩ = (1 : ℂ) • ((Q v₀ : ℝ) : ℂ) :=
      LinearPMap.mkSpanSingleton'_apply v₀ ((Q v₀ : ℝ) : ℂ) _ 1 h1'
    have e' : (⟨v₀, h1⟩ : (ℂ ∙ v₀)) = ⟨(1 : ℂ) • v₀, h1'⟩ := Subtype.ext (one_smul ℂ v₀).symm
    rw [e', e, one_smul]
  have hQtr : ∀ (k : KG ε) (v : kfin ε σ), Q (tr k v) = Q v := fun k v => hQ _ (toMK_mem_K _) v _ rfl
  refine ⟨bf hU l, fun k hk v y v' y' hv' hy' => ?_, fun v y => ?_, ?_⟩
  ·
    obtain ⟨k0, rfl⟩ : ∃ k0 : KG ε, toMK k0 = k := by rw [← range_toMK ε] at hk; exact hk
    have htr : ∀ (k : KG ε) (w w' : kfin ε σ), (w' : H) = σ (toMK k0) w → tr k w' = tr (k0⁻¹ * k) w := by
      intro k w w' hw
      apply Subtype.ext
      show σ (toMK k⁻¹) (w' : H) = σ (toMK (k0⁻¹ * k)⁻¹) w
      rw [hw, ← sigma_mul hU (K_le_UJ (toMK_mem_K _)) (K_le_UJ (toMK_mem_K _))]
      congr 2
    rw [bf_apply, bf_apply, fm, fm]
    simp only [htr _ _ _ hv', htr _ _ _ hy']
    exact integral_mul_left_eq_self (fun k => conj (l (tr k v)) * l (tr k y)) k0⁻¹
  · rw [bf_apply, fm]
    have h := norm_integral_le_of_norm_le_const (μ := muK ε) (f := fun k => conj (l (tr k v)) * l (tr k y))
      (C := Q v * Q y) (Filter.Eventually.of_forall fun k => by
        rw [norm_mul, RCLike.norm_conj, ← hQtr k v, ← hQtr k y]
        exact mul_le_mul (hlQ _) (hlQ _) (norm_nonneg _) (apply_nonneg _ _))
    simpa [measure_univ] using h
  · rw [bf_apply, fm]
    haveI : CompactSpace (KG ε) := instCompactKG n ε
    have e : ∀ k : KG ε, conj (l (tr k v₀)) * l (tr k v₀) = ((‖l (tr k v₀)‖ ^ 2 : ℝ) : ℂ) := fun k => by
      rw [mul_comm, Complex.mul_conj']
      push_cast
      ring
    simp only [e]
    rw [integral_complex_ofReal]
    have hpos : 0 < ∫ k, ‖l (tr k v₀)‖ ^ 2 ∂(muK ε) := by
      refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
        ((continuous_tr hU l v₀).norm.pow 2) (isClosed_tsupport _).isCompact (fun k => by positivity) ?_
      have h1 : tr (1 : KG ε) v₀ = v₀ := Subtype.ext (by
        show σ (toMK (1 : KG ε)⁻¹) (v₀ : H) = v₀
        rw [inv_one]
        exact sigma_one hU _)
      rw [h1, hlv, Complex.norm_real, Real.norm_of_nonneg (apply_nonneg Q v₀)]
      exact pow_ne_zero 2 hv₀
    exact_mod_cast hpos.ne'

end PositivityTheory.CW

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.DerivativeContinuity
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open ReciprocityTheory.ChartRestriction.DS (actM casimirK)

namespace PositivityTheory.CW.WeightedRepresentationMul

variable {n : ℕ}

theorem actM_add {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (X Y : Mx n) :
    actM E (X + Y) = actM E X + actM E Y := by
  simp [actM, add_smul, Finset.sum_add_distrib]

theorem actM_smul {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (c : ℂ)
    (X : Mx n) : actM E (c • X) = c • actM E X := by
  simp [actM, smul_smul, Finset.smul_sum]

theorem actM_single {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (a b : Fin n) :
    actM E (Matrix.single a b (1 : ℂ)) = E a b := by
  unfold actM
  rw [Finset.sum_eq_single a (fun a' _ h => Finset.sum_eq_zero fun b' _ => by
    simp [Ne.symm h]) (by simp)]
  rw [Finset.sum_eq_single b (fun b' _ h => by simp [Ne.symm h]) (by simp)]
  simp

variable {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

def WRep (ε : Fin n → Bool) (σ : Mx n → (H →L[ℂ] H)) (u : Module.End ℂ (kfin ε σ)) : Prop :=
  ∃ L : List (ℂ × List (Mx n)), (∀ p ∈ L, ∀ X ∈ p.2, X ∈ lieSet ε) ∧
    ∀ v : kfin ε σ, ((u v : kfin ε σ) : H) = (L.map fun p => p.1 • Dw σ p.2 (v : H)).sum

theorem wrep_one : WRep ε σ 1 :=
  ⟨[(1, [])], by simp, fun v => by simp⟩

theorem wrep_zero : WRep ε σ 0 :=
  ⟨[], by simp, fun v => by simp⟩

theorem wrep_add {u w : Module.End ℂ (kfin ε σ)} (hu : WRep ε σ u) (hw : WRep ε σ w) : WRep ε σ (u + w) := by
  obtain ⟨L, hL, hLv⟩ := hu
  obtain ⟨L', hL', hLv'⟩ := hw
  refine ⟨L ++ L', fun p hp => (List.mem_append.1 hp).elim (hL p) (hL' p), fun v => ?_⟩
  rw [LinearMap.add_apply, Submodule.coe_add, hLv, hLv', List.map_append, List.sum_append]

theorem wrep_mul_E (hU : IsURepOn (UJset ε) σ) (hD : Dens ε σ) {E : Fin n → Fin n → Module.End ℂ (kfin ε σ)}
    (hE : KDer ε σ E) {u : Module.End ℂ (kfin ε σ)} (hu : WRep ε σ u) (a b : Fin n) : WRep ε σ (u * E a b) := by
  obtain ⟨L, hL, hLv⟩ := hu
  set Z : Mx n := Matrix.single a b 1
  obtain ⟨h1, h2, h3, -⟩ := Formalism.REAL.complex_parts_mem_lie_algebra_holds n ε Z
  set X1 := Formalism.REAL.cpart1 ε Z
  set X2 := Formalism.REAL.cpart2 ε Z
  have hX1 : X1 ∈ lieSet ε := h1
  have hX2 : X2 ∈ lieSet ε := h2
  have hEab : ∀ v : kfin ε σ, ((E a b v : kfin ε σ) : H) = dRep σ X1 v + Complex.I • dRep σ X2 v := by
    intro v
    have e : E a b = actM E X1 + Complex.I • actM E X2 := by
      rw [← actM_single E a b, ← actM_smul, ← actM_add]
      exact congrArg (actM E) h3
    rw [e, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, hE X1 hX1 v,
      hE X2 hX2 v]
  let f : ℂ × List (Mx n) → List (ℂ × List (Mx n)) := fun p => [(p.1, p.2 ++ [X1]), (p.1 * Complex.I, p.2 ++ [X2])]
  refine ⟨L.flatMap f, ?_, fun v => ?_⟩
  · intro q hq X hX
    obtain ⟨p, hp, hq⟩ := List.mem_flatMap.1 hq
    simp only [f, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · rcases List.mem_append.1 hX with h | h
      · exact hL p hp X h
      · simp only [List.mem_singleton] at h; rw [h]; exact hX1
    · rcases List.mem_append.1 hX with h | h
      · exact hL p hp X h
      · simp only [List.mem_singleton] at h; rw [h]; exact hX2
  · have hv := v.2
    have hs1 : Sm ε σ (dRep σ X1 v) := hD.1 _ (hD.2.1 _ hv X1 hX1)
    have hs2 : Sm ε σ (dRep σ X2 v) := hD.1 _ (hD.2.1 _ hv X2 hX2)
    have hs2' : Sm ε σ (Complex.I • dRep σ X2 v) := hD.1 _ ((kfin ε σ).smul_mem Complex.I (hD.2.1 _ hv X2 hX2))
    have key : ∀ p ∈ L, p.1 • Dw σ p.2 ((E a b v : kfin ε σ) : H) =
        ((f p).map fun q => q.1 • Dw σ q.2 (v : H)).sum := by
      intro p hp
      have hl := hL p hp
      rw [hEab, Dw_add hU hl hs1 hs2', Dw_smul hU hl _ hs2]
      simp only [f, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Dw_append]
      rw [smul_add, smul_smul]
      rfl
    rw [Module.End.mul_apply, hLv]
    clear hLv
    induction L with
    | nil => simp
    | cons p L ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
        key p List.mem_cons_self, ih (fun q hq => hL q (List.mem_cons_of_mem _ hq))
          (fun q hq => key q (List.mem_cons_of_mem _ hq))]

theorem wrep_sum {ι : Type} (s : Finset ι) (g : ι → Module.End ℂ (kfin ε σ)) (h : ∀ i ∈ s, WRep ε σ (g i)) :
    WRep ε σ (∑ i ∈ s, g i) :=
  Finset.sum_induction g (WRep ε σ) (fun _ _ => wrep_add) wrep_zero h

theorem wrep_mul_cas (hU : IsURepOn (UJset ε) σ) (hD : Dens ε σ) {E : Fin n → Fin n → Module.End ℂ (kfin ε σ)}
    (hE : KDer ε σ E) {u : Module.End ℂ (kfin ε σ)} (hu : WRep ε σ u) : WRep ε σ (u * casimirK ε E) := by
  unfold casimirK
  rw [Finset.mul_sum]
  refine wrep_sum _ _ fun a _ => ?_
  rw [Finset.mul_sum]
  refine wrep_sum _ _ fun b _ => ?_
  rw [← mul_assoc]
  exact wrep_mul_E hU hD hE (wrep_mul_E hU hD hE hu a b) b a

theorem norm_sum_le (S : List (List (Mx n))) (w : H) :
    ∀ L : List (ℂ × List (Mx n)), (∀ p ∈ L, p.2 ∈ S) →
      ‖(L.map fun p => p.1 • Dw σ p.2 w).sum‖ ≤ (L.map fun p => ‖p.1‖).sum * sobNorm σ S w
  | [], _ => by simp
  | p :: L, h => by
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, add_mul]
    refine (norm_add_le _ _).trans (add_le_add ?_ (norm_sum_le S w L fun q hq => h q (List.mem_cons_of_mem _ hq)))
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (norm_Dw_le_sobNorm σ (h p List.mem_cons_self) w) (norm_nonneg _)

end PositivityTheory.CW.WeightedRepresentationMul

namespace PositivityTheory.CW

open WeightedRepresentationMul

theorem c4 : C4 := by
  intro n ε H _ _ _ σ hU _ hD E hE m
  have hrep : WRep ε σ ((1 + casimirK ε E) ^ m) := by
    induction m with
    | zero => simpa using (wrep_one : WRep ε σ 1)
    | succ m ih =>
      rw [pow_succ, mul_add, mul_one]
      exact wrep_add ih (wrep_mul_cas hU hD hE ih)
  obtain ⟨L, hL, hLv⟩ := hrep
  refine ⟨L.map Prod.snd, (L.map fun p => ‖p.1‖).sum, ?_, List.sum_nonneg fun x hx => ?_, fun v => ?_⟩
  · intro l hl X hX
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hl
    exact hL p hp X hX
  · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
    exact norm_nonneg _
  · have e : ‖((1 + casimirK ε E) ^ m) v‖ = ‖((((1 + casimirK ε E) ^ m) v : kfin ε σ) : H)‖ := rfl
    rw [e, hLv]
    exact norm_sum_le _ _ L fun p hp => List.mem_map.2 ⟨p, hp, rfl⟩

end PositivityTheory.CW

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.C3B
open Matrix Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum

namespace PositivityTheory.CW

private theorem exp_smul_diagonal_I_single_eq_diagonal_exp {n : ℕ} (a : Fin n) (t : ℝ) :
    NormedSpace.exp (t • (Matrix.diagonal fun j : Fin n => if j = a then Complex.I else 0)) =
      Matrix.diagonal fun j => if j = a then Complex.exp (t * Complex.I) else 1 := by
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal, Pi.exp_def]
  congr 1
  funext j
  by_cases h : j = a
  · simp [h, ← Complex.exp_eq_exp_ℂ, Complex.real_smul]
  · simp [h]

theorem c3b : HighestWeightIntegral := by
  intro n ε H _ _ _ σ hU _ E hE v a x hv hx
  set Y : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun j => if j = a then Complex.I else 0 with hY
  have hYG : Y ∈ lieSet ε := by
    show Yᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * Y = 0
    rw [hY, Formalism.REAL.Jm, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, ← Matrix.diagonal_zero]
    congr 1
    funext j
    by_cases h : j = a
    · subst h
      simp only [ite_true, Pi.star_apply]
      split_ifs <;> simp
    · simp [h]
  have hact : ReciprocityTheory.ChartRestriction.DS.actM E Y = Complex.I • E a a := by
    simp [ReciprocityTheory.ChartRestriction.DS.actM, hY, Matrix.diagonal_apply, ite_smul]
  have hv' : (v : H) ≠ 0 := by simpa using hv
  have hD : dRep σ Y (v : H) = (Complex.I * x) • (v : H) := by
    rw [← hE Y hYG v, hact]
    simp only [hx, LinearMap.smul_apply, Submodule.coe_smul]
    rw [mul_smul]
  set u : ℝ → Matrix (Fin n) (Fin n) ℂ :=
    fun t => Matrix.diagonal fun j => if j = a then Complex.exp (t * Complex.I) else 1 with hu
  have hexp : ∀ t : ℝ, NormedSpace.exp (t • Y) = u t := fun t => exp_smul_diagonal_I_single_eq_diagonal_exp a t
  have huU : ∀ t, u t ∈ UJset ε := by
    intro t
    show (u t)ᴴ * Formalism.REAL.Jm ε * u t = Formalism.REAL.Jm ε
    rw [hu, Formalism.REAL.Jm, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    by_cases h : j = a
    · subst h
      simp only [ite_true, Pi.star_apply]
      rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
        mul_comm _ (if ε j = true then (1 : ℂ) else -1), mul_assoc, ← Complex.exp_add]
      simp
    · simp [h]
  have hmul : ∀ s t, u (s + t) = u s * u t := by
    intro s t
    simp only [hu, Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    by_cases h : j = a
    · simp [h, add_mul, Complex.exp_add]
    · simp [h]
  have hu0 : u 0 = 1 := by simp [hu]
  have hu2 : u (2 * Real.pi) = 1 := by
    simp only [hu]
    rw [← Matrix.diagonal_one]
    congr 1
    funext j
    by_cases h : j = a
    · simp [h, Complex.exp_two_pi_mul_I]
    · simp [h]
  set F : ℝ → H := fun t => σ (u t) (v : H) with hFdef
  have hF : ∀ s t, F (s + t) = σ (u s) (F t) := by
    intro s t
    simp only [hFdef, hmul, hU.1.2 _ (huU s) _ (huU t), ContinuousLinearMap.comp_apply]
  have hx0 : x ≠ 0 → HasDerivAt F ((Complex.I * x) • (v : H)) 0 := by
    intro hx0
    have h1 : deriv F 0 = (Complex.I * x) • (v : H) := by
      have : F = fun t : ℝ => σ (NormedSpace.exp (t • Y)) (v : H) := by
        funext t
        simp only [hFdef, hexp]
      rw [this]
      exact hD
    have hne : deriv F 0 ≠ 0 := by
      rw [h1]
      exact smul_ne_zero (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.2 hx0)) hv'
    have hd : DifferentiableAt ℝ F 0 := by
      by_contra hnd
      exact hne (deriv_zero_of_not_differentiableAt hnd)
    rw [← h1]
    exact hd.hasDerivAt
  by_cases hx00 : x = 0
  · exact ⟨0, by simp [hx00]⟩
  have hder0 := hx0 hx00
  set c : ℂ := Complex.I * x with hc
  have hderF : ∀ s, HasDerivAt F (c • F s) s := by
    intro s
    have h2 : HasDerivAt (fun r => F (r - s)) (c • (v : H)) s := by
      have := HasDerivAt.comp_sub_const (f := F) (f' := c • (v : H)) s s (by simpa using hder0)
      simpa using this
    have h3 := ((σ (u s)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h2
    have heq : (fun r => σ (u s) (F (r - s))) = F := by
      funext r
      have := hF s (r - s)
      simp only [add_sub_cancel] at this
      exact this.symm
    have h4 : σ (u s) (c • (v : H)) = c • F s := by
      rw [map_smul]
    have h5 : HasDerivAt (fun r => σ (u s) (F (r - s))) (c • F s) s := by
      convert h3 using 1
      · rfl
      · exact h4.symm
    rwa [heq] at h5
  set G : ℝ → H := fun t => Complex.exp (-c * t) • F t with hG
  have hGd : ∀ t, HasDerivAt G 0 t := by
    intro t
    have h1 : HasDerivAt (fun y : ℝ => Complex.exp (-c * y)) (Complex.exp (-c * t) * (-c)) t := by
      have := (((hasDerivAt_id (t : ℂ)).const_mul (-c)).cexp).comp_ofReal
      simpa using this
    have := h1.smul (hderF t)
    convert this using 1
    symm
    rw [smul_smul, ← add_smul, show Complex.exp (-c * t) * c + Complex.exp (-c * t) * -c = 0 by ring,
      zero_smul]
  have hGc := is_const_of_deriv_eq_zero (fun t => (hGd t).differentiableAt)
    (fun t => (hGd t).deriv) (2 * Real.pi) 0
  have hG0 : G 0 = (v : H) := by
    simp only [hG, hFdef, hu0, hU.1.1, one_apply_eq_self, Complex.ofReal_zero, mul_zero,
      Complex.exp_zero, one_smul]
  have hG2 : G (2 * Real.pi) = Complex.exp (-c * ((2 * Real.pi : ℝ) : ℂ)) • (v : H) := by
    simp only [hG, hFdef, hu2, hU.1.1, one_apply_eq_self]
  rw [hG2, hG0] at hGc
  have hexp1 : Complex.exp (-c * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
    have : (Complex.exp (-c * ((2 * Real.pi : ℝ) : ℂ)) - 1) • (v : H) = 0 := by
      rw [sub_smul, hGc, one_smul, sub_self]
    rcases smul_eq_zero.1 this with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hv'
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 hexp1
  refine ⟨-m, ?_⟩
  have h2 : ((x + m : ℝ) : ℂ) * (2 * Real.pi * Complex.I) = 0 := by
    rw [hc] at hm
    push_cast at hm ⊢
    linear_combination (-1 : ℂ) * hm
  rcases mul_eq_zero.1 h2 with h | h
  · have : x + m = 0 := by exact_mod_cast h
    push_cast
    linarith
  · exact absurd h Complex.two_pi_I_ne_zero

end PositivityTheory.CW
end
