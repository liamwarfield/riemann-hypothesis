module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.ExistsHighestCoordinateFunctional

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.ExistsIntegralWeightProjections
section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.GlOperatorMemIntegralEnveloping
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem gl_operator_mem_integral_enveloping (E : GLOps n (KK O) V) (a b : Fin n) : E a b ∈ UZmon E := by
  rw [UZmon.eq_1]
  apply Submonoid.subset_closure
  simp only [UZgens.eq_1, Set.mem_setOf_eq]
  by_cases hab : a = b
  · subst hab
    right
    exact ⟨a, 1, by simp [binomE.eq_1]⟩
  · left
    exact ⟨a, b, 1, hab, by simp [divPowE.eq_1]⟩

theorem enveloping_le_integral_enveloping (E : GLOps n (KK O) V) : Umon E ≤ UZmon E := by
  rw [Umon.eq_1, Submonoid.closure_le]
  rintro _ ⟨⟨a, b⟩, rfl⟩
  exact gl_operator_mem_integral_enveloping E a b

theorem mem_nabla_iff_coordinate_integral {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} {xi : V →ₗ[KK O] KK O} (h1 : xi v = 1)
    (h2 : ∀ w ∈ otherWts E lam, xi w = 0) (h3 : ∀ x, x - xi x • v ∈ otherWts E lam) (x : V) :
    x ∈ Nabla (O := O) E lam v ↔ ∀ u ∈ UZmon E, ∃ c : O, xi (u x) = algebraMap O (KK O) c := by
  rw [Nabla.eq_1, Set.mem_setOf_eq]
  constructor
  · intro H u hu
    obtain ⟨c, hc⟩ := H u hu
    refine ⟨c, ?_⟩
    have h := h2 _ hc
    rw [map_sub, map_smul, h1, smul_eq_mul, mul_one, sub_eq_zero] at h
    exact h
  · intro H u hu
    obtain ⟨c, hc⟩ := H u hu
    refine ⟨c, ?_⟩
    have h := h3 (u x)
    rw [hc] at h
    exact h

theorem enveloping_coordinate_separates [NeZero n] [CharZero (KK O)] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    (hI : IsIrrHW E lam v)
    (hCR : ∀ W : Submodule (KK O) V, (∀ a b, ∀ x ∈ W, E a b x ∈ W) →
      ∃ W' : Submodule (KK O) V, IsCompl W W' ∧ ∀ a b, ∀ x ∈ W', E a b x ∈ W')
    {xi : V →ₗ[KK O] KK O} (h1 : xi v = 1) {x : V} (hx : ∀ u ∈ UZmon E, xi (u x) = 0) : x = 0 := by
  classical

  let W : Submodule (KK O) V := ⨅ u : UZmon E, LinearMap.ker (xi ∘ₗ (u : Module.End (KK O) V))
  have hmemW : ∀ y, y ∈ W ↔ ∀ u ∈ UZmon E, xi (u y) = 0 := by
    intro y
    rw [Submodule.mem_iInf]
    constructor
    · intro h u hu
      have h' := h ⟨u, hu⟩
      rwa [LinearMap.mem_ker, LinearMap.comp_apply] at h'
    · intro h u
      rw [LinearMap.mem_ker, LinearMap.comp_apply]
      exact h u.1 u.2
  have hxW : x ∈ W := (hmemW x).2 hx
  have hWst : ∀ a b, ∀ y ∈ W, E a b y ∈ W := by
    intro a b y hy
    rw [hmemW] at hy ⊢
    intro u hu
    have h' := hy (u * E a b) (Submonoid.mul_mem _ hu (gl_operator_mem_integral_enveloping E a b))
    rwa [Module.End.mul_apply] at h'
  have hvW : v ∉ W := by
    intro h
    have h' := (hmemW v).1 h 1 (Submonoid.one_mem _)
    rw [Module.End.one_apply, h1] at h'
    exact one_ne_zero h'
  obtain ⟨W', hC, hW'st⟩ := hCR W hWst
  have hv2 : v ∈ W ⊔ W' := by
    rw [hC.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨w, hw, w', hw', hvs⟩ := Submodule.mem_sup.mp hv2
  have hv := hI.2.2.1
  have hvw : ∀ a, E a a v = (lam a : KK O) • v := by
    intro a
    have h1' := (Submodule.mem_iInf _).mp hv.2.1 a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h1'
    simpa using h1'

  have hww : w ∈ weightSp E lam := by
    unfold weightSp
    refine (Submodule.mem_iInf _).mpr fun a => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    have hd : E a a w - (lam a : KK O) • w ∈ W := sub_mem (hWst a a w hw) (Submodule.smul_mem W _ hw)
    have hd' : E a a w' - (lam a : KK O) • w' ∈ W' :=
      sub_mem (hW'st a a w' hw') (Submodule.smul_mem W' _ hw')
    have hsum : (E a a w - (lam a : KK O) • w) + (E a a w' - (lam a : KK O) • w') = 0 := by
      have h2 := hvw a
      rw [← hvs, map_add (f := _), smul_add] at h2
      rw [sub_add_sub_comm, h2, sub_self]
    have hneg : E a a w - (lam a : KK O) • w ∈ W' := by
      rw [eq_neg_of_add_eq_zero_left hsum]
      exact W'.neg_mem hd'
    exact (Submodule.disjoint_def.mp hC.disjoint) _ hd hneg

  have hmem := top_le_line_sup_higher_weights hI (Submodule.mem_top : w ∈ (⊤ : Submodule (KK O) V))
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hzw : z ∈ weightSp E lam := by
    have e : z = w - c • v := by
      rw [← hyz]
      abel
    rw [e]
    exact sub_mem hww (Submodule.smul_mem _ c hv.2.1)
  have hz0 : z = 0 :=
    weight_support_sum_eq_zero E (fun nu => weightHeightAscending lam < weightHeightAscending nu) hzw hz (lt_irrefl _)
  have hwc : w = c • v := by
    rw [← hyz, hz0, add_zero]
  have hc0 : c = 0 := by
    by_contra hc
    apply hvW
    have e : v = c⁻¹ • w := by
      rw [hwc, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [e]
    exact Submodule.smul_mem W _ hw
  have hvW' : v ∈ W' := by
    rw [hwc, hc0, zero_smul, zero_add] at hvs
    rw [← hvs]
    exact hw'
  have htop := irreducible_stable_contains_eq_top hI hW'st hvW'
  have hxW' : x ∈ W' := by
    rw [htop]
    exact Submodule.mem_top
  exact (Submodule.disjoint_def.mp hC.disjoint) x hxW hxW'

theorem lattice_fg_of_integral_functionals {W : Type*} [AddCommGroup W] [Module (KK O) W] [Module O W] [IsScalarTower O (KK O) W]
    [FiniteDimensional (KK O) W] (N : Submodule O W) (Xi : Set (W →ₗ[KK O] KK O))
    (hsep : ∀ w, (∀ ξ ∈ Xi, ξ w = 0) → w = 0)
    (hint : ∀ ξ ∈ Xi, ∀ w ∈ N, ∃ c : O, ξ w = algebraMap O (KK O) c) : N.FG := by
  classical
  obtain ⟨b, hbXi, hbspan, hbli⟩ := exists_linearIndependent (KK O) Xi
  have hbfin : b.Finite := hbli.setFinite
  haveI : Fintype b := hbfin.fintype
  have hbsep : ∀ w : W, (∀ ξ ∈ b, ξ w = 0) → w = 0 := by
    intro w hw
    apply hsep
    intro ξ hξ
    have hle' : Submodule.span (KK O) b ≤ LinearMap.ker (Module.Dual.eval (KK O) W w) := by
      rw [Submodule.span_le]
      intro η hη
      simp only [SetLike.mem_coe, LinearMap.mem_ker, Module.Dual.eval_apply]
      exact hw η hη
    have hmem : ξ ∈ Submodule.span (KK O) b := by
      rw [hbspan]
      exact Submodule.subset_span hξ
    have h := hle' hmem
    simpa using h
  let Φ : W →ₗ[O] (b → KK O) := LinearMap.pi fun ξ => (ξ.1).restrictScalars O
  have hΦ : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 ?_
    intro w hw
    apply hbsep
    intro ξ hξ
    have h := congrFun hw ⟨ξ, hξ⟩
    simpa [Φ] using h
  let g : (b → O) →ₗ[O] (b → KK O) :=
    LinearMap.pi fun i => (Algebra.linearMap O (KK O)).comp (LinearMap.proj i)
  have hle : N.map Φ ≤ LinearMap.range g := by
    rintro _ ⟨w, hw, rfl⟩
    choose c hc using fun ξ : b => hint ξ.1 (hbXi ξ.2) w hw
    rw [LinearMap.mem_range]
    refine ⟨c, ?_⟩
    funext ξ
    simp [g, Φ, hc]
  apply Submodule.fg_of_fg_map_injective Φ hΦ
  have hQ : ((N.map Φ).comap g).FG := IsNoetherian.noetherian _
  have h := hQ.map g
  rwa [Submodule.map_comap_eq, inf_eq_right.mpr hle] at h

end hw

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem findim_exists_finite_weights [FiniteDimensional (KK O) V] (E : GLOps n (KK O) V)
    (hE : (⨆ mu : Fin n → ℤ, weightSp E mu) = ⊤) :
    ∃ F : Finset (Fin n → ℤ), (⊤ : Submodule (KK O) V) ≤ ⨆ nu ∈ F, weightSp E nu := by
  have hc := (Submodule.fg_iff_compact (⊤ : Submodule (KK O) V)).1 Module.Finite.fg_top
  first
  | exact IsCompactElement.exists_finset_of_le_iSup hc _ hE.ge
  | exact IsCompactElement.exists_finset_of_le_iSup _ hc _ hE.ge
  | exact CompleteLattice.IsCompactElement.exists_finset_of_le_iSup _ hc _ hE.ge
  | exact CompleteLattice.IsCompactElement.exists_finset_of_le_iSup hc _ hE.ge

theorem linear_map_ext_on_weights {E : GLOps n (KK O) V} {F : Finset (Fin n → ℤ)}
    (hF : (⊤ : Submodule (KK O) V) ≤ ⨆ nu ∈ F, weightSp E nu) {W : Type*} [AddCommGroup W] [Module (KK O) W]
    {A B : V →ₗ[KK O] W} (h : ∀ nu ∈ F, ∀ x ∈ weightSp E nu, A x = B x) : A = B := by
  have hle : (⨆ nu ∈ F, weightSp E nu) ≤ LinearMap.ker (A - B) := by
    refine iSup₂_le fun nu hnu x hx => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact h nu hnu x hx
  ext x
  have hx : x ∈ LinearMap.ker (A - B) := hle (hF (Submodule.mem_top : x ∈ (⊤ : Submodule (KK O) V)))
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hx
  exact hx

theorem exists_integral_weight_projection [CharZero (KK O)] (E : GLOps n (KK O) V) (mu : Fin n → ℤ) (F : Finset (Fin n → ℤ)) :
    ∃ (P : Module.End (KK O) V) (g : (Fin n → ℤ) → ℤ), g mu = 1 ∧ (∀ nu ∈ F, nu ≠ mu → g nu = 0) ∧
      (∀ nu, ∀ x ∈ weightSp E nu, P x = ((g nu : ℤ) : KK O) • x) ∧
      ∀ M : Submodule O V, UZStable (O := O) E M → ∀ x ∈ M, P x ∈ M := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, fun _ => 1, rfl, by simp, by simp, fun M _ x hx => by simpa using hx⟩
  | insert nu0 F _ ih =>
    obtain ⟨P, g, g1, g0, hP, hPM⟩ := ih
    by_cases h : nu0 = mu
    · refine ⟨P, g, g1, ?_, hP, hPM⟩
      intro nu hnu hne
      rcases mem_insert.1 hnu with rfl | h2
      · exact absurd h hne
      · exact g0 nu h2 hne
    · obtain ⟨T, g', g'1, g'0, hT, hTM⟩ := lattice_stable_weight_separator (O := O) E h
      refine ⟨T * P, fun nu => g' nu * g nu, by simp [g1, g'1], ?_, ?_, ?_⟩
      · intro nu hnu hne
        rcases mem_insert.1 hnu with rfl | h2
        · simp [g'0]
        · simp [g0 nu h2 hne]
      · intro nu x hx
        rw [Module.End.mul_apply, hP nu x hx, map_smul, hT nu x hx, smul_smul]
        push_cast
        rw [mul_comm]
      · intro M hM x hx
        exact hTM M hM _ (hPM M hM x hx)

theorem exists_integral_weight_projections [CharZero (KK O)] (E : GLOps n (KK O) V) (F : Finset (Fin n → ℤ)) :
    ∃ P : (Fin n → ℤ) → Module.End (KK O) V,
      (∀ mu, ∀ M : Submodule O V, UZStable (O := O) E M → ∀ x ∈ M, P mu x ∈ M) ∧
      (∀ mu, ∀ x ∈ weightSp E mu, P mu x = x) ∧
      (∀ mu, ∀ nu ∈ F, nu ≠ mu → ∀ x ∈ weightSp E nu, P mu x = 0) := by
  choose P g hg1 hg0 hgw hgM using fun mu => exists_integral_weight_projection E mu F
  refine ⟨P, fun mu M hM x hx => hgM mu M hM x hx, fun mu x hx => ?_, fun mu nu hnu hne x hx => ?_⟩
  · rw [hgw mu mu x hx, hg1 mu]
    simp
  · rw [hgw mu nu x hx, hg0 mu nu hnu hne]
    simp

theorem sum_weight_projections_eq_one {E : GLOps n (KK O) V} {F : Finset (Fin n → ℤ)}
    (hF : (⊤ : Submodule (KK O) V) ≤ ⨆ nu ∈ F, weightSp E nu) {P : (Fin n → ℤ) → Module.End (KK O) V}
    (h1 : ∀ mu, ∀ x ∈ weightSp E mu, P mu x = x)
    (h0 : ∀ mu, ∀ nu ∈ F, nu ≠ mu → ∀ x ∈ weightSp E nu, P mu x = 0) : ∑ mu ∈ F, P mu = 1 := by
  refine linear_map_ext_on_weights hF fun nu hnu x hx => ?_
  rw [LinearMap.sum_apply, Finset.sum_eq_single nu (fun mu _ hne => h0 mu nu hnu (Ne.symm hne) x hx)
    (fun h => absurd hnu h)]
  rw [h1 nu x hx]
  rfl

private theorem end_mul_apply' (f g : Module.End (KK O) V) (x : V) : (f * g) x = f (g x) := rfl

private theorem diagonal_apply_of_mem_weightSp {E : GLOps n (KK O) V} {mu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E mu)
    (a : Fin n) : E a a x = ((mu a : ℤ) : KK O) • x := by
  rw [weightSp, Submodule.mem_iInf] at hx
  have h := LinearMap.mem_ker.1 (hx a)
  rw [LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply] at h
  exact h

theorem diagonal_weight_projection_comm {E : GLOps n (KK O) V} {F : Finset (Fin n → ℤ)}
    (hF : (⊤ : Submodule (KK O) V) ≤ ⨆ nu ∈ F, weightSp E nu) {P : (Fin n → ℤ) → Module.End (KK O) V}
    (h1 : ∀ mu, ∀ x ∈ weightSp E mu, P mu x = x)
    (h0 : ∀ mu, ∀ nu ∈ F, nu ≠ mu → ∀ x ∈ weightSp E nu, P mu x = 0) (mu : Fin n → ℤ) (a : Fin n) :
    E a a * P mu = (mu a : KK O) • P mu ∧ P mu * E a a = (mu a : KK O) • P mu := by
  constructor
  · refine linear_map_ext_on_weights hF fun nu hnu x hx => ?_
    by_cases h : nu = mu
    · subst h
      rw [end_mul_apply', LinearMap.smul_apply, h1 _ x hx]
      exact diagonal_apply_of_mem_weightSp hx a
    · rw [end_mul_apply', LinearMap.smul_apply, h0 mu nu hnu h x hx, map_zero, smul_zero]
  · refine linear_map_ext_on_weights hF fun nu hnu x hx => ?_
    rw [end_mul_apply', LinearMap.smul_apply, diagonal_apply_of_mem_weightSp hx a, map_smul]
    by_cases h : nu = mu
    · subst h
      rw [h1 _ x hx]
    · rw [h0 mu nu hnu h x hx, smul_zero, smul_zero]

def adjointEndAction (E : GLOps n (KK O) V) : GLOps n (KK O) (Module.End (KK O) V) :=
  fun a b => LinearMap.mulLeft (KK O) (E a b) - LinearMap.mulRight (KK O) (E a b)

theorem adjointEndAction_apply (E : GLOps n (KK O) V) (a b : Fin n) (f : Module.End (KK O) V) :
    adjointEndAction E a b f = E a b * f - f * E a b := by
  first
  | rfl
  | simp [adjointEndAction]

private theorem end_one_apply {W : Type*} [AddCommGroup W] [Module (KK O) W] (x : W) :
    (1 : Module.End (KK O) W) x = x := rfl

theorem weight_block_adjoint_weight {E : GLOps n (KK O) V} {F : Finset (Fin n → ℤ)}
    (hF : (⊤ : Submodule (KK O) V) ≤ ⨆ nu ∈ F, weightSp E nu) {P : (Fin n → ℤ) → Module.End (KK O) V}
    (h1 : ∀ mu, ∀ x ∈ weightSp E mu, P mu x = x)
    (h0 : ∀ mu, ∀ nu ∈ F, nu ≠ mu → ∀ x ∈ weightSp E nu, P mu x = 0) (mu nu : Fin n → ℤ)
    (f : Module.End (KK O) V) : P mu * f * P nu ∈ weightSp (adjointEndAction E) (mu - nu) := by
  rw [weightSp, Submodule.mem_iInf]
  intro a
  obtain ⟨hm, -⟩ := diagonal_weight_projection_comm hF h1 h0 mu a
  obtain ⟨-, hn⟩ := diagonal_weight_projection_comm hF h1 h0 nu a
  have e1 : E a a * (P mu * f * P nu) = ((mu a : ℤ) : KK O) • (P mu * f * P nu) := by
    rw [← mul_assoc, ← mul_assoc, hm, smul_mul_assoc, smul_mul_assoc]
  have e2 : P mu * f * P nu * E a a = ((nu a : ℤ) : KK O) • (P mu * f * P nu) := by
    rw [mul_assoc, hn, mul_smul_comm]
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, adjointEndAction_apply, LinearMap.smul_apply, end_one_apply,
    e1, e2, Pi.sub_apply, Int.cast_sub, sub_smul]

theorem endomorphism_sum_weight_blocks {E : GLOps n (KK O) V} {F : Finset (Fin n → ℤ)}
    (hF : (⊤ : Submodule (KK O) V) ≤ ⨆ nu ∈ F, weightSp E nu) {P : (Fin n → ℤ) → Module.End (KK O) V}
    (h1 : ∀ mu, ∀ x ∈ weightSp E mu, P mu x = x)
    (h0 : ∀ mu, ∀ nu ∈ F, nu ≠ mu → ∀ x ∈ weightSp E nu, P mu x = 0) (f : Module.End (KK O) V) :
    f = ∑ mu ∈ F, ∑ nu ∈ F, P mu * f * P nu := by
  have hs := sum_weight_projections_eq_one hF h1 h0
  calc f = (∑ mu ∈ F, P mu) * f * (∑ nu ∈ F, P nu) := by rw [hs, one_mul, mul_one]
    _ = ∑ mu ∈ F, ∑ nu ∈ F, P mu * f * P nu := by
      rw [Finset.sum_mul, Finset.sum_mul]
      simp_rw [Finset.mul_sum]

theorem adjoint_end_isGLRep [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V} (hE : IsGLRep E) :
    IsGLRep (adjointEndAction E) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b c d
    refine LinearMap.ext fun f => ?_
    have hr := hE.1 a b c d
    have key : (adjointEndAction E a b * adjointEndAction E c d - adjointEndAction E c d * adjointEndAction E a b) f =
        (E a b * E c d - E c d * E a b) * f - f * (E a b * E c d - E c d * E a b) := by
      simp only [LinearMap.sub_apply, Module.End.mul_apply, adjointEndAction_apply]
      noncomm_ring
    rw [key, hr]
    by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [h1, h2, adjointEndAction_apply] <;> noncomm_ring
  · intro x
    exact ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ _ => Submodule.mem_top⟩
  · obtain ⟨F, hF⟩ := findim_exists_finite_weights E hE.2.2
    obtain ⟨P, -, h1, h0⟩ := exists_integral_weight_projections (O := O) E F
    rw [eq_top_iff]
    intro f _
    rw [endomorphism_sum_weight_blocks hF h1 h0 f]
    refine Submodule.sum_mem _ fun mu _ => Submodule.sum_mem _ fun nu _ => ?_
    exact Submodule.mem_iSup_of_mem (mu - nu) (weight_block_adjoint_weight hF h1 h0 mu nu f)

end hw

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

def nablaToDeltaMaps (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (v : V) : Submodule O (Module.End (KK O) V) where
  carrier := {f | ∀ x ∈ Nabla (O := O) E lam v, f x ∈ Delta (O := O) E v}
  zero_mem' := fun x _ => by simp
  add_mem' := fun {f g} hf hg x hx => by rw [LinearMap.add_apply]; exact Submodule.add_mem _ (hf x hx) (hg x hx)
  smul_mem' := fun c f hf x hx => by rw [LinearMap.smul_apply]; exact Submodule.smul_mem _ _ (hf x hx)

theorem nabla_integral_enveloping_stable (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (v : V) :
    UZStable (O := O) E (NablaSub (O := O) E lam v) := by
  intro u hu x hx u' hu'
  exact hx (u' * u) (Submonoid.mul_mem _ hu' (Submonoid.subset_closure hu))

theorem delta_integral_enveloping_stable (E : GLOps n (KK O) V) (v : V) : UZStable (O := O) E (Delta (O := O) E v) := by
  intro u hu x hx
  have hle : Delta (O := O) E v ≤ (Delta (O := O) E v).comap (u.restrictScalars O) := by
    unfold Delta
    rw [Submodule.span_le]
    rintro _ ⟨u', hu', rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply]
    exact Submodule.subset_span ⟨u * u', Submonoid.mul_mem _ (Submonoid.subset_closure hu) hu', rfl⟩
  exact hle hx

theorem adjoint_divided_power_expansion [CharZero (KK O)] (E : GLOps n (KK O) V) (a b : Fin n) (k : ℕ) (f : Module.End (KK O) V) :
    divPowE (adjointEndAction E) a b k f =
      ∑ m ∈ range (k + 1), ((-1 : KK O) ^ (k - m)) • (divPowE E a b m * f * divPowE E a b (k - m)) := by
  have hc : Commute (LinearMap.mulLeft (KK O) (E a b)) ((-1 : KK O) • LinearMap.mulRight (KK O) (E a b)) :=
    (LinearMap.commute_mulLeft_right _ _).smul_right _
  have hsub : adjointEndAction E a b =
      LinearMap.mulLeft (KK O) (E a b) + (-1 : KK O) • LinearMap.mulRight (KK O) (E a b) := by
    rw [adjointEndAction, neg_one_smul, sub_eq_add_neg]
  simp only [divPowE]
  rw [hsub, hc.add_pow, LinearMap.smul_apply, LinearMap.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmk : m ≤ k := by simp at hm; omega
  rw [smul_pow, LinearMap.pow_mulLeft, LinearMap.pow_mulRight]
  simp only [Module.End.mul_apply, Module.End.natCast_apply, LinearMap.smul_apply, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, map_nsmul, map_smul, smul_mul_assoc, mul_smul_comm, mul_assoc]
  rw [← Nat.cast_smul_eq_nsmul (KK O), smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  rw [Nat.cast_choose (KK O) hmk]
  have h1 : ((m.factorial : ℕ) : KK O) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have h2 : (((k - m).factorial : ℕ) : KK O) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k - m)
  have h3 : ((k.factorial : ℕ) : KK O) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp

theorem nabla_to_delta_maps_stable [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V} (hE : IsGLRep E)
    (lam : Fin n → ℤ) (v : V) : UZStable (O := O) (adjointEndAction E) (nablaToDeltaMaps (O := O) E lam v) := by
  intro u hu f hf x hx
  have hN := nabla_integral_enveloping_stable (O := O) E lam v
  have hD := delta_integral_enveloping_stable (O := O) E v
  have htop : ∀ z : V, z ∈ ⨆ mu, ⨆ (_ : True), weightSp E mu := by
    intro z
    simp only [iSup_true]
    rw [hE.2.2]
    exact Submodule.mem_top
  rcases hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
  · rw [adjoint_divided_power_expansion, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun m _ => ?_
    rw [LinearMap.smul_apply, Module.End.mul_apply, Module.End.mul_apply]
    have h1 : divPowE E a b (k - m) x ∈ NablaSub (O := O) E lam v := hN _ (Or.inl ⟨a, b, k - m, hab, rfl⟩) x hx
    have h2 : f (divPowE E a b (k - m) x) ∈ Delta (O := O) E v := hf _ h1
    have h3 := hD _ (Or.inl ⟨a, b, m, hab, rfl⟩) _ h2
    have h4 := intCast_smul_mem_submodule (Delta (O := O) E v) ((-1 : ℤ) ^ (k - m)) h3
    simpa using h4
  · have hR : ∀ (m : ℕ) (μ ν : Fin n → ℤ) (z : V), z ∈ weightSp E μ →
        (((List.range m).map fun j : ℕ => E a a - ((ν a : KK O) + j) • (1 : Module.End (KK O) V)).prod) z =
          (∏ j ∈ range m, ((μ a : KK O) - ((ν a : KK O) + j))) • z := by
      intro m μ ν z hz
      induction m with
      | zero => simp
      | succ m ih =>
        rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
          Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
          (mem_weightSpace_iff_diag_scalar.1 hz) a, ← sub_smul, map_smul, ih, smul_smul, Finset.prod_range_succ, mul_comm]
    have hw : ∀ (ν : Fin n → ℤ) (y : V), y ∈ weightSp E ν →
        (binomE (adjointEndAction E) a k f) y = ∑ ij ∈ antidiagonal k,
          (((Ring.choose (-(ν a)) ij.2 : ℤ) : KK O)) • binomE E a ij.1 (f y) := by
      intro ν y hy
      have hadx : ∀ (g : Module.End (KK O) V) (c : KK O),
          ((adjointEndAction E a a - c • (1 : Module.End (KK O) (Module.End (KK O) V))) g) y =
            (E a a - ((ν a : KK O) + c) • (1 : Module.End (KK O) V)) (g y) := by
        intro g c
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, adjointEndAction_apply,
          Module.End.mul_apply, (mem_weightSpace_iff_diag_scalar.1 hy) a, map_smul, add_smul, LinearMap.add_apply]
        abel
      have hprod : ∀ (m : ℕ) (g : Module.End (KK O) V),
          (((List.range m).map fun j : ℕ => adjointEndAction E a a - (j : KK O) •
            (1 : Module.End (KK O) (Module.End (KK O) V))).prod g) y =
          (((List.range m).map fun j : ℕ => E a a - ((ν a : KK O) + j) • (1 : Module.End (KK O) V)).prod) (g y) := by
        intro m
        induction m with
        | zero => intro g; simp
        | succ m ih =>
          intro g
          rw [List.range_succ, List.map_append, List.map_append, List.prod_append, List.prod_append,
            List.map_singleton, List.map_singleton, List.prod_singleton, List.prod_singleton]
          simp only [Module.End.mul_apply]
          rw [ih, hadx]
      obtain ⟨G, h, hh, hfy⟩ := mem_weight_sup_exists_finset_sum E (fun _ => True) (htop (f y))
      set_option synthInstance.maxHeartbeats 100000 in
        rw [binomE, LinearMap.smul_apply, LinearMap.smul_apply, hprod, hfy, map_sum, Finset.smul_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, Finset.smul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun μ hμ => ?_
      have hμw := (hh μ hμ).2
      rw [hR k μ ν _ hμw, smul_smul]
      simp only [binomial_diagonal_on_weight hμw, map_smul, smul_smul]
      rw [← Finset.sum_smul]
      congr 1
      calc ((k.factorial : KK O))⁻¹ * ∏ j ∈ range k, ((μ a : KK O) - ((ν a : KK O) + j))
          = ((k.factorial : KK O))⁻¹ * ∏ j ∈ range k, (((μ a + -(ν a) : ℤ) : KK O) - (j : KK O)) := by
            congr 1
            refine Finset.prod_congr rfl fun j _ => ?_
            push_cast
            ring
        _ = ((Ring.choose (μ a + -(ν a)) k : ℤ) : KK O) := inv_factorial_prod_eq_choose _ _
        _ = _ := by
            rw [Ring.add_choose_eq k (Commute.all _ _)]
            push_cast
            refine Finset.sum_congr rfl fun ij _ => ?_
            ring
    obtain ⟨S, hSdef⟩ : ∃ S : ℕ → Module.End (KK O) V,
        S = fun j : ℕ => ((((j : ℤ).negOnePow : ℤˣ) : ℤ) : KK O) • shiftedBinomialOperator E a ((j : ℤ) - 1) j := ⟨_, rfl⟩
    have hS : ∀ (j : ℕ) (ν : Fin n → ℤ) (y : V), y ∈ weightSp E ν →
        S j y = ((Ring.choose (-(ν a)) j : ℤ) : KK O) • y := by
      intro j ν y hy
      rw [hSdef, LinearMap.smul_apply, shifted_binomial_on_weight hy, smul_smul]
      congr 1
      rw [Ring.choose_neg, Units.smul_def, smul_eq_mul, add_sub_assoc]
      push_cast
      ring
    have hop : binomE (adjointEndAction E) a k f = ∑ ij ∈ antidiagonal k, binomE E a ij.1 * f * S ij.2 := by
      apply LinearMap.ext
      intro z
      obtain ⟨F, g, hg, rfl⟩ := mem_weight_sup_exists_finset_sum E (fun _ => True) (htop z)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun ν hν => ?_
      rw [hw ν _ (hg ν hν).2, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun ij _ => ?_
      rw [Module.End.mul_apply, Module.End.mul_apply, hS _ _ _ (hg ν hν).2, map_smul, map_smul]
    rw [hop, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun ij _ => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply]
    have h1 : S ij.2 x ∈ NablaSub (O := O) E lam v := by
      rw [hSdef, LinearMap.smul_apply]
      exact intCast_smul_mem_submodule _ _ (shifted_binomial_preserves_lattice hN a _ _ hx)
    have h2 : f (S ij.2 x) ∈ Delta (O := O) E v := hf _ h1
    exact hD _ (Or.inr ⟨a, ij.1, rfl⟩) _ h2

end hw

end Formalism.MainNotions.G.GLWeightTheory
