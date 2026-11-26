module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CoefOfEmb

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.PtrScalar
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

section Helpers
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem tpsc_single_mem {S : Submodule ℂ M} {x : M} (hx : x ∈ S) (c : Fin n) :
    (Pi.single c x : Fin n → M) ∈ tensSub S := by
  refine Submodule.mem_pi.2 fun d _ => ?_
  by_cases h : d = c
  · subst h; simpa using hx
  · simp [h]

theorem tpsc_coord_mem {S : Submodule ℂ M} {f : Fin n → M} (hf : f ∈ tensSub S) (c : Fin n) : f c ∈ S :=
  Submodule.mem_pi.1 hf c (Set.mem_univ _)

theorem tpsc_tensV_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (x : M) :
    tensV E a b (Pi.single c x) = Pi.single c (E a b x) + if b = c then Pi.single a x else 0 := by
  funext d
  rw [tensV_coord]
  by_cases hdc : d = c <;> by_cases hda : d = a <;> by_cases hbc : b = c <;>
    simp [Pi.single_apply, hdc, hda, hbc] <;> split_ifs <;> simp_all

theorem tpsc_tensVd_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (x : M) :
    tensVd E a b (Pi.single c x) = Pi.single c (E a b x) - if a = c then Pi.single b x else 0 := by
  funext d
  rw [tensVd_coord]
  by_cases hdc : d = c <;> by_cases hdb : d = b <;> by_cases hac : a = c <;>
    simp [Pi.single_apply, hdc, hdb, hac] <;> split_ifs <;> simp_all

end Helpers

def tpscK (dual : Bool) (k : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n) : ℂ := cond dual (star (k c d)) (k c d)

theorem tpscK_rows {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (dual : Bool)
    (c c' : Fin n) : ∑ d, tpscK dual k c' d * star (tpscK dual k c d) = if c' = c then 1 else 0 := by
  have hu : k * star k = 1 := Matrix.mem_unitaryGroup_iff.1 hk
  cases dual
  · have := congrFun (congrFun hu c') c
    simpa [tpscK, Matrix.mul_apply, Matrix.one_apply] using this
  · have := congrFun (congrFun hu c) c'
    simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.star_apply] at this
    simp only [tpscK, cond_true, star_star]
    rw [show (∑ d, star (k c' d) * k c d) = ∑ d, k c d * star (k c' d) from
      Finset.sum_congr rfl fun d _ => mul_comm _ _, this]
    by_cases h : c' = c
    · subst h; simp
    · simp [h, Ne.symm h]

theorem tpscK_cols {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (dual : Bool)
    (e d : Fin n) : ∑ c, tpscK dual k c d * star (tpscK dual k c e) = if e = d then 1 else 0 := by
  have hu : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk
  cases dual
  · have := congrFun (congrFun hu e) d
    simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.star_apply] at this
    simp only [tpscK, cond_false]
    rw [show (∑ c, k c d * star (k c e)) = ∑ c, star (k c e) * k c d from
      Finset.sum_congr rfl fun c _ => mul_comm _ _, this]
  · have := congrFun (congrFun hu d) e
    simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.star_apply] at this
    simp only [tpscK, cond_true, star_star]
    rw [this]
    by_cases h : e = d
    · subst h; simp
    · simp [h, Ne.symm h]

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
  {V : Submodule ℂ D} {A : Module.End ℂ (Fin n → D)}

theorem ptr_mem {dual : Bool} (hA : IsGKEndo dual ε σ E (genSub E V) A) :
    ∀ x ∈ genSub E V, ptr A x ∈ genSub E V := by
  intro x hx
  rw [ptr_apply]
  exact Submodule.sum_mem _ fun c _ => tpsc_coord_mem (hA.1 _ (tpsc_single_mem hx c)) c

theorem ptr_comm {dual : Bool} (hE : IsGlRep E) (hA : IsGKEndo dual ε σ E (genSub E V) A) (a b : Fin n) :
    ∀ x ∈ genSub E V, ptr A (E a b x) = E a b (ptr A x) := by
  intro x hx
  have hs : ∀ c, (Pi.single c x : Fin n → D) ∈ tensSub (genSub E V) := fun c => tpsc_single_mem hx c
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ptr_apply, ptr_apply, map_sum]
  cases dual
  · have key : ∀ c, A (Pi.single c (E a b x)) c = E a b (A (Pi.single c x) c) +
        (if c = a then A (Pi.single c x) b else 0) - (if b = c then A (Pi.single a x) c else 0) := by
      intro c
      have h1 : (Pi.single c (E a b x) : Fin n → D) =
          tensV E a b (Pi.single c x) - (if b = c then Pi.single a x else 0) := by
        rw [tpsc_tensV_single]; abel
      have h2 := hA.2.1 a b _ (hs c)
      simp only [tensF, cond_false] at h2
      rw [h1, map_sub, h2, Pi.sub_apply, tensV_coord]
      split_ifs <;> simp
    simp only [key, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true, add_sub_cancel_right]
  · have key : ∀ c, A (Pi.single c (E a b x)) c = E a b (A (Pi.single c x) c) -
        (if c = b then A (Pi.single c x) a else 0) + (if a = c then A (Pi.single b x) c else 0) := by
      intro c
      have h1 : (Pi.single c (E a b x) : Fin n → D) =
          tensVd E a b (Pi.single c x) + (if a = c then Pi.single b x else 0) := by
        rw [tpsc_tensVd_single]; abel
      have h2 := hA.2.1 a b _ (hs c)
      simp only [tensF, cond_true] at h2
      rw [h1, map_add (f := _), h2, Pi.add_apply, tensVd_coord]
      split_ifs <;> simp
    simp only [key, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true, sub_add_cancel]

theorem tpsc_kDiag (dual : Bool) (k : Matrix (Fin n) (Fin n) ℂ) (f : Fin n → H) (c : Fin n) :
    kDiag dual σ k f c = ∑ d, tpscK dual k c d • σ k (f d) := rfl

theorem ptr_kcomm {dual : Bool} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hA : IsGKEndo dual ε σ E (genSub E V) A) :
    ∀ k ∈ Kset ε, ∀ x ∈ genSub E V, ∀ y ∈ genSub E V, (y : H) = σ k (x : H) →
      ((ptr A y : D) : H) = σ k ((ptr A x : D) : H) := by
  intro k hk x hx y hy hxy
  have hku := hk.1
  let g : Fin n → Fin n → D := fun c d => star (tpscK dual k c d) • x
  have hg : ∀ c, g c ∈ tensSub (genSub E V) := fun c =>
    Submodule.mem_pi.2 fun d _ => Submodule.smul_mem _ _ hx
  have hgs : ∀ c, g c = ∑ e, star (tpscK dual k c e) • (Pi.single e x : Fin n → D) := by
    intro c; funext d
    simp [g, Finset.sum_apply, Pi.single_apply]
  have hf' : ∀ c, (fun c' => (((Pi.single c y : Fin n → D) c' : D) : H)) =
      kDiag dual σ k (fun d => ((g c d : D) : H)) := by
    intro c; funext c'
    rw [tpsc_kDiag]
    simp only [g, Submodule.coe_smul, map_smul, smul_smul]
    rw [← Finset.sum_smul, tpscK_rows hku dual c c', ← hxy]
    by_cases h : c' = c
    · subst h; simp
    · simp [h]
  have hAf : ∀ c c', ((A (Pi.single c y) c' : D) : H) = ∑ d, tpscK dual k c' d •
      σ k (∑ e, star (tpscK dual k c e) • ((A (Pi.single e x) d : D) : H)) := by
    intro c c'
    have := congrFun (hA.2.2 k hk _ (hg c) _ (tpsc_single_mem hy c) (hf' c)) c'
    rw [this, tpsc_kDiag, hgs c]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_smul, Finset.sum_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ptr_apply, ptr_apply, Submodule.coe_sum, Submodule.coe_sum, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hAf, map_sum, map_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, tpscK_cols hku dual]
  simp [ite_smul]

end

theorem ptr_scalar (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) {A : Module.End ℂ (Fin n → D)} (hA : IsGKEndo dual ε σ E (genSub E V) A) :
    ∃ c : ℂ, ∀ x ∈ genSub E V, ptr A x = c • x :=
  data_end_scalar hgap hσ hD hV hc hVK (ptr A) (ptr_mem hA) (fun a b => ptr_comm hD.glRep hA a b)
    (ptr_kcomm hσ hD hA)

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

noncomputable section

open Finset MeasureTheory
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

open UnitA UnitB

section SlopeTestRemainingChoices

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

def hvec (f : Fin n → D) : Fin n → H := fun c => ((f c : D) : H)

theorem hvec_add (f g : Fin n → D) : hvec (f + g) = hvec f + hvec g := by
  funext c; simp [hvec]

theorem hvec_smul (a : ℂ) (f : Fin n → D) : hvec (a • f) = a • hvec f := by
  funext c; simp [hvec]

theorem mx_mem {M : Submodule ℂ D} (dual : Bool) (X : Matrix (Fin n) (Fin n) ℂ)
    (hst : ∀ a b, ∀ f ∈ tensSub M, tensF dual E a b f ∈ tensSub M) {f : Fin n → D} (hf : f ∈ tensSub M) :
    mx (tensF dual E) X f ∈ tensSub M := by
  unfold mx
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
    Submodule.smul_mem _ _ (hst a b f hf)

theorem mat_decomp2 (Y Z : Matrix (Fin n) (Fin n) ℂ) :
    (1 / 2 : ℂ) • (Y - Z) + (Complex.I / 2) • (Complex.I • (Y + Z)) = -Z := by
  rw [smul_smul, show Complex.I / 2 * Complex.I = -(1 / 2) by
    rw [div_mul_eq_mul_div, Complex.I_mul_I]; ring]
  module

end SlopeTestRemainingChoices

theorem tens_unitarize (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) :
    ∃ Q : (Fin n → D) →ₗ⋆[ℂ] (Fin n → D) →ₗ[ℂ] ℂ,
      (∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V), Q g f = star (Q f g)) ∧
      (∀ f ∈ tensSub (genSub E V), f ≠ 0 → 0 < (Q f f).re) ∧
      (∀ a b, ∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V),
        Q (tensF dual E a b f) g = adjSign ε a b * Q f (tensF dual E b a g)) ∧
      ∀ k ∈ Kset ε, ∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V),
        ∀ f' ∈ tensSub (genSub E V), ∀ g' ∈ tensSub (genSub E V),
          (fun c => ((f' c : D) : H)) = kDiag dual σ k (fun c => ((f c : D) : H)) →
          (fun c => ((g' c : D) : H)) = kDiag dual σ k (fun c => ((g c : D) : H)) → Q f' g' = Q f g := by
  classical
  haveI : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  haveI : FiniteDimensional ℂ V := hV.1
  let bV := Module.finBasis ℂ V
  let ys : Fin (Module.finrank ℂ V) → H := fun j => (((bV j : V) : D) : H)
  have hVM : V ≤ genSub E V := le_sInf fun T hT => hT.1
  have hmem : ∀ f : Fin n → D, f ∈ tensSub (genSub E V) → ∀ c, f c ∈ genSub E V := fun f hf c =>
    (Submodule.mem_pi.1 hf) c (Set.mem_univ c)
  have hst : ∀ a b : Fin n, ∀ f ∈ tensSub (n := n) (genSub E V), tensF dual E a b f ∈ tensSub (genSub E V) :=
    tensSub_stable dual
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (tensSub (n := n) (genSub E V))
  let P : (Fin n → D) →ₗ[ℂ] (Fin n → D) :=
    (tensSub (n := n) (genSub E V)).subtype ∘ₗ Submodule.linearProjOfIsCompl _ _ hC
  have hPm : ∀ f : Fin n → D, P f ∈ tensSub (genSub E V) := fun f => (Submodule.linearProjOfIsCompl _ _ hC f).2
  have hPid : ∀ f ∈ tensSub (n := n) (genSub E V), P f = f := fun f hf => by
    exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hC ⟨f, hf⟩)
  let u : Fin (Module.finrank ℂ V) → Fin n → (Fin n → D) → Formalism.REAL.UJ ε → ℂ :=
    fun j ξ f => cf dual ε σ (ys j) ξ (hvec f)
  have hL : ∀ f ∈ tensSub (n := n) (genSub E V), ∀ j ξ, MemLp (u j ξ f) 2 (Formalism.REAL.muG ε) := fun f hf j ξ =>
    memLp_cf hσ dual _ ξ _ fun c => hW (f c) (hmem f hf c) ((bV j : V) : D) (hVM (bV j).2)
  have hLP : ∀ (f : Fin n → D) j ξ, MemLp (u j ξ (P f)) 2 (Formalism.REAL.muG ε) := fun f => hL _ (hPm f)
  have hu_add : ∀ j ξ f g, u j ξ (f + g) = u j ξ f + u j ξ g := fun j ξ f g => by
    simp only [u, hvec_add, cf_add]
  have hu_smul : ∀ j ξ (a : ℂ) f, u j ξ (a • f) = a • u j ξ f := fun j ξ a f => by
    simp only [u, hvec_smul, cf_smul]
  let Q0 : (Fin n → D) → (Fin n → D) → ℂ := fun f g =>
    ∑ j, ∑ ξ, pr (Formalism.REAL.muG ε) (u j ξ (P f)) (u j ξ (P g))
  let Q : (Fin n → D) →ₗ⋆[ℂ] (Fin n → D) →ₗ[ℂ] ℂ := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) Q0
    (fun f f' g => by
      simp only [Q0, map_add (f := _), hu_add, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun ξ _ =>
        pr_add_left (hLP f j ξ) (hLP f' j ξ) (hLP g j ξ))
    (fun a f g => by
      simp only [Q0, map_smul, hu_smul, pr_smul_left, Finset.mul_sum, smul_eq_mul, starRingEnd_apply])
    (fun f g g' => by
      simp only [Q0, map_add (f := _), hu_add, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun ξ _ =>
        pr_add_right (hLP f j ξ) (hLP g j ξ) (hLP g' j ξ))
    (fun a f g => by
      simp only [Q0, map_smul, hu_smul, pr_smul_right, Finset.mul_sum, smul_eq_mul, RingHom.id_apply])
  have hQ : ∀ f ∈ tensSub (n := n) (genSub E V), ∀ g ∈ tensSub (genSub E V),
      Q f g = ∑ j, ∑ ξ, pr (Formalism.REAL.muG ε) (u j ξ f) (u j ξ g) := by
    intro f hf g hg
    simp only [Q, LinearMap.mk₂'ₛₗ_apply, Q0, hPid f hf, hPid g hg]
  have hskew : ∀ X (hX : inG ε X), ∀ f ∈ tensSub (n := n) (genSub E V), ∀ g ∈ tensSub (genSub E V),
      Q (mx (tensF dual E) X f) g = -Q f (mx (tensF dual E) X g) := by
    intro X hX f hf g hg
    have hXf := mx_mem dual X hst hf
    have hXg := mx_mem dual X hst hg
    rw [hQ _ hXf g hg, hQ f hf _ hXg, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    exact skew (continuous_ex hX) (ex_zero hX) (ex_add hX)
      (continuous_cf hσ dual _ ξ _) (continuous_cf hσ dual _ ξ _) (continuous_cf hσ dual _ ξ _)
      (continuous_cf hσ dual _ ξ _)
      (hL f hf j ξ) (hL _ hXf j ξ) (hL g hg j ξ) (hL _ hXg j ξ)
      (fun x t => hasDerivAt_cf hσ hD hX dual (ys j) ξ f x t)
      (fun x t => hasDerivAt_cf hσ hD hX dual (ys j) ξ g x t)
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · intro f _ g _
    simp only [Q, LinearMap.mk₂'ₛₗ_apply, Q0, star_sum, pr_star]
  · intro f hf hf0
    rw [hQ f hf f hf]
    have hre : ∀ j ξ, (pr (Formalism.REAL.muG ε) (u j ξ f) (u j ξ f)).re =
        ∫ x, ‖u j ξ f x‖ ^ 2 ∂(Formalism.REAL.muG ε) := by
      intro j ξ
      rw [(pr_self_re (hL f hf j ξ)).1, Complex.ofReal_re]
    simp only [Complex.re_sum, hre]
    have hnn : ∀ j ξ, 0 ≤ ∫ x, ‖u j ξ f x‖ ^ 2 ∂(Formalism.REAL.muG ε) := fun j ξ =>
      integral_nonneg fun x => by positivity
    by_contra hneg
    push_neg at hneg
    have h0 : ∑ j, ∑ ξ, ∫ x, ‖u j ξ f x‖ ^ 2 ∂(Formalism.REAL.muG ε) = 0 :=
      le_antisymm hneg (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun ξ _ => hnn j ξ)
    have hz : ∀ j ξ, ∫ x, ‖u j ξ f x‖ ^ 2 ∂(Formalism.REAL.muG ε) = 0 := by
      intro j ξ
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => Finset.sum_nonneg fun ξ _ => hnn j ξ).1 h0 j
        (Finset.mem_univ j)
      exact (Finset.sum_eq_zero_iff_of_nonneg fun ξ _ => hnn j ξ).1 h1 ξ (Finset.mem_univ ξ)
    have hz' : ∀ j ξ x, u j ξ f x = 0 := by
      intro j ξ
      have hi := (pr_self_re (hL f hf j ξ)).2
      have hae := (integral_eq_zero_iff_of_nonneg (fun x => by positivity) hi).1 (hz j ξ)
      have hc : Continuous (fun x => ‖u j ξ f x‖ ^ 2) := ((continuous_cf hσ dual _ ξ _).norm).pow 2
      have h2 := (hc.ae_eq_iff_eq (Formalism.REAL.muG ε) continuous_zero).1 hae
      intro x
      have h3 := congrFun h2 x
      simpa using h3
    apply hf0
    refine cf_inj hσ hD dual (hmem f hf) fun y hy ξ x => ?_
    have hy' : ((y : D) : H) = ∑ j, (bV.repr ⟨y, hy⟩ j) • ys j := by
      have h2 := congrArg (fun w : V => ((w : D) : H)) (bV.sum_repr ⟨y, hy⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
      exact h2.symm
    have e : cf dual ε σ ((y : D) : H) ξ (fun c => ((f c : D) : H)) x =
        ∑ j, star (bV.repr ⟨y, hy⟩ j) * u j ξ f x := by
      simp only [u, cf, hvec, hy', sum_inner, inner_smul_left, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => ?_
      simp only [starRingEnd_apply]
      ring
    rw [e]
    exact Finset.sum_eq_zero fun j _ => by rw [hz' j ξ x, mul_zero]
  · intro a b f hf g hg
    obtain ⟨Z, hZ⟩ : ∃ Z, Z = Jm ε * (Matrix.single a b (1 : ℂ))ᴴ * Jm ε := ⟨_, rfl⟩
    have hX1 : inG ε (Matrix.single a b 1 - Z) := by rw [hZ]; exact inG_sub _
    have hX2 : inG ε (Complex.I • (Matrix.single a b 1 + Z)) := by rw [hZ]; exact inG_add _
    have hTab : tensF dual E a b = (1 / 2 : ℂ) • mx (tensF dual E) (Matrix.single a b 1 - Z) +
        (-(Complex.I / 2)) • mx (tensF dual E) (Complex.I • (Matrix.single a b 1 + Z)) := by
      rw [← mx_smul, ← mx_smul, ← mx_add, ← mat_decomp, mx_single]
    have hTba : (1 / 2 : ℂ) • mx (tensF dual E) (Matrix.single a b 1 - Z) +
        (Complex.I / 2) • mx (tensF dual E) (Complex.I • (Matrix.single a b 1 + Z)) =
        -(adjSign ε a b • tensF dual E b a) := by
      rw [← mx_smul, ← mx_smul, ← mx_add, mat_decomp2, hZ, single_conj, ← neg_smul, mx_smul, mx_single,
        neg_smul]
    have s1 : star (1 / 2 : ℂ) = 1 / 2 := by simp
    have s2 : star (-(Complex.I / 2)) = Complex.I / 2 := by simp [Complex.conj_I, neg_div]
    have e1 : Q (tensF dual E a b f) g =
        (1 / 2 : ℂ) * Q (mx (tensF dual E) (Matrix.single a b 1 - Z) f) g +
        (Complex.I / 2) * Q (mx (tensF dual E) (Complex.I • (Matrix.single a b 1 + Z)) f) g := by
      rw [hTab]
      simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add (f := _), map_smulₛₗ, smul_eq_mul,
        starRingEnd_apply, s1, s2]
    have e2 := congrArg (fun A : Module.End ℂ (Fin n → D) => Q f (A g)) hTba
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply, map_add (f := _), map_smul, map_neg,
      smul_eq_mul] at e2
    rw [e1, hskew _ hX1 f hf g hg, hskew _ hX2 f hf g hg]
    linear_combination (-1 : ℂ) * e2
  · intro k hk f hf g hg f' hf' g' hg' hff hgg
    have hkU : k ∈ UJset ε := closure_inUJ_of_mem_Kset hk
    rw [hQ f' hf' g' hg', hQ f hf g hg]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun ξ _ => ?_
    have e : ∀ (h h' : Fin n → D), (fun c => ((h' c : D) : H)) = kDiag dual σ k (fun c => ((h c : D) : H)) →
        u j ξ h' = fun x => u j ξ h (x * toG k hkU) := by
      intro h h' hh
      funext x
      show cf dual ε σ (ys j) ξ (hvec h') x = _
      rw [show hvec h' = kDiag dual σ (Formalism.MainNotions.S.umat (toG k hkU)) (hvec h) from hh]
      exact cf_kDiag hσ dual _ ξ _ (toG k hkU) hk.2 x
    rw [e f f' hff, e g g' hgg, pr_rt]

end ReciprocityTheory.ChartRestriction.DS.G2
