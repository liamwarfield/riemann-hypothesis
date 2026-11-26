module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Unitarize
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DcAevalIntertwineAlt

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.DecompC
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.DecompB
noncomputable section

open Polynomial Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

theorem dc_tensF_single_false {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (a b c : Fin n) (v : M) :
    tensF false E a b (Pi.single c v) = Pi.single c (E a b v) + (if b = c then Pi.single a v else 0) := by
  funext c'
  simp only [tensF, cond_false, tensV_coord, Pi.add_apply, Pi.single_apply]
  by_cases h1 : c' = c <;> by_cases h2 : c' = a <;> by_cases h3 : b = c <;> subst_vars <;> simp_all

theorem dc_tensF_single_true {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (a b c : Fin n) (v : M) :
    tensF true E a b (Pi.single c v) = Pi.single c (E a b v) - (if a = c then Pi.single b v else 0) := by
  funext c'
  simp only [tensF, cond_true, tensVd_coord, Pi.sub_apply, Pi.single_apply]
  by_cases h1 : c' = c <;> by_cases h2 : c' = b <;> by_cases h3 : a = c <;> subst_vars <;> simp_all

theorem dc_mem_tensSub {M : Type*} [AddCommGroup M] [Module ℂ M] {S : Submodule ℂ M} {f : Fin n → M} :
    f ∈ tensSub S ↔ ∀ c, f c ∈ S := by
  simp [tensSub, Submodule.mem_pi]

theorem dc_tens_gen_le {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    {V : Submodule ℂ M} (dual : Bool) {T : Submodule ℂ (Fin n → M)} (hVT : tensSub V ≤ T)
    (hT : ∀ a b, ∀ f ∈ T, tensF dual E a b f ∈ T) : tensSub (genSub E V) ≤ T := by
  classical
  let S : Submodule ℂ M := ⨅ c, T.comap (LinearMap.single ℂ (fun _ : Fin n => M) c)
  have hS : ∀ x, x ∈ S ↔ ∀ c, Pi.single c x ∈ T := by
    intro x; simp [S, Submodule.mem_iInf]
  have hVS : V ≤ S := by
    intro x hx
    rw [hS]
    intro c
    refine hVT (dc_mem_tensSub.mpr fun i => ?_)
    rw [Pi.single_apply]
    split_ifs
    · exact hx
    · exact V.zero_mem
  have hSt : ∀ a b, ∀ v ∈ S, E a b v ∈ S := by
    intro a b v hv
    rw [hS] at hv ⊢
    intro c
    cases dual
    · have : Pi.single c (E a b v) = tensF false E a b (Pi.single c v) - (if b = c then Pi.single a v else 0) := by
        rw [dc_tensF_single_false]; abel
      rw [this]
      refine T.sub_mem (hT a b _ (hv c)) ?_
      split_ifs
      · exact hv a
      · exact T.zero_mem
    · have : Pi.single c (E a b v) = tensF true E a b (Pi.single c v) + (if a = c then Pi.single b v else 0) := by
        rw [dc_tensF_single_true]; abel
      rw [this]
      refine T.add_mem (hT a b _ (hv c)) ?_
      split_ifs
      · exact hv b
      · exact T.zero_mem
  have hgen : genSub E V ≤ S := sInf_le ⟨hVS, hSt⟩
  intro f hf
  rw [← Finset.univ_sum_single f]
  exact T.sum_mem fun c _ => (hS _).1 (hgen (dc_mem_tensSub.mp hf c)) c

section Ambient
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}
  {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {E : Fin n → Fin n → Module.End ℂ D}
  {S : Submodule ℂ D} {dual : Bool}

theorem dc_kDiag_add (k : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → H) :
    kDiag dual σ k (fun c => x c + y c) = fun c => kDiag dual σ k x c + kDiag dual σ k y c := by
  funext c
  simp only [kDiag, map_add (f := _), smul_add, Finset.sum_add_distrib]

theorem dc_kDiag_smul (k : Matrix (Fin n) (Fin n) ℂ) (a : ℂ) (x : Fin n → H) :
    kDiag dual σ k (fun c => a • x c) = fun c => a • kDiag dual σ k x c := by
  funext c
  simp only [kDiag, map_smul, Finset.smul_sum]
  exact Finset.sum_congr rfl fun d _ => smul_comm _ _ _

theorem dc_isGKEndo_add' {A B : Module.End ℂ (Fin n → D)} (hA : IsGKEndo dual ε σ E S A)
    (hB : IsGKEndo dual ε σ E S B) : IsGKEndo dual ε σ E S (A + B) := by
  refine ⟨fun f hf => (tensSub S).add_mem (hA.1 f hf) (hB.1 f hf), fun a b f hf => ?_,
    fun k hk f hf f' hf' h => ?_⟩
  · simp only [LinearMap.add_apply, map_add (f := _), hA.2.1 a b f hf, hB.2.1 a b f hf]
  · have e1 := hA.2.2 k hk f hf f' hf' h
    have e2 := hB.2.2 k hk f hf f' hf' h
    simp only [LinearMap.add_apply, Pi.add_apply, Submodule.coe_add]
    rw [dc_kDiag_add, ← e1, ← e2]

theorem dc_isGKEndo_smul' {A : Module.End ℂ (Fin n → D)} (hA : IsGKEndo dual ε σ E S A) (a : ℂ) :
    IsGKEndo dual ε σ E S (a • A) := by
  refine ⟨fun f hf => (tensSub S).smul_mem a (hA.1 f hf), fun x y f hf => ?_,
    fun k hk f hf f' hf' h => ?_⟩
  · simp only [LinearMap.smul_apply, map_smul, hA.2.1 x y f hf]
  · have e1 := hA.2.2 k hk f hf f' hf' h
    simp only [LinearMap.smul_apply, Pi.smul_apply, Submodule.coe_smul]
    rw [dc_kDiag_smul, ← e1]

theorem dc_isGKEndo_mul' {A B : Module.End ℂ (Fin n → D)} (hA : IsGKEndo dual ε σ E S A)
    (hB : IsGKEndo dual ε σ E S B) : IsGKEndo dual ε σ E S (A * B) := by
  refine ⟨fun f hf => hA.1 _ (hB.1 f hf), fun a b f hf => ?_, fun k hk f hf f' hf' h => ?_⟩
  · simp only [Module.End.mul_apply, hB.2.1 a b f hf, hA.2.1 a b _ (hB.1 f hf)]
  · exact hA.2.2 k hk _ (hB.1 f hf) _ (hB.1 f' hf') (hB.2.2 k hk f hf f' hf' h)

theorem dc_isGKEndo_one' : IsGKEndo dual ε σ E S 1 :=
  ⟨fun f hf => hf, fun _ _ _ _ => rfl, fun _ _ _ _ _ _ h => h⟩

theorem dc_isGKEndo_zero' : IsGKEndo dual ε σ E S 0 := by
  refine ⟨fun _ _ => (tensSub S).zero_mem, fun _ _ _ _ => by simp, fun k _ _ _ _ _ _ => ?_⟩
  funext c
  simp [kDiag]

theorem dc_isGKEndo_aeval {A : Module.End ℂ (Fin n → D)} (hA : IsGKEndo dual ε σ E S A) (p : ℂ[X]) :
    IsGKEndo dual ε σ E S (aeval A p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _)]; exact dc_isGKEndo_add' hp hq
  | monomial k a =>
    rw [aeval_monomial, Module.algebraMap_end_eq_smul_id]
    refine dc_isGKEndo_mul' (dc_isGKEndo_smul' dc_isGKEndo_one' a) ?_
    induction k with
    | zero => rw [pow_zero]; exact dc_isGKEndo_one'
    | succ k ih => rw [pow_succ]; exact dc_isGKEndo_mul' ih hA

end Ambient

end ReciprocityTheory.ChartRestriction.DS.G2

end

noncomputable section

open Polynomial Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ} {ε : Fin n → Bool}

def dc_wsh (dual : Bool) (μ : Fin n → ℝ) (c : Fin n) : Fin n → ℝ :=
  if dual then μ + Pi.single c 1 else μ - Pi.single c 1

section
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}

theorem dc_top_coord_false {μ : Fin n → ℝ} {f : Fin n → M} (hf : IsKHWVec ε (tensF false E) μ f)
    (h0 : f ≠ 0) : ∃ c, f c ≠ 0 ∧ IsKHWVec ε E (dc_wsh false μ c) (f c) := by
  classical
  have hne : (univ.filter fun c => f c ≠ 0).Nonempty := by
    obtain ⟨c, hc⟩ := Function.ne_iff.mp h0
    exact ⟨c, by simpa using hc⟩
  set c := (univ.filter fun c => f c ≠ 0).max' hne with hcdef
  have hc : f c ≠ 0 := by
    have := Finset.max'_mem _ hne
    simpa using this
  have hmax : ∀ b, c < b → f b = 0 := by
    intro b hb
    by_contra h
    have := Finset.le_max' (univ.filter fun c => f c ≠ 0) b (by simpa using h)
    exact absurd hb (not_lt.mpr this)
  refine ⟨c, hc, fun a => ?_, fun a b hab he => ?_⟩
  · have h := congrFun (hf.1 a) c
    simp only [tensF, cond_false, tensV_coord, Pi.smul_apply] at h
    simp only [dc_wsh, Bool.false_eq_true, if_false, Pi.sub_apply, Pi.single_apply]
    by_cases hca : c = a
    · subst hca
      simp only [if_true] at h ⊢
      rw [eq_sub_of_add_eq h]
      push_cast
      rw [sub_smul, one_smul]
    · have hac : a ≠ c := Ne.symm hca
      simp only [hca, hac, if_false, add_zero] at h ⊢
      rw [h]
      push_cast
      simp
  · have h := congrFun (hf.2 a b hab he) c
    simp only [tensF, cond_false, tensV_coord, Pi.zero_apply] at h
    by_cases hca : c = a
    · subst hca
      simpa [hmax b hab] using h
    · simpa [hca] using h

theorem dc_top_coord_true {μ : Fin n → ℝ} {f : Fin n → M} (hf : IsKHWVec ε (tensF true E) μ f)
    (h0 : f ≠ 0) : ∃ c, f c ≠ 0 ∧ IsKHWVec ε E (dc_wsh true μ c) (f c) := by
  classical
  have hne : (univ.filter fun c => f c ≠ 0).Nonempty := by
    obtain ⟨c, hc⟩ := Function.ne_iff.mp h0
    exact ⟨c, by simpa using hc⟩
  set c := (univ.filter fun c => f c ≠ 0).min' hne with hcdef
  have hc : f c ≠ 0 := by
    have := Finset.min'_mem _ hne
    simpa using this
  have hmin : ∀ a, a < c → f a = 0 := by
    intro a ha
    by_contra h
    have := Finset.min'_le (univ.filter fun c => f c ≠ 0) a (by simpa using h)
    exact absurd ha (not_lt.mpr this)
  refine ⟨c, hc, fun a => ?_, fun a b hab he => ?_⟩
  · have h := congrFun (hf.1 a) c
    simp only [tensF, cond_true, tensVd_coord, Pi.smul_apply] at h
    simp only [dc_wsh, if_true, Pi.add_apply, Pi.single_apply]
    by_cases hca : c = a
    · subst hca
      simp only [if_true] at h ⊢
      rw [eq_add_of_sub_eq h]
      push_cast
      rw [add_smul, one_smul]
    · have hac : a ≠ c := Ne.symm hca
      simp only [hca, hac, if_false, sub_zero] at h ⊢
      rw [h]
      push_cast
      simp
  · have h := congrFun (hf.2 a b hab he) c
    simp only [tensF, cond_true, tensVd_coord, Pi.zero_apply] at h
    by_cases hcb : c = b
    · subst hcb
      simpa [hmin a hab] using h
    · simpa [hcb] using h

theorem dc_top_coord {dual : Bool} {μ : Fin n → ℝ} {f : Fin n → M} (hf : IsKHWVec ε (tensF dual E) μ f)
    (h0 : f ≠ 0) : ∃ c, f c ≠ 0 ∧ IsKHWVec ε E (dc_wsh dual μ c) (f c) := by
  cases dual
  · exact dc_top_coord_false hf h0
  · exact dc_top_coord_true hf h0

end

section Pi
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D]

abbrev dc_TX (n : ℕ) (D : Type*) [NormedAddCommGroup D] [InnerProductSpace ℂ D] := PiLp 2 (fun _ : Fin n => D)

def dc_eqv : dc_TX n D ≃ₗ[ℂ] (Fin n → D) := WithLp.linearEquiv 2 ℂ (Fin n → D)

theorem dc_eqv_apply (x : dc_TX n D) : dc_eqv x = x.ofLp := rfl

theorem dc_eqv_symm_apply (f : Fin n → D) : (dc_eqv (n := n)).symm f = WithLp.toLp 2 f := rfl

def dc_tensX (dual : Bool) (E : Fin n → Fin n → Module.End ℂ D) (a b : Fin n) : Module.End ℂ (dc_TX n D) :=
  dc_eqv.symm.conj (tensF dual E a b)

theorem dc_tensX_apply (dual : Bool) (E : Fin n → Fin n → Module.End ℂ D) (a b : Fin n) (x : dc_TX n D) :
    dc_tensX dual E a b x = dc_eqv.symm (tensF dual E a b (dc_eqv x)) := by
  simp [dc_tensX, LinearEquiv.conj_apply]

theorem dc_eqv_tensX (dual : Bool) (E : Fin n → Fin n → Module.End ℂ D) (a b : Fin n) (x : dc_TX n D) :
    dc_eqv (dc_tensX dual E a b x) = tensF dual E a b (dc_eqv x) := by
  rw [dc_tensX_apply, LinearEquiv.apply_symm_apply]

theorem dc_tensX_isGlRep {dual : Bool} {E : Fin n → Fin n → Module.End ℂ D} (hE : IsGlRep E) :
    IsGlRep (dc_tensX dual E) := by
  have hT : IsGlRep (tensF dual E) := by
    cases dual
    · exact tensV_isGlRep hE
    · exact tensVd_isGlRep hE
  intro a b c d
  refine LinearMap.ext fun x => dc_eqv.injective ?_
  have h := LinearMap.congr_fun (hT a b c d) (dc_eqv x)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, dc_eqv_tensX, map_sub] at h ⊢
  rw [h]
  split_ifs <;> simp [dc_eqv_tensX]

theorem dc_sum_inner_ite_left (a : Fin n) (u : D) (g : Fin n → D) :
    ∑ i, inner ℂ (if i = a then u else 0) (g i) = inner ℂ u (g a) := by
  rw [Finset.sum_eq_single a (fun i _ hi => by simp [hi]) (by simp)]
  simp

theorem dc_sum_inner_ite_right (b : Fin n) (u : D) (g : Fin n → D) :
    ∑ i, inner ℂ (g i) (if i = b then u else 0) = inner ℂ (g b) u := by
  rw [Finset.sum_eq_single b (fun i _ hi => by simp [hi]) (by simp)]
  simp

theorem dc_tensX_isKUnitary {dual : Bool} {E : Fin n → Fin n → Module.End ℂ D} (hU : IsKUnitary ε E) :
    IsKUnitary ε (dc_tensX dual E) := by
  intro a b hab x y
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [← dc_eqv_apply, dc_eqv_tensX]
  cases dual
  · simp only [tensF, cond_false, tensV_coord, inner_add_left, inner_add_right, Finset.sum_add_distrib,
      hU a b hab]
    congr 1
    simp only [dc_sum_inner_ite_left, dc_sum_inner_ite_right]
  · simp only [tensF, cond_true, tensVd_coord, inner_sub_left, inner_sub_right, Finset.sum_sub_distrib,
      hU a b hab]
    congr 1
    simp only [dc_sum_inner_ite_left, dc_sum_inner_ite_right]

end Pi

end ReciprocityTheory.ChartRestriction.DS.G2

end
end

noncomputable section

open Polynomial Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ} {ε : Fin n → Bool}

theorem dc_aeval_intertwine {Y Z : Type*} [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    (ψ : Y →ₗ[ℂ] Z) (A : Module.End ℂ Y) (B : Module.End ℂ Z) (h : ∀ y, ψ (A y) = B (ψ y)) (p : ℂ[X])
    (y : Y) : ψ (aeval A p y) = aeval B p (ψ y) := by
  first | exact UpperTheory.Reformulated.B.Qk13.dc_aeval_intertwine .. | (apply UpperTheory.Reformulated.B.Qk13.dc_aeval_intertwine <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qk13.dc_aeval_intertwine <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk13.dc_aeval_intertwine <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qk13.dc_aeval_intertwine <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk13.dc_aeval_intertwine <;> first | assumption | infer_instance)

theorem dc_tensSub_fd {M : Type*} [AddCommGroup M] [Module ℂ M] {S : Submodule ℂ M}
    (hS : FiniteDimensional ℂ S) : FiniteDimensional ℂ (tensSub (n := n) S) := by
  let F : (Fin n → S) →ₗ[ℂ] (Fin n → M) := LinearMap.pi fun c => S.subtype ∘ₗ LinearMap.proj c
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range F) fun f hf => ?_
  refine ⟨fun c => ⟨f c, dc_mem_tensSub.mp hf c⟩, ?_⟩
  funext c
  simp [F]

theorem dc_tensSub_mono {M : Type*} [AddCommGroup M] [Module ℂ M] {S T : Submodule ℂ M} (h : S ≤ T) :
    tensSub (n := n) S ≤ tensSub T :=
  fun f hf => dc_mem_tensSub.mpr fun c => h (dc_mem_tensSub.mp hf c)

theorem dc_tens_kStable {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    (dual : Bool) {S : Submodule ℂ M} (hS : IsKStableSub ε E S) (a b : Fin n) (hab : ε a = ε b) :
    ∀ f ∈ tensSub S, tensF dual E a b f ∈ tensSub S := by
  intro f hf
  rw [dc_mem_tensSub] at hf ⊢
  intro c
  cases dual
  · simp only [tensF, cond_false, tensV_coord]
    refine S.add_mem (hS a b hab _ (hf c)) ?_
    split_ifs
    · exact hf b
    · exact S.zero_mem
  · simp only [tensF, cond_true, tensVd_coord]
    refine S.sub_mem (hS a b hab _ (hf c)) ?_
    split_ifs
    · exact hf a
    · exact S.zero_mem

theorem dc_genSub_stable' {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    {V : Submodule ℂ M} (a b : Fin n) {v : M} (hv : v ∈ genSub E V) : E a b v ∈ genSub E V := by
  rw [genSub, Submodule.mem_sInf] at hv ⊢
  intro T hT
  exact hT.2 a b v (hv T hT)

theorem dc_eeF_mem {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    {V : Submodule ℂ M} (dual : Bool) : ∀ f ∈ tensSub (genSub E V), eeF dual E f ∈ tensSub (genSub E V) := by
  intro f hf
  rw [dc_mem_tensSub] at hf ⊢
  intro c
  cases dual
  · simp only [eeF, cond_false, eeV_coord]
    exact Submodule.sum_mem _ fun r _ => dc_genSub_stable' _ _ (hf r)
  · simp only [eeF, cond_true, eeVd_coord]
    exact Submodule.neg_mem _ (Submodule.sum_mem _ fun r _ => dc_genSub_stable' _ _ (hf r))

theorem dc_eeF_comm {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (dual : Bool) (a b : Fin n) (y : Fin n → M) :
    tensF dual E a b (eeF dual E y) = eeF dual E (tensF dual E a b y) := by
  cases dual
  · simpa [tensF, eeF, Module.End.mul_apply] using LinearMap.congr_fun (eeV_comm hE a b) y
  · simpa [tensF, eeF, Module.End.mul_apply] using LinearMap.congr_fun (eeVd_comm hE a b) y

theorem dc_eeF_pow_comm {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (dual : Bool) (a b : Fin n) (j : ℕ) (y : Fin n → M) :
    tensF dual E a b ((eeF dual E ^ j) y) = (eeF dual E ^ j) (tensF dual E a b y) := by
  induction j generalizing y with
  | zero => simp
  | succ j ih => rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, dc_eeF_comm hE]

end ReciprocityTheory.ChartRestriction.DS.G2

end

noncomputable section

open Polynomial Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ} {ε : Fin n → Bool}

theorem dc_core {Xs Ys : Type*} [NormedAddCommGroup Xs] [InnerProductSpace ℂ Xs] [AddCommGroup Ys] [Module ℂ Ys]
    {A : Fin n → Fin n → Module.End ℂ Xs} {B : Fin n → Fin n → Module.End ℂ Ys}
    (hA : IsGlRep A) (hU : IsKUnitary ε A)
    {LX : Submodule ℂ Xs} (hLfd : FiniteDimensional ℂ LX) (hLk : IsKStableSub ε A LX)
    {S0 : Submodule ℂ Ys} (hS0fd : FiniteDimensional ℂ S0) (hS0k : IsKStableSub ε B S0)
    (ψ0 : Ys →ₗ[ℂ] Xs) (hψ0 : ∀ a b, ε a = ε b → ∀ y, ψ0 (B a b y) = A a b (ψ0 y))
    (p : Fin n → ℂ[X]) (hp : ∀ c, ∀ y ∈ S0, aeval (B c c) (p c) y = 0)
    (hgood : ∀ y ∈ S0, ∀ z ∈ LX, ψ0 y - z ∈ LXᗮ → ψ0 y - z ≠ 0 → ∀ μ : Fin n → ℝ,
      (∀ c, (p c).eval (μ c : ℂ) = 0) → IsKHWVec ε A μ (ψ0 y - z) → False) :
    ∀ y ∈ S0, ψ0 y ∈ LX := by
  classical
  haveI : CompleteSpace LX := FiniteDimensional.complete ℂ LX
  have hcomm := fun a b (hab : ε a = ε b) x => starProjection_comm (S := LX) hU hLk hab x
  let ψ : Ys →ₗ[ℂ] Xs := ψ0 - (LX.starProjection : Xs →ₗ[ℂ] Xs) ∘ₗ ψ0
  have hψ : ∀ y, ψ y = ψ0 y - LX.starProjection (ψ0 y) := fun y => rfl
  have hψi : ∀ a b, ε a = ε b → ∀ y, ψ (B a b y) = A a b (ψ y) := by
    intro a b hab y
    rw [hψ, hψ, hψ0 a b hab, hcomm a b hab, map_sub]
  have hRfd : FiniteDimensional ℂ (S0.map ψ) := inferInstance
  have hRk : IsKStableSub ε A (S0.map ψ) := by
    intro a b hab x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨_, hS0k a b hab y hy, hψi a b hab y⟩
  have hR : S0.map ψ = ⊥ := by
    by_contra hne
    obtain ⟨w, hwR, hw0, μ, hμ⟩ := exists_khw hA hU hRfd hRk hne
    obtain ⟨y, hy, rfl⟩ := hwR
    refine hgood y hy _ (Submodule.starProjection_apply_mem _ _)
      (Submodule.sub_starProjection_mem_orthogonal _) hw0 μ (fun c => ?_) hμ
    have h1 := dc_aeval_intertwine ψ (B c c) (A c c) (hψi c c rfl) (p c) y
    rw [hp c y hy, map_zero, dc_aeval_eigen (hμ.1 c)] at h1
    exact (smul_eq_zero.mp h1.symm).resolve_right hw0
  intro y hy
  have h0 : ψ y = 0 := by
    have : ψ y ∈ S0.map ψ := ⟨y, hy, rfl⟩
    rw [hR] at this
    exact this
  rw [hψ, sub_eq_zero] at h0
  rw [h0]
  exact Submodule.starProjection_apply_mem _ _

theorem dc_layer_map {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D} (dual : Bool) (hE : IsGlRep E) (hKU : IsKUnitary ε E)
    (hVfd : FiniteDimensional ℂ V) (hVk : IsKStableSub ε E V) (L : Submodule ℂ D) (hLfd : FiniteDimensional ℂ L)
    (hLk : IsKStableSub ε E L) (hLM : L ≤ genSub E V) (p : Fin n → ℂ[X])
    (hp : ∀ c, ∀ y ∈ tensSub V, aeval (tensF dual E c c) (p c) y = 0)
    (hL : ∀ μ : Fin n → ℝ, (∀ c, (p c).eval (μ c : ℂ) = 0) → ∀ c, ∀ w ∈ genSub E V,
      IsKHWVec ε E (dc_wsh dual μ c) w → w ∈ L)
    (T : Module.End ℂ (Fin n → D)) (hT : ∀ a b, ε a = ε b → ∀ y, T (tensF dual E a b y) = tensF dual E a b (T y))
    (hTM : ∀ y ∈ tensSub V, T y ∈ tensSub (genSub E V)) :
    ∀ y ∈ tensSub V, T y ∈ tensSub L := by
  classical
  have h4 : IsKStableSub ε (dc_tensX dual E) ((tensSub (n := n) L).map ((dc_eqv (n := n) (D := ↥D)).symm : (Fin n → D) →ₗ[ℂ] dc_TX n D)) := by
    intro a b hab x hx
    obtain ⟨f, hf, rfl⟩ := hx
    exact ⟨tensF dual E a b f, dc_tens_kStable dual hLk a b hab f hf, by simp [dc_tensX_apply]⟩
  have h5 : ∀ a b, ε a = ε b → ∀ y, (((dc_eqv (n := n) (D := ↥D)).symm : (Fin n → D) →ₗ[ℂ] dc_TX n D) ∘ₗ T) (tensF dual E a b y) = dc_tensX dual E a b ((((dc_eqv (n := n) (D := ↥D)).symm : (Fin n → D) →ₗ[ℂ] dc_TX n D) ∘ₗ T) y) := by
      intro a b hab y
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [dc_tensX_apply, LinearEquiv.apply_symm_apply, hT a b hab]
  have h3 : FiniteDimensional ℂ ((tensSub (n := n) L).map ((dc_eqv (n := n) (D := ↥D)).symm : (Fin n → D) →ₗ[ℂ] dc_TX n D)) := by
    haveI := dc_tensSub_fd (n := n) hLfd; infer_instance
  have key := dc_core (Xs := dc_TX n ↥D) (Ys := Fin n → ↥D) (A := dc_tensX dual E) (B := tensF dual E)
    (dc_tensX_isGlRep hE) (dc_tensX_isKUnitary hKU) h3 h4 (dc_tensSub_fd hVfd) (dc_tens_kStable dual hVk) _ h5 p hp
  intro y hy
  obtain ⟨z, hz, hze⟩ := key (by
    intro y hy x hx horth hx0 μ hμ hhw
    obtain ⟨zf, hzf, rfl⟩ := hx
    set f : Fin n → D := dc_eqv (((dc_eqv (n := n) (D := ↥D)).symm (T y)) - (dc_eqv (n := n) (D := ↥D)).symm zf) with hfdef
    have hfe : f = T y - zf := by
      rw [hfdef, map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    have hfM : f ∈ tensSub (genSub E V) := by
      rw [hfe]
      exact Submodule.sub_mem _ (hTM y hy) (dc_tensSub_mono hLM hzf)
    have hf0 : f ≠ 0 := by
      intro h
      apply hx0
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [← (dc_eqv (n := n) (D := ↥D)).map_eq_zero_iff]
      exact h
    have hfhw : IsKHWVec ε (tensF dual E) μ f := by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hhw
      refine ⟨fun a => ?_, fun a b hab he => ?_⟩
      · rw [hfdef, ← dc_eqv_tensX, hhw.1 a, map_smul]
      · rw [hfdef, ← dc_eqv_tensX, hhw.2 a b hab he, map_zero]
    obtain ⟨c, hc0, hchw⟩ := dc_top_coord hfhw hf0
    have hcL : f c ∈ L := hL μ hμ c _ (dc_mem_tensSub.mp hfM c) hchw
    have hsing : ((dc_eqv (n := n) (D := ↥D)).symm (Pi.single c (f c)) : dc_TX n D) ∈
        (tensSub (n := n) L).map ((dc_eqv (n := n) (D := ↥D)).symm : (Fin n → D) →ₗ[ℂ] dc_TX n D) := by
      refine ⟨Pi.single c (f c), dc_mem_tensSub.mpr fun i => ?_, rfl⟩
      rw [Pi.single_apply]
      split_ifs with h
      · subst h; exact hcL
      · exact L.zero_mem
    have h0 := Submodule.inner_right_of_mem_orthogonal hsing horth
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h0
    have h0' : inner ℂ (f c) (f c) = 0 := by
      rw [PiLp.inner_apply, Finset.sum_eq_single c (fun i _ hi => by simp [dc_eqv_symm_apply, hi]) (by simp)] at h0
      simpa [hfdef, dc_eqv_symm_apply, dc_eqv_apply] using h0
    exact hc0 (inner_self_eq_zero.mp h0')) y hy
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hze
  have : z = T y := (dc_eqv (n := n) (D := ↥D)).symm.injective hze
  rw [← this]
  exact hz

end ReciprocityTheory.ChartRestriction.DS.G2

end

noncomputable section

open Polynomial Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ} {ε : Fin n → Bool}

theorem dc_ee_fin_stable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D} {lam : Fin n → ℝ} (dual : Bool)
    (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) (hgap : StdGap ε lam) :
    ∃ W : Submodule ℂ (Fin n → D), FiniteDimensional ℂ W ∧ tensSub V ≤ W ∧
      W ≤ tensSub (genSub E V) ∧ ∀ f ∈ W, eeF dual E f ∈ W := by
  classical
  have hKU : IsKUnitary ε E := isKUnitary_of_isInfUnitary hU
  set EE := eeF dual E with hEE
  set S0 : Submodule ℂ (Fin n → D) := tensSub V with hS0
  have hS0fd : FiniteDimensional ℂ S0 := dc_tensSub_fd hV.1
  have hS0k := dc_tens_kStable dual hV.2.1
  have hS0c : ∀ c, ∀ f ∈ S0, tensF dual E c c f ∈ S0 := fun c => hS0k c c rfl
  let p : Fin n → ℂ[X] := fun c => minpoly ℂ ((tensF dual E c c).restrict (hS0c c))
  have hp0 : ∀ c, p c ≠ 0 := fun c => minpoly.ne_zero (Algebra.IsIntegral.isIntegral _)
  have hpS : ∀ c, ∀ f ∈ S0, aeval (tensF dual E c c) (p c) f = 0 := by
    intro c f hf
    have h := dc_aeval_intertwine S0.subtype ((tensF dual E c c).restrict (hS0c c)) (tensF dual E c c)
      (fun y => rfl) (p c) ⟨f, hf⟩
    rw [minpoly.aeval] at h
    simpa using h.symm
  set Λs : Set (Fin n → ℝ) := {μ | ∀ c, (p c).eval (μ c : ℂ) = 0} with hΛs
  have hΛ : Λs.Finite := by
    refine (Set.Finite.pi (t := fun c => {r : ℝ | (p c).eval (r : ℂ) = 0}) fun c => ?_).subset ?_
    · refine ((p c).roots.toFinset.finite_toSet.preimage Complex.ofReal_injective.injOn).subset ?_
      intro r hr
      simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
      exact (Polynomial.mem_roots (hp0 c)).mpr hr
    · intro μ hμ c _
      exact hμ c
  choose kf hkf using fun μ => khw_mem_layer hE hU hV hc hgap μ
  let g : (Fin n → ℝ) → ℕ := fun μ => univ.sup fun c => kf (dc_wsh dual μ c)
  obtain ⟨K0, hK0⟩ := (hΛ.image g).bddAbove
  have hKb : ∀ μ ∈ Λs, ∀ c, kf (dc_wsh dual μ c) ≤ K0 := fun μ hμ c =>
    (Finset.le_sup (f := fun c => kf (dc_wsh dual μ c)) (mem_univ c)).trans (hK0 ⟨μ, hμ, rfl⟩)
  set L := layer ε E V K0 with hL
  have hLfd : FiniteDimensional ℂ L := finiteDimensional_layer hV.1 K0
  have hLk : IsKStableSub ε E L := layer_kStable hE hV.2.1 K0
  have hLM : tensSub (n := n) L ≤ tensSub (genSub E V) := dc_tensSub_mono (layer_le_genSub K0)
  have hpowM : ∀ j, ∀ f ∈ tensSub (genSub E V), (EE ^ j) f ∈ tensSub (genSub E V) := by
    intro j
    induction j with
    | zero => intro f hf; simpa using hf
    | succ j ih => intro f hf; rw [pow_succ', Module.End.mul_apply]; exact dc_eeF_mem dual _ (ih f hf)
  haveI hLfd' : FiniteDimensional ℂ (tensSub (n := n) L) := dc_tensSub_fd hLfd
  have hVg : V ≤ genSub E V := by unfold genSub; exact le_sInf fun T hT => hT.1
  have key : ∀ j, S0.map (EE ^ j) ≤ tensSub L := by
    intro j x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact dc_layer_map dual hE hKU hV.1 hV.2.1 L hLfd hLk (layer_le_genSub K0) p hpS
      (fun μ hμ c w hw hhw => layer_mono (hKb μ hμ c) (hkf _ w hw hhw))
      (EE ^ j) (fun a b _ y => (dc_eeF_pow_comm hE dual a b j y).symm)
      (fun y hy => hpowM j y (dc_tensSub_mono hVg hy)) y hy
  let W : Submodule ℂ (Fin n → D) := ⨆ j, S0.map (EE ^ j)
  have hWL : W ≤ tensSub L := iSup_le key
  refine ⟨W, Submodule.finiteDimensional_of_le hWL, ?_, hWL.trans hLM, ?_⟩
  · have : S0.map (EE ^ 0) ≤ W := le_iSup (fun j => S0.map (EE ^ j)) 0
    simpa [pow_zero, Module.End.one_eq_id, Submodule.map_id] using this
  · intro f hf
    induction hf using Submodule.iSup_induction' with
    | mem j x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      refine le_iSup (fun j => S0.map (EE ^ j)) (j + 1) ⟨y, hy, ?_⟩
      rw [pow_succ', Module.End.mul_apply]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact W.add_mem hx hy

end ReciprocityTheory.ChartRestriction.DS.G2

end

noncomputable section

open Polynomial Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ} {ε : Fin n → Bool}

theorem dc_adjSign_mul_swap (a b : Fin n) : adjSign ε a b * adjSign ε b a = 1 := by
  unfold adjSign
  by_cases h : ε a = ε b
  · simp [h]
  · have h' : ¬ ε b = ε a := fun e => h e.symm
    simp [h, h']

theorem dc_tens_genSub_stable {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    {V : Submodule ℂ M} (dual : Bool) (a b : Fin n) :
    ∀ f ∈ tensSub (genSub E V), tensF dual E a b f ∈ tensSub (genSub E V) :=
  dc_tens_kStable (ε := fun _ => true) dual (fun a b _ v hv => dc_genSub_stable' a b hv) a b rfl

theorem dc_casimir_tensF_apply {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (dual : Bool) {c0 : ℂ} {S : Submodule ℂ M} (hc : ∀ v ∈ S, casimir E v = c0 • v) :
    ∀ f ∈ tensSub S, casimir (tensF dual E) f = (c0 + n) • f + (2 : ℂ) • eeF dual E f := by
  intro f hf
  have hd : diagOp (n := n) (casimir E) f = c0 • f := by
    funext c
    rw [diagOp_coord, hc _ (dc_mem_tensSub.mp hf c), Pi.smul_apply]
  cases dual
  · have h := LinearMap.congr_fun (casimir_tensV (n := n) hE) f
    simp only [tensF, eeF, cond_false, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply] at h ⊢
    rw [h, hd, add_smul]
  · have h := LinearMap.congr_fun (casimir_tensVd (n := n) hE) f
    simp only [tensF, eeF, cond_true, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply] at h ⊢
    rw [h, hd, add_smul]

theorem dc_eeF_Qsymm {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    {V : Submodule ℂ M} (hE : IsGlRep E) (dual : Bool) {c0 : ℝ}
    (hc : ∀ v ∈ genSub E V, casimir E v = (c0 : ℂ) • v) {Q : (Fin n → M) →ₗ⋆[ℂ] (Fin n → M) →ₗ[ℂ] ℂ}
    (hadj : ∀ a b, ∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V),
      Q (tensF dual E a b f) g = adjSign ε a b * Q f (tensF dual E b a g)) :
    ∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V),
      Q (eeF dual E f) g = Q f (eeF dual E g) := by
  intro f hf g hg
  have hΩ : Q (casimir (tensF dual E) f) g = Q f (casimir (tensF dual E) g) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hadj a b _ (dc_tens_genSub_stable dual b a f hf) g hg,
      hadj b a f hf _ (dc_tens_genSub_stable dual b a g hg), ← mul_assoc, dc_adjSign_mul_swap, one_mul]
  have e : ∀ x ∈ tensSub (genSub E V), eeF dual E x =
      (1 / 2 : ℂ) • (casimir (tensF dual E) x - (((c0 : ℝ) : ℂ) + n) • x) := by
    intro x hx
    rw [dc_casimir_tensF_apply hE dual hc x hx, add_sub_cancel_left, smul_smul]
    norm_num
  rw [e f hf, e g hg]
  simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_sub, LinearMap.sub_apply, map_smul, hΩ,
    smul_eq_mul]
  simp [Complex.conj_ofReal, map_ofNat]

end ReciprocityTheory.ChartRestriction.DS.G2

end
end

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

open MeasureTheory

theorem dc_ee_nodal (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) :
    ∃ B : Finset ℝ, ∀ f ∈ tensSub (genSub E V),
      Polynomial.aeval (eeF dual E) (Lagrange.nodal (dc_cplxPts B) id) f = 0 := by
  classical
  have hE : IsGlRep E := hD.glRep
  have hU : IsInfUnitary ε E := isInfUnitary_of_isDerivedOn hσ hD
  obtain ⟨Q, -, hpos, hadj, -⟩ := tens_unitarize dual hσ hD hgap hV hc hVK hW
  obtain ⟨W, hWfd, hVW, hWM, hWst⟩ := dc_ee_fin_stable dual hE hU hV hc hgap
  have hsym := dc_eeF_Qsymm hE dual (casimir_genSub hE hc) hadj
  obtain ⟨B, hB⟩ := dc_symm_nodal hpos hsym (dc_eeF_mem dual) hWM hWfd hWst
  refine ⟨B, ?_⟩
  let K0 : Submodule ℂ (Fin n → D) :=
    LinearMap.ker (Polynomial.aeval (eeF dual E) (Lagrange.nodal (dc_cplxPts B) id)) ⊓ tensSub (genSub E V)
  have hle : tensSub (genSub E V) ≤ K0 := by
    refine dc_tens_gen_le dual (fun f hf => ⟨hB f (hVW hf), hWM (hVW hf)⟩) ?_
    intro a b f hf
    refine ⟨?_, dc_tens_genSub_stable dual a b f hf.2⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker] at hf ⊢
    rw [← dc_aeval_intertwine (tensF dual E a b) (eeF dual E) (eeF dual E)
      (fun y => dc_eeF_comm hE dual a b y), hf.1, map_zero]
  exact fun f hf => (hle hf).1

theorem ee_decomp (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) :
    ∃ B : Finset ℝ,
      (∀ f ∈ tensSub (genSub E V), ∃ fb : ℝ → (Fin n → D),
        (∀ b, fb b ∈ tensSub (genSub E V) ∧ eeF dual E (fb b) = ((b : ℝ) : ℂ) • fb b) ∧ f = ∑ b ∈ B, fb b) ∧
      ∀ z : ℂ, ∀ f ∈ tensSub (genSub E V), f ≠ 0 → eeF dual E f = z • f → ∃ b ∈ B, z = ((b : ℝ) : ℂ) := by
  obtain ⟨B, hB⟩ := dc_ee_nodal dual hσ hD hgap hV hc hVK hW
  exact ⟨B, dc_lagrange_decomp (dc_eeF_mem dual) hB, dc_lagrange_eig hB⟩

theorem eigenProj_exists (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) (z : ℂ) :
    ∃ P : Module.End ℂ (Fin n → D), IsGKEndo dual ε σ E (genSub E V) P ∧
      (∀ f ∈ tensSub (genSub E V), P (P f) = P f) ∧
      (∀ f ∈ tensSub (genSub E V), eeF dual E (P f) = z • P f) ∧
      (∀ f ∈ tensSub (genSub E V), eeF dual E f = z • f → P f = f) ∧
      ∀ f ∈ tensSub (genSub E V), ∀ z' : ℂ, z' ≠ z → eeF dual E f = z' • f → P f = 0 := by
  obtain ⟨B, hB⟩ := dc_ee_nodal dual hσ hD hgap hV hc hVK hW
  refine ⟨dc_lagProj (eeF dual E) B z, ?_, dc_lagProj_props (dc_eeF_mem dual) hB z⟩
  unfold dc_lagProj
  split_ifs
  · exact dc_isGKEndo_aeval (isGKEndo_eeF hσ hD V dual) _
  · exact dc_isGKEndo_zero'

end ReciprocityTheory.ChartRestriction.DS.G2
