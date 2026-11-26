module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Transported
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccDTensKStable

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccDAdj
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccDAdjB
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccDAdjA
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

theorem adjA_high {D : Type*} [AddCommGroup D] [Module ℂ D] {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (M : Submodule ℂ D) (T : Module.End ℂ D) (hT : ∀ y ∈ M, T y ∈ M)
    (Φ : D →ₗ[ℂ] W) (hΦ : ∀ y ∈ M, Φ y = 0 → Φ (T y) = 0) :
    ∃ C : ℝ, ∀ y ∈ M, ∀ θ : ℝ, C < θ → T y = (θ : ℂ) • y → Φ y = 0 := by
  classical
  set TM : Module.End ℂ M := T.restrict hT
  set Φ' : M →ₗ[ℂ] W := Φ.comp M.subtype
  set p : Submodule ℂ M := LinearMap.ker Φ'
  have hp : p ≤ p.comap TM := by
    intro y hy
    simp only [Submodule.mem_comap, p, LinearMap.mem_ker, Φ', LinearMap.comp_apply,
      Submodule.subtype_apply] at hy ⊢
    exact hΦ y y.2 hy
  set Tb : Module.End ℂ (M ⧸ p) := p.mapQ p TM hp
  have : FiniteDimensional ℂ (LinearMap.range Φ') := inferInstance
  have : FiniteDimensional ℂ (M ⧸ p) := LinearEquiv.finiteDimensional Φ'.quotKerEquivRange.symm
  have hfin := Module.End.finite_hasEigenvalue Tb
  refine ⟨∑ μ ∈ hfin.toFinset, ‖μ‖, fun y hy θ hθ hTy => ?_⟩
  by_contra hne
  have hq : Submodule.Quotient.mk (p := p) (⟨y, hy⟩ : M) ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero]
    exact hne
  have hTb : Tb (Submodule.Quotient.mk (⟨y, hy⟩ : M)) = (θ : ℂ) • Submodule.Quotient.mk (⟨y, hy⟩ : M) := by
    rw [Submodule.mapQ_apply, ← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext hTy
  have hev : Tb.HasEigenvalue (θ : ℂ) :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 hTb, hq⟩
  have hmem : (θ : ℂ) ∈ hfin.toFinset := hfin.mem_toFinset.2 hev
  have hle : ‖(θ : ℂ)‖ ≤ ∑ μ ∈ hfin.toFinset, ‖μ‖ :=
    Finset.single_le_sum (f := fun μ : ℂ => ‖μ‖) (fun _ _ => norm_nonneg _) hmem
  rw [Complex.norm_real, Real.norm_eq_abs] at hle
  linarith [le_abs_self θ]

theorem adjA_tensF_single {M : Type*} [AddCommGroup M] [Module ℂ M] (dual : Bool)
    (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (y : M) :
    ∃ c' : Fin n, ∃ r : ℂ, tensF dual E a b (Pi.single c y) = Pi.single c (E a b y) + r • (Pi.single c' y : Fin n → M) := by
  classical
  cases dual
  · refine ⟨a, if b = c then 1 else 0, ?_⟩
    funext x
    simp only [tensF, cond_false, tensV_coord, Pi.add_apply, Pi.smul_apply, Pi.single_apply]
    split_ifs <;> simp_all
  · refine ⟨b, if a = c then -1 else 0, ?_⟩
    funext x
    simp only [tensF, cond_true, tensVd_coord, Pi.add_apply, Pi.smul_apply, Pi.single_apply]
    split_ifs <;> simp_all [sub_eq_add_neg]

theorem adjA_single_mem {M : Type*} [AddCommGroup M] [Module ℂ M] {S : Submodule ℂ M} (c : Fin n) {y : M}
    (hy : y ∈ S) : (Pi.single c y : Fin n → M) ∈ tensSub S := by
  classical
  refine Submodule.mem_pi.2 fun x _ => ?_
  rw [Pi.single_apply]
  split_ifs
  · exact hy
  · exact S.zero_mem

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem adjA_rep (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {lam : Fin n → ℝ} {V V' : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) (hV'f : FiniteDimensional ℂ V')
    (hV'k : IsKStableSub ε E V') {ps : (Fin n → D) →ₗ[ℂ] D}
    (hps : ∀ a b, ∀ f ∈ tensSub (genSub E V), ps (tensF dual E a b f) = E a b (ps f))
    {x' : D} (hx' : x' ∈ genSub E V') (c : Fin n) :
    ∃ z ∈ genSub E V, ∀ y ∈ genSub E V, inner ℂ z y = inner ℂ x' (ps (Pi.single c y)) := by
  classical
  have hE := hD.glRep
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  have hUk := isKUnitary_of_isInfUnitary hU
  obtain ⟨m', hm'⟩ := exists_layer_of_mem_genSub hE hV'k hx'
  set L' := layer ε E V' m'
  have hL'f : FiniteDimensional ℂ L' := finiteDimensional_layer hV'f m'
  have hL'k : IsKStableSub ε E L' := layer_kStable hE hV'k m'
  set bs := Module.finBasis ℂ L'
  set Φ : D →ₗ[ℂ] (Fin n × Fin (Module.finrank ℂ L') → ℂ) :=
    LinearMap.pi fun p => (innerₛₗ ℂ (bs p.2 : D)).comp (ps.comp (LinearMap.single ℂ (fun _ => D) p.1))
  have hΦ : ∀ y, ∀ p : Fin n × Fin (Module.finrank ℂ L'), Φ y p = inner ℂ (bs p.2 : D) (ps (Pi.single p.1 y)) :=
    fun y p => rfl

  set P : D → Prop := fun y => ∀ v ∈ L', ∀ c, inner ℂ v (ps (Pi.single c y)) = 0
  have hPΦ : ∀ y, Φ y = 0 → P y := by
    intro y hy v hv c
    have hv' : v = ∑ i, (bs.repr ⟨v, hv⟩ i) • (bs i : D) := by
      have := congrArg Subtype.val (bs.sum_repr ⟨v, hv⟩)
      rw [Submodule.coe_sum] at this
      simpa only [Submodule.coe_smul] using this.symm
    rw [hv', sum_inner]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [inner_smul_left, ← hΦ y (c, i), hy, Pi.zero_apply, mul_zero]
  have hΦP : ∀ y, P y → Φ y = 0 := by
    intro y hy
    funext p
    rw [hΦ, Pi.zero_apply]
    exact hy _ (bs p.2).2 p.1
  have hMk : IsKStableSub ε E (genSub E V) := fun a b _ v hv => closure_E_mem_genSub a b hv
  have hPE : ∀ y ∈ genSub E V, P y → ∀ a b, ε a = ε b → P (E a b y) := by
    intro y hy hPy a b hab v hv c
    obtain ⟨c', r, hcr⟩ := adjA_tensF_single dual E a b c y
    have h1 : ps (Pi.single c (E a b y)) = E a b (ps (Pi.single c y)) - r • ps (Pi.single c' y) := by
      rw [← hps a b _ (adjA_single_mem c hy), hcr, map_add (f := _), map_smul]
      abel
    rw [h1, inner_sub_right, inner_smul_right, hPy v hv c', mul_zero, sub_zero, ← hUk b a hab.symm]
    exact hPy _ (hL'k b a hab.symm v hv) c
  have hPadd : ∀ s : Finset (Fin n), ∀ g : Fin n → D, (∀ q ∈ s, P (g q)) → P (∑ q ∈ s, g q) := by
    intro s g hg v hv c
    have : (Pi.single c (∑ q ∈ s, g q) : Fin n → D) = ∑ q ∈ s, Pi.single c (g q) := by
      funext x
      simp only [Pi.single_apply, Finset.sum_apply]
      split_ifs <;> simp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, map_sum, inner_sum]
    exact Finset.sum_eq_zero fun q hq => hg q hq v hv c
  have hcasP : ∀ y ∈ genSub E V, P y → P (casimirK ε E y) := by
    intro y hy hPy
    simp only [casimirK, LinearMap.sum_apply, Module.End.mul_apply]
    refine hPadd _ _ fun a _ => hPadd _ _ fun b hb => ?_
    have hq' : ε b = ε a := (Finset.mem_filter.1 hb).2
    exact hPE _ (closure_E_mem_genSub _ _ hy) (hPE y hy hPy b a hq') a b hq'.symm
  obtain ⟨C, hC⟩ := adjA_high (genSub E V) (casimirK ε E)
    (fun y hy => casimirK_mem_of_kStable hMk hy) Φ (fun y hy h0 => hΦP _ (hcasP y hy (hPΦ y h0)))
  obtain ⟨K, hK⟩ := coefB_adm hE hU hV hc hgap C
  have hTsym : ∀ x y, inner ℂ (casimirK ε E x) y = inner ℂ x (casimirK ε E y) := casimirK_inner_symm hUk
  set ℓ : D →ₗ[ℂ] ℂ := (innerₛₗ ℂ x').comp (ps.comp (LinearMap.single ℂ (fun _ => D) c))
  obtain ⟨z, hzM, hz⟩ := coefA_toSum hTsym (coefB_locFin hE hV.1 hV.2.1) ℓ C
    (finiteDimensional_layer hV.1 K) (layer_le_genSub K) (fun y hy θ hθ hyθ => hK y hy θ hθ hyθ)
    (fun y hy θ hθ hyθ => hPΦ y (hC y hy θ hθ hyθ) x' hm' c)
  exact ⟨z, hzM, fun y hy => hz y hy⟩

end Rep

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

noncomputable section

open Finset
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

def adjSg (ε : Fin n → Bool) (c : Fin n) : ℂ := if ε c then 1 else -1

theorem adjSg_mul_self (ε : Fin n → Bool) (c : Fin n) : adjSg ε c * adjSg ε c = 1 := by
  unfold adjSg; split_ifs <;> norm_num

theorem adjSg_conj (ε : Fin n → Bool) (c : Fin n) : (starRingEnd ℂ) (adjSg ε c) = adjSg ε c := by
  unfold adjSg; split_ifs <;> simp

theorem adjSign_eq_adjSg (ε : Fin n → Bool) (a b : Fin n) : adjSign ε a b = adjSg ε a * adjSg ε b := by
  unfold adjSign adjSg
  cases ε a <;> cases ε b <;> norm_num

section R

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

def adjR (ε : Fin n → Bool) (M : Submodule ℂ X) (ps : (Fin n → X) →ₗ[ℂ] X) (x : X) (u : Fin n → X) : Prop :=
  u ∈ tensSub M ∧ ∀ c, ∀ y ∈ M, inner ℂ (u c) y = adjSg ε c * inner ℂ x (ps (Pi.single c y))

variable {ε : Fin n → Bool} {M : Submodule ℂ X} {ps : (Fin n → X) →ₗ[ℂ] X}

theorem adjR_inv {x : X} {u : Fin n → X} (h : adjR ε M ps x u) (c : Fin n) {y : X} (hy : y ∈ M) :
    inner ℂ x (ps (Pi.single c y)) = adjSg ε c * inner ℂ (u c) y := by
  rw [h.2 c y hy, ← mul_assoc, adjSg_mul_self, one_mul]

theorem adjR_unique {x : X} {u u' : Fin n → X} (h : adjR ε M ps x u) (h' : adjR ε M ps x u') : u = u' := by
  funext c
  have hm : u c - u' c ∈ M := M.sub_mem (tset_mem.1 h.1 c) (tset_mem.1 h'.1 c)
  have h0 : inner ℂ (u c - u' c) (u c - u' c) = (0 : ℂ) := by
    rw [inner_sub_left, h.2 c _ hm, h'.2 c _ hm, sub_self]
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h0)

theorem adjR_add {x x' : X} {u u' : Fin n → X} (h : adjR ε M ps x u) (h' : adjR ε M ps x' u') :
    adjR ε M ps (x + x') (u + u') := by
  refine ⟨(tensSub M).add_mem h.1 h'.1, fun c y hy => ?_⟩
  rw [Pi.add_apply, inner_add_left, inner_add_left, h.2 c y hy, h'.2 c y hy, mul_add]

theorem adjR_smul {x : X} {u : Fin n → X} (h : adjR ε M ps x u) (r : ℂ) : adjR ε M ps (r • x) (r • u) := by
  refine ⟨(tensSub M).smul_mem r h.1, fun c y hy => ?_⟩
  rw [Pi.smul_apply, inner_smul_left, inner_smul_left, h.2 c y hy]
  ring

theorem adjR_linear {M' : Submodule ℂ X} (hex : ∀ x ∈ M', ∃ u, adjR ε M ps x u) :
    ∃ ι : X →ₗ[ℂ] (Fin n → X), ∀ x ∈ M', adjR ε M ps x (ι x) := by
  classical
  choose g hg using hex
  let φ : M' →ₗ[ℂ] (Fin n → X) :=
    { toFun := fun x => g x.1 x.2
      map_add' := fun x y => (adjR_unique (hg _ (x + y).2) (adjR_add (hg _ x.2) (hg _ y.2))).trans rfl
      map_smul' := fun r x => (adjR_unique (hg _ (r • x).2) (adjR_smul (hg _ x.2) r)).trans rfl }
  obtain ⟨ι, hι⟩ := LinearMap.exists_extend φ
  refine ⟨ι, fun x hx => ?_⟩
  have : ι x = g x hx := LinearMap.congr_fun hι ⟨x, hx⟩
  rw [this]
  exact hg x hx

end R

section Amb

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem adjB_tensF_mem (dual : Bool) {M : Submodule ℂ D} (hME : ∀ a b, ∀ v ∈ M, E a b v ∈ M)
    {u : Fin n → D} (hu : u ∈ tensSub M) (a b : Fin n) : tensF dual E a b u ∈ tensSub M := by
  refine tset_mem.2 fun c => ?_
  have hu' := tset_mem.1 hu
  cases dual
  · simp only [tensF, cond_false, tensV_coord]
    refine M.add_mem (hME a b _ (hu' c)) ?_
    split_ifs
    · exact hu' b
    · exact M.zero_mem
  · simp only [tensF, cond_true, tensVd_coord]
    refine M.sub_mem (hME a b _ (hu' c)) ?_
    split_ifs
    · exact hu' a
    · exact M.zero_mem

theorem adjB_E (dual : Bool) (hU : IsInfUnitary ε E) {M : Submodule ℂ D} (hME : ∀ a b, ∀ v ∈ M, E a b v ∈ M)
    {ps : (Fin n → D) →ₗ[ℂ] D} (hps2 : ∀ a b, ∀ f ∈ tensSub M, ps (tensF dual E a b f) = E a b (ps f))
    {x : D} {u : Fin n → D} (h : adjR ε M ps x u) (a b : Fin n) :
    adjR ε M ps (E a b x) (tensF dual E a b u) := by
  classical
  refine ⟨adjB_tensF_mem dual hME h.1 a b, fun c y hy => ?_⟩
  have hsc : ∀ d, (Pi.single c y : Fin n → D) d ∈ M := tset_mem.1 (adjA_single_mem c hy)
  have e1 := adjSg_mul_self ε c
  rw [hU a b x, ← hps2 b a _ (adjA_single_mem c hy), adjSign_eq_adjSg]
  cases dual
  · have hT : tensF false E b a (Pi.single c y) =
        Pi.single c (E b a y) + Pi.single b ((Pi.single c y : Fin n → D) a) := by
      funext d
      simp only [tensF, cond_false, tensV_coord, Pi.add_apply, Pi.single_apply]
      split_ifs <;> simp_all
    rw [hT, map_add (f := _), inner_add_right, adjR_inv h c (hME b a y hy), adjR_inv h b (hsc a)]
    simp only [tensF, cond_false, tensV_coord, inner_add_left, hU a b (u c) y, adjSign_eq_adjSg]
    by_cases hca : c = a
    · subst hca
      have e2 := adjSg_mul_self ε b
      simp only [Pi.single_eq_same, if_true]
      linear_combination (-(adjSg ε c * adjSg ε b * inner ℂ (u c) (E b c y)) -
        inner ℂ (u b) y * adjSg ε b * adjSg ε b) * e1 + (-inner ℂ (u b) y) * e2
    · have hac : a ≠ c := Ne.symm hca
      simp only [hca, if_false, inner_zero_left, inner_zero_right, add_zero, mul_zero, Pi.single_apply, hac]
      linear_combination (-(adjSg ε a * adjSg ε b * inner ℂ (u c) (E b a y))) * e1
  · have hT : tensF true E b a (Pi.single c y) =
        Pi.single c (E b a y) - Pi.single a ((Pi.single c y : Fin n → D) b) := by
      funext d
      simp only [tensF, cond_true, tensVd_coord, Pi.sub_apply, Pi.single_apply]
      split_ifs <;> simp_all
    rw [hT, map_sub, inner_sub_right, adjR_inv h c (hME b a y hy), adjR_inv h a (hsc b)]
    simp only [tensF, cond_true, tensVd_coord, inner_sub_left, hU a b (u c) y, adjSign_eq_adjSg]
    by_cases hcb : c = b
    · subst hcb
      have e2 := adjSg_mul_self ε a
      simp only [Pi.single_eq_same, if_true]
      linear_combination (-(adjSg ε a * adjSg ε c * inner ℂ (u c) (E c a y)) +
        inner ℂ (u a) y * adjSg ε a * adjSg ε a) * e1 + (inner ℂ (u a) y) * e2
    · have hbc : b ≠ c := Ne.symm hcb
      simp only [hcb, if_false, inner_zero_left, inner_zero_right, sub_zero, mul_zero, Pi.single_apply, hbc]
      linear_combination (-(adjSg ε a * adjSg ε b * inner ℂ (u c) (E b a y))) * e1

theorem adjB_block {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) {c d : Fin n} (h : ε c ≠ ε d) :
    k c d = 0 := by
  have h1 := congrFun (congrFun hk.2 c) d
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
  have key : ∀ s t : Bool, s ≠ t → k c d * (if t = true then 1 else -1) = (if s = true then 1 else -1) * k c d →
      k c d = 0 := by
    intro s t hst h2
    cases s <;> cases t
    · exact absurd rfl hst
    · simp only [Bool.false_eq_true, ↓reduceIte, mul_one, one_mul] at h2
      first | exact h2 | linear_combination h2 / 2 | linear_combination -h2 / 2
    · simp only [Bool.false_eq_true, ↓reduceIte, mul_one, one_mul] at h2
      first | exact h2 | linear_combination h2 / 2 | linear_combination -h2 / 2
    · exact absurd rfl hst
  exact key _ _ h h1

theorem adjB_sgn {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (dual : Bool) (c d : Fin n) :
    (starRingEnd ℂ) (cond dual (star (k c d)) (k c d)) * (adjSg ε c * adjSg ε d) =
      (starRingEnd ℂ) (cond dual (star (k c d)) (k c d)) := by
  by_cases h : ε c = ε d
  · rw [show adjSg ε c * adjSg ε d = 1 by unfold adjSg; rw [h]; split_ifs <;> norm_num, mul_one]
  · rw [adjB_block hk h]
    cases dual <;> simp

theorem adjB_star_Kset {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : kᴴ ∈ Kset ε := by
  refine ⟨?_, ?_⟩
  · simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem hk.1
  · have h := congrArg Matrix.conjTranspose hk.2
    simp only [Matrix.conjTranspose_mul] at h
    have hJ : (Jm ε)ᴴ = Jm ε := by
      rw [Jm, Matrix.diagonal_conjTranspose]
      congr 1
      ext a
      exact adjSg_conj ε a
    rw [hJ] at h
    exact h.symm

theorem adjB_inner (hσ : IsURepOn (UJset ε) σ) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (v w : H) :
    inner ℂ (σ k v) w = inner ℂ v (σ kᴴ w) := by
  have hkU : k ∈ UJset ε := smd_inUJ_of_Kset hk
  have hkhU : kᴴ ∈ UJset ε := smd_inUJ_of_Kset (adjB_star_Kset hk)
  have hkk : k * kᴴ = 1 := by
    have := hk.1
    rw [Matrix.mem_unitaryGroup_iff] at this
    simpa [Matrix.star_eq_conjTranspose] using this
  have hinv : σ k (σ kᴴ w) = w := by
    have := hσ.1.2 k hkU kᴴ hkhU
    rw [hkk, hσ.1.1] at this
    exact (congrArg (fun T : H →L[ℂ] H => T w) this).symm
  conv_lhs => rw [← hinv]
  exact inner_map_map_of_isURep hσ hkU v (σ kᴴ w)

end Amb

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

noncomputable section

open Finset
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

section Amb

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem adjB_K (dual : Bool) (hσ : IsURepOn (UJset ε) σ) {M : Submodule ℂ D}
    (hMK : ∀ k ∈ Kset ε, ∀ x ∈ M, ∃ y ∈ M, (y : H) = σ k x) {ps : (Fin n → D) →ₗ[ℂ] D}
    (hps3 : ∀ k ∈ Kset ε, ∀ f ∈ tensSub M, ∀ f' ∈ tensSub M,
      (fun c => ((f' c : D) : H)) = kDiag dual σ k (fun c => ((f c : D) : H)) →
      ((ps f' : D) : H) = σ k ((ps f : D) : H))
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) {x x'' : D} (hxx : (x'' : H) = σ k (x : H))
    {u : Fin n → D} (h : adjR ε M ps x u) {f' : Fin n → D} (hf' : f' ∈ tensSub M)
    (hff : (fun c => ((f' c : D) : H)) = kDiag dual σ k (fun c => ((u c : D) : H))) :
    adjR ε M ps x'' f' := by
  classical
  refine ⟨hf', fun c y hy => ?_⟩
  have hkh := adjB_star_Kset hk
  obtain ⟨y', hy'M, hy'⟩ := hMK kᴴ hkh y hy
  have hL : inner ℂ (f' c) y = ∑ d, (starRingEnd ℂ) (cond dual (star (k c d)) (k c d)) * inner ℂ (u d) y' := by
    rw [Submodule.coe_inner, show ((f' c : D) : H) = kDiag dual σ k (fun c => ((u c : D) : H)) c from congrFun hff c]
    simp only [kDiag, sum_inner, inner_smul_left]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [adjB_inner hσ hk, ← hy', ← Submodule.coe_inner]
  set g : Fin n → D := fun d => (starRingEnd ℂ) (cond dual (star (k c d)) (k c d)) • y'
  have hg : g ∈ tensSub M := tset_mem.2 fun d => M.smul_mem _ hy'M
  have hgk : (fun d => ((g d : D) : H)) =
      kDiag dual σ kᴴ (fun d => (((Pi.single c y : Fin n → D) d : D) : H)) := by
    funext d
    simp only [kDiag, g, Submodule.coe_smul]
    rw [Finset.sum_eq_single c (fun e _ he => by simp [he]) (by simp)]
    simp only [Pi.single_eq_same, hy']
    congr 1
    cases dual <;> simp [Matrix.conjTranspose_apply]
  have hps := hps3 kᴴ hkh _ (adjA_single_mem c hy) g hg hgk
  have hgsum : g = ∑ d, (starRingEnd ℂ) (cond dual (star (k c d)) (k c d)) • (Pi.single d y' : Fin n → D) := by
    funext e
    simp [g, Finset.sum_apply, Pi.single_apply]
  have hR : inner ℂ x'' (ps (Pi.single c y)) =
      ∑ d, (starRingEnd ℂ) (cond dual (star (k c d)) (k c d)) * (adjSg ε d * inner ℂ (u d) y') := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Submodule.coe_inner, hxx, adjB_inner hσ hk, ← hps, ← Submodule.coe_inner, hgsum, map_sum, inner_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [map_smul, inner_smul_right, adjR_inv h d hy'M]
  rw [hL, hR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  have := adjB_sgn hk dual c d
  linear_combination (-inner ℂ (u d) y') * this

theorem adjB_emb (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {lam lam' : Fin n → ℝ} {V V' : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) (hgap' : StdGap ε lam')
    (hV' : IsKIrrHW ε E (lowK ε lam') V') (hc' : ∀ v ∈ V', casimir E v = (casVal lam' : ℂ) • v)
    (hVK' : ∀ k ∈ Kset ε, ∀ v ∈ V', ∃ w ∈ V', (w : H) = σ k v) {ps : (Fin n → D) →ₗ[ℂ] D}
    (hps1 : ∀ f ∈ tensSub (genSub E V), ps f ∈ genSub E V')
    (hps2 : ∀ a b, ∀ f ∈ tensSub (genSub E V), ps (tensF dual E a b f) = E a b (ps f))
    (hps3 : ∀ k ∈ Kset ε, ∀ f ∈ tensSub (genSub E V), ∀ f' ∈ tensSub (genSub E V),
      (fun c => ((f' c : D) : H)) = kDiag dual σ k (fun c => ((f c : D) : H)) →
      ((ps f' : D) : H) = σ k ((ps f : D) : H))
    (hne : ∃ f ∈ tensSub (genSub E V), ps f ≠ 0) :
    ∃ ι : D →ₗ[ℂ] (Fin n → D), IsGKEmb dual ε σ E (genSub E V) (genSub E V') ι := by
  classical
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  have hME : ∀ a b, ∀ v ∈ genSub E V, E a b v ∈ genSub E V := fun a b v hv => closure_E_mem_genSub a b hv
  have hME' : ∀ a b, ∀ v ∈ genSub E V', E a b v ∈ genSub E V' := fun a b v hv => closure_E_mem_genSub a b hv
  have hMK : ∀ k ∈ Kset ε, ∀ x ∈ genSub E V, ∃ y ∈ genSub E V, (y : H) = σ k x :=
    fun k hk x hx => occD_genSub_K hσ hD hV.1 hV.2.1 hk hx
  have hM'K : ∀ k ∈ Kset ε, ∀ x ∈ genSub E V', ∃ y ∈ genSub E V', (y : H) = σ k x :=
    fun k hk x hx => occD_genSub_K hσ hD hV'.1 hV'.2.1 hk hx
  have hex : ∀ x ∈ genSub E V', ∃ u, adjR ε (genSub E V) ps x u := by
    intro x hx
    choose z hz hzr using fun c => adjA_rep dual hσ hD hgap hV hc hV'.1 hV'.2.1 hps2 hx c
    refine ⟨fun c => adjSg ε c • z c, tset_mem.2 fun c => Submodule.smul_mem _ _ (hz c), fun c y hy => ?_⟩
    rw [inner_smul_left, adjSg_conj, hzr c y hy]
  obtain ⟨ι, hι⟩ := adjR_linear hex
  have hEcl : ∀ a b, ∀ x ∈ genSub E V', ι (E a b x) = tensF dual E a b (ι x) := fun a b x hx =>
    adjR_unique (hι _ (hME' a b x hx)) (adjB_E dual hU hME hps2 (hι x hx) a b)
  have hKcl : ∀ k ∈ Kset ε, ∀ x ∈ genSub E V', ∀ x'' ∈ genSub E V', (x'' : H) = σ k (x : H) →
      (fun c => ((ι x'' c : D) : H)) = kDiag dual σ k (fun c => ((ι x c : D) : H)) := by
    intro k hk x hx x'' hx'' hxx
    choose w hw hwe using fun d => hMK k hk _ (tset_mem.1 (hι x hx).1 d)
    set f' : Fin n → D := fun c => ∑ d, (cond dual (star (k c d)) (k c d)) • w d
    have hf' : f' ∈ tensSub (genSub E V) :=
      tset_mem.2 fun c => Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _ (hw d)
    have hff : (fun c => ((f' c : D) : H)) = kDiag dual σ k (fun c => ((ι x c : D) : H)) := by
      funext c
      simp only [f', kDiag, Submodule.coe_sum, Submodule.coe_smul, hwe]
    rw [adjR_unique (hι x'' hx'') (adjB_K dual hσ hMK hps3 hk hxx (hι x hx) hf' hff)]
    exact hff
  refine ⟨ι, fun x hx => (hι x hx).1, ?_, hEcl, hKcl⟩
  intro x hx hx0
  set N : Submodule ℂ D := genSub E V' ⊓ LinearMap.ker ι
  have hNE : ∀ a b, ∀ y ∈ N, E a b y ∈ N := by
    intro a b y hy
    refine ⟨hME' a b y hy.1, ?_⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hEcl a b y hy.1, LinearMap.mem_ker.1 hy.2, map_zero]
  have hNK : ∀ k ∈ Kset ε, ∀ y ∈ N, ∃ y' ∈ N, (y' : H) = σ k y := by
    intro k hk y hy
    obtain ⟨y', hy'M, hy'⟩ := hM'K k hk y hy.1
    refine ⟨y', ⟨hy'M, ?_⟩, hy'⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    have h1 := hKcl k hk y hy.1 y' hy'M hy'
    rw [LinearMap.mem_ker.1 hy.2] at h1
    funext c
    have h2 := congrFun h1 c
    simp only [kDiag, Pi.zero_apply, ZeroMemClass.coe_zero, map_zero, smul_zero, Finset.sum_const_zero] at h2
    exact Subtype.ext h2
  rcases data_genSub_irred hgap' hσ hD hV' hc' hVK' N inf_le_left hNE hNK with h | h
  · have : x ∈ N := ⟨hx, LinearMap.mem_ker.2 hx0⟩
    rw [h] at this
    exact (Submodule.mem_bot ℂ).1 this
  · exfalso
    obtain ⟨f₀, hf₀, hps0⟩ := hne
    have hm : ps f₀ ∈ N := h ▸ hps1 f₀ hf₀
    have hR := hι _ (hps1 f₀ hf₀)
    rw [LinearMap.mem_ker.1 hm.2] at hR
    have h0 : ∀ c, inner ℂ (ps f₀) (ps (Pi.single c (f₀ c))) = (0 : ℂ) := by
      intro c
      rw [adjR_inv hR c (tset_mem.1 hf₀ c)]
      simp
    apply hps0
    rw [← inner_self_eq_zero (𝕜 := ℂ)]
    calc inner ℂ (ps f₀) (ps f₀) = ∑ c, inner ℂ (ps f₀) (ps (Pi.single c (f₀ c))) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [← inner_sum, ← map_sum, Finset.univ_sum_single]
      _ = 0 := Finset.sum_eq_zero fun c _ => h0 c

end Amb

section Psi

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}
  {v₀ : T.V} {v₀' : T'.V}

theorem occAdj_emb (dual : Bool) (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hgap' : StdGap ε lam') (hP' : IsPsiFor ε lam' T' Ψ') (hv₀' : v₀' ≠ 0)
    {ps : (Fin n → smD ε (rreg ε)) →ₗ[ℂ] smD ε (rreg ε)}
    (hps : occPsOK dual ε (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) (genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀')) ps)
    (hne : ∃ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), ps f ≠ 0) :
    ∃ ι : smD ε (rreg ε) →ₗ[ℂ] (Fin n → smD ε (rreg ε)),
      IsGKEmb dual ε (rreg ε) (smE ε (rreg ε)) (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))
        (genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀')) ι := by
  have hσ := rreg_isURepOn ε
  exact adjB_emb dual hσ (isDerivedOn_smE hσ) hgap (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀) hgap'
    (datumV_isKIrrHW hP' hv₀') (datumV_casimir hP' v₀') (datumV_kStable hP' v₀') hps.1 hps.2.1 hps.2.2 hne

end Psi

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

open MeasureTheory

def coefMap {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (dual : Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (η f : Fin n → H) (g : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ c, inner ℂ (η c) (tensGrp dual σ g f c)

theorem coef_embed (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) (η : Fin n → D) (hη : η ∈ tensSub (genSub E V)) :
    ∀ f ∈ tensSub (genSub E V),
      IsSmoothL2 ε (coefMap dual σ (fun c => ((η c : D) : H)) (fun c => ((f c : D) : H))) ∧
      (∀ a b, ∀ g, Formalism.REAL.inUJ ε g →
        Formalism.REAL.Eab ε a b (coefMap dual σ (fun c => ((η c : D) : H)) (fun c => ((f c : D) : H))) g =
          coefMap dual σ (fun c => ((η c : D) : H)) (fun c => ((tensF dual E a b f c : D) : H)) g) ∧
      ∀ k ∈ Kset ε, ∀ f' ∈ tensSub (genSub E V),
        (fun c => ((f' c : D) : H)) = kDiag dual σ k (fun c => ((f c : D) : H)) →
        ∀ g ∈ UJset ε, coefMap dual σ (fun c => ((η c : D) : H)) (fun c => ((f c : D) : H)) (g * k) =
          coefMap dual σ (fun c => ((η c : D) : H)) (fun c => ((f' c : D) : H)) g := by
  intro f hf
  refine ⟨⟨occA_coef_smooth dual hσ _ _ (fun d => hsm (f d)), fun w => ?_⟩,
    fun a b g hg => occA_coef_Eab dual hσ hD _ f a b hg, ?_⟩
  · refine (occA_coef_memLp dual hσ hW η (tensWord dual E w f) hη (occA_tensWord_mem dual w f hf)).ae_eq ?_
    exact Filter.Eventually.of_forall fun g => (occA_coef_Eword dual hσ hD _ w f g.2).symm
  · intro k hk f' _ hff g hg
    show ∑ c, _ = ∑ c, _
    rw [occA_tensGrp_mul dual hσ hg hk, ← hff]

theorem occ_exists (dual : Bool) {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {T' : S7.KType ε (lowK ε lam')} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}
    {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)} {v₀ : T.V} {v₀' : T'.V}
    (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hgap' : StdGap ε lam') (hP' : IsPsiFor ε lam' T' Ψ') (hv₀' : v₀' ≠ 0)
    {h h' : ℝ} (hh : GapAtLeast ε lam h) (hth : thrS ε < h) (hh' : GapAtLeast ε lam' h') (hth' : thrS ε < h')
    (hpos : ∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive)
    (hpos' : ∀ X, inP ε X → (Ψ' (NormedSpace.exp X)).IsPositive)
    (hW : ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε))
    (s : Fin n) (hlam' : lam' = shiftF dual lam s) :
    ∃ ι : smD ε (rreg ε) →ₗ[ℂ] (Fin n → smD ε (rreg ε)),
      IsGKEmb dual ε (rreg ε) (smE ε (rreg ε)) (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) (genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀')) ι ∧
      ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), eeF dual (smE ε (rreg ε)) (ι x) = poleF dual lam s • ι x := by
  have hB := occB_pairing_ne dual hP hP' hv₀' hpos hpos' (occB_memLp_psi hgap hP hv₀ hW) s hlam'
  obtain ⟨ps, hps, hne⟩ :=
    occC_exists_ps dual hgap hP hv₀ hgap' hP' hv₀' hW (occC_pairing dual hgap hP hv₀ hP' hW hB)
  obtain ⟨ι, hι⟩ := occAdj_emb dual hgap hP hv₀ hgap' hP' hv₀' hps hne
  exact ⟨ι, hι, occD_eeF dual hP hP' s hlam' hι⟩

end ReciprocityTheory.ChartRestriction.DS.G2
