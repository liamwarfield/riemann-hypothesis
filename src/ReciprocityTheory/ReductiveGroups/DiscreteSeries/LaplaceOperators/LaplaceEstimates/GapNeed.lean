module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.WhittakerZeroStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RightDerivativeToL2
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.ExistsCommutingProjectionImage

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.GapNeed
namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem gapNeed : GapNeedStatement := by
  intro k r ε h hp hq hg
  unfold StepGap at hg
  unfold hNeed S7.q0
  obtain ⟨h1, h2⟩ := hg
  rw [← Nat.cast_min] at h2 ⊢
  have hqr : ((qOf ε : ℕ) : ℝ) - 1 = (r : ℝ) := by rw [hq]; push_cast; ring
  rw [hqr]
  have hm : 1 ≤ min (pOf ε) (qOf ε) := by
    by_contra hc
    have h0 : min (pOf ε) (qOf ε) = 0 := by omega
    rw [h0] at h2
    simp at h2
    linarith [le_max_left (0 : ℝ) (2 * (r : ℝ) * (2 * (r : ℝ) + (k : ℝ) + 1) ^ 2)]
  refine ⟨hm, ?_⟩
  set m := min (pOf ε) (qOf ε) with hmdef
  set N : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hN
  have hN1 : (1 : ℝ) ≤ N := by rw [hN]; norm_cast; omega
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hsq : 1 ≤ Real.sqrt (2 * (m : ℝ)) := Real.one_le_sqrt.mpr (by linarith)
  set s := 8 * Real.sqrt (2 * (m : ℝ)) with hs
  have hs8 : 8 ≤ s := by rw [hs]; linarith
  have hspos : 0 < s := by linarith
  set X := max (2 * N * (m : ℝ)) (2 * (r : ℝ) * N ^ 2) with hX
  have hX1 : 2 * N * m ≤ X := le_max_left _ _
  have hNm : 1 ≤ N * m := by nlinarith
  have hC : s * (4 * X + 1) < h := by
    have h4 := h2
    rw [lt_sub_iff_add_lt, lt_div_iff₀ hspos] at h4
    linarith
  have hsX : 8 * X ≤ s * X := by nlinarith
  refine max_lt (by linarith) (max_lt ?_ hC)
  nlinarith

end ReciprocityTheory.ChartRestriction.DS.Lap
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.ListProdMemOfForall
namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

namespace CapelliMinorMembership

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem list_prod_mem_of_forall {S : Submodule ℂ M} :
    ∀ (l : List (Module.End ℂ M)), (∀ f ∈ l, ∀ x ∈ S, f x ∈ S) → ∀ x ∈ S, l.prod x ∈ S
  | [], _, x, hx => by simpa using hx
  | f :: l, h, x, hx => by
    rw [List.prod_cons, Module.End.mul_apply]
    exact h f List.mem_cons_self _
      (list_prod_mem_of_forall l (fun g hg => h g (List.mem_cons_of_mem _ hg)) x hx)

theorem capEntry_mem {n : ℕ} {E : Fin n → Fin n → Module.End ℂ M} {S : Submodule ℂ M}
    (hS : ∀ a b, ∀ x ∈ S, E a b x ∈ S) (t : ℂ) (a b : Fin n) :
    ∀ x ∈ S, Capelli.capEntry E t a b x ∈ S := by
  intro x hx
  unfold Capelli.capEntry
  rw [LinearMap.add_apply]
  refine S.add_mem (hS a b x hx) ?_
  split_ifs
  · simpa using S.smul_mem t hx
  · simp

theorem cminor_mem {n p : ℕ} {E : Fin n → Fin n → Module.End ℂ M} {S : Submodule ℂ M}
    (hS : ∀ a b, ∀ x ∈ S, E a b x ∈ S) (R C : Fin p → Fin n) (t : ℂ) :
    ∀ x ∈ S, Capelli.cminor E R C t x ∈ S := by
  intro x hx
  unfold Capelli.cminor
  rw [LinearMap.sum_apply]
  refine S.sum_mem fun σ _ => ?_
  rw [LinearMap.smul_apply]
  refine S.smul_of_tower_mem _ ?_
  refine list_prod_mem_of_forall _ ?_ x hx
  intro f hf
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hf
  exact capEntry_mem hS _ _ _

end CapelliMinorMembership

open CapelliMinorMembership

theorem eig : EigStatement := by
  intro M _ _ m E S ω y β v hE hS hC hv
  have h0 : Capelli.capelliC E (ω : ℂ) v = 0 := hC v hv
  have eV : Capelli.eeV E = LemK.eeV E := by
    ext f d; simp [Capelli.eeV, LemK.eeV, LemK.prj]
  have eVd : Capelli.eeVd E = LemK.eeVd E := by
    ext f d; simp [Capelli.eeVd, LemK.eeVd, LemK.prj]
  constructor
  · refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Submodule.mem_pi]
      intro d _
      unfold Capelli.nnPlus
      exact S.sum_mem fun c _ => S.smul_mem _ (cminor_mem hS _ _ _ v hv)
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, ← eV,
        Capelli.capelliAPlus M m E y (ω : ℂ) v hE h0]
      simp
  · refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Submodule.mem_pi]
      intro d _
      unfold Capelli.nnMinus
      exact S.sum_mem fun c _ => S.smul_mem _ (cminor_mem hS _ _ _ v hv)
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, ← eVd,
        Capelli.capelliAMinus M m E β (ω : ℂ) v hE h0]
      simp

end ReciprocityTheory.ChartRestriction.DS.Lap
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.QuotMA
noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.TransportMapLinear

open ReciprocityTheory.ChartRestriction.DS

section Cls

variable {n : ℕ}

theorem toL2_congr_on_unitary_bis (ε : Fin n → Bool) {F G : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ g ∈ UJset ε, F g = G g) : toL2 ε F = toL2 ε G := by
  have e : (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) = fun g => G (Formalism.MainNotions.S.umat g) :=
    funext fun g => h _ (unitary_matrix_mem_set ε g)
  by_cases hF : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)
  · have hG : MemLp (fun g : Formalism.REAL.UJ ε => G (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := e ▸ hF
    rw [toL2_eq_memLp_toLp ε hF, toL2_eq_memLp_toLp ε hG, MemLp.toLp_eq_toLp_iff]
    exact Filter.EventuallyEq.of_eq e
  · have hG : ¬ MemLp (fun g : Formalism.REAL.UJ ε => G (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := e ▸ hF
    rw [toL2_eq_zero_of_not_memLp ε hF, toL2_eq_zero_of_not_memLp ε hG]

theorem exists_lin {Y : Type*} [AddCommGroup Y] [Module ℂ Y] (ε : Fin n → Bool)
    (A : Fin n → Fin n → Module.End ℂ Y) (G : Submodule ℂ Y)
    (L : Y →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (hsm : ∀ f ∈ G, IsSmoothL2 ε (L f))
    (hG : ∀ a b, ∀ f ∈ G, A a b f ∈ G)
    (hder : ∀ f ∈ G, ∀ a b, ∀ g ∈ UJset ε, Formalism.REAL.Eab ε a b (L f) g = L (A a b f) g) :
    ∃ T : Y →ₗ[ℂ] smD ε (rreg ε), (∀ f ∈ G, (T f : L2 ε) = toL2 ε (L f)) ∧
      ∀ a b, ∀ f ∈ G, T (A a b f) = smE ε (rreg ε) a b (T f) := by
  classical
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl G
  let p := G.projectionOnto q hq
  have hpG : ∀ f ∈ G, ((p f : G) : Y) = f := fun f hf => by
    exact congrArg Subtype.val (Submodule.projectionOnto_apply_left hq ⟨f, hf⟩)
  have hmem : ∀ f : Y, toL2 ε (L (p f)) ∈ smD ε (rreg ε) := fun f => toL2_mem_smD_of_isSmoothL2 (hsm _ (p f).2)
  have hL2 : ∀ f : Y, MemLp (fun g : Formalism.REAL.UJ ε => L (p f) (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) :=
    fun f => (hsm _ (p f).2).2 []
  let T : Y →ₗ[ℂ] smD ε (rreg ε) :=
    { toFun := fun f => ⟨toL2 ε (L (p f)), hmem f⟩
      map_add' := fun f g => by
        apply Subtype.ext
        simp only [Submodule.coe_add]
        rw [map_add (f := _), Submodule.coe_add, map_add (f := _)]
        exact toL2_add_smooth ε (hL2 f) (hL2 g)
      map_smul' := fun c f => by
        apply Subtype.ext
        simp only [Submodule.coe_smul, RingHom.id_apply]
        rw [map_smul, Submodule.coe_smul, map_smul]
        exact toL2_smul_smooth ε c _ }
  have hT : ∀ f ∈ G, (T f : L2 ε) = toL2 ε (L f) := fun f hf => by
    show toL2 ε (L (p f)) = _
    rw [hpG f hf]
  refine ⟨T, hT, fun a b f hf => ?_⟩
  have e1 : T f = ⟨toL2 ε (L f), toL2_mem_smD_of_isSmoothL2 (hsm f hf)⟩ := Subtype.ext (hT f hf)
  apply Subtype.ext
  rw [hT _ (hG a b f hf), e1, rightDerivative_toL2 (hsm f hf) a b]
  exact toL2_congr_on_unitary_bis ε fun g hg => (hder f hf a b g hg).symm

end Cls

section Lin

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}

def tMapDL (σ : Mat k r → (H →L[ℂ] H)) (x₁ : Fin (2 * r + k + 1) → ℂ) (x₀ : Mat k r) (w : H) :
    (Fin (2 * r + k + 1) → D) →ₗ[ℂ] (Mat k r → ℂ) where
  toFun f := tMapD σ x₁ x₀ w (fun c => ((f c : D) : H))
  map_add' f g := by
    funext x
    simp only [tMapD, coefX, Pi.add_apply, Submodule.coe_add, map_add (f := _), inner_add_right, mul_add,
      Finset.sum_add_distrib]
  map_smul' c f := by
    funext x
    simp only [tMapD, coefX, Pi.smul_apply, Submodule.coe_smul, map_smul, inner_smul_right,
      RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring

end Lin

section Line

universe u

variable {n : ℕ} {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem line (hU : IsKUnitary ε E) (X : Submodule ℂ (Fin n → D)) (Λ : Fin n → ℝ)
    (hXk : ∀ y ∈ X, ∃ S : Submodule ℂ (Fin n → D), S ≤ X ∧ FiniteDimensional ℂ S ∧
      IsKStableSub ε (LemK.tensVd E) S ∧ y ∈ S)
    (hK2 : ∀ f₁ f₂ : Fin n → D, f₁ ∈ X → f₂ ∈ X → IsKHWVec ε (LemK.tensVd E) Λ f₁ →
      IsKHWVec ε (LemK.tensVd E) Λ f₂ → ∃ c₁ c₂ : ℂ, (c₁ ≠ 0 ∨ c₂ ≠ 0) ∧ c₁ • f₁ + c₂ • f₂ = 0) :
    ∃ ys ∈ X, ∀ (Y : Type u) [AddCommGroup Y] [Module ℂ Y] (B : Fin n → Fin n → Module.End ℂ Y)
      (ψ : (Fin n → D) →ₗ[ℂ] Y), (∀ a b, ε a = ε b → ∀ x ∈ X, ψ (LemK.tensVd E a b x) = B a b (ψ x)) →
      ∀ y ∈ X.map ψ, IsKHWVec ε B Λ y → ∃ c : ℂ, y = c • ψ ys := by
  classical

  have hlift : ∀ (Y : Type u) [AddCommGroup Y] [Module ℂ Y] (B : Fin n → Fin n → Module.End ℂ Y)
      (ψ : (Fin n → D) →ₗ[ℂ] Y), (∀ a b, ε a = ε b → ∀ x ∈ X, ψ (LemK.tensVd E a b x) = B a b (ψ x)) →
      ∀ y ∈ X.map ψ, IsKHWVec ε B Λ y → ∃ x ∈ X, IsKHWVec ε (LemK.tensVd E) Λ x ∧ ψ x = y := by
    intro Y _ _ B ψ hψ y hy hyK
    obtain ⟨x₀, hx₀, rfl⟩ := Submodule.mem_map.1 hy
    obtain ⟨S, hSX, hfd, hSk, hx₀S⟩ := hXk x₀ hx₀
    obtain ⟨x, hxS, hxK, hx⟩ := LemK.exists_highest_weight_lift_pi hU ψ hfd hSk
      (fun a b hab z hz => hψ a b hab z (hSX hz)) hx₀S hyK
    exact ⟨x, hSX hxS, hxK, hx⟩
  by_cases hex : ∃ ys ∈ X, ys ≠ 0 ∧ IsKHWVec ε (LemK.tensVd E) Λ ys
  · obtain ⟨ys, hys, hys0, hysK⟩ := hex
    refine ⟨ys, hys, fun Y _ _ B ψ hψ y hy hyK => ?_⟩
    obtain ⟨x, hx, hxK, rfl⟩ := hlift Y B ψ hψ y hy hyK
    obtain ⟨c₁, c₂, hc, hsum⟩ := hK2 x ys hx hys hxK hysK
    by_cases h1 : c₁ = 0
    · exfalso
      have h2 : c₂ ≠ 0 := hc.resolve_left (not_not.2 h1)
      rw [h1, zero_smul, zero_add] at hsum
      exact hys0 ((smul_eq_zero.1 hsum).resolve_left h2)
    · refine ⟨-(c₂ / c₁), ?_⟩
      have : x = -(c₂ / c₁) • ys := by
        have h3 : c₁ • x = -(c₂ • ys) := eq_neg_of_add_eq_zero_left hsum
        calc x = c₁⁻¹ • (c₁ • x) := by rw [smul_smul, inv_mul_cancel₀ h1, one_smul]
          _ = -(c₂ / c₁) • ys := by rw [h3, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
      rw [this, map_smul]
  · refine ⟨0, zero_mem _, fun Y _ _ B ψ hψ y hy hyK => ?_⟩
    obtain ⟨x, hx, hxK, rfl⟩ := hlift Y B ψ hψ y hy hyK
    have : x = 0 := by
      by_contra h0
      exact hex ⟨x, hx, h0, hxK⟩
    exact ⟨0, by rw [this, map_zero, zero_smul]⟩

end Line

end ReciprocityTheory.ChartRestriction.DS.Lap.TransportMapLinear
end
end
