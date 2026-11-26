module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.HasDerivAtExp
open Matrix Filter Topology

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open Formalism.QuantumDeterminants

namespace ExponentialSlopeDerivatives

section Linfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
  Matrix.linftyOpNormedSpace

theorem hasDerivAt_exp {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) X 0 := by
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℂ) X ((0 : ℝ) : ℂ))
  have h2 := h.scomp (x := (0:ℝ)) Complex.ofRealCLM.hasDerivAt
  exact h2.congr_deriv (by simp)

end Linfty

theorem slope_exp {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (slope (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) 0) (𝓝[≠] 0) (𝓝 X) := by
  let _ := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℂ) (n := Fin n) (α := ℂ)
  let _ := Matrix.linftyOpNormedSpace (R := ℝ) (m := Fin n) (n := Fin n) (α := ℂ)
  exact (hasDerivAt_exp X).tendsto_slope

theorem rdv_of_linear {n : ℕ} (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (g X Y : Matrix (Fin n) (Fin n) ℂ)
    (Lf : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ)
    (hf : ∀ t : ℝ, f (g * NormedSpace.exp ((t : ℂ) • X)) = Lf (NormedSpace.exp ((t : ℂ) • Y))) :
    S7.RdV X f g = Lf Y := by
  have hc : Continuous Lf := LinearMap.continuous_of_finiteDimensional Lf
  have hT := (hc.tendsto Y).comp (slope_exp Y)
  have hD : HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (Lf Y) 0 := by
    rw [hasDerivAt_iff_tendsto_slope]
    refine hT.congr (fun t => ?_)
    simp only [Function.comp_apply, slope_def_module, hf]
    rw [LinearMap.map_smul_of_tower, map_sub]
  exact hD.deriv

end ExponentialSlopeDerivatives

end ReciprocityTheory.ChartRestriction.DS.Lap

namespace ReciprocityTheory.ChartRestriction.DS.Lap
namespace ExponentialSlopeDerivatives
open Formalism.QuantumDeterminants

def sg (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if r ≤ i.val ∧ i.val ≤ r + k then i else ⟨2 * r + k - i.val, by omega⟩

theorem sg_val (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    (sg k r i).val = if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val := by
  unfold sg; split_ifs <;> rfl

theorem sg_sg (k r : ℕ) (i : Fin (2 * r + k + 1)) : sg k r (sg k r i) = i := by
  apply Fin.ext; rw [sg_val, sg_val]; split_ifs <;> omega

theorem sg_mid (k r : ℕ) (i : Fin (2 * r + k + 1)) : (sg k r i).val = r + k ↔ i.val = r + k := by
  rw [sg_val]; split_ifs <;> omega

theorem hpk_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = sg k r i then (if i.val = r + k then -1 else 1) else 0 := by
  have key : j = sg k r i ↔ j.val = (if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val) := by
    rw [← sg_val, Fin.ext_iff]
  unfold Hpk
  simp only [key, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mul_self (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [hpk_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, sg_sg, sg_mid]
  by_cases hij : i = j
  · subst hij; split_ifs <;> simp_all
  · have : ¬ j = i := fun h => hij h.symm
    simp [hij, this]

theorem inv_of_UH {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hH : H * H = 1) (hg : gᴴ * H * g = H) :
    g⁻¹ = H * gᴴ * H := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg, hH]

theorem inv_mul_of_UH {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hH : H * H = 1) (hg : gᴴ * H * g = H) :
    g⁻¹ * g = 1 := by
  rw [inv_of_UH hH hg, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg, hH]

theorem herm_UH {n : ℕ} {H s : Matrix (Fin n) (Fin n) ℂ} (hs : sᴴ * H * s = H) (a b : Fin n → ℂ) :
    star (s *ᵥ a) ⬝ᵥ (H *ᵥ (s *ᵥ b)) = star a ⬝ᵥ (H *ᵥ b) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hs]

end ExponentialSlopeDerivatives
end ReciprocityTheory.ChartRestriction.DS.Lap

namespace ReciprocityTheory.ChartRestriction.DS.Lap
namespace ExponentialSlopeDerivatives
open Formalism.QuantumDeterminants

theorem s_fix (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    ∀ s ∈ Sset k r z, s ∈ UH (Hpk k r) ∧ s *ᵥ xOne k r z = xOne k r z := by
  rintro s ⟨h, ⟨hU, hfix, hz⟩, m, ⟨mU, mcol, mmid⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · show (h * m)ᴴ * Hpk k r * (h * m) = Hpk k r
    have hU' : hᴴ * Hpk k r * h = Hpk k r := hU
    have mU' : mᴴ * Hpk k r * m = Hpk k r := mU
    rw [Matrix.conjTranspose_mul]
    calc mᴴ * hᴴ * Hpk k r * (h * m) = mᴴ * (hᴴ * Hpk k r * h) * m := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hU', mU']
  · rw [← Matrix.mulVec_mulVec]
    unfold xOne
    split_ifs with hr
    · have hm : m = 1 := by
        ext i j
        rw [mmid i j (by omega) (by omega) (by omega), Matrix.one_apply]
      rw [hm, Matrix.one_mulVec, hz]
    · have hm : m *ᵥ Pi.single (⟨0, by omega⟩ : Fin (2 * r + k + 1)) (1 : ℂ) =
          Pi.single (⟨0, by omega⟩ : Fin (2 * r + k + 1)) (1 : ℂ) := by
        funext i
        rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply]
        exact mcol ⟨0, by omega⟩ i (Nat.zero_le _)
      rw [hm]
      exact (hfix ⟨0, by omega⟩).1

theorem dot_bound {n : ℕ} (a b : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    ‖a ⬝ᵥ (M *ᵥ b)‖ ≤ ((∑ i, ‖a i‖) * (∑ j, ‖b j‖)) * ∑ i, ∑ j, ‖M i j‖ := by
  have h1 : a ⬝ᵥ (M *ᵥ b) = ∑ i, ∑ j, a i * M i j * b j := by
    simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  rw [h1, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, norm_mul]
  have ha : ‖a i‖ ≤ ∑ i, ‖a i‖ :=
    Finset.single_le_sum (f := fun i => ‖a i‖) (fun i _ => norm_nonneg (a i)) (Finset.mem_univ i)
  have hb : ‖b j‖ ≤ ∑ j, ‖b j‖ :=
    Finset.single_le_sum (f := fun j => ‖b j‖) (fun j _ => norm_nonneg (b j)) (Finset.mem_univ j)
  calc ‖a i‖ * ‖M i j‖ * ‖b j‖ ≤ (∑ i, ‖a i‖) * ‖M i j‖ * (∑ j, ‖b j‖) := by gcongr
    _ = _ := by ring

end ExponentialSlopeDerivatives

open ExponentialSlopeDerivatives Formalism.QuantumDeterminants

theorem mult : MultStatement := by
  intro k r z _
  have hH := hpk_mul_self k r
  refine ⟨?_, ?_, ?_⟩
  · intro y β s hs g hg
    obtain ⟨hsU, hsx⟩ := s_fix k r z s hs
    have hsU' : sᴴ * Hpk k r * s = Hpk k r := hsU
    refine ⟨?_, ?_⟩
    · show star (xOne k r z) ⬝ᵥ (Hpk k r *ᵥ ((s * g) *ᵥ y)) =
        star (xOne k r z) ⬝ᵥ (Hpk k r *ᵥ (g *ᵥ y))
      rw [← Matrix.mulVec_mulVec]
      have := herm_UH hsU' (xOne k r z) (g *ᵥ y)
      rwa [hsx] at this
    · show β ⬝ᵥ ((s * g)⁻¹ *ᵥ xOne k r z) = β ⬝ᵥ (g⁻¹ *ᵥ xOne k r z)
      have hinv : s⁻¹ *ᵥ xOne k r z = xOne k r z := by
        conv_lhs => rw [← hsx]
        rw [Matrix.mulVec_mulVec, inv_mul_of_UH hH hsU', Matrix.one_mulVec]
      rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, hinv]
  · intro y β X g _
    refine ⟨?_, ?_⟩
    · let Lf : Mat k r →ₗ[ℂ] ℂ :=
        { toFun := fun M => star (xOne k r z) ⬝ᵥ (Hpk k r *ᵥ ((g * M) *ᵥ y))
          map_add' := by
            intro A B
            simp [Matrix.mul_add, Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add]
          map_smul' := by
            intro c A
            simp [Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul] }
      rw [rdv_of_linear (cMul k r z y) g X X Lf (fun t => rfl)]
      show star (xOne k r z) ⬝ᵥ (Hpk k r *ᵥ ((g * X) *ᵥ y)) =
        star (xOne k r z) ⬝ᵥ (Hpk k r *ᵥ (g *ᵥ (X *ᵥ y)))
      rw [Matrix.mulVec_mulVec y g X]
    · let Lf : Mat k r →ₗ[ℂ] ℂ :=
        { toFun := fun M => β ⬝ᵥ (M *ᵥ (g⁻¹ *ᵥ xOne k r z))
          map_add' := by
            intro A B
            simp only [Matrix.add_mulVec, dotProduct_add]
          map_smul' := by
            intro c A
            simp [Matrix.smul_mulVec, dotProduct_smul] }
      have hf : ∀ t : ℝ, cMulD k r z β (g * NormedSpace.exp ((t : ℂ) • X)) =
          Lf (NormedSpace.exp ((t : ℂ) • -X)) := by
        intro t
        show β ⬝ᵥ ((g * NormedSpace.exp ((t : ℂ) • X))⁻¹ *ᵥ xOne k r z) =
          β ⬝ᵥ (NormedSpace.exp ((t : ℂ) • -X) *ᵥ (g⁻¹ *ᵥ xOne k r z))
        rw [Matrix.mul_inv_rev, smul_neg, Matrix.exp_neg, ← Matrix.mulVec_mulVec]
      rw [rdv_of_linear (cMulD k r z β) g X (-X) Lf hf]
      show β ⬝ᵥ ((-X) *ᵥ (g⁻¹ *ᵥ xOne k r z)) = -((β ᵥ* X) ⬝ᵥ (g⁻¹ *ᵥ xOne k r z))
      rw [Matrix.neg_mulVec, dotProduct_neg, Matrix.dotProduct_mulVec]
  · intro y β
    set x1 := xOne k r z
    set C1 : ℝ := (∑ i, ‖(star x1 ᵥ* Hpk k r) i‖) * (∑ j, ‖y j‖)
    set C2 : ℝ := (∑ i, ‖(β ᵥ* Hpk k r) i‖) * (∑ j, ‖(Hpk k r *ᵥ x1) j‖)
    refine ⟨max C1 C2, fun g hg => ?_⟩
    have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
    have hS : 0 ≤ ∑ i, ∑ j, ‖g i j‖ :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
    refine ⟨?_, ?_⟩
    · have e : cMul k r z y g = (star x1 ᵥ* Hpk k r) ⬝ᵥ (g *ᵥ y) := by
        show star x1 ⬝ᵥ (Hpk k r *ᵥ (g *ᵥ y)) = _
        rw [Matrix.dotProduct_mulVec]
      rw [e]
      exact (dot_bound _ _ _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hS)
    · have e : cMulD k r z β g = (β ᵥ* Hpk k r) ⬝ᵥ (gᴴ *ᵥ (Hpk k r *ᵥ x1)) := by
        show β ⬝ᵥ (g⁻¹ *ᵥ x1) = _
        rw [inv_of_UH hH hg', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          Matrix.dotProduct_mulVec]
      have hT : ∑ i, ∑ j, ‖gᴴ i j‖ = ∑ i, ∑ j, ‖g i j‖ := by
        simp only [Matrix.conjTranspose_apply, norm_star]
        exact Finset.sum_comm
      rw [e]
      refine (dot_bound _ _ _).trans ?_
      rw [hT]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hS

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

namespace CapelliMinorRestriction

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem cminor_reindex {n n' p : ℕ} (E : Fin n' → Fin n' → Module.End ℂ M) (e : Fin n → Fin n')
    (he : Function.Injective e) (R C : Fin p → Fin n) (x : ℂ) :
    Capelli.cminor (fun a b => E (e a) (e b)) R C x = Capelli.cminor E (e ∘ R) (e ∘ C) x := by
  unfold Capelli.cminor
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 2
  refine List.ofFn_inj.mpr (funext fun j => ?_)
  simp only [Capelli.capEntry, Function.comp_apply, he.eq_iff]

theorem cminor_cast {n p p' : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (h : p = p')
    (R C : Fin p' → Fin n) (x : ℂ) :
    Capelli.cminor E (R ∘ Fin.cast h) (C ∘ Fin.cast h) x = Capelli.cminor E R C x := by
  subst h
  rfl

theorem ofFn_prod_intertwine (S : Submodule ℂ M) :
    ∀ (p : ℕ) (f : Fin p → Module.End ℂ S) (g : Fin p → Module.End ℂ M),
      (∀ j, S.subtype ∘ₗ f j = g j ∘ₗ S.subtype) →
      S.subtype ∘ₗ (List.ofFn f).prod = (List.ofFn g).prod ∘ₗ S.subtype
  | 0, f, g, _ => by ext; simp
  | p + 1, f, g, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_eq_comp,
      Module.End.mul_eq_comp, ← LinearMap.comp_assoc, h 0, LinearMap.comp_assoc,
      ofFn_prod_intertwine S p (fun j => f j.succ) (fun j => g j.succ) (fun j => h j.succ),
      LinearMap.comp_assoc]

def resE {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (S : Submodule ℂ M)
    (hS : ∀ a b, ∀ x ∈ S, E a b x ∈ S) (a b : Fin n) : Module.End ℂ S :=
  (E a b).restrict (hS a b)

theorem capEntry_resE {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (S : Submodule ℂ M)
    (hS : ∀ a b, ∀ x ∈ S, E a b x ∈ S) (t : ℂ) (a b : Fin n) :
    S.subtype ∘ₗ Capelli.capEntry (resE E S hS) t a b = Capelli.capEntry E t a b ∘ₗ S.subtype := by
  ext m
  simp only [Capelli.capEntry, LinearMap.comp_apply, LinearMap.add_apply, map_add (f := _), resE,
    Submodule.subtype_apply, LinearMap.coe_restrict_apply]
  split_ifs <;> simp

theorem cminor_resE {n p : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (S : Submodule ℂ M)
    (hS : ∀ a b, ∀ x ∈ S, E a b x ∈ S) (R C : Fin p → Fin n) (x : ℂ) (m : S) :
    ((Capelli.cminor (resE E S hS) R C x m : S) : M) = Capelli.cminor E R C x (m : M) := by
  unfold Capelli.cminor
  simp only [LinearMap.sum_apply, Submodule.coe_sum, LinearMap.smul_apply,
    Submodule.coe_smul_of_tower]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  exact congrArg (fun f => f m) (ofFn_prod_intertwine S p _ _ (fun j => capEntry_resE E S hS _ _ _))

theorem isGlRep_resE {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (S : Submodule ℂ M)
    (hS : ∀ a b, ∀ x ∈ S, E a b x ∈ S) (hE : IsGlRep E) : IsGlRep (resE E S hS) := by
  intro a b c d
  ext m
  have := congrArg (fun f => f (m : M)) (hE a b c d)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
  simp only [LinearMap.sub_apply, Module.End.mul_apply, resE, Submodule.coe_sub,
    LinearMap.coe_restrict_apply]
  rw [this]
  split_ifs <;> simp [resE, LinearMap.coe_restrict_apply]

end CapelliMinorRestriction

end ReciprocityTheory.ChartRestriction.DS.Lap

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

namespace CapelliMinorRestriction

section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem cont_of_smoothOnG {n : ℕ} {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hf : Formalism.REAL.SmoothOnG ε f) : ContinuousOn f (UJset ε) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  have hFc : ContinuousAt F g₀ := (hF.continuousOn).continuousAt (hU.mem_nhds hgU)
  refine (hFc.continuousWithinAt (s := UJset ε)).congr_of_eventuallyEq ?_ (hfF g₀ hgU hg₀)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hU.mem_nhds hgU)] with g hg hgU'
  exact hfF g hgU' hg

end

variable {k r : ℕ}

theorem cJ_transport (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r)
    (hP : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r) (x1 y : Fin (2 * r + k + 1) → ℂ) (G : Mat k r) :
    cJ ε (P *ᵥ x1) y (P * G * P⁻¹) = star x1 ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ (G *ᵥ (P⁻¹ *ᵥ y))) := by
  have e1 : (P * G * P⁻¹) *ᵥ y = P *ᵥ (G *ᵥ (P⁻¹ *ᵥ y)) := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  unfold cJ Formalism.QuantumDeterminants.herm
  rw [e1, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [← hP]
  rfl

theorem cJ_sinv (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r)
    (hP : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r) (z y : Fin (2 * r + k + 1) → ℂ) (s x : Mat k r)
    (hs : s ∈ Formalism.QuantumDeterminants.Sset k r z) :
    cJ ε (xJ P z) y (P * (s * x) * P⁻¹) = cJ ε (xJ P z) y (P * x * P⁻¹) := by
  obtain ⟨hsU, hsx⟩ := ExponentialSlopeDerivatives.s_fix k r z s hs
  have hsU' : sᴴ * Formalism.QuantumDeterminants.Hpk k r * s = Formalism.QuantumDeterminants.Hpk k r := hsU
  unfold xJ
  rw [cJ_transport ε P hP, cJ_transport ε P hP, ← Matrix.mulVec_mulVec]
  have := ExponentialSlopeDerivatives.herm_UH hsU' (xOne k r z) (x *ᵥ (P⁻¹ *ᵥ y))
  rwa [hsx] at this

theorem ae_S {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW) (hN : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) :
    ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Sset k r z := by
  have := hW.1
  have := hN.1
  have h1 : ∀ᵐ x ∂μW, Matrix.of x ∈ Formalism.QuantumDeterminants.UWset k r z :=
    (measure_eq_zero_iff_ae_notMem.mp hW.2.2.1).mono fun x hx => not_not.mp hx
  have h2 : ∀ᵐ x ∂μN, Matrix.of x ∈ Formalism.QuantumDeterminants.Nset k r :=
    (measure_eq_zero_iff_ae_notMem.mp hN.2.2.1).mono fun x hx => not_not.mp hx
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae h1, Measure.quasiMeasurePreserving_snd.ae h2]
    with p hp1 hp2
  exact ⟨_, hp1, _, hp2, rfl⟩

theorem tMap_single {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ε : Fin (2 * r + k + 1) → Bool) (σ : Mat k r → (H →L[ℂ] H)) (x1 : Fin (2 * r + k + 1) → ℂ)
    (x₀ : Mat k r) (w : H) (d : Fin (2 * r + k + 1)) (m : H) (G : Mat k r) :
    tMap ε σ x1 x₀ w (Pi.single d m) G = cJ ε x1 (Pi.single d 1) G * coefX σ x₀ w m G := by
  unfold tMap
  rw [Finset.sum_eq_single d]
  · simp
  · intro c _ hc
    simp [Pi.single_eq_of_ne hc, coefX]
  · simp

theorem tMap_sum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ε : Fin (2 * r + k + 1) → Bool) (σ : Mat k r → (H →L[ℂ] H)) (x1 : Fin (2 * r + k + 1) → ℂ)
    (x₀ : Mat k r) (w : H) (f : Fin (2 * r + k + 1) → H) (G : Mat k r) :
    tMap ε σ x1 x₀ w f G = ∑ d, tMap ε σ x1 x₀ w (Pi.single d (f d)) G := by
  rw [Finset.sum_congr rfl fun d _ => tMap_single ε σ x1 x₀ w d (f d) G]
  rfl

theorem coefX_add {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H))
    (x₀ : Mat k r) (w m₁ m₂ : H) (G : Mat k r) :
    coefX σ x₀ w (m₁ + m₂) G = coefX σ x₀ w m₁ G + coefX σ x₀ w m₂ G := by
  simp [coefX, inner_add_right]

theorem coefX_smul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H))
    (x₀ : Mat k r) (w m : H) (a : ℂ) (G : Mat k r) :
    coefX σ x₀ w (a • m) G = a * coefX σ x₀ w m G := by
  simp [coefX, inner_smul_right]

variable {Vp : Type*} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]

def perI (P : Mat k r) (ψ : Mat k r → ℂ) (π : Mat k r → (Vp →L[ℂ] Vp)) (F : Mat k r → ℂ) (ξ : Vp)
    (x : Mat k r) (p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) : Vp :=
  F (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) • chiInv ψ π (Matrix.of p.1) (Matrix.of p.2) ξ

theorem per_eq (P : Mat k r) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (ψ : Mat k r → ℂ)
    (π : Mat k r → (Vp →L[ℂ] Vp)) (F : Mat k r → ℂ) (ξ : Vp) (x : Mat k r) :
    per P μW μN ψ π F ξ x = ∫ p, perI P ψ π F ξ x p ∂(μW.prod μN) := rfl

theorem per_smul (P : Mat k r) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (ψ : Mat k r → ℂ)
    (π : Mat k r → (Vp →L[ℂ] Vp)) (F : Mat k r → ℂ) (a : ℂ) (ξ : Vp) (x : Mat k r) :
    per P μW μN ψ π (fun G => a * F G) ξ x = a • per P μW μN ψ π F ξ x := by
  rw [per_eq, per_eq, ← integral_smul]
  congr 1
  funext p
  simp [perI, mul_smul]

theorem per_sum (P : Mat k r) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (ψ : Mat k r → ℂ)
    (π : Mat k r → (Vp →L[ℂ] Vp)) {ι : Type*} (s : Finset ι) (F : ι → Mat k r → ℂ) (ξ : Vp) (x : Mat k r)
    (hF : ∀ i ∈ s, Integrable (perI P ψ π (F i) ξ x) (μW.prod μN)) :
    per P μW μN ψ π (fun G => ∑ i ∈ s, F i G) ξ x = ∑ i ∈ s, per P μW μN ψ π (F i) ξ x := by
  simp only [per_eq]
  rw [← integral_finsetSum s hF]
  congr 1
  funext p
  simp [perI, Finset.sum_smul]

theorem per_tMap_single (ε : Fin (2 * r + k + 1) → Bool) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (z : Fin (2 * r + k + 1) → ℂ) (P : Mat k r)
    (hP : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (hW : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW) (hN : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    (ψ : Mat k r → ℂ) (π : Mat k r → (Vp →L[ℂ] Vp)) (x₀ : Mat k r) (w : H) (d : Fin (2 * r + k + 1)) (m : H)
    (ξ : Vp) (g : Mat k r) :
    per P μW μN ψ π (tMap ε σ (xJ P z) x₀ w (Pi.single d m)) ξ g =
      cJ ε (xJ P z) (Pi.single d 1) (P * g * P⁻¹) • per P μW μN ψ π (coefX σ x₀ w m) ξ g := by
  rw [per_eq, per_eq, ← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [ae_S hW hN] with p hp
  simp only [perI]
  rw [tMap_single, cJ_sinv ε P hP z _ _ g hp, mul_smul]

end CapelliMinorRestriction

end ReciprocityTheory.ChartRestriction.DS.Lap
