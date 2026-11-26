module

public import Mathlib

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaN
namespace Bl.FirstLemmaN

noncomputable def goal1 :
  {n : Nat} → Matrix (Fin n) (Fin n) Complex → Prop := fun {n} A =>
  (∀ i j : Fin n, i < j → A i j = 0) ∧ ∀ i : Fin n, A i i = 1

end Bl.FirstLemmaN
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaO
universe u_1

namespace Bl.FirstLemmaO

noncomputable def goal1 :
  {A : Type u_1} → [inst : CommRing A] → {d : Nat} → Ideal A → Matrix (Fin d) (Fin d) A → Prop :=
  fun I M => ∀ i j, M i j ∈ I

end Bl.FirstLemmaO
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaM
namespace Bl.FirstLemmaM

noncomputable def goal1 (K : Type*) [NormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    show ‖a * b‖ ≤ 1
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

end Bl.FirstLemmaM
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaJ
universe u_1

namespace Bl.MatrixMapSmul

theorem goal1 :
  ∀ {A : Type u_1} [inst : CommRing.{u_1} A] {d : Nat} (σ : RingHom.{u_1, u_1} A A) (a : A)
  (X : Matrix.{0, 0, u_1} (Fin d) (Fin d) A),
  Eq.{u_1 + 1}
    (Matrix.map.{u_1, u_1, 0, 0} (HSMul.hSMul.{u_1, u_1, u_1} a X) (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} σ))
    (HSMul.hSMul.{u_1, u_1, u_1} (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} σ a)
      (Matrix.map.{u_1, u_1, 0, 0} X (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} σ))) := by
  intro A _ d σ a X
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

end Bl.MatrixMapSmul
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaI
universe u_1

namespace Bl.MatrixMapSub

theorem goal1 :
  ∀ {A : Type u_1} [inst : CommRing.{u_1} A] {d : Nat} (σ : RingHom.{u_1, u_1} A A)
  (X Y : Matrix.{0, 0, u_1} (Fin d) (Fin d) A),
  Eq.{u_1 + 1}
    (Matrix.map.{u_1, u_1, 0, 0} (HSub.hSub.{u_1, u_1, u_1} X Y) (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} σ))
    (HSub.hSub.{u_1, u_1, u_1} (Matrix.map.{u_1, u_1, 0, 0} X (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} σ))
      (Matrix.map.{u_1, u_1, 0, 0} Y (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} σ))) := by
  intro A _ d σ X Y
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]

end Bl.MatrixMapSub
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.GeneralBFactAlt
universe u_1 u_2

namespace Bl.general_b_fact'''''''

theorem goal1 :
  ∀ {O : Type u_1} [inst : CommRing.{u_1} O] [inst_1 : IsDomain.{u_1} O] [inst_2 : IsDiscreteValuationRing.{u_1} O]
  {ι : Type u_2} (s : Finset.{u_2} ι) (a : ι → O),
  Eq.{1}
    (DFunLike.coe.{u_1 + 1, u_1 + 1, 1} (IsDiscreteValuationRing.addVal.{u_1} O)
      (Finset.prod.{u_2, u_1} s fun (i : ι) ↦ a i))
    (Finset.sum.{u_2, 0} s fun (i : ι) ↦
      DFunLike.coe.{u_1 + 1, u_1 + 1, 1} (IsDiscreteValuationRing.addVal.{u_1} O) (a i)) := by
  intro O _ _ _ ι s a
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty, AddValuation.map_one]
  | insert i t hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, AddValuation.map_mul, ih]

end Bl.general_b_fact'''''''
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaK
namespace Bl.FirstLemmaK

theorem goal1 :
  ∀ {α : Type} {S : Set.{0} α},
  Set.Finite.{0} S →
    ∀ (f : α → Real),
      (∀ (x : α), Membership.mem.{0, 0} S x → LT.lt.{0} 0 (f x)) →
        Exists.{1} fun (r : Real) ↦
          And (LT.lt.{0} 0 r) (And (LE.le.{0} r 1) (∀ (x : α), Membership.mem.{0, 0} S x → LT.lt.{0} r (f x))) := by
  intro α S hS f hf
  rcases S.eq_empty_or_nonempty with h | hne
  · refine ⟨1, one_pos, le_rfl, ?_⟩
    intro x hx
    rw [h] at hx
    exact absurd hx (Set.notMem_empty x)
  · obtain ⟨a, ha, hmin⟩ := Set.exists_min_image S f hS hne
    have hfa : 0 < f a := hf a ha
    refine ⟨min (f a) 1 / 2, ?_, ?_, ?_⟩
    · have : 0 < min (f a) 1 := lt_min hfa one_pos
      linarith
    · have : min (f a) 1 ≤ 1 := min_le_right _ _
      linarith
    · intro x hx
      have h1 : min (f a) 1 ≤ f a := min_le_left _ _
      have h2 : f a ≤ f x := hmin x hx
      have : 0 < min (f a) 1 := lt_min hfa one_pos
      linarith

end Bl.FirstLemmaK
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaB
open Matrix

namespace Bl.FirstLemmaB

theorem goal1 {R : Type*} [CommRing R] {n : ℕ} (P Q : Matrix (Fin n) (Fin n) R)
    (c : R) (hc : c ∈ nonZeroDivisors R) (h : Q * P = c • (1 : Matrix (Fin n) (Fin n) R)) :
    P * Q = c • (1 : Matrix (Fin n) (Fin n) R) := by
  have hdet : Q.det * P.det = c ^ n := by
    rw [← det_mul, h, det_smul, det_one, mul_one, Fintype.card_fin]
  have hcn : c ^ n ∈ nonZeroDivisors R := pow_mem hc n
  have hP : P.det ∈ nonZeroDivisors R := by
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    apply (mem_nonZeroDivisors_iff_right.mp hcn) x
    rw [← hdet, mul_comm Q.det P.det, ← mul_assoc, hx, zero_mul]
  have h1 : Q * P * P.adjugate = c • P.adjugate := by
    rw [h, smul_mul_assoc, Matrix.one_mul]
  have h2 : P.det • Q = c • P.adjugate := by
    rw [← h1, Matrix.mul_assoc, mul_adjugate, mul_smul_comm, Matrix.mul_one]
  have key : P.det • (P * Q) = P.det • (c • (1 : Matrix (Fin n) (Fin n) R)) := by
    calc P.det • (P * Q) = P * (P.det • Q) := (mul_smul_comm _ _ _).symm
      _ = P * (c • P.adjugate) := by rw [h2]
      _ = c • (P * P.adjugate) := mul_smul_comm _ _ _
      _ = c • (P.det • (1 : Matrix (Fin n) (Fin n) R)) := by rw [mul_adjugate]
      _ = P.det • (c • (1 : Matrix (Fin n) (Fin n) R)) := smul_comm _ _ _
  ext i j
  have hij := congrArg (fun M : Matrix (Fin n) (Fin n) R => M i j) key
  simp only [Matrix.smul_apply, smul_eq_mul] at hij
  have hz : P.det * ((P * Q) i j - (c • (1 : Matrix (Fin n) (Fin n) R)) i j) = 0 := by
    rw [mul_sub, sub_eq_zero]
    simpa only [Matrix.smul_apply, smul_eq_mul] using hij
  exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff_left.mp hP) _ hz)

end Bl.FirstLemmaB
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaE
namespace Bl.FirstLemmaE

theorem goal1 :
  ∀ {L : Type} [inst : NontriviallyNormedField.{0} L] [IsUltrametricDist.{0} L] {ι : Type} (s : Finset.{0} ι)
  (f g : ι → L) {r : Real},
  LE.le.{0} 0 r →
    (∀ (i : ι), LE.le.{0} (Norm.norm.{0} (f i)) 1) →
      (∀ (i : ι), LE.le.{0} (Norm.norm.{0} (g i)) 1) →
        (∀ (i : ι), LE.le.{0} (Norm.norm.{0} (HSub.hSub.{0, 0, 0} (f i) (g i))) r) →
          LE.le.{0}
            (Norm.norm.{0}
              (HSub.hSub.{0, 0, 0} (Finset.prod.{0, 0} s fun (i : ι) ↦ f i) (Finset.prod.{0, 0} s fun (i : ι) ↦ g i)))
            r := by
  intro L _ _ ι s f g r hr hf hg hfg
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hr
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hG : ‖∏ i ∈ t, g i‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => hg i)
    have key : f a * ∏ i ∈ t, f i - g a * ∏ i ∈ t, g i
        = f a * (∏ i ∈ t, f i - ∏ i ∈ t, g i) + (f a - g a) * ∏ i ∈ t, g i := by ring
    rw [key]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖f a‖ * ‖∏ i ∈ t, f i - ∏ i ∈ t, g i‖ ≤ 1 * r :=
            mul_le_mul (hf a) ih (norm_nonneg _) zero_le_one
        _ = r := one_mul r
    · rw [norm_mul]
      calc ‖f a - g a‖ * ‖∏ i ∈ t, g i‖ ≤ r * 1 :=
            mul_le_mul (hfg a) hG (norm_nonneg _) hr
        _ = r := mul_one r

end Bl.FirstLemmaE
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaL
namespace Bl.FirstLemmaL

theorem goal1 :
  ∀ {G : Type} [inst : Group.{0} G] [inst_1 : TopologicalSpace.{0} G] [IsTopologicalGroup.{0} G]
  [LocallyCompactSpace.{0} G] [SecondCountableTopology.{0} G] [T2Space.{0} G] [inst_6 : MeasurableSpace.{0} G]
  [BorelSpace.{0} G] {μ : MeasureTheory.Measure.{0} G} [MeasureTheory.Measure.IsHaarMeasure.{0} μ] {φ : G → Complex},
  MeasureTheory.Integrable.{0, 0} φ μ →
    (∀ (w : G),
        Eq.{1}
          (MeasureTheory.integral.{0, 0} μ fun (y : G) ↦
            HMul.hMul.{0, 0, 0} (φ y) (φ (HMul.hMul.{0, 0, 0} (Inv.inv.{0} y) w)))
          (φ w)) →
      ∀ {F : G → Complex},
        Continuous.{0, 0} F →
          ∀ {M : Real},
            (∀ (y : G), LE.le.{0} (Norm.norm.{0} (F y)) M) →
              Eq.{1}
                (MeasureTheory.integral.{0, 0} μ fun (y : G) ↦
                  HMul.hMul.{0, 0, 0} (φ y)
                    (MeasureTheory.integral.{0, 0} μ fun (z : G) ↦
                      HMul.hMul.{0, 0, 0} (φ z) (F (HMul.hMul.{0, 0, 0} y z))))
                (MeasureTheory.integral.{0, 0} μ fun (w : G) ↦ HMul.hMul.{0, 0, 0} (φ w) (F w)) := by
  intro G _ _ _ _ _ _ _ _ μ _ φ hφ hid F hF M hM
  have hT : MeasureTheory.MeasurePreserving (MeasurableEquiv.shearMulRight G) (μ.prod μ) (μ.prod μ) :=
    MeasureTheory.measurePreserving_prod_mul μ μ
  have hcomp : ((fun p : G × G => φ p.1 * φ (p.1⁻¹ * p.2) * F p.2) ∘ (MeasurableEquiv.shearMulRight G))
      = fun p : G × G => φ p.1 * (φ p.2 * F (p.1 * p.2)) := by
    funext p
    simp [MeasurableEquiv.shearMulRight, mul_assoc]
  have hGi : MeasureTheory.Integrable (fun p : G × G => φ p.1 * (φ p.2 * F (p.1 * p.2))) (μ.prod μ) := by
    have h1 : MeasureTheory.Integrable (fun p : G × G => φ p.1 * φ p.2) (μ.prod μ) := hφ.mul_prod hφ
    have h2 := h1.mul_bdd (c := M) (g := fun p : G × G => F (p.1 * p.2))
      ((hF.comp continuous_mul).aestronglyMeasurable) (Filter.Eventually.of_forall fun p => hM _)
    refine h2.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [mul_assoc]
  have hHi : MeasureTheory.Integrable (fun p : G × G => φ p.1 * φ (p.1⁻¹ * p.2) * F p.2) (μ.prod μ) := by
    rw [← hT.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _), hcomp]
    exact hGi
  calc ∫ y, φ y * ∫ z, φ z * F (y * z) ∂μ ∂μ
      = ∫ p, (fun p : G × G => φ p.1 * (φ p.2 * F (p.1 * p.2))) p ∂(μ.prod μ) := by
        rw [MeasureTheory.integral_prod _ hGi]
        congr 1
        funext y
        dsimp only
        exact (MeasureTheory.integral_const_mul _ _).symm
    _ = ∫ p, ((fun p : G × G => φ p.1 * φ (p.1⁻¹ * p.2) * F p.2) ∘ (MeasurableEquiv.shearMulRight G)) p ∂(μ.prod μ) := by
        rw [hcomp]
    _ = ∫ p, (fun p : G × G => φ p.1 * φ (p.1⁻¹ * p.2) * F p.2) p ∂(μ.prod μ) :=
        hT.integral_comp' (fun p : G × G => φ p.1 * φ (p.1⁻¹ * p.2) * F p.2)
    _ = ∫ w, ∫ y, φ y * φ (y⁻¹ * w) * F w ∂μ ∂μ := MeasureTheory.integral_prod_symm _ hHi
    _ = ∫ w, φ w * F w ∂μ := by
        congr 1
        funext w
        rw [MeasureTheory.integral_mul_const, hid]

end Bl.FirstLemmaL
end
