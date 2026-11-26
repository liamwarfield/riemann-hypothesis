module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CARUnit

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Transported
noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def thrStar (ε : Fin n → Bool) : ℝ :=
  max ((n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1)
    (16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ)))

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.DSymmHypsInhabited
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.FockTA
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

section Gen

variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem fockT_cm_cp {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm) {ε : Fin n → Bool}
    {j b u v : Fin n} (hjb : ¬(ε j = true ∧ ε b = false)) (huv : ε u = true ∧ ε v = false) (y : W) :
    cm j b (cp u v y) = -(cp u v (cm j b y)) := by
  have h3 := (hC j b u v).2.2
  have hne : ¬(j = u ∧ b = v) := by
    rintro ⟨rfl, rfl⟩
    exact hjb huv
  rw [if_neg hne] at h3
  have h := LinearMap.congr_fun h3 y
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply] at h
  exact eq_neg_of_add_eq_zero_left h

theorem fockT_cm_cm {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm) (j b w z : Fin n) (y : W) :
    cm j b (cm w z y) = -(cm w z (cm j b y)) := by
  have h := LinearMap.congr_fun (hC j b w z).2.1 y
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply] at h
  exact eq_neg_of_add_eq_zero_left h

theorem fockT_stable_gen {E cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm)
    (hK : CommutesCAR E cp cm) (ε : Fin n → Bool) {j b : Fin n} (hjb : ¬(ε j = true ∧ ε b = false))
    {x : W} (hx : ∀ j b, ¬(ε j = true ∧ ε b = false) → cm j b x = 0) :
    (∀ a c, cm j b (E a c x) = 0) ∧ (∀ a c, cm j b (diagE ε E cp cm a c x) = 0) ∧
      cm j b (dOp ε E cp x) = 0 ∧ cm j b (dOp' ε E cm x) = 0 := by
  have hEc : ∀ a c y, cm j b (E a c y) = E a c (cm j b y) := fun a c y => by
    have h := LinearMap.congr_fun (hK a c j b).2 y
    simp only [Module.End.mul_apply] at h
    exact h.symm
  have hx0 := hx j b hjb
  have hE0 : ∀ a c, cm j b (E a c x) = 0 := fun a c => by rw [hEc, hx0, map_zero]
  have hcpcm : ∀ u v w z, ε u = true ∧ ε v = false → cm j b (cp u v (cm w z x)) = 0 := by
    intro u v w z huv
    rw [fockT_cm_cp hC hjb huv, fockT_cm_cm hC, hx0]
    simp
  refine ⟨hE0, ?_, ?_, ?_⟩
  · intro a c
    simp only [diagE, LinearMap.add_apply, map_add (f := _), hE0, zero_add, sgE]
    by_cases ha : ε a = true <;> by_cases hc : ε c = true
    · simp only [if_pos (And.intro ha hc), LinearMap.sum_apply, map_sum, Module.End.mul_apply]
      refine Finset.sum_eq_zero fun y hy => hcpcm a y c y ⟨ha, ?_⟩
      simpa [minusIdx] using hy
    · simp [ha, hc, sgE]
    · simp [ha, hc, sgE]
    · have ha0 : ε a = false := by cases h : ε a <;> simp_all
      have hc0 : ε c = false := by cases h : ε c <;> simp_all
      simp only [if_neg (show ¬(ε a = true ∧ ε c = true) from fun h => ha h.1),
        if_pos (And.intro ha0 hc0), LinearMap.neg_apply, LinearMap.sum_apply, map_neg, map_sum,
        Module.End.mul_apply]
      refine neg_eq_zero.mpr (Finset.sum_eq_zero fun i hi => hcpcm i c i a ⟨?_, hc0⟩)
      simpa [plusIdx] using hi
  · simp only [dOp, LinearMap.sum_apply, map_sum, Module.End.mul_apply]
    refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun a ha => ?_
    rw [hEc, fockT_cm_cp hC hjb ⟨by simpa [plusIdx] using hi, by simpa [minusIdx] using ha⟩, hx0]
    simp
  · simp only [dOp', LinearMap.neg_apply, LinearMap.sum_apply, map_neg, map_sum, Module.End.mul_apply]
    refine neg_eq_zero.mpr (Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun a _ => ?_)
    rw [hEc, fockT_cm_cm hC, hx0]
    simp

theorem fockT_anti_sum {R : Type*} [Ring R] {ι κ : Type*} (s : Finset ι) (t : Finset κ) (G : R)
    (A B : ι → κ → R) (hA : ∀ i k, G * A i k = A i k * G) (hB : ∀ i k, G * B i k = -(B i k * G)) :
    G * ∑ i ∈ s, ∑ k ∈ t, A i k * B i k = -((∑ i ∈ s, ∑ k ∈ t, A i k * B i k) * G) := by
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  calc G * (A i k * B i k) = A i k * (G * B i k) := by rw [← mul_assoc, hA, mul_assoc]
    _ = -(A i k * B i k * G) := by rw [hB, mul_neg, mul_assoc]

end Gen

section FockLemmas

variable {n : ℕ}

theorem fock_contractLeft_involute (d : Module.Dual ℂ (Fin n × Fin n → ℂ)) (x : Fock n) :
    CliffordAlgebra.contractLeft d (CliffordAlgebra.involute x) =
      -CliffordAlgebra.involute (CliffordAlgebra.contractLeft d x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp [CliffordAlgebra.contractLeft_algebraMap]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, neg_add]
  | ι_mul x m hx =>
    simp only [map_mul, CliffordAlgebra.involute_ι, neg_mul, map_neg, CliffordAlgebra.contractLeft_ι_mul,
      hx, map_sub, map_smul, mul_neg]

theorem fock_inv_sq :
    (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap *
      (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap = 1 :=
  LinearMap.ext fun x => CliffordAlgebra.involute_involute x

theorem fock_inv_cp (i a : Fin n) :
    (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap * cpFock i a =
      -(cpFock i a * (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap) := by
  refine LinearMap.ext fun x => ?_
  simp [cpFock, CliffordAlgebra.involute_ι]

theorem fock_inv_cm (i a : Fin n) :
    (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap * cmFock i a =
      -(cmFock i a * (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap) := by
  refine LinearMap.ext fun x => ?_
  simp [cmFock, fock_contractLeft_involute]

end FockLemmas

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {N : Type*} [AddCommGroup N] [Module ℂ N]

def eT (E : Fin n → Fin n → Module.End ℂ N) (a b : Fin n) : Module.End ℂ (TensorProduct ℂ N (Fock n)) :=
  TensorProduct.map (E a b) LinearMap.id

def cpT (i a : Fin n) : Module.End ℂ (TensorProduct ℂ N (Fock n)) := TensorProduct.map LinearMap.id (cpFock i a)

def cmT (i a : Fin n) : Module.End ℂ (TensorProduct ℂ N (Fock n)) := TensorProduct.map LinearMap.id (cmFock i a)

def gradT : Module.End ℂ (TensorProduct ℂ N (Fock n)) :=
  TensorProduct.map LinearMap.id (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap

def physicalSubspace (ε : Fin n → Bool) : Submodule ℂ (TensorProduct ℂ N (Fock n)) :=
  ⨅ i : Fin n, ⨅ a : Fin n, ⨅ (_ : ¬ (ε i = true ∧ ε a = false)), LinearMap.ker (cmT (N := N) i a)

def tensFock (V : Submodule ℂ N) : Submodule ℂ (TensorProduct ℂ N (Fock n)) :=
  LinearMap.range (TensorProduct.map V.subtype (LinearMap.id : Fock n →ₗ[ℂ] Fock n))

theorem gradT_eq : gradT (N := N) (n := n) =
    Module.End.lTensorAlgHom ℂ (Fock n) N (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap := rfl

theorem mem_physicalSubspace_iff (ε : Fin n → Bool) (x : TensorProduct ℂ N (Fock n)) :
    x ∈ physicalSubspace (N := N) ε ↔ ∀ j b, ¬(ε j = true ∧ ε b = false) → cmT j b x = 0 := by
  simp only [physicalSubspace, Submodule.mem_iInf, LinearMap.mem_ker]

theorem gradT_cpT (i a : Fin n) : gradT (N := N) * cpT i a = -(cpT i a * gradT) := by
  have h := congrArg (Module.End.lTensorAlgHom ℂ (Fock n) N) (fock_inv_cp (n := n) i a)
  simp only [map_neg, map_mul] at h
  exact h

theorem gradT_cmT (i a : Fin n) : gradT (N := N) * cmT i a = -(cmT i a * gradT) := by
  have h := congrArg (Module.End.lTensorAlgHom ℂ (Fock n) N) (fock_inv_cm (n := n) i a)
  simp only [map_neg, map_mul] at h
  exact h

theorem eT_gradT (E : Fin n → Fin n → Module.End ℂ N) (a b : Fin n) : eT E a b * gradT = gradT * eT E a b :=
  TensorProduct.ext' fun x y => by simp [eT, gradT, TensorProduct.map_tmul]

theorem eT_isGlRep {E : Fin n → Fin n → Module.End ℂ N} (hE : IsGlRep E) : IsGlRep (eT (n := n) E) := by
  intro a b c d
  have h := congrArg (Module.End.rTensorAlgHom ℂ N (Fock n)) (hE a b c d)
  rw [map_sub, map_sub, map_mul, map_mul] at h
  refine h.trans ?_
  congr 1 <;> split_ifs <;> first | rfl | simp

theorem cpT_cmT_isCAR : IsCAR (cpT (N := N) (n := n)) cmT := by
  intro i a j b
  obtain ⟨h1, h2, h3⟩ := isCAR_fock (n := n) i a j b
  refine ⟨?_, ?_, ?_⟩
  · have h := congrArg (Module.End.lTensorAlgHom ℂ (Fock n) N) h1
    simp only [map_add (f := _), map_mul, map_zero] at h
    exact h
  · have h := congrArg (Module.End.lTensorAlgHom ℂ (Fock n) N) h2
    simp only [map_add (f := _), map_mul, map_zero] at h
    exact h
  · have h := congrArg (Module.End.lTensorAlgHom ℂ (Fock n) N) h3
    rw [map_add (f := _), map_mul, map_mul] at h
    refine h.trans ?_
    split_ifs <;> simp

theorem eT_commutesCAR (E : Fin n → Fin n → Module.End ℂ N) : CommutesCAR (eT E) cpT cmT := by
  intro a b i j
  refine ⟨TensorProduct.ext' fun x y => ?_, TensorProduct.ext' fun x y => ?_⟩ <;>
    simp [eT, cpT, cmT, TensorProduct.map_tmul]

theorem physSub_stable (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ N) :
    (∀ a b, ∀ x ∈ physicalSubspace (N := N) ε, eT E a b x ∈ physicalSubspace ε) ∧
      (∀ a b, ∀ x ∈ physicalSubspace (N := N) ε, diagE ε (eT E) cpT cmT a b x ∈ physicalSubspace ε) ∧
      (∀ x ∈ physicalSubspace (N := N) ε, dOp ε (eT E) cpT x ∈ physicalSubspace ε) ∧
      (∀ x ∈ physicalSubspace (N := N) ε, dOp' ε (eT E) cmT x ∈ physicalSubspace ε) ∧
      ∀ x ∈ physicalSubspace (N := N) ε, gradT x ∈ physicalSubspace ε := by
  have hC := cpT_cmT_isCAR (N := N) (n := n)
  have hK := eT_commutesCAR (N := N) E
  refine ⟨fun a c x hx => ?_, fun a c x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩ <;>
    rw [mem_physicalSubspace_iff] at hx ⊢ <;> intro j b hjb
  · exact (fockT_stable_gen hC hK ε hjb hx).1 a c
  · exact (fockT_stable_gen hC hK ε hjb hx).2.1 a c
  · exact (fockT_stable_gen hC hK ε hjb hx).2.2.1
  · exact (fockT_stable_gen hC hK ε hjb hx).2.2.2
  · have h := LinearMap.congr_fun (gradT_cmT (N := N) j b) x
    simp only [Module.End.mul_apply, LinearMap.neg_apply] at h
    rw [← neg_neg (cmT j b (gradT x)), ← h, hx j b hjb, map_zero, neg_zero]

theorem gradT_props (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ N) :
    gradT (N := N) (n := n) * gradT = 1 ∧ gradT * dOp ε (eT E) cpT = -(dOp ε (eT E) cpT * gradT) ∧
      gradT * dOp' ε (eT E) cmT = -(dOp' ε (eT E) cmT * gradT) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [gradT_eq, ← map_mul, fock_inv_sq, map_one]
  · exact fockT_anti_sum _ _ _ (fun i a => eT E a i) (fun i a => cpT i a) (fun i a => (eT_gradT E a i).symm)
      (fun i a => gradT_cpT i a)
  · simp only [dOp', mul_neg, neg_mul]
    rw [fockT_anti_sum _ _ _ (fun i a => eT E i a) (fun i a => cmT i a) (fun i a => (eT_gradT E i a).symm)
      (fun i a => gradT_cmT i a)]

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Residue
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def resid (a : Fin n → ℂ) (s : Fin n) : ℂ := ∏ s' ∈ univ.erase s, (a s - a s' + 1) / (a s - a s')

def ratioV (μ : Fin n → ℝ) (s : Fin n) : ℝ := ∏ s' ∈ univ.erase s, (μ s + 1 - μ s') / (μ s - μ s')

def ratioVd (μ : Fin n → ℝ) (s : Fin n) : ℝ := ∏ s' ∈ univ.erase s, (μ s - 1 - μ s') / (μ s - μ s')

theorem prod_one_add_eq_of_resolvent {ι : Type} [DecidableEq ι] (S : Finset ι) :
    ∀ (R : Type) [CommRing R] [Algebra ℂ R] (a : ι → ℂ) (_ : Set.InjOn a S) (g : ι → R)
      (_ : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → (a t - a s) • (g t * g s) = g t - g s),
      ∏ s ∈ S, (1 + g s) =
        1 + ∑ s ∈ S, (∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) • g s := by
  refine Finset.induction_on S ?_ ?_
  · intro R _ _ a _ g _
    simp
  · intro t S ht ih R _ _ a ha g hg
    have hinj : ∀ x ∈ insert t S, ∀ y ∈ insert t S, a x = a y → x = y :=
      fun x hx y hy h => ha (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) h
    have haS : Set.InjOn a ↑S := fun x hx y hy h =>
      hinj x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) h
    have hne : ∀ s ∈ S, a t - a s ≠ 0 := fun s hs h =>
      ht ((hinj t (Finset.mem_insert_self t S) s (Finset.mem_insert_of_mem hs) (sub_eq_zero.mp h)) ▸ hs)
    have hgS : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → (a s' - a s) • (g s' * g s) = g s' - g s :=
      fun s hs s' hs' h => hg s (Finset.mem_insert_of_mem hs) s' (Finset.mem_insert_of_mem hs') h
    have hC : ∏ s ∈ S, (1 + 1 / (a t - a s)) = 1 + ∑ s ∈ S, (∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) • (1 / (a t - a s)) :=
      ih ℂ a haS (fun s => 1 / (a t - a s)) (fun s hs s' hs' _ => by
        have h1 := hne s hs
        have h2 := hne s' hs'
        simp only [smul_eq_mul]
        field_simp
        ring)
    have hR := ih R a haS g hgS
    have hts : ∀ s ∈ S, g t * g s = (1 / (a t - a s)) • (g t - g s) := by
      intro s hs
      have h' := hg s (Finset.mem_insert_of_mem hs) t (Finset.mem_insert_self t S) (fun h => ht (h ▸ hs))
      rw [← h', smul_smul, one_div, inv_mul_cancel₀ (hne s hs), one_smul]
    have hcs : ∀ s ∈ S, (∏ s' ∈ (insert t S).erase s, (a s - a s' + 1) / (a s - a s')) =
        (a s - a t + 1) / (a s - a t) * (∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) := by
      intro s hs
      have hst : t ≠ s := fun h => ht (h ▸ hs)
      rw [Finset.erase_insert_of_ne hst, Finset.prod_insert (fun h => ht (Finset.mem_of_mem_erase h))]
    have hct : ∏ s' ∈ S, (a t - a s' + 1) / (a t - a s') =
        1 + ∑ s ∈ S, (∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) * (1 / (a t - a s)) := by
      calc ∏ s' ∈ S, (a t - a s' + 1) / (a t - a s') = ∏ s ∈ S, (1 + 1 / (a t - a s)) :=
            Finset.prod_congr rfl fun s hs => by
              have := hne s hs
              field_simp
        _ = _ := by rw [hC]; simp only [smul_eq_mul]
    have hper : ∀ s ∈ S, ((a s - a t + 1) / (a s - a t) * (∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s'))) • g s =
        (∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) • g s - ((∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) * (1 / (a t - a s))) • g s := by
      intro s hs
      rw [← sub_smul]
      congr 1
      have h1 := hne s hs
      have h2 : a s - a t ≠ 0 := fun h => h1 (by linear_combination -h)
      field_simp
      ring
    have hmul : ∀ s ∈ S, g t * ((∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) • g s) =
        ((∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) * (1 / (a t - a s))) • g t - ((∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) * (1 / (a t - a s))) • g s := by
      intro s hs
      rw [mul_smul_comm, hts s hs, smul_smul, smul_sub]
    have hsum2 : ∑ s ∈ S, (∏ s' ∈ (insert t S).erase s, (a s - a s' + 1) / (a s - a s')) • g s =
        ∑ s ∈ S, ((a s - a t + 1) / (a s - a t) * (∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s'))) • g s :=
      Finset.sum_congr rfl fun s hs => by rw [hcs s hs]
    rw [Finset.prod_insert ht, hR, Finset.sum_insert ht, Finset.erase_insert ht, hsum2, hct, Finset.sum_congr rfl hper, add_mul,
      one_mul, mul_add, mul_one, Finset.mul_sum, Finset.sum_congr rfl hmul, add_smul, one_smul,
      Finset.sum_smul]
    simp only [Finset.sum_sub_distrib]
    abel

theorem inv_one_sub_C_mul_X (c : ℂ) :
    (1 - PowerSeries.C c * PowerSeries.X)⁻¹ = PowerSeries.mk (fun k => c ^ k) := by
  symm
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by simp)]
  ext n
  rw [mul_sub, mul_one, ← mul_assoc, mul_comm (PowerSeries.mk _) (PowerSeries.C c), mul_assoc]
  cases n with
  | zero => simp
  | succ n =>
    rw [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mk,
      PowerSeries.coeff_mk, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n), pow_succ]
    ring

theorem resSeries_eq_sum {n : ℕ} {a : Fin n → ℂ} (ha : Function.Injective a) :
    resSeries a = ∑ s, (∏ s' ∈ univ.erase s, (a s - a s' + 1) / (a s - a s')) •
      (PowerSeries.X * (1 - PowerSeries.C (a s) * PowerSeries.X)⁻¹) := by
  have hP : ∀ s, PowerSeries.constantCoeff (1 - PowerSeries.C (a s) * PowerSeries.X) ≠ 0 := by
    intro s; simp
  have h := prod_one_add_eq_of_resolvent (Finset.univ : Finset (Fin n)) (PowerSeries ℂ) a ha.injOn
    (fun s => PowerSeries.X * (1 - PowerSeries.C (a s) * PowerSeries.X)⁻¹) (fun s _ t _ _ => by
      have key : (1 - PowerSeries.C (a t) * PowerSeries.X)⁻¹ - (1 - PowerSeries.C (a s) * PowerSeries.X)⁻¹ =
          (1 - PowerSeries.C (a t) * PowerSeries.X)⁻¹ * (1 - PowerSeries.C (a s) * PowerSeries.X)⁻¹ *
            ((1 - PowerSeries.C (a s) * PowerSeries.X) - (1 - PowerSeries.C (a t) * PowerSeries.X)) := by
        rw [mul_sub, mul_assoc, PowerSeries.inv_mul_cancel _ (hP s), mul_one,
          mul_comm ((1 - PowerSeries.C (a t) * PowerSeries.X)⁻¹), mul_assoc,
          PowerSeries.inv_mul_cancel _ (hP t), mul_one]
      rw [← mul_sub, key, PowerSeries.smul_eq_C_mul, map_sub]
      ring)
  rw [resSeries, h, add_sub_cancel_left]

theorem resSeries_coeff_succ' {n : ℕ} {a : Fin n → ℂ} (ha : Function.Injective a) (k : ℕ) :
    PowerSeries.coeff (k + 1) (resSeries a) =
      ∑ s, (∏ s' ∈ univ.erase s, (a s - a s' + 1) / (a s - a s')) * a s ^ k := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [resSeries_eq_sum ha, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [PowerSeries.coeff_smul, inv_one_sub_C_mul_X, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk,
    smul_eq_mul]

theorem not_injective_shift_iff {μ ν : Fin n → ℝ} (hμ : Function.Injective μ) (s : Fin n) (c : ℝ)
    (hs : ν s = μ s + c) (ho : ∀ x, x ≠ s → ν x = μ x) :
    ¬ Function.Injective ν ↔ ∃ s' ∈ univ.erase s, μ s + c = μ s' := by
  constructor
  · intro h
    simp only [Function.Injective, not_forall] at h
    obtain ⟨x, y, hxy, hne⟩ := h
    by_cases hx : x = s
    · subst hx
      refine ⟨y, by simp [Ne.symm hne], ?_⟩
      rw [← hs, hxy, ho y (Ne.symm hne)]
    · by_cases hy : y = s
      · subst hy
        refine ⟨x, by simp [hx], ?_⟩
        rw [← hs, ← hxy, ho x hx]
      · exact absurd (hμ (by rw [← ho x hx, ← ho y hy, hxy])) hne
  · rintro ⟨s', hs', h⟩ hinj
    have hne : s' ≠ s := (Finset.mem_erase.mp hs').1
    exact hne (hinj (by rw [ho s' hne, hs, h]))

theorem resSeries_coeff_succ {a : Fin n → ℂ} (ha : Function.Injective a) (k : ℕ) :
    PowerSeries.coeff (k + 1) (resSeries a) = ∑ s, resid a s * a s ^ k := by
  rw [resSeries_coeff_succ' ha k]
  rfl

theorem resid_poleV (μ : Fin n → ℝ) (s : Fin n) : resid (poleV μ) s = ((ratioV μ s : ℝ) : ℂ) := by
  simp only [resid, ratioV, poleV]
  push_cast
  refine Finset.prod_congr rfl fun s' _ => ?_
  ring

theorem resid_poleVd (μ : Fin n → ℝ) (s : Fin n) : resid (poleVd μ) s = ((ratioVd μ s : ℝ) : ℂ) := by
  simp only [resid, ratioVd, poleVd]
  push_cast
  refine Finset.prod_congr rfl fun s' _ => ?_
  rw [← neg_div_neg_eq]
  ring

theorem poleV_injective {μ : Fin n → ℝ} (hμ : Function.Injective μ) : Function.Injective (poleV μ) := by
  intro x y h
  apply hμ
  simp only [poleV] at h
  have h' := Complex.ofReal_injective h
  linarith

theorem poleVd_injective {μ : Fin n → ℝ} (hμ : Function.Injective μ) : Function.Injective (poleVd μ) := by
  intro x y h
  apply hμ
  simp only [poleVd] at h
  have h' := Complex.ofReal_injective h
  linarith

theorem ratioVd_add_single_mul {μ : Fin n → ℝ} (s : Fin n) (hμ : Function.Injective μ)
    (hμs : Function.Injective (μ + Pi.single s 1)) :
    ratioVd (μ + Pi.single s 1) s * ratioV μ s = 1 := by
  rw [ratioVd, ratioV, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro s' hs'
  have hne : s' ≠ s := (Finset.mem_erase.mp hs').1
  have h1 : μ s - μ s' ≠ 0 := sub_ne_zero.mpr (fun h => hne (hμ h).symm)
  have h2 : μ s + 1 - μ s' ≠ 0 := by
    intro h
    apply hne
    apply hμs
    simp [Pi.single_apply, hne]
    linarith
  simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_apply, hne, if_false, add_zero]
  rw [show μ s + 1 - 1 - μ s' = μ s - μ s' by ring]
  field_simp

end ReciprocityTheory.ChartRestriction.DS
end
end
