module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LinearIndependentOrth
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDensityCorank.FieldCountHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDensityCorank.ResidueEqZeroIff

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocDensCorank
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDensityCorank.LocDensCorankOfCounts
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.EulerFactorTwo
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S

theorem locE_isUnit_or_exists_algEquiv_prod_swap {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) :
    (∀ x : E, x ≠ 0 → IsUnit x) ∨ ∃ e : E ≃ₐ[F] F × F, ∀ x, e (L.cj x) = (e x).swap := by
  classical
  have hrank := L.rank
  have : Module.Free F E := L.free
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hrank]; norm_num)
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [hrank]; norm_num)
  have : IsReduced E := L.reduced
  by_cases hfield : ∀ x : E, x ≠ 0 → IsUnit x
  · exact Or.inl hfield
  right
  obtain ⟨x, hx⟩ := not_forall.1 hfield
  have hx0 : x ≠ 0 := fun heq => hx (fun hne => (hne heq).elim)
  have hxu : ¬ IsUnit x := fun hu => hx (fun _ => hu)
  have hfix : ∀ y : E, L.cj y = y → ∃ a : F, algebraMap F E a = y := fun y hy => (L.cj_fix y).1 hy
  obtain ⟨a, ha⟩ := hfix (x * L.cj x) (by rw [map_mul, L.cj_cj, mul_comm])
  have hN : x * L.cj x = 0 := by
    by_contra hne
    apply hxu
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at ha
      exact hne ha.symm
    refine IsUnit.of_mul_eq_one (L.cj x * algebraMap F E a⁻¹) ?_
    rw [← mul_assoc, ← ha, ← map_mul, mul_inv_cancel₀ ha0, map_one]
  obtain ⟨t, ht⟩ := hfix (x + L.cj x) (by rw [map_add (f := _), L.cj_cj, add_comm])
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [map_zero] at ht
    have hc : L.cj x = -x := by linear_combination -ht
    have hsq : x ^ 2 = 0 := by
      rw [hc] at hN
      linear_combination -hN
    exact hx0 (IsReduced.eq_zero x ⟨2, hsq⟩)
  have hcu : L.cj (algebraMap F E t⁻¹) = algebraMap F E t⁻¹ := L.cj.commutes _
  have hpq : x * algebraMap F E t⁻¹ + L.cj x * algebraMap F E t⁻¹ = 1 := by
    rw [← add_mul, ← ht, ← map_mul, mul_inv_cancel₀ ht0, map_one]
  set p := x * algebraMap F E t⁻¹ with hp
  set q := L.cj x * algebraMap F E t⁻¹ with hq
  have hpq0 : p * q = 0 := by
    rw [hp, hq]
    linear_combination (algebraMap F E t⁻¹ * algebraMap F E t⁻¹) * hN
  have hqp : q * p = 0 := by rw [mul_comm]; exact hpq0
  have hcp : L.cj p = q := by rw [hp, hq, map_mul, hcu]
  have hcq : L.cj q = p := by rw [hp, hq, map_mul, hcu, L.cj_cj]
  have hpp : p * p = p := by
    have h : p * (p + q) = p := by rw [hpq, mul_one]
    linear_combination h - hpq0
  have hqq : q * q = q := by
    have h : (p + q) * q = q := by rw [hpq, one_mul]
    linear_combination h - hpq0
  have hp0 : p ≠ 0 := by
    intro h
    have h1 : q = 1 := by rw [← hpq, h, zero_add]
    apply one_ne_zero (α := E)
    rw [← h1, ← hcp, h, map_zero]
  have hq0 : q ≠ 0 := by
    intro h
    have h1 : p = 1 := by rw [← hpq, h, add_zero]
    apply one_ne_zero (α := E)
    rw [← h1, ← hcq, h, map_zero]
  let g : (F × F) →ₐ[F] E :=
    { toFun := fun z => z.1 • p + z.2 • q
      map_one' := by simp [hpq]
      map_mul' := fun z w => by
        simp only [Prod.fst_mul, Prod.snd_mul, Algebra.smul_def, map_mul]
        linear_combination (-(algebraMap F E z.1 * algebraMap F E w.1)) * hpp -
          (algebraMap F E z.2 * algebraMap F E w.2) * hqq -
          (algebraMap F E z.1 * algebraMap F E w.2 + algebraMap F E z.2 * algebraMap F E w.1) * hpq0
      map_zero' := by simp
      map_add' := fun z w => by
        simp only [Prod.fst_add, Prod.snd_add, add_smul]
        abel
      commutes' := fun r => by
        simp only [Prod.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        rw [← smul_add, hpq, Algebra.algebraMap_eq_smul_one] }
  have ginj : Function.Injective g := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    have hz' : z.1 • p + z.2 • q = 0 := hz
    have h1 : z.1 • p = 0 := by
      have h := congrArg (· * p) hz'
      simp only [add_mul, smul_mul_assoc, hpp, hqp, smul_zero, add_zero, zero_mul] at h
      exact h
    have h2 : z.2 • q = 0 := by
      have h := congrArg (· * q) hz'
      simp only [add_mul, smul_mul_assoc, hqq, hpq0, smul_zero, zero_add, zero_mul] at h
      exact h
    rw [smul_eq_zero] at h1 h2
    exact Prod.ext (h1.resolve_right hp0) (h2.resolve_right hq0)
  have gsurj : Function.Surjective g := by
    have hdim : Module.finrank F (F × F) = Module.finrank F E := by
      rw [Module.finrank_prod, Module.finrank_self, hrank]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := g.toLinearMap)).1 ginj
  let e0 := AlgEquiv.ofBijective g ⟨ginj, gsurj⟩
  refine ⟨e0.symm, fun y => ?_⟩
  obtain ⟨z, rfl⟩ := gsurj y
  have hez : e0.symm (g z) = z := e0.symm_apply_apply z
  have hcz : L.cj (g z) = g z.swap := by
    show L.cj (z.1 • p + z.2 • q) = z.2 • p + z.1 • q
    rw [map_add (f := _), map_smul, map_smul, hcp, hcq, add_comm]
  rw [hcz, hez]
  exact e0.symm_apply_apply z.swap

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDensityCorank.CongruenceDensity
open ValuativeRel Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocDensCorank

open Formalism.MainNotions.S

def act {R N ι : Type} [CommRing R] [AddCommGroup N] [Module R N] [Fintype ι] (P : Matrix ι ι R)
    (v : ι → N) : ι → N :=
  fun a => ∑ i, P i a • v i

theorem act_act {R N ι : Type} [CommRing R] [AddCommGroup N] [Module R N] [Fintype ι]
    (P Q : Matrix ι ι R) (v : ι → N) : act Q (act P v) = act (P * Q) v := by
  funext a
  simp only [act, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

theorem act_one {R N ι : Type} [CommRing R] [AddCommGroup N] [Module R N] [Fintype ι] [DecidableEq ι]
    (v : ι → N) : act (1 : Matrix ι ι R) v = v := by
  funext a
  simp [act, Matrix.one_apply]

theorem act_map {R N N' ι : Type} [CommRing R] [AddCommGroup N] [Module R N] [AddCommGroup N']
    [Module R N'] [Fintype ι] (f : N →ₗ[R] N') (P : Matrix ι ι R) (v : ι → N) :
    (fun a => f (act P v a)) = act P (fun a => f (v a)) := by
  funext a
  set_option synthInstance.maxHeartbeats 100000 in
    simp [act, map_sum, map_smul]

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]

def cls (H : Loc.HermSp M V) (ϖ : 𝒪[F]) (Λ : Submodule M.L.O V) {ι : Type} (G : Matrix ι ι E) :
    Set (ι → V ⧸ H.smulLat (algebraMap F E (ϖ : F)) Λ) :=
  Set.range fun v : {v : ι → V // H.Prim Λ v ∧ ∀ a b,
      H.h (v b) (v a) - G a b ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)}} =>
      fun a => Submodule.Quotient.mk (p := H.smulLat (algebraMap F E (ϖ : F)) Λ) (v.1 a)

theorem dens_eq_cls (H : Loc.HermSp M V) (ϖ : 𝒪[F]) (Λ : Submodule M.L.O V) {ι : Type} [Fintype ι]
    (G : Matrix ι ι E) :
    H.dens ϖ Λ G = (Nat.card (cls H ϖ Λ G) : ℝ) /
      (Nat.card 𝓀[F] : ℝ) ^ ((2 * Module.finrank E V * Fintype.card ι : ℤ) - (Fintype.card ι : ℤ) ^ 2) := rfl

end

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem mul_mem_span {ϖE x y : E} (hx : x ∈ M.L.O) (hy : y ∈ Submodule.span M.L.O {ϖE}) :
    x * y ∈ Submodule.span M.L.O {ϖE} := Submodule.smul_mem (Submodule.span M.L.O {ϖE}) (⟨x, hx⟩ : M.L.O) hy

theorem prim_act (H : Loc.HermSp M V) (Λ : Submodule M.L.O V) {ι : Type} [Fintype ι] [DecidableEq ι]
    (P B : Matrix ι ι M.L.O) (hPB : P * B = 1) (hBP : B * P = 1) {v : ι → V} (hv : H.Prim Λ v) :
    H.Prim Λ (act P v) := by
  obtain ⟨h1, h2, h3⟩ := hv
  have back : act B (act P v) = v := by rw [act_act, hPB, act_one]
  have memO : ∀ (Q : Matrix ι ι M.L.O) (w : ι → V) a, act Q w a ∈ Submodule.span M.L.O (Set.range w) :=
    fun Q w a => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨fun a => Λ.sum_mem fun i _ => Λ.smul_mem _ (h1 i), ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff] at h2 ⊢
    intro g hg
    have E1 : ∀ g : ι → E, ∑ j, (∑ a, g a * (P j a : E)) • v j = ∑ a, g a • act P v a := by
      intro g
      simp only [act, Finset.sum_smul, Finset.smul_sum, Subring.smul_def, smul_smul]
      exact Finset.sum_comm
    have key : ∀ j, ∑ a, g a * (P j a : E) = 0 := h2 _ ((E1 g).trans hg)
    have hB'P' : B.map M.L.O.subtype * P.map M.L.O.subtype = 1 := by
      rw [← Matrix.map_mul, hBP, Matrix.map_one _ (map_zero _) (map_one _)]
    have hPg : Matrix.mulVec (P.map M.L.O.subtype) g = 0 := by
      funext j
      show ∑ a, (P j a : E) * g a = 0
      exact (Finset.sum_congr rfl fun a _ => mul_comm _ _).trans (key j)
    have hg0 : g = 0 := by
      rw [← Matrix.one_mulVec g, ← hB'P', ← Matrix.mulVec_mulVec, hPg, Matrix.mulVec_zero]
    intro i
    rw [hg0]
    rfl
  · intro x hxΛ hxspan
    have hE : Submodule.span E (Set.range (act P v)) ≤ Submodule.span E (Set.range v) := by
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (P i a : E) (Submodule.subset_span ⟨i, rfl⟩)
    have h' := h3 x hxΛ (hE hxspan)
    have hO : Submodule.span M.L.O (Set.range v) ≤ Submodule.span M.L.O (Set.range (act P v)) := by
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      have e : v a = act B (act P v) a := by rw [back]
      rw [e]
      exact memO B (act P v) a
    exact hO h'

theorem gram_act (H : Loc.HermSp M V) (ϖE : E) {ι : Type} [Fintype ι]
    (P : Matrix ι ι M.L.O) (G : Matrix ι ι E) {v : ι → V}
    (hv : ∀ a b, H.h (v b) (v a) - G a b ∈ Submodule.span M.L.O {ϖE}) (a b : ι) :
    H.h (act P v b) (act P v a) -
        (((P.map M.L.O.subtype).map M.L.cj).transpose * G * P.map M.L.O.subtype) a b
      ∈ Submodule.span M.L.O {ϖE} := by
  have hR : ∀ x y y', H.h x (y + y') = H.h x y + H.h x y' := by
    intro x y y'
    rw [H.h_herm (y + y') x, H.h_add_left, map_add (f := _), ← H.h_herm y x, ← H.h_herm y' x]
  have hS : ∀ (c : E) x y, H.h x (c • y) = M.L.cj c * H.h x y := by
    intro c x y
    rw [H.h_herm (c • y) x, H.h_smul_left, map_mul, ← H.h_herm y x]
  have hsumL : ∀ (f : ι → V) y, H.h (∑ i, f i) y = ∑ i, H.h (f i) y := fun f y =>
    map_sum (AddMonoidHom.mk' (fun x => H.h x y) (fun x x' => H.h_add_left x x' y)) f Finset.univ
  have hsumR : ∀ x (f : ι → V), H.h x (∑ i, f i) = ∑ i, H.h x (f i) := fun x f =>
    map_sum (AddMonoidHom.mk' (fun y => H.h x y) (fun y y' => hR x y y')) f Finset.univ
  have e1 : H.h (act P v b) (act P v a) = ∑ j, ∑ i, ((P j b : E) * M.L.cj (P i a)) * H.h (v j) (v i) := by
    rw [show act P v b = ∑ j, (P j b : E) • v j from rfl, show act P v a = ∑ i, (P i a : E) • v i from rfl, hsumL]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [H.h_smul_left, hsumR, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hS]
    ring
  have e2 : (((P.map M.L.O.subtype).map M.L.cj).transpose * G * P.map M.L.O.subtype) a b
      = ∑ j, ∑ i, ((P j b : E) * M.L.cj (P i a)) * G i j := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [Subring.coe_subtype]
    ring
  rw [e1, e2, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [← mul_sub]
  exact mul_mem_span (M.L.O.mul_mem (P j b).2 (PI.UnitaryGroupMassFormula.CntFormula.fl_cj_mem M.L (P i a).2)) (hv i j)

theorem cls_act (H : Loc.HermSp M V) (ϖ : 𝒪[F]) (Λ : Submodule M.L.O V) {ι : Type} [Fintype ι]
    [DecidableEq ι] (P B : Matrix ι ι M.L.O) (hPB : P * B = 1) (hBP : B * P = 1) (G : Matrix ι ι E) :
    act P '' cls H ϖ Λ G ⊆
      cls H ϖ Λ (((P.map M.L.O.subtype).map M.L.cj).transpose * G * P.map M.L.O.subtype) := by
  rintro _ ⟨_, ⟨⟨w, hw1, hw2⟩, rfl⟩, rfl⟩
  refine ⟨⟨act P w, prim_act H Λ P B hPB hBP hw1, gram_act H _ P G hw2⟩, ?_⟩
  exact act_map (Submodule.mkQ _) P w

theorem cong_dens (H : Loc.HermSp M V) (ϖ : 𝒪[F]) (Λ : Submodule M.L.O V) {ι : Type} [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι E) (hA : ∀ i j, A i j ∈ M.L.O)
    (hdet : ∃ y ∈ M.L.O, A.det * y = 1) (G : Matrix ι ι E) :
    H.dens ϖ Λ ((A.map M.L.cj).transpose * G * A) = H.dens ϖ Λ G := by
  obtain ⟨y, hy, hAy⟩ := hdet
  set P : Matrix ι ι M.L.O := Matrix.of fun i j => ⟨A i j, hA i j⟩ with hPdef
  have hPA : P.map M.L.O.subtype = A := by
    ext i j
    rfl
  have hdetA : ((P.det : M.L.O) : E) = A.det := by
    rw [← hPA]
    exact RingHom.map_det M.L.O.subtype P
  have hdetP : P.det * ⟨y, hy⟩ = 1 := by
    apply Subtype.ext
    rw [Subring.coe_mul, hdetA]
    exact hAy
  set B : Matrix ι ι M.L.O := (⟨y, hy⟩ : M.L.O) • P.adjugate with hBdef
  have hPB : P * B = 1 := by
    rw [hBdef, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, mul_comm, hdetP, one_smul]
  have hBP : B * P = 1 := by
    rw [hBdef, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, mul_comm, hdetP, one_smul]
  have hmc : ∀ X Y : Matrix ι ι E, (X * Y).map M.L.cj = X.map M.L.cj * Y.map M.L.cj := fun X Y =>
    Matrix.map_mul (f := (M.L.cj : E →+* E))
  have hAB : A * B.map M.L.O.subtype = 1 := by
    rw [← hPA, ← Matrix.map_mul, hPB, Matrix.map_one _ (map_zero _) (map_one _)]
  have hG : ((B.map M.L.O.subtype).map M.L.cj).transpose * ((A.map M.L.cj).transpose * G * A) *
      B.map M.L.O.subtype = G := by
    calc _ = ((A * B.map M.L.O.subtype).map M.L.cj).transpose * G * (A * B.map M.L.O.subtype) := by
            rw [hmc, Matrix.transpose_mul]
            simp only [Matrix.mul_assoc]
      _ = G := by
            rw [hAB, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul,
              Matrix.mul_one]
  have h1 : act B '' cls H ϖ Λ ((A.map M.L.cj).transpose * G * A) ⊆ cls H ϖ Λ G := by
    have := cls_act H ϖ Λ B P hBP hPB ((A.map M.L.cj).transpose * G * A)
    rwa [hG] at this
  have h2 : act P '' cls H ϖ Λ G ⊆ cls H ϖ Λ ((A.map M.L.cj).transpose * G * A) := by
    have := cls_act H ϖ Λ P B hPB hBP G
    rwa [hPA] at this
  let e : cls H ϖ Λ ((A.map M.L.cj).transpose * G * A) ≃ cls H ϖ Λ G :=
    { toFun := fun x => ⟨act B x.1, h1 ⟨x.1, x.2, rfl⟩⟩
      invFun := fun x => ⟨act P x.1, h2 ⟨x.1, x.2, rfl⟩⟩
      left_inv := fun x => Subtype.ext (by
        show act P (act B x.1) = x.1
        rw [act_act, hBP, act_one])
      right_inv := fun x => Subtype.ext (by
        show act B (act P x.1) = x.1
        rw [act_act, hPB, act_one]) }
  rw [dens_eq_cls, dens_eq_cls, Nat.card_congr e]

end

theorem congruence_density : CongStep := by
  intro F E _ _ _ _ _ _ _ M V _ _ H Λ ϖ ι _ _ A a hA hdet
  exact cong_dens H ϖ Λ A hA hdet _

end PI.UnitaryGroupMassFormula.LocDensCorank
end
end

open ValuativeRel Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocDensCorank

theorem locDensCorank_of (hC : CongStep) (hF : FieldCount) (hS : SplitCount) :
    PI.LocDensCorank.LocDensCorank := by
  intro F E _ _ _ _ _ _ _ M hloc hchar V _ _ H Λ hsd ϖ hϖ ι _ _ A a hA hdet hcard
  rw [hC F E M V H Λ ϖ ι A a hA hdet]
  by_cases hE : ∀ x : E, x ≠ 0 → IsUnit x
  · rw [if_pos hE]
    exact hF F E M hloc hchar hE V H Λ hsd ϖ hϖ ι a hcard
  · rw [if_neg hE]
    exact hS F E M hloc hchar ((PI.UnitaryGroupMassFormula.CntFormula.locE_isUnit_or_exists_algEquiv_prod_swap M.L).resolve_left hE) V H Λ hsd ϖ hϖ ι a hcard

theorem locDensCorank_of_counts (hF : FieldCount) (hS : SplitCount) : PI.LocDensCorank.LocDensCorank := by
  exact locDensCorank_of congruence_density hF hS

end PI.UnitaryGroupMassFormula.LocDensCorank
end
end

theorem local_density_corank : PI.LocDensCorank.LocDensCorank :=
  PI.UnitaryGroupMassFormula.LocDensCorank.locDensCorank_of_counts PI.UnitaryGroupMassFormula.LocDensCorank.fieldCount_holds
    PI.UnitaryGroupMassFormula.LocDensCorank.splitCount_holds
end

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LocSelfDual : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (p : PlF D), (L.H p).IsSelfDual (lattice₂ L p (VS D).L0)

def GaPlusDiag : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) →
      ∀ (Z : MatZ D) (F' : LFlag (D.sp.Y 0) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') → ∀ p : PlF D,
          ∃ (A : Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (D.s.atP p).Ep)
            (a : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → 𝒪[(D.s.atP p).Fp]),
            (∀ i j, A i j ∈ (M p).L.O) ∧ (∃ y ∈ (M p).L.O, A.det * y = 1) ∧
            GaPlus M δ p (Tn u) (Tn u') Z = (A.map (M p).L.cj).transpose *
              Matrix.diagonal (fun i => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (a i : (D.s.atP p).Fp)) * A ∧
            (Finset.univ.filter fun i => ϖ p ∣ a i).card =
              cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal

def NotIntDens : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) →
      ∀ (Z : MatZ D) (F' : LFlag (D.sp.Y 0) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        ¬ Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') → ∃ p : PlF D, densP L δ ϖ (Tn u) (Tn u') Z p = 0

end Formalism.L2.SG.Pf.Cnt
