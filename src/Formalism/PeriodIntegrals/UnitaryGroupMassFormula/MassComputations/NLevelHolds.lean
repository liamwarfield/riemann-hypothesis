module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.StrongApproxN
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.FrameStd

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Imports
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.FmatInvMul
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.SigROneTmul
noncomputable section

open NumberField Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped TensorProduct
open Matrix

namespace MassDataMassesW.NLev

section Calc

variable (I : AutInst)

theorem hA_add_right (y z z' : VA I) : hA I y (z + z') = hA I y z + hA I y z' := by
  simp only [hA, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hA_add_left (y y' z : VA I) : hA I (y + y') z = hA I y z + hA I y' z := by
  simp only [hA, Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hA_sub_right (y z z' : VA I) : hA I y (z - z') = hA I y z - hA I y z' := by
  simp only [hA, Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem hA_sub_left (y y' z : VA I) : hA I (y - y') z = hA I y z - hA I y' z := by
  simp only [hA, Formalism.UG.hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem hA_zero_left (z : VA I) : hA I 0 z = 0 := by
  simp [hA, Formalism.UG.hform]

theorem hA_smul_right (y z : VA I) (r : I.E ⊗[I.F] Af I.F) : hA I y (r • z) = r * hA I y z := by
  simp only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hA_smul_left (y z : VA I) (r : I.E ⊗[I.F] Af I.F) :
    hA I (r • y) z = Formalism.UG.sigR I.cm.sig (Af I.F) r * hA I y z := by
  simp only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hA_nat_left (y z : VA I) (c : ℕ) :
    hA I ((c : I.E ⊗[I.F] Af I.F) • y) z = (c : I.E ⊗[I.F] Af I.F) * hA I y z := by
  rw [hA_smul_left, map_natCast]

theorem hA_sum_right {ι : Type} (s : Finset ι) (y : VA I) (v : ι → VA I) :
    hA I y (∑ i ∈ s, v i) = ∑ i ∈ s, hA I y (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hA, Formalism.UG.hform]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hA_add_right, ih]

theorem sigR_inclE (e : I.E) :
    Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) e) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (star e) := by
  show Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F)) (e ⊗ₜ[I.F] (1 : Af I.F)) =
    star e ⊗ₜ[I.F] (1 : Af I.F)
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem sigR_one_tmul (a : Af I.F) :
    Formalism.UG.sigR I.cm.sig (Af I.F) ((1 : I.E) ⊗ₜ[I.F] a) = (1 : I.E) ⊗ₜ[I.F] a := by
  show Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F)) ((1 : I.E) ⊗ₜ[I.F] a) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem hA_incl (v w : Fin I.n → I.E) :
    hA I (incl I v) (incl I w) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (Formalism.UG.hform (starRingEnd I.E) I.J v w) := by
  unfold hA Formalism.UG.hform incl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.map_apply, sigR_inclE, map_sum, map_mul, starRingEnd_apply]

theorem inclE_int {e : I.E} (he : e ∈ (algebraMap (𝓞 I.E) I.E).range) :
    Formalism.UG.inclE (F := I.F) (Af I.F) e ∈ IntAf I.F I.E :=
  Subring.subset_closure (Or.inl ⟨⟨e, he⟩, rfl⟩)

theorem star_int (a : 𝓞 I.E) : star (algebraMap (𝓞 I.E) I.E a) ∈ (algebraMap (𝓞 I.E) I.E).range :=
  ⟨RingOfIntegers.mapRingHom (starRingEnd I.E) a, RingOfIntegers.mapRingHom_apply _ _⟩

theorem sigR_int {r : I.E ⊗[I.F] Af I.F} (hr : r ∈ IntAf I.F I.E) :
    Formalism.UG.sigR I.cm.sig (Af I.F) r ∈ IntAf I.F I.E := by
  have key : IntAf I.F I.E ≤ (IntAf I.F I.E).comap (Formalism.UG.sigR I.cm.sig (Af I.F)) := by
    show Subring.closure _ ≤ _
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨_, a, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · show Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E a)) ∈
        IntAf I.F I.E
      rw [sigR_inclE]
      exact inclE_int I (star_int I a)
    · show Formalism.UG.sigR I.cm.sig (Af I.F) ((1 : I.E) ⊗ₜ[I.F] y) ∈ IntAf I.F I.E
      rw [sigR_one_tmul]
      exact Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  exact key hr

theorem natCast_int (c : ℕ) : (c : I.E ⊗[I.F] Af I.F) ∈ IntAf I.F I.E := natCast_mem _ c

theorem sm {P : Submodule (IntAf I.F I.E) (VA I)} {t : I.E ⊗[I.F] Af I.F} (ht : t ∈ IntAf I.F I.E)
    {v : VA I} (hv : v ∈ P) : t • v ∈ P :=
  P.smul_mem ⟨t, ht⟩ hv

theorem Lf_le (p : Submodule (IntAf I.F I.E) (VA I)) (h : ∀ l ∈ I.L, incl I l ∈ p) : I.Lf ≤ p := by
  show Submodule.span _ _ ≤ p
  rw [Submodule.span_le]
  rintro _ ⟨⟨l, hl⟩, rfl⟩
  exact h l hl

theorem hA_int : ∀ y ∈ I.Lf, ∀ z ∈ I.Lf, hA I y z ∈ IntAf I.F I.E := by
  have gen : ∀ l ∈ I.L, ∀ z ∈ I.Lf, hA I (incl I l) z ∈ IntAf I.F I.E := by
    intro l hl
    refine Lf_le I
      { carrier := {z | hA I (incl I l) z ∈ IntAf I.F I.E}
        add_mem' := fun {a b} ha hb => by
          show hA I (incl I l) (a + b) ∈ IntAf I.F I.E
          rw [hA_add_right]; exact add_mem ha hb
        zero_mem' := by
          show hA I (incl I l) 0 ∈ IntAf I.F I.E
          simp [hA, Formalism.UG.hform]
        smul_mem' := fun r z hz => by
          show hA I (incl I l) ((r : I.E ⊗[I.F] Af I.F) • z) ∈ IntAf I.F I.E
          rw [hA_smul_right]; exact mul_mem r.2 hz } ?_
    intro l' hl'
    show hA I (incl I l) (incl I l') ∈ IntAf I.F I.E
    rw [hA_incl]
    exact inclE_int I (((I.L_dual l').1 hl') l hl)
  intro y hy z hz
  refine Lf_le I
    { carrier := {y | hA I y z ∈ IntAf I.F I.E}
      add_mem' := fun {a b} ha hb => by
        show hA I (a + b) z ∈ IntAf I.F I.E
        rw [hA_add_left]; exact add_mem ha hb
      zero_mem' := by
        show hA I 0 z ∈ IntAf I.F I.E
        rw [hA_zero_left]; exact zero_mem _
      smul_mem' := fun r y hy => by
        show hA I ((r : I.E ⊗[I.F] Af I.F) • y) z ∈ IntAf I.F I.E
        rw [hA_smul_left]; exact mul_mem (sigR_int I r.2) hy } (fun l hl => gen l hl z hz) hy

theorem hA_fmat (s : I.Gf) (x y : VA I) : hA I (I.fmat s *ᵥ x) (I.fmat s *ᵥ y) = hA I x y := by
  have hs : Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.fmat s) *
      (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))) * I.fmat s =
      I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := s.2
  unfold hA
  rw [Formalism.UG.P.hform_mulVec, hs]

theorem smul_mem_mL (m : ℕ) {x : VA I} (hx : x ∈ I.Lf) : (m : I.E ⊗[I.F] Af I.F) • x ∈ mL I m :=
  Submodule.subset_span ⟨x, hx, rfl⟩

theorem mL_le_Lf (m : ℕ) : mL I m ≤ I.Lf := by
  show Submodule.span _ _ ≤ _
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  exact sm I (natCast_int I m) hx

theorem hA_mL_left (m : ℕ) : ∀ v ∈ mL I m, ∀ w ∈ I.Lf, ZMod' I m (hA I v w) := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    intro w hw
    exact ⟨hA I y w, hA_int I y hy w hw, hA_nat_left I y w m⟩
  | zero => intro w _; exact ⟨0, zero_mem _, by rw [hA_zero_left, mul_zero]⟩
  | add x y _ _ hx hy =>
    intro w hw
    obtain ⟨t, ht, he⟩ := hx w hw
    obtain ⟨t', ht', he'⟩ := hy w hw
    exact ⟨t + t', add_mem ht ht', by rw [hA_add_left, he, he', mul_add]⟩
  | smul r x _ hx =>
    intro w hw
    obtain ⟨t, ht, he⟩ := hx w hw
    refine ⟨Formalism.UG.sigR I.cm.sig (Af I.F) r * t, mul_mem (sigR_int I r.2) ht, ?_⟩
    show hA I ((r : I.E ⊗[I.F] Af I.F) • x) w = _
    rw [hA_smul_left, he]; ring

theorem bezout {P : Submodule (IntAf I.F I.E) (VA I)} {m c : ℕ} (hc : Nat.Coprime c m) (hmP : mL I m ≤ P)
    {v : VA I} (hv : v ∈ I.Lf) (hcv : (c : I.E ⊗[I.F] Af I.F) • v ∈ P) : v ∈ P := by
  obtain ⟨a, b, hab⟩ : IsCoprime (c : ℤ) (m : ℤ) := Nat.isCoprime_iff_coprime.2 hc
  have h1 : (((a * c + b * m : ℤ)) : I.E ⊗[I.F] Af I.F) = 1 := by rw [hab]; simp
  have hv' : v = a • ((c : I.E ⊗[I.F] Af I.F) • v) + b • ((m : I.E ⊗[I.F] Af I.F) • v) := by
    calc v = (((a * c + b * m : ℤ)) : I.E ⊗[I.F] Af I.F) • v := by rw [h1, one_smul]
      _ = _ := by
        rw [← Int.cast_smul_eq_zsmul (I.E ⊗[I.F] Af I.F) a, ← Int.cast_smul_eq_zsmul (I.E ⊗[I.F] Af I.F) b,
          smul_smul, smul_smul, ← add_smul]
        push_cast; ring_nf
  rw [hv']
  exact add_mem (zsmul_mem hcv a) (zsmul_mem (hmP (smul_mem_mL I m hv)) b)

theorem dvd_smul {P : Submodule (IntAf I.F I.E) (VA I)} {c d : ℕ} (h : c ∣ d) {v : VA I}
    (hv : (c : I.E ⊗[I.F] Af I.F) • v ∈ P) : (d : I.E ⊗[I.F] Af I.F) • v ∈ P := by
  obtain ⟨k, rfl⟩ := h
  rw [Nat.cast_mul, mul_comm, mul_smul]
  exact sm I (natCast_int I k) hv

theorem close {P : Submodule (IntAf I.F I.E) (VA I)} {m : ℕ} (hmP : mL I m ≤ P) {v w r : VA I}
    (hv : v ∈ I.Lf) (hvr : v = w + r) {c k : ℕ} (hc : Nat.Coprime c m) (hk : Nat.Coprime k m)
    (hw : (k : I.E ⊗[I.F] Af I.F) • w ∈ P) (hr : (c : I.E ⊗[I.F] Af I.F) • r ∈ mL I m) : v ∈ P := by
  refine bezout I (Nat.coprime_mul_iff_left.mpr ⟨hk, hc⟩) hmP hv ?_
  rw [hvr, smul_add, Nat.cast_mul]
  refine add_mem ?_ ?_
  · rw [mul_comm, mul_smul]; exact sm I (natCast_int I c) hw
  · rw [mul_smul]; exact hmP (sm I (natCast_int I k) hr)

end Calc

end MassDataMassesW.NLev
end
end

noncomputable section

open NumberField Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped TensorProduct
open Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace MassDataMassesW.NLev

section Grp

variable {I : AutInst}

theorem Kset_Lf {x : I.Gf} (hx : x ∈ I.Kset) : ∀ v ∈ I.Lf, I.fmat x *ᵥ v ∈ I.Lf := by
  intro v hv
  have h : ∀ w, w ∈ I.Lf ↔ I.fmat x *ᵥ w ∈ I.Lf := hx
  exact (h v).1 hv

theorem Kset_inv {x : I.Gf} (hx : x ∈ I.Kset) : x⁻¹ ∈ I.Kset := by
  show ((x⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
  rw [InvMemClass.coe_inv]
  exact (Formalism.UG.stabGL I.Lf).inv_mem hx

theorem Kset_mul {x y : I.Gf} (hx : x ∈ I.Kset) (hy : y ∈ I.Kset) : x * y ∈ I.Kset := by
  show ((x * y : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
  rw [MulMemClass.coe_mul]
  exact (Formalism.UG.stabGL I.Lf).mul_mem hx hy

theorem fmat_inv_mul (x : I.Gf) : I.fmat x⁻¹ * I.fmat x = 1 := by
  simp only [Formalism.MainNotions.S.AutInst.fmat, InvMemClass.coe_inv, Units.inv_mul]

theorem fmat_mul_inv (x : I.Gf) : I.fmat x * I.fmat x⁻¹ = 1 := by
  simp only [Formalism.MainNotions.S.AutInst.fmat, InvMemClass.coe_inv, Units.mul_inv]

def Tm (Ai By A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (v : VA I) : VA I :=
  Ai *ᵥ ((By - 1) *ᵥ (A *ᵥ v))

theorem Tm_add (Ai By A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (v w : VA I) :
    Tm Ai By A (v + w) = Tm Ai By A v + Tm Ai By A w := by
  simp only [Tm, Matrix.mulVec_add]

theorem Tm_sub (Ai By A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (v w : VA I) :
    Tm Ai By A (v - w) = Tm Ai By A v - Tm Ai By A w := by
  simp only [Tm, Matrix.mulVec_sub]

theorem Tm_smul (Ai By A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (r : I.E ⊗[I.F] Af I.F) (v : VA I) :
    Tm Ai By A (r • v) = r • Tm Ai By A v := by
  simp only [Tm, Matrix.mulVec_smul]

theorem sub_one_Lf {M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hM : ∀ v ∈ I.Lf, M *ᵥ v ∈ I.Lf) :
    ∀ v ∈ I.Lf, (M - 1) *ᵥ v ∈ I.Lf := by
  intro v hv
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  exact I.Lf.sub_mem (hM v hv) hv

theorem Tm_Lf {Ai By A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hAi : ∀ v ∈ I.Lf, Ai *ᵥ v ∈ I.Lf)
    (hBy : ∀ v ∈ I.Lf, By *ᵥ v ∈ I.Lf) (hA : ∀ v ∈ I.Lf, A *ᵥ v ∈ I.Lf) :
    ∀ v ∈ I.Lf, Tm Ai By A v ∈ I.Lf :=
  fun v hv => hAi _ (sub_one_Lf hBy _ (hA v hv))

theorem Tm_mL (m : ℕ) {Ai By A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)}
    (hAi : ∀ v ∈ I.Lf, Ai *ᵥ v ∈ I.Lf) (hBy : ∀ v ∈ I.Lf, By *ᵥ v ∈ I.Lf) (hA : ∀ v ∈ I.Lf, A *ᵥ v ∈ I.Lf) :
    ∀ v ∈ mL I m, Tm Ai By A v ∈ mL I m := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    rw [Tm_smul]
    exact Submodule.subset_span ⟨_, Tm_Lf hAi hBy hA x hx, rfl⟩
  | zero =>
    have h0 : Tm Ai By A 0 = 0 := by simp [Tm]
    rw [h0]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [Tm_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have h1 : Tm Ai By A (a • x) = a • Tm Ai By A x := by
      rw [Subring.smul_def, Subring.smul_def, Tm_smul]
    rw [h1]
    exact Submodule.smul_mem _ a hx

end Grp

variable {D : Formalism.BasicNotions.D7} (X : HidaSetting D)

theorem sig_eq : (starRingEnd X.B.I.E) = (X.B.I.cm.sig : X.B.I.E →+* X.B.I.E) := by
  first
  | rfl
  | exact RingHom.ext fun _ => rfl

theorem hA_e_f (a b : Fin D.R.rS) :
    hA X.B.I (incl X.B.I (X.eR a)) (incl X.B.I (X.fR b)) = if a = b then 1 else 0 := by
  rw [hA_incl, sig_eq]
  have h := MassDataLevelSSteps.FrameW.hE_crdOf X (X.eX a) (X.fY b)
  change Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE X.B.I.cm.sig X.B.I.J
    (crdOf X.B.I X.ιE X.bas (X.eX a)) (crdOf X.B.I X.ιE X.bas (X.fY b))) = _
  rw [h, X.ef]
  split_ifs <;> simp

theorem hA_f_e (b a : Fin D.R.rS) :
    hA X.B.I (incl X.B.I (X.fR b)) (incl X.B.I (X.eR a)) = if b = a then 1 else 0 := by
  rw [hA_incl, sig_eq]
  have h := MassDataLevelSSteps.FrameW.hE_crdOf X (X.fY b) (X.eX a)
  change Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE X.B.I.cm.sig X.B.I.J
    (crdOf X.B.I X.ιE X.bas (X.fY b)) (crdOf X.B.I X.ιE X.bas (X.eX a))) = _
  rw [h, ← LinearMap.isSymm_def.1 (VS D).herm (X.eX a) (X.fY b), X.ef]
  by_cases hab : a = b
  · subst hab; simp
  · simp [hab, Ne.symm hab]

theorem key {c d : ℕ} (hfL : ∀ b, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (X.fR b) ∈ X.B.I.Lf)
    (hec : ∀ b, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 b - incl X.B.I (X.eR b)) ∈ mL X.B.I X.B.g)
    {s : Set (Fin D.R.rS)} {w : VA X.B.I}
    (hw : w ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ((fun b => incl X.B.I (X.eR b)) '' s))
    (hdw : (d : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w ∈ X.B.I.Lf) :
    ((c * d * c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w ∈
      Submodule.span (IntAf X.B.I.F X.B.I.E) (X.e0 '' s) ⊔ mL X.B.I X.B.g := by
  classical
  obtain ⟨l, hls, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination _).1 hw
  have hsum : Finsupp.linearCombination (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (fun b => incl X.B.I (X.eR b)) l =
      ∑ b, l b • incl X.B.I (X.eR b) := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; exact zero_smul _ _
  rw [hsum] at hdw ⊢
  have hcoef : ∀ b, ((c * d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * l b ∈ IntAf X.B.I.F X.B.I.E := by
    intro b
    have h := hA_int X.B.I _ (hfL b) _ hdw
    rw [hA_nat_left, hA_smul_right, hA_sum_right] at h
    simp only [hA_smul_right, hA_f_e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true] at h
    convert h using 1
    push_cast; ring
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun b _ => ?_
  by_cases hb : l b = 0
  · rw [hb, zero_smul, smul_zero]; exact zero_mem _
  have hbs : b ∈ s := hls (Finsupp.mem_support_iff.2 hb)
  have heq : ((c * d * c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (l b • incl X.B.I (X.eR b)) =
      (((c * d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * l b) • ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.e0 b) -
      (((c * d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * l b) •
        ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 b - incl X.B.I (X.eR b))) := by
    rw [← smul_sub, ← smul_sub, sub_sub_cancel]
    simp only [smul_smul]
    congr 1; push_cast; ring
  rw [heq]
  refine sub_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right (sm X.B.I (hcoef b) (hec b)))
  exact sm X.B.I (hcoef b) (sm X.B.I (natCast_int X.B.I c) (Submodule.subset_span ⟨b, hbs, rfl⟩))

theorem mults (u : D.what₂.Word) : ∃ c : ℕ, Nat.Coprime c X.B.g ∧
    (∀ b, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 b - incl X.B.I (X.eR b)) ∈ mL X.B.I X.B.g) ∧
    (∀ b, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.f0 b - incl X.B.I (X.fR b)) ∈ mL X.B.I X.B.g) ∧
    (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u) - X.z0) ∈
      mL X.B.I X.B.g := by
  have h1 : ∀ a, ∃ c : ℕ, Nat.Coprime c X.B.g ∧
      (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 a - incl X.B.I (X.eR a)) ∈ mL X.B.I X.B.g :=
    fun a => (X.basisApprox a).1
  have h2 : ∀ a, ∃ c : ℕ, Nat.Coprime c X.B.g ∧
      (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.f0 a - incl X.B.I (X.fR a)) ∈ mL X.B.I X.B.g :=
    fun a => (X.basisApprox a).2
  have h3 : ∃ c : ℕ, Nat.Coprime c X.B.g ∧
      (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u) - X.z0) ∈
        mL X.B.I X.B.g := X.xu_z u
  choose ce hce1 hce2 using h1
  choose cf hcf1 hcf2 using h2
  obtain ⟨cz, hcz1, hcz2⟩ := h3
  have hP : ∀ b, ce b * cf b ∣ ∏ a, ce a * cf a := fun b =>
    Finset.dvd_prod_of_mem (fun a => ce a * cf a) (Finset.mem_univ b)
  have hcop : Nat.Coprime ((∏ a, ce a * cf a) * cz) X.B.g :=
    Nat.Coprime.mul_left (Nat.Coprime.prod_left fun a _ => Nat.Coprime.mul_left (hce1 a) (hcf1 a)) hcz1
  have hd1 : ∀ b, ce b ∣ (∏ a, ce a * cf a) * cz := fun b =>
    Dvd.dvd.mul_right ((Dvd.intro (cf b) rfl).trans (hP b)) cz
  have hd2 : ∀ b, cf b ∣ (∏ a, ce a * cf a) * cz := fun b =>
    Dvd.dvd.mul_right ((Dvd.intro_left (ce b) rfl).trans (hP b)) cz
  have hd3 : cz ∣ (∏ a, ce a * cf a) * cz := Dvd.intro_left _ rfl
  exact ⟨(∏ a, ce a * cf a) * cz, hcop, fun b => dvd_smul X.B.I (hd1 b) (hce2 b),
    fun b => dvd_smul X.B.I (hd2 b) (hcf2 b), dvd_smul X.B.I hd3 hcz2⟩

end MassDataMassesW.NLev
end
end

noncomputable section

open NumberField Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped TensorProduct
open Matrix

namespace MassDataMassesW.NLev

variable {D : Formalism.BasicNotions.D7} (X : HidaSetting D)

theorem core {c : ℕ} (hc : Nat.Coprime c X.B.g)
    (hec : ∀ b, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 b - incl X.B.I (X.eR b)) ∈ mL X.B.I X.B.g)
    (hfc : ∀ b, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.f0 b - incl X.B.I (X.fR b)) ∈ mL X.B.I X.B.g)
    {A Ai By : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)}
    (hAL : ∀ v ∈ X.B.I.Lf, A *ᵥ v ∈ X.B.I.Lf) (hAiL : ∀ v ∈ X.B.I.Lf, Ai *ᵥ v ∈ X.B.I.Lf)
    (hByL : ∀ v ∈ X.B.I.Lf, By *ᵥ v ∈ X.B.I.Lf) (hAiA : Ai * A = 1) (hAAi : A * Ai = 1)
    (hAform : ∀ x y, hA X.B.I (A *ᵥ x) (A *ᵥ y) = hA X.B.I x y)
    (hAe : ∀ a, A *ᵥ incl X.B.I (X.eR a) = incl X.B.I (X.eR a))
    (hN1 : ∀ a, (By - 1) *ᵥ incl X.B.I (X.eR a) ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
      ((fun b => incl X.B.I (X.eR b)) '' {b | b.1 < a.1}))
    (zz : VA X.B.I)
    (hN2 : (By - 1) *ᵥ zz ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
      (Set.range fun b => incl X.B.I (X.eR b)))
    (hN3 : ∀ v : VA X.B.I, (∀ a, hA X.B.I (incl X.B.I (X.eR a)) v = 0) →
      (By - 1) *ᵥ v ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range fun b => incl X.B.I (X.eR b)))
    (hzc : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (Ai *ᵥ zz - X.z0) ∈ mL X.B.I X.B.g) :
    (∀ a, InMod X.B.I X.B.g (X.e0 '' {b | b.1 < a.1}) (Tm Ai By A (X.e0 a))) ∧
      InMod X.B.I X.B.g (Set.range X.e0) (Tm Ai By A X.z0) ∧
      ∀ i, InMod X.B.I X.B.g (Set.range X.e0 ∪ X.bw '' {j | j.1 < i.1}) (Tm Ai By A (X.bw i)) := by
  have hAie : ∀ a, Ai *ᵥ incl X.B.I (X.eR a) = incl X.B.I (X.eR a) := by
    intro a
    conv_lhs => rw [← hAe a]
    rw [mulVec_mulVec, hAiA, one_mulVec]
  have hspan : ∀ (s : Set (Fin D.R.rS)) (w : VA X.B.I),
      w ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ((fun b => incl X.B.I (X.eR b)) '' s) →
      Ai *ᵥ w ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ((fun b => incl X.B.I (X.eR b)) '' s) := by
    intro s w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, rfl⟩ := hx
      rw [hAie]; exact Submodule.subset_span ⟨b, hb, rfl⟩
    | zero => rw [mulVec_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
    | smul r x _ hx => rw [mulVec_smul]; exact Submodule.smul_mem _ r hx
  have hTL := Tm_Lf hAiL hByL hAL
  have hTmL := Tm_mL X.B.g hAiL hByL hAL
  have hmLL := mL_le_Lf X.B.I X.B.g
  have hcI := natCast_int X.B.I c
  have hWL : ∀ v ∈ X.B.I.Lf, Ai *ᵥ ((By - 1) *ᵥ v) ∈ X.B.I.Lf := fun v hv => hAiL _ (sub_one_Lf hByL _ hv)
  have heL : ∀ b, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (X.eR b) ∈ X.B.I.Lf := by
    intro b
    have h : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (X.eR b) =
        (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.e0 b -
          (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 b - incl X.B.I (X.eR b)) := by
      rw [← smul_sub, sub_sub_cancel]
    rw [h]; exact sub_mem (sm X.B.I hcI (X.vectorsInLattice.1 b).1) (hmLL (hec b))
  have hfL : ∀ b, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (X.fR b) ∈ X.B.I.Lf := by
    intro b
    have h : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (X.fR b) =
        (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.f0 b -
          (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.f0 b - incl X.B.I (X.fR b)) := by
      rw [← smul_sub, sub_sub_cancel]
    rw [h]; exact sub_mem (sm X.B.I hcI (X.vectorsInLattice.1 b).2) (hmLL (hfc b))
  have hsig : starRingEnd X.B.I.E = (X.B.I.cm.sig : X.B.I.E →+* X.B.I.E) := by
    exact RingHom.ext fun _ => rfl
  have hpair (a b : Fin D.R.rS) :
      hA X.B.I (incl X.B.I (X.eR a)) (incl X.B.I (X.fR b)) = if a = b then 1 else 0 := by
    rw [hA_incl, hsig]
    change Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE X.B.I.cm.sig X.B.I.J
        (crdOf X.B.I X.ιE X.bas (X.eX a)) (crdOf X.B.I X.ιE X.bas (X.fY b))) = _
    rw [MassDataLevelSSteps.FrameW.hE_crdOf X, X.ef]
    split_ifs <;> simp
  have hpair_rev (b a : Fin D.R.rS) :
      hA X.B.I (incl X.B.I (X.fR b)) (incl X.B.I (X.eR a)) = if b = a then 1 else 0 := by
    let : StarRing D.host.E := D.host.cmStar
    rw [hA_incl, hsig]
    change Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE X.B.I.cm.sig X.B.I.J
        (crdOf X.B.I X.ιE X.bas (X.fY b)) (crdOf X.B.I X.ιE X.bas (X.eX a))) = _
    rw [MassDataLevelSSteps.FrameW.hE_crdOf X,
      ← LinearMap.isSymm_def.1 (VS D).herm (X.eX a) (X.fY b), X.ef]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Ne.symm hab]
  have hclear {d : ℕ} {s : Set (Fin D.R.rS)} {w : VA X.B.I}
      (hw : w ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ((fun b => incl X.B.I (X.eR b)) '' s))
      (hdw : (d : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w ∈ X.B.I.Lf) :
      ((c * d * c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w ∈
        Submodule.span (IntAf X.B.I.F X.B.I.E) (X.e0 '' s) ⊔ mL X.B.I X.B.g := by
    classical
    obtain ⟨l, hls, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination _).1 hw
    have hsum : Finsupp.linearCombination (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (fun b => incl X.B.I (X.eR b)) l =
        ∑ b, l b • incl X.B.I (X.eR b) := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
      intro i
      exact zero_smul _ _
    rw [hsum] at hdw ⊢
    have hcoef (b : Fin D.R.rS) :
        ((c * d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * l b ∈ IntAf X.B.I.F X.B.I.E := by
      have h := hA_int X.B.I _ (hfL b) _ hdw
      rw [hA_nat_left, hA_smul_right, hA_sum_right] at h
      simp only [hA_smul_right, hpair_rev, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true] at h
      convert h using 1
      push_cast
      ring
    rw [Finset.smul_sum]
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hb : l b = 0
    · rw [hb, zero_smul, smul_zero]
      exact zero_mem _
    have hbs : b ∈ s := hls (Finsupp.mem_support_iff.2 hb)
    have heq : ((c * d * c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (l b • incl X.B.I (X.eR b)) =
        (((c * d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * l b) • ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.e0 b) -
        (((c * d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * l b) •
          ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 b - incl X.B.I (X.eR b))) := by
      rw [← smul_sub, ← smul_sub, sub_sub_cancel]
      simp only [smul_smul]
      congr 1
      push_cast
      ring
    rw [heq]
    refine sub_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right (sm X.B.I (hcoef b) (hec b)))
    exact sm X.B.I (hcoef b) (sm X.B.I hcI (Submodule.subset_span ⟨b, hbs, rfl⟩))
  have hc3 : Nat.Coprime (c * c * c) X.B.g := Nat.Coprime.mul_left (Nat.Coprime.mul_left hc hc) hc
  refine ⟨fun a => ?_, ?_, fun i => ?_⟩
  ·
    have hv := hTL _ (X.vectorsInLattice.1 a).1
    have hTe : Tm Ai By A (incl X.B.I (X.eR a)) = Ai *ᵥ ((By - 1) *ᵥ incl X.B.I (X.eR a)) := by
      simp only [Tm, hAe]
    have hsplit : Tm Ai By A (X.e0 a) =
        Ai *ᵥ ((By - 1) *ᵥ incl X.B.I (X.eR a)) + Tm Ai By A (X.e0 a - incl X.B.I (X.eR a)) := by
      rw [Tm_sub, hTe]; abel
    have hw := hspan _ _ (hN1 a)
    have hdw : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (Ai *ᵥ ((By - 1) *ᵥ incl X.B.I (X.eR a))) ∈ X.B.I.Lf := by
      rw [← mulVec_smul, ← mulVec_smul]; exact hWL _ (heL a)
    have hk := hclear hw hdw
    unfold InMod
    refine close X.B.I le_sup_right hv hsplit hc hc3 hk ?_
    rw [← Tm_smul]; exact hTmL _ (hec a)
  ·
    have hv := hTL _ X.vectorsInLattice.2.1
    have hAq : A *ᵥ (Ai *ᵥ zz) = zz := by rw [mulVec_mulVec, hAAi, one_mulVec]
    have hTq : Tm Ai By A (Ai *ᵥ zz) = Ai *ᵥ ((By - 1) *ᵥ zz) := by simp only [Tm, hAq]
    have hsplit : Tm Ai By A X.z0 = Ai *ᵥ ((By - 1) *ᵥ zz) + -Tm Ai By A (Ai *ᵥ zz - X.z0) := by
      rw [Tm_sub, hTq]; abel
    have hw : Ai *ᵥ ((By - 1) *ᵥ zz) ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
        ((fun b => incl X.B.I (X.eR b)) '' Set.univ) := hspan _ _ (by rw [Set.image_univ]; exact hN2)
    have hcq : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (Ai *ᵥ zz) ∈ X.B.I.Lf := by
      have h : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (Ai *ᵥ zz) =
          (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.z0 + (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (Ai *ᵥ zz - X.z0) := by
        rw [← smul_add, add_sub_cancel]
      rw [h]; exact add_mem (sm X.B.I hcI X.vectorsInLattice.2.1) (hmLL hzc)
    have hcz : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • zz ∈ X.B.I.Lf := by
      rw [← hAq, ← mulVec_smul]; exact hAL _ hcq
    have hdw : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (Ai *ᵥ ((By - 1) *ᵥ zz)) ∈ X.B.I.Lf := by
      rw [← mulVec_smul, ← mulVec_smul]; exact hWL _ hcz
    have hk := hclear hw hdw
    rw [Set.image_univ] at hk
    unfold InMod
    refine close X.B.I le_sup_right hv hsplit hc hc3 hk ?_
    rw [smul_neg, ← Tm_smul]; exact neg_mem (hTmL _ hzc)
  ·
    have hbL := (X.vectorsInLattice.2.2 i).1
    have hv := hTL _ hbL
    obtain ⟨t, ht⟩ : ∃ t, A *ᵥ X.bw i = t := ⟨_, rfl⟩
    have htL : t ∈ X.B.I.Lf := ht ▸ hAL _ hbL
    obtain ⟨t', ht'⟩ : ∃ t', t - ∑ b, hA X.B.I (incl X.B.I (X.eR b)) t • incl X.B.I (X.fR b) = t' := ⟨_, rfl⟩
    have horth : ∀ a, hA X.B.I (incl X.B.I (X.eR a)) t' = 0 := by
      intro a
      rw [← ht', hA_sub_right, hA_sum_right]
      simp only [hA_smul_right, hpair, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
        ite_true, sub_self]
    have hsplit : Tm Ai By A (X.bw i) = Ai *ᵥ ((By - 1) *ᵥ t') +
        ∑ b, hA X.B.I (incl X.B.I (X.eR b)) t • (Ai *ᵥ ((By - 1) *ᵥ incl X.B.I (X.fR b))) := by
      have h : t = t' + ∑ b, hA X.B.I (incl X.B.I (X.eR b)) t • incl X.B.I (X.fR b) := by
        rw [← ht', sub_add_cancel]
      simp only [Tm, ht]
      conv_lhs => rw [h]
      rw [mulVec_add, mulVec_add, mulVec_sum, mulVec_sum]
      simp only [mulVec_smul]
    have hw : Ai *ᵥ ((By - 1) *ᵥ t') ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
        ((fun b => incl X.B.I (X.eR b)) '' Set.univ) :=
      hspan _ _ (by rw [Set.image_univ]; exact hN3 _ horth)
    have hZ : ∀ b, ∃ τ ∈ IntAf X.B.I.F X.B.I.E,
        (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I (incl X.B.I (X.eR b)) t =
          (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * τ := by
      intro b
      have h1 : hA X.B.I (incl X.B.I (X.eR b)) t = hA X.B.I (incl X.B.I (X.eR b)) (X.bw i) := by
        calc hA X.B.I (incl X.B.I (X.eR b)) t
            = hA X.B.I (A *ᵥ incl X.B.I (X.eR b)) (A *ᵥ X.bw i) := by rw [hAe, ht]
          _ = _ := hAform _ _
      have h2 : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I (incl X.B.I (X.eR b)) (X.bw i) =
          (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I (X.e0 b) (X.bw i) -
            hA X.B.I ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 b - incl X.B.I (X.eR b))) (X.bw i) := by
        rw [hA_nat_left, hA_sub_left]; ring
      obtain ⟨t1, ht1, he1⟩ := ((X.weightVectorsIntegral i).2.2 b).1
      obtain ⟨t2, ht2, he2⟩ := hA_mL_left X.B.I X.B.g _ (hec b) _ hbL
      exact ⟨(c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t1 - t2, sub_mem (mul_mem hcI ht1) ht2,
        by rw [h1, h2, he1, he2]; ring⟩
    choose τ hτI hτ using hZ
    have hterm : ∀ b (V : VA X.B.I),
        ((c * c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (incl X.B.I (X.eR b)) t • V) =
          τ b • ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • V)) := by
      intro b V
      simp only [smul_smul]
      congr 1
      push_cast
      linear_combination (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hτ b
    have hr : ((c * c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) •
        ∑ b, hA X.B.I (incl X.B.I (X.eR b)) t • (Ai *ᵥ ((By - 1) *ᵥ incl X.B.I (X.fR b))) ∈ mL X.B.I X.B.g := by
      rw [Finset.smul_sum]
      refine Submodule.sum_mem _ fun b _ => ?_
      rw [hterm]
      refine sm X.B.I (hτI b) (smul_mem_mL X.B.I X.B.g ?_)
      rw [← mulVec_smul, ← mulVec_smul]; exact hWL _ (hfL b)
    have hdw : ((c * c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (Ai *ᵥ ((By - 1) *ᵥ t')) ∈ X.B.I.Lf := by
      rw [← mulVec_smul, ← mulVec_smul]
      refine hWL _ ?_
      rw [← ht', smul_sub, Finset.smul_sum]
      refine sub_mem (sm X.B.I (natCast_int X.B.I _) htL) (Submodule.sum_mem _ fun b _ => ?_)
      rw [hterm]
      exact hmLL (sm X.B.I (hτI b) (smul_mem_mL X.B.I X.B.g (hfL b)))
    have hk := hclear hw hdw
    have hle : Submodule.span (IntAf X.B.I.F X.B.I.E) (X.e0 '' Set.univ) ⊔ mL X.B.I X.B.g ≤
        Submodule.span (IntAf X.B.I.F X.B.I.E) (Set.range X.e0 ∪ X.bw '' {j | j.1 < i.1}) ⊔ mL X.B.I X.B.g :=
      sup_le_sup_right (Submodule.span_mono (by rw [Set.image_univ]; exact Set.subset_union_left)) _
    have hcc : Nat.Coprime (c * c) X.B.g := Nat.Coprime.mul_left hc hc
    have hc4 : Nat.Coprime (c * (c * c) * c) X.B.g := Nat.Coprime.mul_left (Nat.Coprime.mul_left hc hcc) hc
    unfold InMod
    exact close X.B.I le_sup_right hv hsplit hcc hc4 (hle hk) hr

end MassDataMassesW.NLev
end
end

noncomputable section

open NumberField Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped TensorProduct
open Matrix

namespace MassDataMassesW.NLev

theorem nLevel_holds : NLevel := by
  intro D X u y hyN hyK
  obtain ⟨c, hc, hec, hfc, hzc⟩ := mults X u
  have hxK := X.xu_K u
  have hxiK : (X.xu u)⁻¹ ∈ X.B.I.Kset := Kset_inv hxK
  have hκK : (X.xu u)⁻¹ * y * X.xu u ∈ X.B.I.Kset := Kset_mul (Kset_mul hxiK hyK) hxK
  have hAiA := fmat_inv_mul (X.xu u)
  have hT : ∀ v, (X.B.I.fmat ((X.xu u)⁻¹ * y * X.xu u) - 1) *ᵥ v =
      Tm (X.B.I.fmat (X.xu u)⁻¹) (X.B.I.fmat y) (X.B.I.fmat (X.xu u)) v := by
    intro v
    show (X.B.I.fmat (X.xu u)⁻¹ * X.B.I.fmat y * X.B.I.fmat (X.xu u) - 1) *ᵥ v = _
    simp only [Tm, sub_mulVec, one_mulVec, mulVec_mulVec, Matrix.mul_assoc]
    rw [sub_mul, one_mul, mul_sub, hAiA, sub_mulVec, one_mulVec]
  have hN : y ∈ Nfin X.B.I X.eR (X.zR u) := hyN
  have hcore := core X hc hec hfc (Kset_Lf hxK) (Kset_Lf hxiK) (Kset_Lf hyK) hAiA (fmat_mul_inv (X.xu u))
    (hA_fmat X.B.I (X.xu u)) (fun a => (X.xu_fix u a).1) hN.1 (incl X.B.I (X.zR u)) hN.2.1 hN.2.2 hzc
  refine ⟨hκK, ?_⟩
  unfold K2cong
  simp only [hT]
  exact hcore

end MassDataMassesW.NLev
