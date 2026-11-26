module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ColPhaseCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LeviMul
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.NormCut

section LeviMul

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

theorem resT_of_mem (v : TR.Pl) {z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hz : z ∈ IntAf X.B.I.F X.B.I.E) :
    resT TR v z = TR.res v ⟨z, hz⟩ := by
  unfold resT; rw [dite_eq_left hz]

theorem res_eq_zero_of_Z (v : TR.Pl) {z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hz : z ∈ IntAf X.B.I.F X.B.I.E)
    (hZ : ZMod' X.B.I X.B.g z) : TR.res v ⟨z, hz⟩ = 0 :=
  (TR.res_ker ⟨z, hz⟩).2 (Z_smul X.B.I X.B.g X.ew_int hZ) v

def PhiSub (x : X.B.I.Gf) (i : Fin D.R.k) : Submodule (IntAf X.B.I.F X.B.I.E) (VA X.B.I) where
  carrier := {z | ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ z) -
    ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) z)}
  add_mem' {z w} hz hw := by
    show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ (z + w)) -
      ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) (z + w))
    have e : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ (z + w)) -
        ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) (z + w) =
        (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ z) -
          ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) z) +
        (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ w) -
          ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) w) := by
      simp only [Matrix.mulVec_add, hA_add_right, mul_add, Finset.sum_add_distrib]; ring
    rw [e]; exact Z_add X.B.I X.B.g hz hw
  zero_mem' := by
    show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ 0) -
      ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) 0)
    have h0 : ∀ u : VA X.B.I, hA X.B.I u 0 = 0 := fun u => (hL X.B.I u).map_zero
    simp only [Matrix.mulVec_zero, h0, mul_zero, Finset.sum_const_zero, sub_zero]
    exact Z_zero X.B.I X.B.g
  smul_mem' c z hz := by
    show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z)) -
      ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z))
    have e : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z)) -
        ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z) =
        (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ z) -
          ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) z) := by
      simp only [Matrix.mulVec_smul, hA_smul_right, mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [e]; exact Z_smul X.B.I X.B.g c.2 hz

theorem dual_beta_reference_congruence (i : Fin D.R.k) (a : Fin D.R.rS) : ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.e0 a)) := by
  rw [hA_symm]
  exact Z_sig X.B.I X.B.g ((X.weightVectorsIntegral i).2.2 a).2.2.1

theorem leviM_mul {x y : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hy : y ∈ X.B.I.Kset)
    (hyb : ∀ j, X.B.I.fmat y *ᵥ X.bw j ∈ Mo X.B.I X.B.g (Set.range X.e0 ∪ Set.range X.bw))
    (hxe : ∀ a, X.B.I.fmat x *ᵥ X.e0 a ∈ Mo X.B.I X.B.g (Set.range X.e0)) (v : TR.Pl) :
    leviM TR (x * y) v = leviM TR x v * leviM TR y v := by
  have hbw : ∀ j, X.bw j ∈ X.B.I.Lf := fun j => (X.vectorsInLattice.2.2 j).1
  have hbwd : ∀ j, X.bwd j ∈ X.B.I.Lf := fun j => (X.vectorsInLattice.2.2 j).2
  have he0 : ∀ a, X.e0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).1

  have key : ∀ i, Mo X.B.I X.B.g (Set.range X.e0 ∪ Set.range X.bw) ≤ PhiSub x i := by
    intro i
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro z (⟨a, rfl⟩ | ⟨m, rfl⟩)
      · show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.e0 a) -
          ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) (X.e0 a))
        refine Z_sub X.B.I X.B.g ?_ (Z_sum X.B.I X.B.g _ _ fun l _ =>
          Z_smul X.B.I X.B.g (hA_int X.B.I (hbwd i) (K_mv X.B.I hx (hbw l))) (dual_beta_reference_congruence l a))
        have hQ : Mo X.B.I X.B.g (Set.range X.e0) ≤ Qs X.B.I X.B.g (X.bwd i) :=
          sup_le (Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact dual_beta_reference_congruence i b)) (mL_Qs X.B.I X.B.g (hbwd i))
        exact hQ (hxe a)
      · show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) -
          ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) (X.bw m))
        have hw : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) = X.ew * hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) := by
          conv_lhs => rw [X.bw_w m, Matrix.mulVec_smul, hA_smul_right]
        have e : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) -
            ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) (X.bw m) =
            (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) - hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) * X.ew) -
            ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) *
              (hA X.B.I (X.bwd l) (X.bw m) - if l = m then X.ew else 0) := by
          simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
            if_true]
          ring
        have e2 : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) - hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m) * X.ew = 0 := by
          rw [hw]
          have := X.ew_idem
          linear_combination (-(hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw m))) * this
        rw [e, e2, zero_sub]
        have := Z_sum X.B.I X.B.g Finset.univ _ fun l _ =>
          Z_smul X.B.I X.B.g (hA_int X.B.I (hbwd i) (K_mv X.B.I hx (hbw l))) (X.bw_dual l m)
        obtain ⟨t, ht, htt⟩ := this
        exact ⟨-t, neg_mem ht, by rw [htt]; ring⟩
    · rintro _ ⟨w, hw, rfl⟩
      show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w)) -
        ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w))
      refine ⟨hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ w) -
        ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) w, ?_, ?_⟩
      · exact sub_mem (hA_int X.B.I (hbwd i) (K_mv X.B.I hx hw)) (sum_mem fun l _ =>
          mul_mem (hA_int X.B.I (hbwd i) (K_mv X.B.I hx (hbw l))) (hA_int X.B.I (hbwd l) hw))
      · simp only [Matrix.mulVec_smul, hA_smul_right, mul_sub, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun l _ => ?_
        ring
  ext i j
  have hxy : X.B.I.fmat (x * y) *ᵥ X.bw j = X.B.I.fmat x *ᵥ (X.B.I.fmat y *ᵥ X.bw j) := by
    rw [fmat_mul, Matrix.mulVec_mulVec]
  have hZ := key i (hyb j)
  simp only [PhiSub, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq] at hZ
  rw [← hxy] at hZ

  have hI1 : hA X.B.I (X.bwd i) (X.B.I.fmat (x * y) *ᵥ X.bw j) ∈ IntAf X.B.I.F X.B.I.E :=
    hA_int X.B.I (hbwd i) (K_mv X.B.I (K_mul X.B.I hx hy) (hbw j))
  have hI2 : ∀ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) ∈ IntAf X.B.I.F X.B.I.E :=
    fun l => hA_int X.B.I (hbwd i) (K_mv X.B.I hx (hbw l))
  have hI3 : ∀ l, hA X.B.I (X.bwd l) (X.B.I.fmat y *ᵥ X.bw j) ∈ IntAf X.B.I.F X.B.I.E :=
    fun l => hA_int X.B.I (hbwd l) (K_mv X.B.I hy (hbw j))
  have hIs : ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) (X.B.I.fmat y *ᵥ X.bw j) ∈
      IntAf X.B.I.F X.B.I.E := sum_mem fun l _ => mul_mem (hI2 l) (hI3 l)
  have hD := res_eq_zero_of_Z TR v (sub_mem hI1 hIs) hZ
  simp only [leviM, Matrix.mul_apply]
  rw [resT_of_mem TR v hI1]
  simp only [resT_of_mem TR v (hI2 _), resT_of_mem TR v (hI3 _)]
  have e3 : (⟨hA X.B.I (X.bwd i) (X.B.I.fmat (x * y) *ᵥ X.bw j), hI1⟩ : IntAf X.B.I.F X.B.I.E) =
      ⟨_, sub_mem hI1 hIs⟩ + ∑ l, (⟨_, hI2 l⟩ : IntAf X.B.I.F X.B.I.E) * ⟨_, hI3 l⟩ := by
    apply Subtype.ext
    simp only [Subring.coe_add, AddSubmonoidClass.coe_finsetSum, Subring.coe_mul]
    ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e3, map_add (f := _), hD, zero_add, map_sum]
  simp only [map_mul]

end LeviMul

end Formalism.L2.SG.NormCut
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DualCoords
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.unitaryCongruence Matrix

namespace Formalism.L2.SG.NormCut

section Dual

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def repr0 (v : VA X.B.I) : VA X.B.I :=
  (∑ a, hA X.B.I (X.f0 a) v • X.e0 a) + (∑ a, hA X.B.I (X.e0 a) v • X.f0 a) - hA X.B.I X.z0 v • X.z0 +
    (∑ l, hA X.B.I (X.bwd l) v • X.bw l) + (∑ l, hA X.B.I (X.bw l) v • X.bwd l)

theorem Z_smul_mL {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} {u : VA X.B.I} (hc : ZMod' X.B.I X.B.g c)
    (hu : u ∈ X.B.I.Lf) : c • u ∈ mL X.B.I X.B.g := by
  obtain ⟨t, ht, rfl⟩ := hc
  unfold mL
  refine Submodule.subset_span ⟨(⟨t, ht⟩ : IntAf X.B.I.F X.B.I.E) • u, Submodule.smul_mem _ _ hu, ?_⟩
  rw [mul_smul]
  rfl

theorem reference_repr_add (v w : VA X.B.I) : repr0 X (v + w) = repr0 X v + repr0 X w := by
  have hadd : ∀ x, hA X.B.I x (v + w) = hA X.B.I x v + hA X.B.I x w := fun x => by
    simp only [hA, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  simp only [repr0, hadd, add_smul, Finset.sum_add_distrib]
  abel

theorem reference_repr_smul (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (v : VA X.B.I) : repr0 X (c • v) = c • repr0 X v := by
  have hsm : ∀ x, hA X.B.I x (c • v) = c * hA X.B.I x v := fun x => by
    simp only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp only [repr0, hsm, mul_smul, smul_add, smul_sub, Finset.smul_sum]

theorem frame_Lf : (∀ a, X.e0 a ∈ X.B.I.Lf) ∧ (∀ a, X.f0 a ∈ X.B.I.Lf) ∧ X.z0 ∈ X.B.I.Lf ∧
    (∀ l, X.bw l ∈ X.B.I.Lf) ∧ (∀ l, X.bwd l ∈ X.B.I.Lf) := by
  exact ⟨fun a => (X.vectorsInLattice.1 a).1, fun a => (X.vectorsInLattice.1 a).2, X.vectorsInLattice.2.1, fun l => (X.vectorsInLattice.2.2 l).1,
    fun l => (X.vectorsInLattice.2.2 l).2⟩

theorem reference_repr_mem_lattice {v : VA X.B.I} (hv : v ∈ X.B.I.Lf) : repr0 X v ∈ X.B.I.Lf := by
  have hincl : ∀ e : X.B.I.E, sigA X.B.I (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) e) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (star e) := by
    intro e
    first
      | rfl
      | simp [sigA, Formalism.UG.sigR, Formalism.UG.inclE, Formalism.BasicNotions.CMData.sig]
  have hInt : ∀ s ∈ IntAf X.B.I.F X.B.I.E, sigA X.B.I s ∈ IntAf X.B.I.F X.B.I.E := by
    have hle : IntAf X.B.I.F X.B.I.E ≤ (IntAf X.B.I.F X.B.I.E).comap (sigA X.B.I) := by
      show Subring.closure _ ≤ _
      rw [Subring.closure_le]
      rintro _ (⟨⟨x, a, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
      · rw [SetLike.mem_coe, Subring.mem_comap]
        refine Subring.subset_closure (Or.inl ⟨⟨_, RingOfIntegers.mapRingEquiv (starRingAut : RingAut X.B.I.E) a, rfl⟩, ?_⟩)
        first
          | rfl
          | simp [sigA, Formalism.UG.sigR, Formalism.BasicNotions.CMData.sig]
      · rw [SetLike.mem_coe, Subring.mem_comap]
        refine Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, ?_⟩)
        simp [sigA, Formalism.UG.sigR]
    exact fun s hs => hle hs
  have hzl : ∀ v : VA X.B.I, hA X.B.I 0 v = 0 := fun v => by simp [hA, Formalism.UG.hform]
  have hzr : ∀ x : VA X.B.I, hA X.B.I x 0 = 0 := fun x => by simp [hA, Formalism.UG.hform]
  have hal : ∀ x x' v : VA X.B.I, hA X.B.I (x + x') v = hA X.B.I x v + hA X.B.I x' v := fun x x' v => by
    simp only [hA, Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]
  have har : ∀ x v v' : VA X.B.I, hA X.B.I x (v + v') = hA X.B.I x v + hA X.B.I x v' := fun x v v' => by
    simp only [hA, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have hsl : ∀ (s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (x y : VA X.B.I),
      hA X.B.I (s • x) y = sigA X.B.I s * hA X.B.I x y := by
    intro s x y
    simp only [hA, sigA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsr : ∀ (s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (x y : VA X.B.I),
      hA X.B.I x (s • y) = s * hA X.B.I x y := by
    intro s x y
    simp only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsl' : ∀ (r : IntAf X.B.I.F X.B.I.E) (x y : VA X.B.I),
      hA X.B.I (r • x) y = sigA X.B.I r * hA X.B.I x y := fun r x y => hsl r x y
  have hsr' : ∀ (r : IntAf X.B.I.F X.B.I.E) (x y : VA X.B.I),
      hA X.B.I x (r • y) = r * hA X.B.I x y := fun r x y => hsr r x y
  have hgen : ∀ y ∈ X.B.I.L, ∀ y' ∈ X.B.I.L,
      hA X.B.I (fun i => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (y i))
        (fun i => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (y' i)) ∈ IntAf X.B.I.F X.B.I.E := by
    intro y hy y' hy'
    obtain ⟨b, hb⟩ := (X.B.I.L_dual y').1 hy' y hy
    have e : hA X.B.I (fun i => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (y i))
        (fun i => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (y' i)) =
        Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (Formalism.UG.hform (starRingEnd _) X.B.I.J y y') := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hA, Formalism.UG.hform, map_sum, map_mul, Matrix.map_apply, hincl, starRingEnd_apply]
    rw [e, ← hb]
    show _ ∈ Subring.closure _
    exact Subring.subset_closure (Or.inl ⟨⟨_, b, rfl⟩, rfl⟩)
  have hpair : ∀ x ∈ X.B.I.Lf, ∀ w ∈ X.B.I.Lf, hA X.B.I x w ∈ IntAf X.B.I.F X.B.I.E := by
    intro x hx w hw
    unfold AutInst.Lf lamAf at hx hw
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨⟨y, hy⟩, rfl⟩ := hz
      induction hw using Submodule.span_induction with
      | mem z' hz' =>
        obtain ⟨⟨y', hy'⟩, rfl⟩ := hz'
        exact hgen y hy y' hy'
      | zero => rw [hzr]; exact zero_mem _
      | add a b _ _ ha hb => rw [har]; exact add_mem ha hb
      | smul r a _ ha => rw [hsr']; exact mul_mem r.2 ha
    | zero => rw [hzl]; exact zero_mem _
    | add a b _ _ ha hb => rw [hal]; exact add_mem ha hb
    | smul r a _ ha => rw [hsl']; exact mul_mem (hInt _ r.2) ha
  obtain ⟨he, hf, hz, hb, hbd⟩ := frame_Lf X
  have hterm : ∀ x ∈ X.B.I.Lf, ∀ u ∈ X.B.I.Lf, hA X.B.I x v • u ∈ X.B.I.Lf := fun x hx u hu =>
    Submodule.smul_mem _ (⟨_, hpair x hx v hv⟩ : IntAf X.B.I.F X.B.I.E) hu
  unfold repr0
  refine add_mem (add_mem (sub_mem (add_mem ?_ ?_) (hterm _ hz _ hz)) ?_) ?_
  · exact Submodule.sum_mem _ fun a _ => hterm _ (hf a) _ (he a)
  · exact Submodule.sum_mem _ fun a _ => hterm _ (he a) _ (hf a)
  · exact Submodule.sum_mem _ fun l _ => hterm _ (hbd l) _ (hb l)
  · exact Submodule.sum_mem _ fun l _ => hterm _ (hb l) _ (hbd l)

def ReprSub : Submodule (IntAf X.B.I.F X.B.I.E) (VA X.B.I) where
  carrier := {v | v - repr0 X v ∈ mL X.B.I X.B.g}
  add_mem' {v w} hv hw := by
    show v + w - repr0 X (v + w) ∈ mL X.B.I X.B.g
    rw [reference_repr_add, show v + w - (repr0 X v + repr0 X w) = (v - repr0 X v) + (w - repr0 X w) by abel]
    exact add_mem hv hw
  zero_mem' := by
    show (0 : VA X.B.I) - repr0 X 0 ∈ mL X.B.I X.B.g
    have : repr0 X 0 = 0 := by simpa using reference_repr_smul X 0 0
    rw [this, sub_zero]; exact zero_mem _
  smul_mem' c v hv := by
    show (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • v - repr0 X ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • v) ∈ mL X.B.I X.B.g
    rw [reference_repr_smul, ← smul_sub]
    exact Submodule.smul_mem _ c hv

theorem T_gen (s : VA X.B.I) (tA tB : Fin D.R.rS → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
    (tC : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (tP tQ : Fin D.R.k → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
    (hs : s = (∑ a, tA a • X.e0 a) + (∑ a, tB a • X.f0 a) - tC • X.z0 + (∑ l, tP l • X.bw l) +
      (∑ l, tQ l • X.bwd l))
    (h1 : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) s - tA a))
    (h2 : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) s - tB a))
    (h3 : ZMod' X.B.I X.B.g (hA X.B.I X.z0 s - tC))
    (h4 : ∀ l, ZMod' X.B.I X.B.g (hA X.B.I (X.bwd l) s - tP l))
    (h5 : ∀ l, ZMod' X.B.I X.B.g (hA X.B.I (X.bw l) s - tQ l)) :
    s ∈ ReprSub X := by
  have hneg' : ∀ x y, ZMod' X.B.I X.B.g (x - y) → ZMod' X.B.I X.B.g (y - x) := by
    rintro x y ⟨t, ht, e⟩
    exact ⟨-t, neg_mem ht, by rw [mul_neg, ← e, neg_sub]⟩
  obtain ⟨he, hf, hz, hb, hbd⟩ := frame_Lf X
  show s - repr0 X s ∈ mL X.B.I X.B.g
  have h0 : s - repr0 X s = ((∑ a, tA a • X.e0 a) + (∑ a, tB a • X.f0 a) - tC • X.z0 + (∑ l, tP l • X.bw l) +
      (∑ l, tQ l • X.bwd l)) - repr0 X s := congrArg (· - repr0 X s) hs
  rw [h0]
  have hexp : ((∑ a, tA a • X.e0 a) + (∑ a, tB a • X.f0 a) - tC • X.z0 + (∑ l, tP l • X.bw l) +
      (∑ l, tQ l • X.bwd l)) - repr0 X s =
      (∑ a, (tA a - hA X.B.I (X.f0 a) s) • X.e0 a) + (∑ a, (tB a - hA X.B.I (X.e0 a) s) • X.f0 a) -
        (tC - hA X.B.I X.z0 s) • X.z0 + (∑ l, (tP l - hA X.B.I (X.bwd l) s) • X.bw l) +
        (∑ l, (tQ l - hA X.B.I (X.bw l) s) • X.bwd l) := by
    unfold repr0
    simp only [sub_smul, Finset.sum_sub_distrib]
    abel
  rw [hexp]
  refine add_mem (add_mem (sub_mem (add_mem ?_ ?_) (Z_smul_mL X (hneg' _ _ h3) hz)) ?_) ?_
  · exact Submodule.sum_mem _ fun a _ => Z_smul_mL X (hneg' _ _ (h1 a)) (he a)
  · exact Submodule.sum_mem _ fun a _ => Z_smul_mL X (hneg' _ _ (h2 a)) (hf a)
  · exact Submodule.sum_mem _ fun l _ => Z_smul_mL X (hneg' _ _ (h4 l)) (hb l)
  · exact Submodule.sum_mem _ fun l _ => Z_smul_mL X (hneg' _ _ (h5 l)) (hbd l)

theorem Z_of_sym {u w : VA X.B.I} {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}
    (h : ZMod' X.B.I X.B.g (hA X.B.I w u - sigA X.B.I c)) : ZMod' X.B.I X.B.g (hA X.B.I u w - c) := by
  have hinv : ∀ t, sigA X.B.I (sigA X.B.I t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      first
        | simp [sigA, Formalism.UG.sigR, Formalism.BasicNotions.CMData.sig]
        | (show TensorProduct.tmul X.B.I.F (X.B.I.cm.sig (X.B.I.cm.sig a)) b = TensorProduct.tmul X.B.I.F a b
           rw [show X.B.I.cm.sig (X.B.I.cm.sig a) = a from star_star a])
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hincl : ∀ e : X.B.I.E, sigA X.B.I (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) e) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (star e) := by
    intro e
    first
      | rfl
      | simp [sigA, Formalism.UG.sigR, Formalism.UG.inclE, Formalism.BasicNotions.CMData.sig]
  have hsym : hA X.B.I u w = sigA X.B.I (hA X.B.I w u) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hA, Formalism.UG.hform, map_sum, map_mul, hinv, Matrix.map_apply, hincl]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hJ : star (X.B.I.J i j) = X.B.I.J j i := by
      have e := congrFun (congrFun X.B.I.J_herm j) i
      simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at e
      exact e
    rw [hJ]
    ring
  have hInt : ∀ s ∈ IntAf X.B.I.F X.B.I.E, sigA X.B.I s ∈ IntAf X.B.I.F X.B.I.E := by
    have hle : IntAf X.B.I.F X.B.I.E ≤ (IntAf X.B.I.F X.B.I.E).comap (sigA X.B.I) := by
      show Subring.closure _ ≤ _
      rw [Subring.closure_le]
      rintro _ (⟨⟨x, a, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
      · rw [SetLike.mem_coe, Subring.mem_comap]
        refine Subring.subset_closure (Or.inl ⟨⟨_, RingOfIntegers.mapRingEquiv (starRingAut : RingAut X.B.I.E) a, rfl⟩, ?_⟩)
        first
          | rfl
          | simp [sigA, Formalism.UG.sigR, Formalism.BasicNotions.CMData.sig]
      · rw [SetLike.mem_coe, Subring.mem_comap]
        refine Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, ?_⟩)
        simp [sigA, Formalism.UG.sigR]
    exact fun s hs => hle hs
  obtain ⟨t, ht, e⟩ := h
  refine ⟨sigA X.B.I t, hInt t ht, ?_⟩
  have e' : hA X.B.I w u = sigA X.B.I c + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t := by
    rw [← e]
    ring
  rw [hsym, e', map_add (f := _), hinv, map_mul, map_natCast]
  ring

theorem Z0 {x : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (h : ZMod' X.B.I X.B.g x) : ZMod' X.B.I X.B.g (x - 0) := by
  rw [sub_zero]
  exact h

theorem hA_bw_bw (l m : Fin D.R.k) : hA X.B.I (X.bw l) (X.bw m) = 0 := by
  have hsl : ∀ (s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (x y : VA X.B.I),
      hA X.B.I (s • x) y = sigA X.B.I s * hA X.B.I x y := by
    intro s x y
    simp only [hA, sigA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsr : ∀ (s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (x y : VA X.B.I),
      hA X.B.I x (s • y) = s * hA X.B.I x y := by
    intro s x y
    simp only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [X.bw_w l, X.bw_w m, hsl, hsr, ← mul_assoc, mul_comm (sigA X.B.I X.ew) X.ew, X.ew_orth, zero_mul]

theorem hA_bwd_bwd (l m : Fin D.R.k) : hA X.B.I (X.bwd l) (X.bwd m) = 0 := by
  have hsl : ∀ (s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (x y : VA X.B.I),
      hA X.B.I (s • x) y = sigA X.B.I s * hA X.B.I x y := by
    intro s x y
    simp only [hA, sigA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsr : ∀ (s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (x y : VA X.B.I),
      hA X.B.I x (s • y) = s * hA X.B.I x y := by
    intro s x y
    simp only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hinv : ∀ t, sigA X.B.I (sigA X.B.I t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      first
        | simp [sigA, Formalism.UG.sigR, Formalism.BasicNotions.CMData.sig]
        | (show TensorProduct.tmul X.B.I.F (X.B.I.cm.sig (X.B.I.cm.sig a)) b = TensorProduct.tmul X.B.I.F a b
           rw [show X.B.I.cm.sig (X.B.I.cm.sig a) = a from star_star a])
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  rw [X.bwd_w l, X.bwd_w m, hsl, hsr, hinv, ← mul_assoc, X.ew_orth, zero_mul]

theorem dual_coords {v : VA X.B.I} (hv : v ∈ X.B.I.Lf) : v - repr0 X v ∈ mL X.B.I X.B.g := by
  have hinv : ∀ t, sigA X.B.I (sigA X.B.I t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      first
        | simp [sigA, Formalism.UG.sigR, Formalism.BasicNotions.CMData.sig]
        | (show TensorProduct.tmul X.B.I.F (X.B.I.cm.sig (X.B.I.cm.sig a)) b = TensorProduct.tmul X.B.I.F a b
           rw [show X.B.I.cm.sig (X.B.I.cm.sig a) = a from star_star a])
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have zsym : ∀ u w : VA X.B.I, ZMod' X.B.I X.B.g (hA X.B.I w u) → ZMod' X.B.I X.B.g (hA X.B.I u w - 0) := by
    intro u w h
    apply Z_of_sym X
    rw [map_zero, sub_zero]
    exact h
  have zz : ZMod' X.B.I X.B.g ((0 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) - 0) := ⟨0, zero_mem _, by simp⟩
  have hmL : mL X.B.I X.B.g ≤ ReprSub X := by
    unfold mL
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    show _ - repr0 X _ ∈ mL X.B.I X.B.g
    rw [reference_repr_smul, ← smul_sub]
    unfold mL
    exact Submodule.subset_span ⟨x - repr0 X x, sub_mem hx (reference_repr_mem_lattice X hx), rfl⟩
  have hS : Set.range X.e0 ∪ Set.range X.f0 ∪ {X.z0} ∪ Set.range X.bw ∪ Set.range X.bwd ⊆ ReprSub X := by
    rintro _ ((((⟨a, rfl⟩ | ⟨a, rfl⟩) | rfl) | ⟨l, rfl⟩) | ⟨l, rfl⟩)
    · refine T_gen X (X.e0 a) (fun a' => if a' = a then 1 else 0) 0 0 0 0 ?_ ?_ ?_ ?_ ?_ ?_
      · simp [ite_smul]
      · intro a'
        apply Z_of_sym X
        have e : sigA X.B.I (if a' = a then 1 else 0) = if a = a' then 1 else 0 := by
          by_cases h : a = a'
          · subst h
            simp
          · simp [h, Ne.symm h]
        rw [e]
        exact (X.gramIntegral a a').2.2
      · exact fun a' => Z0 X (X.gramIntegral a' a).1
      · exact zsym _ _ ((X.formsAtZero.2 a).1)
      · exact fun l => zsym _ _ (((X.weightVectorsIntegral l).2.2 a).2.2.1)
      · exact fun l => zsym _ _ (((X.weightVectorsIntegral l).2.2 a).1)
    · refine T_gen X (X.f0 a) 0 (fun a' => if a' = a then 1 else 0) 0 0 0 ?_ ?_ ?_ ?_ ?_ ?_
      · simp [ite_smul]
      · exact fun a' => Z0 X (X.gramIntegral a' a).2.1
      · exact fun a' => (X.gramIntegral a' a).2.2
      · exact zsym _ _ ((X.formsAtZero.2 a).2)
      · exact fun l => zsym _ _ (((X.weightVectorsIntegral l).2.2 a).2.2.2)
      · exact fun l => zsym _ _ (((X.weightVectorsIntegral l).2.2 a).2.1)
    · refine T_gen X X.z0 0 0 (-1) 0 0 ?_ ?_ ?_ ?_ ?_ ?_
      · simp
      · exact fun a' => Z0 X ((X.formsAtZero.2 a').2)
      · exact fun a' => Z0 X ((X.formsAtZero.2 a').1)
      · rw [sub_neg_eq_add]
        exact X.formsAtZero.1
      · exact fun l => zsym _ _ ((X.weightVectorsIntegral l).2.1)
      · exact fun l => zsym _ _ ((X.weightVectorsIntegral l).1)
    · refine T_gen X (X.bw l) 0 0 0 (fun l' => if l' = l then X.ew else 0) 0 ?_ ?_ ?_ ?_ ?_ ?_
      · have hw := X.bw_w l
        simpa [ite_smul] using hw
      · exact fun a' => Z0 X (((X.weightVectorsIntegral l).2.2 a').2.1)
      · exact fun a' => Z0 X (((X.weightVectorsIntegral l).2.2 a').1)
      · exact Z0 X ((X.weightVectorsIntegral l).1)
      · exact fun l' => X.bw_dual l' l
      · intro l'
        rw [hA_bw_bw]
        exact zz
    · refine T_gen X (X.bwd l) 0 0 0 0 (fun l' => if l' = l then sigA X.B.I X.ew else 0) ?_ ?_ ?_ ?_ ?_ ?_
      · have hw := X.bwd_w l
        simpa [ite_smul] using hw
      · exact fun a' => Z0 X (((X.weightVectorsIntegral l).2.2 a').2.2.2)
      · exact fun a' => Z0 X (((X.weightVectorsIntegral l).2.2 a').2.2.1)
      · exact Z0 X ((X.weightVectorsIntegral l).2.1)
      · intro l'
        rw [hA_bwd_bwd]
        exact zz
      · intro l'
        apply Z_of_sym X
        have e : sigA X.B.I (if l' = l then sigA X.B.I X.ew else 0) = if l = l' then X.ew else 0 := by
          by_cases h : l = l'
          · subst h
            simp [hinv]
          · simp [h, Ne.symm h]
        rw [e]
        exact X.bw_dual l l'
  have hle : Submodule.span (IntAf X.B.I.F X.B.I.E)
      (Set.range X.e0 ∪ Set.range X.f0 ∪ {X.z0} ∪ Set.range X.bw ∪ Set.range X.bwd) ⊔ mL X.B.I X.B.g ≤ ReprSub X :=
    sup_le (Submodule.span_le.2 hS) hmL
  exact hle (X.latticeSpan v hv)

end Dual

end Formalism.L2.SG.NormCut
end
end

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.NormCut

section Par

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem hform_mulVec' {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A)
    (J M : Matrix n n A) (hM : Formalism.UG.cT σ M * J * M = J) (x y : n → A) :
    Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ J x y := by
  have key : ∀ a b : n → A, Formalism.UG.hform σ J a b = ((fun i => σ (a i)) ᵥ* J) ⬝ᵥ b := by
    intro a b
    simp only [Formalism.UG.hform, dotProduct, Matrix.vecMul, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hσ : (fun i => σ ((M *ᵥ x) i)) = (fun i => σ (x i)) ᵥ* (Formalism.UG.cT σ M) := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply,
      map_sum, map_mul]
    exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  rw [key, key, Matrix.dotProduct_mulVec, hσ, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hM]

theorem hA_unit (g : X.B.I.Gf) (x y : VA X.B.I) :
    hA X.B.I (X.B.I.fmat g *ᵥ x) (X.B.I.fmat g *ᵥ y) = hA X.B.I x y := by
  unfold hA
  refine hform_mulVec' _ _ (X.B.I.fmat g) ?_ x y
  exact g.2

theorem hA_adj (g : X.B.I.Gf) (x y : VA X.B.I) :
    hA X.B.I x (X.B.I.fmat g *ᵥ y) = hA X.B.I (X.B.I.fmat g⁻¹ *ᵥ x) y := by
  have e : X.B.I.fmat g *ᵥ (X.B.I.fmat g⁻¹ *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec]
    have h1 : X.B.I.fmat g * X.B.I.fmat g⁻¹ = 1 := by
      change X.B.I.fmat (g * g⁻¹) = 1
      rw [mul_inv_cancel]
      rfl
    rw [h1, Matrix.one_mulVec]
  calc hA X.B.I x (X.B.I.fmat g *ᵥ y) = hA X.B.I (X.B.I.fmat g *ᵥ (X.B.I.fmat g⁻¹ *ᵥ x)) (X.B.I.fmat g *ᵥ y) := by
        rw [e]
    _ = hA X.B.I (X.B.I.fmat g⁻¹ *ᵥ x) y := hA_unit X g _ y

theorem mem_mL_of_InAt {d : VA X.B.I} (hd : d ∈ X.B.I.Lf) (h : InAt X.B.I X.B.g X.B.g d) :
    d ∈ mL X.B.I X.B.g := by
  obtain ⟨c, hc, hcd⟩ := h
  have hb : ((c : ℤ) * Nat.gcdA c X.B.g + (X.B.g : ℤ) * Nat.gcdB c X.B.g) = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hc.gcd_eq_one]; rfl
  have e : d = ((Nat.gcdA c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • d) +
      ((Nat.gcdB c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • d) := by
    rw [smul_smul, smul_smul, ← add_smul]
    have : ((Nat.gcdA c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) +
        ((Nat.gcdB c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = 1 := by
      have := congrArg (fun z : ℤ => (z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) hb
      push_cast at this
      linear_combination this
    rw [this, one_smul]
  rw [e]
  have hint : ∀ z : ℤ, ((z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) ∈ IntAf X.B.I.F X.B.I.E := fun z => intCast_mem _ z
  have sm : ∀ (z : ℤ) (w : VA X.B.I), w ∈ mL X.B.I X.B.g →
      ((z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) • w ∈ mL X.B.I X.B.g := fun z w hw => by
    have : ((z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) • w = (⟨_, hint z⟩ : IntAf X.B.I.F X.B.I.E) • w := rfl
    rw [this]; exact Submodule.smul_mem _ _ hw
  exact add_mem (sm _ _ hcd) (sm _ _ (smul_mem_mL X.B.I hd))

theorem mem_Mo_eb {v : VA X.B.I} (hv : v ∈ X.B.I.Lf) (he : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) v))
    (hz : ZMod' X.B.I X.B.g (hA X.B.I X.z0 v)) (hb : ∀ l, ZMod' X.B.I X.B.g (hA X.B.I (X.bw l) v)) :
    v ∈ Mo X.B.I X.B.g (Set.range X.e0 ∪ Set.range X.bw) := by
  obtain ⟨hE, hF, hZ, hB, hBd⟩ := frame_Lf X
  have hd := dual_coords X hv
  have e : v = (v - repr0 X v) + repr0 X v := by abel
  rw [e]
  refine add_mem (mL_Mo X.B.I hd) ?_
  have spn : ∀ (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (w : VA X.B.I), c ∈ IntAf X.B.I.F X.B.I.E →
      w ∈ Set.range X.e0 ∪ Set.range X.bw → c • w ∈ Mo X.B.I X.B.g (Set.range X.e0 ∪ Set.range X.bw) :=
    fun c w hc hw => by
      have : c • w = (⟨c, hc⟩ : IntAf X.B.I.F X.B.I.E) • w := rfl
      rw [this]; exact Submodule.smul_mem _ _ (sub_Mo X.B.I hw)
  unfold repr0
  refine add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_
  · exact sum_mem fun a _ => spn _ _ (hA_int X.B.I (hF a) hv) (Or.inl ⟨a, rfl⟩)
  · exact sum_mem fun a _ => mL_Mo X.B.I (Z_smul_mL X (he a) (hF a))
  · exact mL_Mo X.B.I (Z_smul_mL X hz hZ)
  · exact sum_mem fun l _ => spn _ _ (hA_int X.B.I (hBd l) hv) (Or.inr ⟨l, rfl⟩)
  · exact sum_mem fun l _ => mL_Mo X.B.I (Z_smul_mL X (hb l) (hBd l))

def Par (x : X.B.I.Gf) : Prop :=
  x ∈ X.B.I.Kset ∧ (∀ a, X.B.I.fmat x *ᵥ X.e0 a ∈ Mo X.B.I X.B.g (Set.range X.e0)) ∧
    ∀ j, X.B.I.fmat x *ᵥ X.bw j ∈ Mo X.B.I X.B.g (Set.range X.e0 ∪ Set.range X.bw)

def Good (x : X.B.I.Gf) : Prop := Par X x ∧ Par X x⁻¹

theorem par_one : Par X 1 := by
  unfold Par Mo
  refine ⟨?_, fun a => ?_, fun j => ?_⟩
  · first
    | exact (Formalism.UG.stabGL X.B.I.Lf).one_mem
    | exact one_mem (Formalism.UG.stabGL X.B.I.Lf)
    | (show ((1 : X.B.I.Gf) : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) ∈ Formalism.UG.stabGL X.B.I.Lf
       exact one_mem _)
  · rw [show X.B.I.fmat 1 = 1 from rfl, Matrix.one_mulVec]
    exact Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩)
  · rw [show X.B.I.fmat 1 = 1 from rfl, Matrix.one_mulVec]
    exact Submodule.mem_sup_left (Submodule.subset_span (Or.inr ⟨j, rfl⟩))

theorem par_mul {x y : X.B.I.Gf} (hx : Par X x) (hy : Par X y) : Par X (x * y) := by
  refine ⟨K_mul X.B.I hx.1 hy.1, fun a => ?_, fun j => ?_⟩
  · rw [fmat_mul, ← Matrix.mulVec_mulVec]
    refine pres X.B.I hx.1 X.B.g (Set.range X.e0) _ (sub_Mo X.B.I) ?_ (mL_Mo X.B.I) _ (hy.2.1 a)
    rintro _ ⟨b, rfl⟩
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_mem (hx.2.1 b) (sub_Mo X.B.I ⟨b, rfl⟩)
  · rw [fmat_mul, ← Matrix.mulVec_mulVec]
    refine pres X.B.I hx.1 X.B.g (Set.range X.e0 ∪ Set.range X.bw) _ (sub_Mo X.B.I) ?_ (mL_Mo X.B.I) _ (hy.2.2 j)
    rintro s (⟨b, rfl⟩ | ⟨l, rfl⟩)
    · rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      exact sub_mem (Mo_mono X.B.I Set.subset_union_left (hx.2.1 b)) (sub_Mo X.B.I (Or.inl ⟨b, rfl⟩))
    · rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      exact sub_mem (hx.2.2 l) (sub_Mo X.B.I (Or.inr ⟨l, rfl⟩))

theorem good_one : Good X 1 := by
  exact ⟨par_one X, by rw [inv_one]; exact par_one X⟩

theorem good_mul {x y : X.B.I.Gf} (hx : Good X x) (hy : Good X y) : Good X (x * y) := by
  exact ⟨par_mul X hx.1 hy.1, by rw [_root_.mul_inv_rev]; exact par_mul X hy.2 hx.2⟩

theorem good_inv {x : X.B.I.Gf} (hx : Good X x) : Good X x⁻¹ := by
  exact ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

variable {X} (TR : TypedRed X)

theorem leviM_mul_par {x y : X.B.I.Gf} (hx : Par X x) (hy : Par X y) (v : TR.Pl) :
    leviM TR (x * y) v = leviM TR x v * leviM TR y v :=
  leviM_mul TR hx.1 hy.1 hy.2.2 hx.2.1 v

theorem leviM_one (v : TR.Pl) : leviM TR 1 v = 1 := by
  ext i j
  have hbw : ∀ j, X.bw j ∈ X.B.I.Lf := fun j => (X.vectorsInLattice.2.2 j).1
  have hbwd : ∀ j, X.bwd j ∈ X.B.I.Lf := fun j => (X.vectorsInLattice.2.2 j).2
  simp only [leviM, show X.B.I.fmat 1 = 1 from rfl, Matrix.one_mulVec]
  have hI := hA_int X.B.I (hbwd i) (hbw j)
  rw [resT_of_mem TR v hI]
  have hZ := X.bw_dual i j
  have hIt : (if i = j then X.ew else 0) ∈ IntAf X.B.I.F X.B.I.E := by
    split_ifs
    · exact X.ew_int
    · exact zero_mem _
  have e : (⟨_, hI⟩ : IntAf X.B.I.F X.B.I.E) = ⟨_, sub_mem hI hIt⟩ + ⟨_, hIt⟩ := by
    apply Subtype.ext; simp
  rw [e, map_add (f := _), res_eq_zero_of_Z TR v _ hZ, zero_add]
  by_cases h : i = j
  · subst h
    simp only [if_true, Matrix.one_apply_eq]
    have e2 : (⟨X.ew, X.ew_int⟩ : IntAf X.B.I.F X.B.I.E) = ⟨X.ew * (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F),
        (IntAf X.B.I.F X.B.I.E).mul_mem X.ew_int (one_mem _)⟩ := by apply Subtype.ext; simp
    have := TR.res_ew v 1
    simp only [OneMemClass.coe_one] at this
    convert this using 2
    exact (map_one (TR.res v)).symm
  · simp only [h, if_false, Matrix.one_apply_ne h]
    exact map_zero (TR.res v) |>.symm ▸ (by congr 1)

end Par

end Formalism.L2.SG.NormCut
