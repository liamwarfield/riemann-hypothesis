module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.CommensuratedOfIsOpenIsCompact
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.LocLift

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.LocSplitChiOf
noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S

def GLChi : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (n : ℕ) (χ : GL (Fin n) k →* ℚ), (∀ g, 0 < χ g) →
    (∀ d : kˣ, χ (Units.map (algebraMap k (Matrix (Fin n) (Fin n) k)).toMonoidHom d) = 1) →
    ∀ g, χ g = 1

theorem spl_sig_sig (I : AutInst) (a : I.E) : I.cm.sig (I.cm.sig a) = a := by
  change star (star a) = a
  exact star_star a

theorem spl_sig_fix (I : AutInst) (a : I.E) (h : I.cm.sig a = a) : a ∈ (algebraMap I.F I.E).range := (I.cm.fixed a).1 h

theorem spl_sigV_inclV (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (x : I.E) :
    sigV I v (inclV I v x) = inclV I v (starRingEnd I.E x) := by
  simp only [sigV, inclV, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  rfl

theorem spl_herm_v (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    Formalism.UG.cT (sigV I v) (I.J.map (inclV I v)) = I.J.map (inclV I v) := by
  have h := I.J_herm
  unfold Formalism.UG.IsHerm at h
  ext i j
  have hij := congrFun (congrFun h i) j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at hij ⊢
  rw [spl_sigV_inclV, hij]

theorem spl_det_v (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) : IsUnit (I.J.map (inclV I v)).det := by
  have h := RingHom.map_det (inclV I v) I.J
  rw [RingHom.mapMatrix_apply] at h
  rw [← h]
  exact (isUnit_iff_ne_zero.2 I.J_det).map _

theorem locSplitChi_of (hG : GLChi) : LocSplitChi := by
  intro I v hnf χ hpos hcent _ g
  haveI : CharZero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) :=
    charZero_of_injective_algebraMap (algebraMap I.F _).injective
  obtain ⟨π, hπ⟩ := SplitIso.exists_split (K := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) I.cm.sig
    (spl_sig_sig I) (spl_sig_fix I) I.cm.deg2 two_ne_zero hnf
  have hπ' : ∀ r, π (sigV I v r) = (π r).swap := hπ
  let f : Uv I v →* GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) :=
    SplitGL.proj (sigV I v) π (I.J.map (inclV I v))
  have hbij : Function.Bijective f :=
    SplitGL.proj_bijective (sigV I v) π hπ' (I.J.map (inclV I v)) (spl_herm_v I v) (spl_det_v I v)
  let e : Uv I v ≃* GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) := MulEquiv.ofBijective f hbij
  have key := hG (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) I.n (χ.comp e.symm.toMonoidHom) (fun g => hpos _) ?_ (e g)
  · have h2 : e.symm (e g) = g := e.symm_apply_apply g
    rw [← h2]; exact key
  · intro d
    show χ (e.symm _) = 1
    apply hcent
    intro t
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    apply Units.ext
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
    exact Algebra.commutes _ _

end PI.UnitaryGroupMassFormula.AdIndexEq

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.CompactLocalGlobal
noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S

theorem matV_coe (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (g : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
    ((matV I v g : GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) : Matrix _ _ _) =
      (g : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)).map (PI.FinKW.psiV I v).toRingHom := rfl

private theorem eq_of_forall_evalV_eq {F : Type} [Field F] [NumberField F] (a b : Af F)
    (h : ∀ v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v a = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v b) : a = b :=
  Subtype.ext (funext fun v => h v)

private theorem tensorBasis_repr_psiV_eq_evalV_repr_comm (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (z : I.E ⊗[I.F] Af I.F) (i : Module.Free.ChooseBasisIndex I.F I.E) :
    (Algebra.TensorProduct.basis (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (Module.Free.chooseBasis I.F I.E)).repr
        (PI.FinKW.psiV I v z) i =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v
        ((Algebra.TensorProduct.basis (Af I.F) (Module.Free.chooseBasis I.F I.E)).repr
          (Algebra.TensorProduct.comm I.F I.E (Af I.F) z) i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e a =>
    simp [PI.FinKW.psiV, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply,
      Finsupp.mapRange_apply, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem mat_ext_of_psiV (I : AutInst) (M N : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))
    (h : ∀ v, M.map (PI.FinKW.psiV I v).toRingHom = N.map (PI.FinKW.psiV I v).toRingHom) :
    M = N := by
  ext i j
  have hij : ∀ v, PI.FinKW.psiV I v (M i j) = PI.FinKW.psiV I v (N i j) := fun v => by
    have := congrFun (congrFun (h v) i) j
    simpa [Matrix.map_apply] using this
  apply (Algebra.TensorProduct.comm I.F I.E (Af I.F)).injective
  apply (Algebra.TensorProduct.basis (Af I.F) (Module.Free.chooseBasis I.F I.E)).repr.injective
  refine Finsupp.ext fun k => ?_
  apply eq_of_forall_evalV_eq
  intro v
  rw [← tensorBasis_repr_psiV_eq_evalV_repr_comm, ← tensorBasis_repr_psiV_eq_evalV_repr_comm, hij v]

theorem matrix_v_injective : MatVInj := by
  unfold MatVInj
  intro I y z h
  apply Subtype.ext
  apply Units.ext
  apply mat_ext_of_psiV I
  intro v
  have := congrArg Units.val (h v)
  simpa only [matV_coe] using this

theorem psiV_sigR (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (z : I.E ⊗[I.F] Af I.F) :
    PI.FinKW.psiV I v (Formalism.UG.sigR I.cm.sig (Af I.F) z) = sigV I v (PI.FinKW.psiV I v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e a => simp [PI.FinKW.psiV, Formalism.UG.sigR, sigV]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem psiV_inclE (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (e : I.E) :
    PI.FinKW.psiV I v (Formalism.UG.inclE (F := I.F) (Af I.F) e) = inclV I v e := by
  simp [PI.FinKW.psiV, Formalism.UG.inclE, inclV]

theorem map_cT {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (σ : A →+* A) (τ : B →+* B)
    (hf : ∀ a, f (σ a) = τ (f a)) {m p : Type} (M : Matrix m p A) :
    (Formalism.UG.cT σ M).map f = Formalism.UG.cT τ (M.map f) := by
  ext i j
  simp [Formalism.UG.cT, hf]

theorem mapJ (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))).map (PI.FinKW.psiV I v).toRingHom =
      I.J.map (inclV I v) := by
  ext i j
  simp only [Matrix.map_apply]
  exact psiV_inclE I v _

theorem map_unitary (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
    (Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) M * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * M).map
              (PI.FinKW.psiV I v).toRingHom =
      Formalism.UG.cT (sigV I v) (M.map (PI.FinKW.psiV I v).toRingHom) * I.J.map (inclV I v) *
        M.map (PI.FinKW.psiV I v).toRingHom := by
  rw [Matrix.map_mul, Matrix.map_mul,
    map_cT (PI.FinKW.psiV I v).toRingHom (Formalism.UG.sigR I.cm.sig (Af I.F)) (sigV I v)
      (fun a => psiV_sigR I v a), mapJ]

theorem mem_Uv_iff (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (g : GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) :
    g ∈ Uv I v ↔ Formalism.UG.cT (sigV I v) g.val * I.J.map (inclV I v) * g.val = I.J.map (inclV I v) := Iff.rfl

theorem mem_Gf_iff (I : AutInst) (g : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
    g ∈ Formalism.UG.UPts I.cm.sig I.J (Af I.F) ↔
      Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) g.val * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *
        g.val = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := Iff.rfl

theorem matrix_v_unitary : MatVU := by
  unfold MatVU
  intro I v y
  rw [mem_Uv_iff, matV_coe]
  have hy := (mem_Gf_iff I y).1 y.2
  rw [← map_unitary, hy]
  exact mapJ I v

theorem vecV_mulVec' (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (x : Fin I.n → I.E ⊗[I.F] Af I.F) :
    PI.FinKW.vecV I v (M *ᵥ x) = M.map (PI.FinKW.psiV I v).toRingHom *ᵥ PI.FinKW.vecV I v x := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [PI.FinKW.vecV, Matrix.mulVec, dotProduct, map_sum]

theorem stab_iff_loc (I : AutInst) (g : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
    g ∈ Formalism.UG.stabGL I.Lf ↔ ∀ v, matV I v g ∈ Kv I v := by
  have hL : ∀ x, x ∈ I.Lf ↔
      ∀ v, PI.FinKW.vecV I v x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) :=
    fun x => ⟨PI.FinKW.LocTo.mem_local_lattice_iff I x, PI.FinKW.memLocFrom_of PI.FinKW.local_vector_injective I x⟩
  constructor
  · intro hst v y
    obtain ⟨x, hxv, hxw⟩ := PI.FinKW.local_vector_lift I v y
    have ex : x ∈ I.Lf ↔ y ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
      rw [hL x]
      constructor
      · intro H
        have := H v
        rwa [hxv] at this
      · intro H w
        by_cases hw : w = v
        · subst hw
          rwa [hxv]
        · rw [hxw w hw]
          exact zero_mem _
    have egx : (g : Matrix _ _ _) *ᵥ x ∈ I.Lf ↔
        ((matV I v g : GL (Fin I.n) _) : Matrix _ _ _) *ᵥ y ∈
          Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
      rw [hL, matV_coe]
      constructor
      · intro H
        have := H v
        rwa [vecV_mulVec', hxv] at this
      · intro H w
        rw [vecV_mulVec']
        by_cases hw : w = v
        · subst hw
          rwa [hxv]
        · rw [hxw w hw, Matrix.mulVec_zero]
          exact zero_mem _
    exact ex.symm.trans ((hst x).trans egx)
  · intro hK x
    show x ∈ I.Lf ↔ (g : Matrix _ _ _) *ᵥ x ∈ I.Lf
    rw [hL x, hL ((g : Matrix _ _ _) *ᵥ x)]
    refine forall_congr' fun v => ?_
    rw [vecV_mulVec', ← matV_coe]
    exact hK v (PI.FinKW.vecV I v x)

theorem compact_local_global : KLocGlob := by
  unfold KLocGlob
  intro I y
  rw [PI.AdIndexEq.Ksub, Subgroup.mem_comap]
  exact stab_iff_loc I _

end PI.UnitaryGroupMassFormula.AdIndexEq

end
end
