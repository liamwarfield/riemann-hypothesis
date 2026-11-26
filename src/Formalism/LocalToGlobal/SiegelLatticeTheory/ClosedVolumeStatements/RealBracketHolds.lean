module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.BruhatHaarProved
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittExtensionTheorem
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXPS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeDensPf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TopoAF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TopoPolish
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContinuousMeasureSplitting
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.ContinuousCrdAllSymm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Assembly
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXLeaves

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AprimeInf
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.NuBridge
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.NuBridgeA
noncomputable section

namespace PI.AprimeInfW.NuB

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix ComplexConjugate

section Tr

variable {D : D7} (X : HidaSetting D)

theorem emb_real (v : InfinitePlace X.B.I.F) (a : X.B.I.F) : conj (v.embedding a) = v.embedding a := by
  have hv : v.IsReal := totReal_of X v
  have h := NumberField.ComplexEmbedding.isReal_iff.1 (InfinitePlace.isReal_iff.1 hv)
  have := RingHom.congr_fun h a
  simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using this

theorem phi_star (v : InfinitePlace X.B.I.F) (e : X.B.I.E) : X.B.I.φ v (star e) = conj (X.B.I.φ v e) :=
  X.B.I.cm.cmUnram.2.1 _ e

theorem phi_notReal (v : InfinitePlace X.B.I.F) : ¬ ∀ e : X.B.I.E, conj (X.B.I.φ v e) = X.B.I.φ v e := by
  intro h
  have hr : NumberField.ComplexEmbedding.IsReal (X.B.I.φ v) := by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext e
    simp [NumberField.ComplexEmbedding.conjugate_coe_eq, h e]
  have hc := X.B.I.cm.cmUnram.1.isComplex (InfinitePlace.mk (X.B.I.φ v))
  exact (InfinitePlace.not_isReal_iff_isComplex.2 hc) (InfinitePlace.isReal_mk_iff.2 hr)

theorem emb_trace (v : InfinitePlace X.B.I.F) (e : X.B.I.E) :
    v.embedding (Algebra.trace X.B.I.F X.B.I.E e) = X.B.I.φ v e + conj (X.B.I.φ v e) := by
  classical
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  letI : Algebra X.B.I.F ℂ := v.embedding.toAlgebra
  let φA : X.B.I.E →ₐ[X.B.I.F] ℂ := { X.B.I.φ v with commutes' := X.B.I.φ_over v }
  let ψA : X.B.I.E →ₐ[X.B.I.F] ℂ :=
    { (starRingEnd ℂ).comp (X.B.I.φ v) with
      commutes' := fun a => by
        show conj (X.B.I.φ v (algebraMap X.B.I.F X.B.I.E a)) = v.embedding a
        rw [X.B.I.φ_over, emb_real] }
  have hne : φA ≠ ψA := by
    intro h
    apply phi_notReal X v
    intro e
    have := congrArg (fun f : X.B.I.E →ₐ[X.B.I.F] ℂ => f e) h
    exact this.symm
  have hcard : Fintype.card (X.B.I.E →ₐ[X.B.I.F] ℂ) = 2 := by
    rw [AlgHom.card X.B.I.F X.B.I.E ℂ, X.B.I.cm.deg2]
  have huniv : (Finset.univ : Finset (X.B.I.E →ₐ[X.B.I.F] ℂ)) = {φA, ψA} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, hcard, Finset.card_pair hne]
  have h := trace_eq_sum_embeddings (K := X.B.I.F) (L := X.B.I.E) ℂ (x := e)
  rw [huniv, Finset.sum_pair hne] at h
  exact h

theorem evInf_conj (v : InfinitePlace X.B.I.F) (a : Ainf X.B.I.F) :
    conj (PI.AprimeInfU.evInf X v a) = PI.AprimeInfU.evInf X v a := by
  have hv : v.IsReal := totReal_of X v
  show conj (InfinitePlace.Completion.extensionEmbedding v (a v)) =
    InfinitePlace.Completion.extensionEmbedding v (a v)
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv]
  exact Complex.conj_ofReal _

theorem evInf_alg (v : InfinitePlace X.B.I.F) (a : X.B.I.F) :
    PI.AprimeInfU.evInf X v (algebraMap X.B.I.F (Ainf X.B.I.F) a) = v.embedding a :=
  evV_algebraMap X.B.I v a

theorem trace_one_tmul (e : X.B.I.E) :
    Algebra.trace (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) ((1 : Ainf X.B.I.F) ⊗ₜ[X.B.I.F] e) =
      algebraMap X.B.I.F (Ainf X.B.I.F) (Algebra.trace X.B.I.F X.B.I.E e) := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  rw [Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange, ← Algebra.trace_apply]

theorem evInf_trace (v : InfinitePlace X.B.I.F) (z : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :
    PI.AprimeInfU.evInf X v (Algebra.trace (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) z) =
      PI.AprimeInfU.thetaInf X v z + conj (PI.AprimeInfU.thetaInf X v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have h1 : a ⊗ₜ[X.B.I.F] e = a • ((1 : Ainf X.B.I.F) ⊗ₜ[X.B.I.F] e) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h1, map_smul, trace_one_tmul, smul_eq_mul, map_mul, evInf_alg, emb_trace, ← h1, thetaInf_tmul, map_mul,
      evInf_conj]
    ring
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]; ring

theorem theta_sigR (v : InfinitePlace X.B.I.F) (t : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :
    PI.AprimeInfU.thetaInf X v (sigR (Ainf X.B.I.F) X.B.I.cm.sig t) = conj (PI.AprimeInfU.thetaInf X v t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have h : sigR (Ainf X.B.I.F) X.B.I.cm.sig (a ⊗ₜ[X.B.I.F] e) = a ⊗ₜ[X.B.I.F] (star e) := rfl
    rw [h, thetaInf_tmul, thetaInf_tmul, map_mul, evInf_conj, phi_star]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem theta_alg (v : InfinitePlace X.B.I.F) (q : X.B.I.F) :
    PI.AprimeInfU.thetaInf X v (algebraMap X.B.I.F (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) q) = v.embedding q := by
  rw [Algebra.TensorProduct.algebraMap_apply, thetaInf_tmul, evInf_alg, map_one, mul_one]

theorem theta_surj (z : InfinitePlace X.B.I.F → ℂ) :
    ∃ y : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E, ∀ v, PI.AprimeInfU.thetaInf X v y = z v := by
  classical
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  let b : Module.Basis (Fin 2) X.B.I.F X.B.I.E := Module.finBasisOfFinrankEq X.B.I.F X.B.I.E X.B.I.cm.deg2
  have hr : ∀ v : InfinitePlace X.B.I.F, ∃ r : Fin 2 → ℝ,
      (r 0 : ℂ) * X.B.I.φ v (b 0) + (r 1 : ℂ) * X.B.I.φ v (b 1) = z v := by
    intro v
    let f : Fin 2 → ℂ := ![X.B.I.φ v (b 0), X.B.I.φ v (b 1)]
    have hli : LinearIndependent ℝ f := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [Fin.sum_univ_two] at hg
      have key := theta_lin_indep (X.B.I.φ v) (X.B.I.cm.sig : X.B.I.E →+* X.B.I.E)
        (fun a => X.B.I.cm.cmUnram.2.1 (X.B.I.φ v) a)
        (fun a ha => RingHom.mem_range.1 ((X.B.I.cm.fixed a).1 ha)) b g (by
          simpa [f, Complex.real_smul] using hg)
      intro i
      fin_cases i
      · exact key.1
      · exact key.2
    have hsp : Submodule.span ℝ (Set.range f) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank (by simp [Complex.finrank_real_complex])
    have hz : z v ∈ Submodule.span ℝ (Set.range f) := by rw [hsp]; trivial
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hz
    refine ⟨r, ?_⟩
    rw [← hr, Fin.sum_univ_two]
    simp [f, Complex.real_smul]
  choose r hr using hr
  have hv : ∀ v : InfinitePlace X.B.I.F, v.IsReal := fun v => totReal_of X v
  let c : Fin 2 → Ainf X.B.I.F := fun i =>
    (fun w => (InfinitePlace.Completion.ringEquivRealOfIsReal (hv w)).symm (r w i) :
      ∀ w : InfinitePlace X.B.I.F, w.Completion)
  have hc : ∀ i v, PI.AprimeInfU.evInf X v (c i) = (r v i : ℂ) := by
    intro i v
    show InfinitePlace.Completion.extensionEmbedding v
      ((InfinitePlace.Completion.ringEquivRealOfIsReal (hv v)).symm (r v i)) = _
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (hv v),
      ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply (hv v), RingEquiv.apply_symm_apply]
  refine ⟨c 0 ⊗ₜ[X.B.I.F] b 0 + c 1 ⊗ₜ[X.B.I.F] b 1, fun v => ?_⟩
  rw [map_add (f := _), thetaInf_tmul, thetaInf_tmul, hc, hc, hr]

end Tr

end PI.AprimeInfW.NuB
end
end

noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct RealInnerProductSpace FourierTransform ComplexConjugate
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

section Gen

variable {V : Type} [Fintype V] {n m : ℕ}

def reimVE : (V → Matrix (Fin n) (Fin m) ℂ) ≃ₗ[ℝ] EuclideanSpace ℝ (V × Fin n × Fin m × Bool) where
  toFun M := reimV M
  invFun y := fun v i j => ⟨y (v, i, j, true), y (v, i, j, false)⟩
  map_add' M N := by
    ext p
    rcases p with ⟨v, i, j, s⟩
    cases s <;> simp [reimV]
  map_smul' c M := by
    ext p
    rcases p with ⟨v, i, j, s⟩
    cases s <;> simp [reimV]
  left_inv M := by
    funext v i j
    apply Complex.ext <;> simp [reimV]
  right_inv y := by
    ext p
    rcases p with ⟨v, i, j, s⟩
    cases s <;> simp [reimV]

theorem reimVE_apply (M : V → Matrix (Fin n) (Fin m) ℂ) : reimVE M = reimV M := rfl

theorem inner_reimV (M N : V → Matrix (Fin n) (Fin m) ℂ) :
    ⟪reimV M, reimV N⟫ = ∑ v, ∑ i, ∑ j, ((M v i j).re * (N v i j).re + (M v i j).im * (N v i j).im) := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  simp [reimV, mul_comm]

theorem norm_reimV_sq (M : V → Matrix (Fin n) (Fin m) ℂ) :
    ‖reimV M‖ ^ 2 = ∑ v, ∑ i, ∑ j, ‖M v i j‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_reimV]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]


variable (V m) in
def hermFam : Submodule ℝ (V → Matrix (Fin m) (Fin m) ℂ) where
  carrier := {M | ∀ v, (M v)ᴴ = M v}
  add_mem' {M N} hM hN v := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Pi.add_apply, Matrix.conjTranspose_add, hM v, hN v]
  zero_mem' v := by simp
  smul_mem' c M hM v := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Pi.smul_apply, Matrix.conjTranspose_smul, hM v, star_trivial]

end Gen

theorem sigR_alg {D : D7} (X : HidaSetting D) (q : X.B.I.F) :
    sigR (Ainf X.B.I.F) X.B.I.cm.sig (algebraMap X.B.I.F (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) q) =
      algebraMap X.B.I.F (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) q :=
  (Algebra.TensorProduct.map (AlgHom.id X.B.I.F (Ainf X.B.I.F)) X.B.I.cm.sig).commutes q

theorem half_re (w : ℂ) : ((1 / 2 : ℂ) * (w + conj w)).re = w.re := by
  rw [Complex.add_conj]
  simp

theorem half_emb {D : D7} (X : HidaSetting D) (v : InfinitePlace X.B.I.F) : v.embedding (1 / 2) = (1 / 2 : ℂ) := by
  rw [map_div₀, map_one, map_ofNat]

set_option maxHeartbeats 1000000 in
theorem nuBridge : NuBridge := by
  classical
  intro D X u' ψ hT μinf νinf fibInf hP
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : BorelSpace (HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) := ⟨rfl⟩
  let Kr : Submodule ℝ (EuclideanSpace ℝ (InfinitePlace X.B.I.F × Fin (D.R.rS + 1 + D.R.rS) ×
      Fin (D.R.rS + 1 + D.R.rS) × Bool)) :=
    (hermFam (InfinitePlace X.B.I.F) (D.R.rS + 1 + D.R.rS)).map (reimVE : _ ≃ₗ[ℝ] _).toLinearMap
  let bK := stdOrthonormalBasis ℝ Kr
  let Hh : EuclideanSpace ℝ (Fin (Module.finrank ℝ Kr)) →ₗ[ℝ]
      (InfinitePlace X.B.I.F → Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) ℂ) :=
    (reimVE : _ ≃ₗ[ℝ] _).symm.toLinearMap ∘ₗ Kr.subtype ∘ₗ bK.repr.symm.toLinearEquiv.toLinearMap
  have hHh : ∀ s, Hh s = (reimVE : _ ≃ₗ[ℝ] _).symm (bK.repr.symm s : _) := fun s => rfl
  let thH : HmI X → InfinitePlace X.B.I.F → Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) ℂ :=
    fun S v => S.1.map (PI.AprimeInfU.thetaInf X v)
  have thH_herm : ∀ S, thH S ∈ hermFam (InfinitePlace X.B.I.F) (D.R.rS + 1 + D.R.rS) := by
    intro S v
    have hS : ∀ a b, sigR (Ainf X.B.I.F) X.B.I.cm.sig (S.1 b a) = S.1 a b := S.2
    ext i j
    simp only [thH, Matrix.conjTranspose_apply, Matrix.map_apply]
    rw [show star (PI.AprimeInfU.thetaInf X v (S.1 j i)) =
      conj (PI.AprimeInfU.thetaInf X v (S.1 j i)) from rfl, ← NuB.theta_sigR X v, hS i j]
  have memK : ∀ S, (reimVE : _ ≃ₗ[ℝ] _) (thH S) ∈ Kr := fun S => Submodule.mem_map_of_mem (thH_herm S)
  let TcF : HmI X → EuclideanSpace ℝ (Fin (Module.finrank ℝ Kr)) := fun S => bK.repr ⟨_, memK S⟩
  have hHT : ∀ S, Hh (TcF S) = thH S := by
    intro S
    rw [hHh, LinearIsometryEquiv.symm_apply_apply]
    exact (reimVE : _ ≃ₗ[ℝ] _).symm_apply_apply (thH S)
  have thH_add : ∀ S T, thH (S + T) = thH S + thH T := by
    intro S T
    funext v i j
    simp [thH, Matrix.map_apply, map_add (f := _)]
  have TcF_add : ∀ S T, TcF (S + T) = TcF S + TcF T := by
    intro S T
    have e : (⟨_, memK (S + T)⟩ : Kr) = ⟨_, memK S⟩ + ⟨_, memK T⟩ := Subtype.ext (by
      show (reimVE : _ ≃ₗ[ℝ] _) (thH (S + T)) = (reimVE : _ ≃ₗ[ℝ] _) (thH S) + (reimVE : _ ≃ₗ[ℝ] _) (thH T)
      rw [thH_add, map_add (f := _)])
    exact (congrArg bK.repr e).trans (map_add bK.repr _ _)
  have hθc : ∀ v i j, Continuous fun S : HmI X => PI.AprimeInfU.thetaInf X v (S.1 i j) :=
    fun v i j => (continuous_thetaInf X v).comp (continuous_subtype_val.matrix_elem i j)
  have hcont : Continuous TcF := by
    refine bK.repr.continuous.comp (Continuous.subtype_mk ?_ _)
    show Continuous fun S => (EuclideanSpace.equiv _ ℝ).symm (fun p : InfinitePlace X.B.I.F × Fin (D.R.rS + 1 + D.R.rS) ×
      Fin (D.R.rS + 1 + D.R.rS) × Bool => if p.2.2.2 then (thH S p.1 p.2.1 p.2.2.1).re else (thH S p.1 p.2.1 p.2.2.1).im)
    refine (EuclideanSpace.equiv _ ℝ).symm.continuous.comp (continuous_pi fun p => ?_)
    rcases p with ⟨v, i, j, s⟩
    cases s
    · exact Complex.continuous_im.comp (hθc v i j)
    · exact Complex.continuous_re.comp (hθc v i j)
  have hinj : Function.Injective TcF := by
    intro S T h
    have h1 : thH S = thH T := by rw [← hHT S, ← hHT T, h]
    apply Subtype.ext
    ext a b
    apply sub_eq_zero.1
    apply thetaInf_inj X
    intro v
    have := congrFun (congrFun (congrFun h1 v) a) b
    simp only [thH, Matrix.map_apply] at this
    rw [map_sub, this, sub_self]
  have hsurj : Function.Surjective TcF := by
    intro s
    obtain ⟨M, hM, hMs⟩ := Submodule.mem_map.1 (bK.repr.symm s).2
    choose y hy using fun a b : Fin (D.R.rS + 1 + D.R.rS) => NuB.theta_surj X (fun v => M v a b)
    let h2 := algebraMap X.B.I.F (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) (1 / 2)
    let Sm : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :=
      fun a b => h2 * (y a b + sigR (Ainf X.B.I.F) X.B.I.cm.sig (y b a))
    have hSm : Sm ∈ HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) := by
      show ∀ a b, sigR (Ainf X.B.I.F) X.B.I.cm.sig (Sm b a) = Sm a b
      intro a b
      simp only [Sm, h2, map_mul, map_add (f := _), sigR_invP _ _ (sig_invI X), sigR_alg]
      ring
    refine ⟨⟨Sm, hSm⟩, ?_⟩
    have e : thH ⟨Sm, hSm⟩ = M := by
      funext v a b
      have hMh : conj (M v b a) = M v a b := by
        have := congrFun (congrFun (hM v) a) b
        simpa [Matrix.conjTranspose_apply] using this
      simp only [thH, Matrix.map_apply, Sm, h2, map_mul, map_add (f := _), NuB.theta_alg, NuB.theta_sigR, hy, hMh,
        half_emb]
      ring
    show bK.repr _ = s
    rw [← bK.repr.apply_symm_apply s]
    congr 1
    apply Subtype.ext
    show (reimVE : _ ≃ₗ[ℝ] _) (thH ⟨Sm, hSm⟩) = _
    rw [e]
    exact hMs
  let Ψa : Wh X →+ EuclideanSpace ℝ (Fin (Module.finrank ℝ Kr)) :=
    AddMonoidHom.mk' (fun x => TcF ((hermCoord X).symm x)) (fun x y => by rw [hermCoord_symm_add, TcF_add])
  let Ψc : Wh X →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ Kr)) :=
    AddMonoidHom.toRealLinearMap Ψa (hcont.comp (hermCoord X).symm.continuous)
  have hΨ : ∀ x, Ψc x = TcF ((hermCoord X).symm x) := fun x => rfl
  have hΨb : Function.Bijective Ψc := by
    refine ⟨fun x y h => (hermCoord X).symm.injective (hinj (by rw [← hΨ, ← hΨ, h])), fun s => ?_⟩
    obtain ⟨S, hS⟩ := hsurj s
    exact ⟨hermCoord X S, by rw [hΨ, Homeomorph.symm_apply_apply, hS]⟩
  let Ψe : Wh X ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ Kr)) :=
    (LinearEquiv.ofBijective (Ψc : Wh X →ₗ[ℝ] _) hΨb).toContinuousLinearEquiv
  let Tc : HmI X ≃ₜ EuclideanSpace ℝ (Fin (Module.finrank ℝ Kr)) := (hermCoord X).trans Ψe.toHomeomorph
  have hTc : ∀ S, Tc S = TcF S := by
    intro S
    show Ψc (hermCoord X S) = TcF S
    rw [hΨ, Homeomorph.symm_apply_apply]
  have key : ∀ S T : HmI X, sumReI X (pairHerm (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) S T) =
      ⟪TcF S, TcF T⟫ := by
    intro S T
    have e1 : ⟪TcF S, TcF T⟫ = ⟪reimV (thH S), reimV (thH T)⟫ := by
      simp only [TcF, LinearIsometryEquiv.inner_map_map]
      rfl
    have hTh : ∀ v a b, PI.AprimeInfU.thetaInf X v (T.1 b a) =
        conj (PI.AprimeInfU.thetaInf X v (T.1 a b)) := by
      intro v a b
      have hT' : ∀ a b, sigR (Ainf X.B.I.F) X.B.I.cm.sig (T.1 b a) = T.1 a b := T.2
      rw [← NuB.theta_sigR X v, hT' b a]
    rw [e1, inner_reimV]
    simp only [sumReI]
    refine Finset.sum_congr rfl fun v _ => ?_
    show (PI.AprimeInfU.evInf X v (pairHerm (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) S T)).re = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [pairHerm, map_mul, NuB.evInf_alg, NuB.evInf_trace, half_emb, half_re, map_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, hTh v a b]
    simp only [thH, Matrix.map_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hS := hP.2.2.1
  have hν : SelfDual νinf (fun S T : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) =>
      psiInf X.B.I.F ψ (pairHerm (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) S T)) := hP.2.2.2.2.2.1
  have h1 : ∀ x y : EuclideanSpace ℝ (Fin (Module.finrank ℝ Kr)),
      (fun S T : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) =>
        psiInf X.B.I.F ψ (pairHerm (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) S T)) (Tc.symm x) (Tc.symm y) =
        ((𝐞 (⟪x, y⟫) : Circle) : ℂ) := by
    intro x y
    obtain ⟨S, rfl⟩ := Tc.surjective x
    obtain ⟨T, rfl⟩ := Tc.surjective y
    have e1 : Tc.symm (Tc S) = S := Tc.symm_apply_apply S
    have e2 : Tc.symm (Tc T) = T := Tc.symm_apply_apply T
    have e3 : ⟪Tc S, Tc T⟫ = sumReI X (pairHerm (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) S T) := by
      rw [hTc S, hTc T, key]
    show psiInf X.B.I.F ψ (pairHerm (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) (Tc.symm (Tc S))
      (Tc.symm (Tc T))) = _
    rw [e1, e2, e3]
    simp only [sumReI]
    rw [psiInf_eq ψ hS, Real.fourierChar_apply]
    push_cast
    ring_nf
  have hd := PI.AprimeInfW.GenericDensity.dens_generic νinf _ hν Tc (fun S T => by rw [hTc, hTc, hTc, TcF_add])
    (fun x y => ⟪x, y⟫) h1 (fun x x' y => inner_add_left x x' y) (fun x y y' => inner_add_right x y y')
    (fun y => continuous_id.inner continuous_const) (fun x => continuous_const.inner continuous_id)
    (fun x y => real_inner_comm y x) (EuclideanSpace.basisFun (Fin (Module.finrank ℝ Kr)) ℝ)
  have hI : (Matrix.of fun i j => ⟪EuclideanSpace.basisFun (Fin (Module.finrank ℝ Kr)) ℝ i,
      EuclideanSpace.basisFun (Fin (Module.finrank ℝ Kr)) ℝ j⟫) = 1 := by
    ext i j
    rw [Matrix.of_apply, orthonormal_iff_ite.1 (EuclideanSpace.basisFun _ ℝ).orthonormal i j, Matrix.one_apply]
  rw [hI, Matrix.det_one, abs_one, Real.sqrt_one, ENNReal.ofReal_one, one_smul] at hd
  refine ⟨Fin (Module.finrank ℝ Kr), inferInstance, Hh, Tc, ?_, ?_, ?_, fun S T => by rw [hTc, hTc, hTc, TcF_add],
    fun S v => by rw [hTc, hHT], hd⟩
  · intro s v
    obtain ⟨M, hM, hMs⟩ := Submodule.mem_map.1 (bK.repr.symm s).2
    have : Hh s = M := by
      rw [hHh, ← hMs]
      exact (reimVE : _ ≃ₗ[ℝ] _).symm_apply_apply M
    rw [this]
    exact hM v
  · intro s
    rw [← norm_reimV_sq, ← reimVE_apply, hHh, LinearEquiv.apply_symm_apply]
    exact congrArg (· ^ 2) (bK.repr.symm.norm_map s)
  · intro M hM
    refine ⟨bK.repr ⟨(reimVE : _ ≃ₗ[ℝ] _) M, Submodule.mem_map_of_mem (show M ∈ hermFam _ _ from hM)⟩, ?_⟩
    rw [hHh, LinearIsometryEquiv.symm_apply_apply]
    exact (reimVE : _ ≃ₗ[ℝ] _).symm_apply_apply M

end PI.AprimeInfW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensExEnd
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayValId
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Metric Filter Formalism.MainNotions.S Formalism.MainNotions.S.Gauge
open scoped ENNReal

namespace CVI

theorem ratio_tendsto {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (g : E → ℝ) (hg : ContinuousAt g 0) :
    Tendsto (fun ρ : ℝ => (∫⁻ p in ball (0 : E) ρ, ENNReal.ofReal (g p) ∂μ).toReal / (μ (ball (0 : E) ρ)).toReal)
      (𝓝[>] 0) (𝓝 (max (g 0) 0)) := by
  set c := max (g 0) 0 with hc
  have hc0 : 0 ≤ c := le_max_right _ _
  have hofr : ∀ p, ENNReal.ofReal (g p) = ENNReal.ofReal (max (g p) 0) := by
    intro p
    rcases le_total (g p) 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
    · rw [max_eq_left h]
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousAt_iff.1 hg (ε / 2) (by linarith)
  refine ⟨δ, hδ, fun ρ hρ hρδ => ?_⟩
  have hρ0 : 0 < ρ := hρ
  have hρδ' : ρ < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hρ0] at hρδ
    exact hρδ
  have hbd : ∀ p ∈ ball (0 : E) ρ, |max (g p) 0 - c| < ε / 2 := by
    intro p hp
    have h1 : dist p 0 < δ := lt_trans (mem_ball.1 hp) hρδ'
    have h2 := hδg h1
    rw [Real.dist_eq] at h2
    exact lt_of_le_of_lt (abs_max_sub_max_le_abs _ _ _) h2
  have hBpos : μ (ball (0 : E) ρ) ≠ 0 := (measure_ball_pos μ 0 hρ0).ne'
  have hBfin : μ (ball (0 : E) ρ) ≠ ⊤ := measure_ball_lt_top.ne
  have hBr : 0 < (μ (ball (0 : E) ρ)).toReal := ENNReal.toReal_pos hBpos hBfin
  have hup : ∫⁻ p in ball (0 : E) ρ, ENNReal.ofReal (g p) ∂μ ≤
      ENNReal.ofReal (c + ε / 2) * μ (ball (0 : E) ρ) := by
    rw [← setLIntegral_const]
    refine setLIntegral_mono' measurableSet_ball fun p hp => ?_
    rw [hofr]
    apply ENNReal.ofReal_le_ofReal
    have := hbd p hp
    rw [abs_lt] at this
    linarith
  have hlo : ENNReal.ofReal (c - ε / 2) * μ (ball (0 : E) ρ) ≤
      ∫⁻ p in ball (0 : E) ρ, ENNReal.ofReal (g p) ∂μ := by
    rw [← setLIntegral_const]
    refine setLIntegral_mono' measurableSet_ball fun p hp => ?_
    rw [hofr]
    apply ENNReal.ofReal_le_ofReal
    have := hbd p hp
    rw [abs_lt] at this
    linarith
  have hfin : ENNReal.ofReal (c + ε / 2) * μ (ball (0 : E) ρ) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBfin
  have hup' := ENNReal.toReal_mono hfin hup
  have hlo' := ENNReal.toReal_mono (ne_top_of_le_ne_top hfin hup) hlo
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at hup'
  rw [ENNReal.toReal_mul] at hlo'
  have hlo'' : (c - ε / 2) * (μ (ball (0 : E) ρ)).toReal ≤
      (∫⁻ p in ball (0 : E) ρ, ENNReal.ofReal (g p) ∂μ).toReal := by
    refine le_trans ?_ hlo'
    apply mul_le_mul_of_nonneg_right _ hBr.le
    rw [ENNReal.toReal_ofReal']
    exact le_max_left _ _
  have hA1 : c - ε / 2 ≤ (∫⁻ p in ball (0 : E) ρ, ENNReal.ofReal (g p) ∂μ).toReal / (μ (ball (0 : E) ρ)).toReal := by
    rw [le_div_iff₀ hBr]
    exact hlo''
  have hA2 : (∫⁻ p in ball (0 : E) ρ, ENNReal.ofReal (g p) ∂μ).toReal / (μ (ball (0 : E) ρ)).toReal ≤ c + ε / 2 := by
    rw [div_le_iff₀ hBr]
    exact hup'
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

theorem expDens_gen {n : ℕ} (ε : Fin n → Bool) (r₀ : ℝ) (hr₀ : 0 < r₀) (f₀ : gLie ε → ℝ) (hfm : Measurable f₀)
    (hfc : ContinuousAt f₀ 0)
    (hf : ∀ S ⊆ ball (0 : gLie ε) r₀, MeasurableSet S →
        Formalism.REAL.muG ε ((fun x : gLie ε => cayR ε (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))) '' S) =
          ∫⁻ x in S, ENNReal.ofReal (f₀ x))
    (m h : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool))) (hmh : m ⊔ h = gLie ε)
    (horth : ∀ x ∈ m, ∀ y ∈ h, inner ℝ x y = 0)
    (ι η : Type) [Fintype ι] [Fintype η] (L₀ : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] m) (L₁ : EuclideanSpace ℝ η ≃ₗᵢ[ℝ] h) :
    ∃ r : ℝ, 0 < r ∧ ∃ D : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → ℝ,
      ContinuousAt D 0 ∧ D 0 = f₀ 0 ∧ Measurable D ∧
      ∀ A ⊆ ball (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) r, MeasurableSet A →
        Formalism.REAL.muG ε ((fun p => expR ε (L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) *
          expR ε (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool))) '' A) =
        ∫⁻ p in A, ENNReal.ofReal (D p) := by

  obtain ⟨-, hpres⟩ := sumLPres_holds n ε m h hmh horth ι η L₀ L₁
  set Ls := sumL ε m h hmh L₀ L₁ with hLs
  have hLc : Continuous Ls := by
    set_option synthInstance.maxHeartbeats 200000 in
      exact Ls.continuous_of_finiteDimensional
  have hL0 : Ls 0 = 0 := map_zero Ls
  have hnorm : ∀ p, ‖Ls p‖ ≤ 2 * ‖p‖ := by
    intro p
    have e : ‖Ls p‖ = ‖(L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) + (L₁ p.2 : _)‖ := rfl
    rw [e]
    calc _ ≤ ‖(L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ + ‖(L₁ p.2 : EuclideanSpace ℝ _)‖ := norm_add_le _ _
      _ = ‖p.1‖ + ‖p.2‖ := by
          have e1 : ‖(L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ = ‖p.1‖ := by
            rw [← LinearIsometryEquiv.norm_map L₀ p.1]; rfl
          have e2 : ‖(L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ = ‖p.2‖ := by
            rw [← LinearIsometryEquiv.norm_map L₁ p.2]; rfl
          rw [e1, e2]
      _ ≤ ‖p‖ + ‖p‖ := add_le_add (norm_fst_le p) (norm_snd_le p)
      _ = 2 * ‖p‖ := by ring
  have hC : ∀ S ⊆ ball (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) (r₀ / 2), MeasurableSet S →
      Formalism.REAL.muG ε ((fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ η =>
        cayR ε ((L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) +
          (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool)))) '' S) = ∫⁻ p in S, ENNReal.ofReal (f₀ (Ls p)) := by
    intro S hS hSm
    obtain ⟨hIm, hint⟩ := hpres S hSm
    have hsub : Ls '' S ⊆ ball (0 : gLie ε) r₀ := by
      rintro _ ⟨q, hq, rfl⟩
      have hq' := hS hq
      rw [mem_ball_zero_iff] at hq' ⊢
      linarith [hnorm q]
    have e : (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ η => cayR ε ((L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) +
        (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool)))) '' S =
        (fun x : gLie ε => cayR ε (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))) '' (Ls '' S) := by
      rw [Set.image_image]; rfl
    rw [e, hf _ hsub hIm]
    exact hint (fun x => ENNReal.ofReal (f₀ x)) (ENNReal.measurable_ofReal.comp hfm)
  have hFc : ContinuousAt (fun p => f₀ (Ls p)) 0 :=
    ContinuousAt.comp (x := 0) (show ContinuousAt f₀ (Ls 0) by rw [hL0]; exact hfc) hLc.continuousAt

  have hHaar : (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  have hL : CayLiftU :=
    cayLiftU_of (cayPsiU_of psiSmooth_holds psiMeas_holds (psiInv_of lieSkew_holds skewLie_holds caySkew_holds cayId_holds))
  obtain ⟨U, hU, ψ, ψ', hψ, hinj, hψ0, hψc, hψm, hψ'm, hdc, hd0, heq⟩ := hL n ε m h hmh horth ι η L₀ L₁
  have hr₁ : 0 < r₀ / 2 := by positivity
  have hpre : ψ ⁻¹' ball 0 (r₀ / 2) ∈ 𝓝 (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) :=
    hψc.preimage_mem_nhds (by rw [hψ0]; exact ball_mem_nhds _ hr₁)
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hU hpre)
  refine ⟨r, hr, fun p => |(ψ' p).det| * f₀ (Ls (ψ p)), ?_, ?_, ?_, ?_⟩
  · exact chart_change_cont (fun p => f₀ (Ls p)) ψ ψ' 0 hψc (by rw [hψ0]; exact hFc) hdc
  · simp only; rw [hd0, hψ0, hL0, one_mul]
  · exact (continuous_abs.measurable.comp (ContinuousLinearMap.continuous_det.measurable.comp hψ'm)).mul
      (hfm.comp (hLc.measurable.comp hψm))
  · intro A hA hAm
    have hAU : A ⊆ ball 0 r := hA
    have e : (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ η =>
        expR ε (L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) *
          expR ε (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool))) '' A =
        ((fun p => cayR ε ((L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) +
          (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool)))) ∘ ψ) '' A := by
      refine Set.image_congr fun p hp => ?_
      exact (heq p (hrs (hAU hp)).1).symm
    rw [e]
    exact chart_change volume _ _ (ball 0 (r₀ / 2)) (fun p => f₀ (Ls p)) hC ψ ψ' (ball 0 r)
      (fun p hp => (hψ p (hrs hp).1).mono fun q hq => (hrs hq).1) (hinj.mono fun q hq => (hrs hq).1)
      (by rintro _ ⟨q, hq, rfl⟩; exact (hrs hq).2) A hAU hAm

theorem expR_zero' {n : ℕ} (ε : Fin n → Bool) : expR ε (0 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) = 1 := by
  unfold expR
  split_ifs with h
  · apply Subtype.ext
    apply Units.ext
    simp [unrealify_zero', NormedSpace.exp_zero]
  · rfl

end CVI


open CVI in
theorem cayValId_holds : CayValId := by
  intro n ε hG r₀ hr₀ f₀ hfm hfc hf
  classical
  let L₀ := (stdOrthonormalBasis ℝ (gLie ε)).repr.symm
  let L₁ := (stdOrthonormalBasis ℝ (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool)))).repr.symm
  have hmh : gLie ε ⊔ (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool))) = gLie ε := sup_bot_eq _
  have horth : ∀ x ∈ gLie ε, ∀ y ∈ (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool))), inner ℝ x y = 0 := by
    intro x _ y hy; rw [(Submodule.mem_bot ℝ).1 hy, inner_zero_right]
  obtain ⟨r, hr, D, hDc, hD0, -, hD⟩ := expDens_gen ε r₀ hr₀ f₀ hfm hfc hf _ _ hmh horth _ _ L₀ L₁
  obtain ⟨-, hpres⟩ := sumLPres_holds n ε _ _ hmh horth _ _ L₀ L₁
  set Ls := sumL ε _ _ hmh L₀ L₁ with hLs
  have hy0 : ∀ y, ((L₁ y : (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool)))) :
      EuclideanSpace ℝ (Fin n × Fin n × Bool)) = 0 := fun y => (Submodule.mem_bot ℝ).1 (L₁ y).2
  have hyz : ∀ y : EuclideanSpace ℝ (Fin (Module.finrank ℝ ↥(⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool))))),
      y = 0 := fun y => by
    have h1 : L₁ y = 0 := Subtype.ext (hy0 y)
    have h2 := congrArg L₁.symm h1
    rwa [LinearIsometryEquiv.symm_apply_apply, map_zero] at h2
  have hLsv : ∀ p, ((Ls p : gLie ε) : EuclideanSpace ℝ (Fin n × Fin n × Bool)) =
      ((L₀ p.1 : gLie ε) : EuclideanSpace ℝ (Fin n × Fin n × Bool)) := fun p => by
    show ((L₀ p.1 : gLie ε) : EuclideanSpace ℝ (Fin n × Fin n × Bool)) + (L₁ p.2 : EuclideanSpace ℝ _) = _
    rw [hy0, add_zero]
  have hnorm : ∀ p, ‖Ls p‖ = ‖p‖ := fun p => by
    have e1 : ‖Ls p‖ = ‖L₀ p.1‖ := by
      show ‖((Ls p : gLie ε) : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ =
        ‖((L₀ p.1 : gLie ε) : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖
      rw [hLsv]
    rw [e1, LinearIsometryEquiv.norm_map, Prod.norm_def, hyz p.2, norm_zero, max_eq_left (norm_nonneg _)]
  have hball : ∀ ρ, Ls '' ball 0 ρ = ball (0 : gLie ε) ρ := fun ρ => by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [mem_ball_zero_iff, hnorm]; exact mem_ball_zero_iff.1 hp
    · intro hx
      refine ⟨(L₀.symm x, 0), ?_, ?_⟩
      · have e : Ls (L₀.symm x, 0) = x := by
          apply Subtype.ext; rw [hLsv]; simp
        rw [mem_ball_zero_iff, ← hnorm, e]; exact mem_ball_zero_iff.1 hx
      · apply Subtype.ext; rw [hLsv]; simp
  have hexp : ∀ ρ, (fun p : EuclideanSpace ℝ (Fin (Module.finrank ℝ (gLie ε))) × EuclideanSpace ℝ (Fin (Module.finrank ℝ ↥(⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool))))) =>
      expR ε ((L₀ p.1 : gLie ε) : EuclideanSpace ℝ (Fin n × Fin n × Bool)) *
        expR ε ((L₁ p.2 : (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool)))) :
          EuclideanSpace ℝ (Fin n × Fin n × Bool))) '' ball 0 ρ = expSet ε (ball 0 ρ) := fun ρ => by
    ext g
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨Ls p, by rw [← hball]; exact ⟨p, hp, rfl⟩, ?_⟩
      dsimp only
      rw [hy0, expR_zero', mul_one, hLsv]
      show (((expR ε _ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = _
      exact expR_val ε _ (lieSkew_holds n ε _ (L₀ p.1).2)
    · rintro ⟨x, hx, hgx⟩
      refine ⟨(L₀.symm x, 0), ?_, ?_⟩
      · rw [mem_ball_zero_iff, ← hnorm]
        have e : Ls (L₀.symm x, 0) = x := by
          apply Subtype.ext; rw [hLsv]; simp
        rw [e]; exact mem_ball_zero_iff.1 hx
      · simp only [hy0, expR_zero', mul_one, LinearIsometryEquiv.apply_symm_apply]
        apply Subtype.ext; apply Units.ext
        rw [expR_val ε _ (lieSkew_holds n ε _ x.2)]
        exact hgx.symm
  have hvol : ∀ ρ, volume (ball (0 : gLie ε) ρ) = volume (ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ (gLie ε))) × EuclideanSpace ℝ (Fin (Module.finrank ℝ ↥(⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool)))))) ρ) :=
    fun ρ => by
      have := (hpres (ball 0 ρ) measurableSet_ball).2 (fun _ => 1) measurable_const
      rw [hball] at this
      simpa using this
  have hHaar : (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ (gLie ε))) × EuclideanSpace ℝ (Fin (Module.finrank ℝ ↥(⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool))))))).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  have hT := ratio_tendsto (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ (gLie ε))) × EuclideanSpace ℝ (Fin (Module.finrank ℝ ↥(⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool))))))) D hDc
  have hlim : Tendsto (ratioAt ε) (𝓝[>] 0) (𝓝 (max (D 0) 0)) := by
    refine hT.congr' (Filter.eventuallyEq_of_mem (Ioo_mem_nhdsGT hr) fun ρ hρ => ?_)
    rw [ratioAt, ← hexp, hD _ (ball_subset_ball hρ.2.le) measurableSet_ball, hvol]
  have hu := tendsto_nhds_unique hG.1 hlim
  rw [hD0] at hu
  rcases le_total (f₀ 0) 0 with h | h
  · rw [max_eq_right h] at hu; linarith [hG.2]
  · rw [max_eq_left h] at hu; exact hu.symm

end PI.AprimeInfW
end
end

namespace PI.AprimeInfW

theorem expProdU_holds : ExpProdU := expProdU_of_hua cayDensEx_holds cayValId_holds

end PI.AprimeInfW
end

namespace PI.AprimeInfAsm

open PI.AprimeInfW

theorem aprimeInf_of_hinfCompact (hC : MassDataMassesW.HinfCompact) (hV : GaugeVolUD) : Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  aprimeInf_of_grp hC (grpStd_full expProdU_holds hV) nuBridge placeJacAll_holds

theorem aprime_infinite_real (hC : MassDataMassesW.HinfCompact) (hV : GaugeVolUD) : Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  aprimeInf_of_hinfCompact hC hV

end PI.AprimeInfAsm
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstFinal
noncomputable section

namespace Formalism.L2.SG.Pf

theorem WB.rhsWLim' [Fact Formalism.L2.SG.Pf.WB.RhsWLim] : WB.RhsWLim := Fact.out


variable [Fact Formalism.L2.SG.Pf.WB.RhsWLim] in
theorem jacGauge : JacGauge := jacGauge_of_rhsW WB.rhsWLim'

end Formalism.L2.SG.Pf
end
end

namespace Formalism.L2.SG.Closed

theorem AprimeInf_holds [hG : Fact PI.AprimeInfW.GaugeVolUD] : Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  PI.AprimeInfAsm.aprime_infinite_real Formalism.L2.SG.Pf.MassDataX.hinfCompact_holds hG.out

variable [Fact Formalism.L2.SG.Pf.WB.RhsWLim] in
theorem JacGauge_holds : Formalism.L2.SG.Pf.JacGauge := Formalism.L2.SG.Pf.jacGauge

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcReal in
variable [Fact PI.AprimeInfW.GaugeVolUD] [Fact Formalism.L2.SG.Pf.WB.RhsWLim] in
theorem RealBracket_holds (hC : Formalism.L2.SG.Pf.NcReal.JX.CovolRef) : Formalism.L2.SG.Pf.NcReal.RealBracket :=
  Formalism.L2.SG.Pf.NcReal.JX.realBracket_of_jac JacGauge_holds hC AprimeInf_holds
    (fun n ε => Formalism.MainNotions.S.Gauge.gauge_density_exists n ε)

end Formalism.L2.SG.Closed
