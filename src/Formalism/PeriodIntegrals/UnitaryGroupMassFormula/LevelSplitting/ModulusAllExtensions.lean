module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.ConjDefs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.OrthogonalInvarianceOfStableRankOne

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.ContinuousFirstOrbitMap
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.MapFstConjTranspose
noncomputable section

namespace PI.LevelKSplit.W.MVA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

section Ring

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R1 R2 : Type) [CommRing R1] [Algebra F R1] [CommRing R2] [Algebra F R2]

def p1 : (R1 × R2) ⊗[F] E →+* R1 ⊗[F] E :=
  (Algebra.TensorProduct.map (AlgHom.fst F R1 R2) (AlgHom.id F E)).toRingHom

def p2 : (R1 × R2) ⊗[F] E →+* R2 ⊗[F] E :=
  (Algebra.TensorProduct.map (AlgHom.snd F R1 R2) (AlgHom.id F E)).toRingHom


variable {R1 R2} in
def crd (R : Type) [CommRing R] [Algebra F R] :
    R ⊗[F] E ≃ₗ[R] (Fin (Module.finrank F E) → R) :=
  (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun

theorem crd_symm (R : Type) [CommRing R] [Algebra F R] (c : Fin (Module.finrank F E) → R) :
    (crd (E := E) R).symm c = ∑ k, c k ⊗ₜ (Module.finBasis F E k) := by
  simp [crd, Module.Basis.equivFun_symm_apply, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']

theorem fst_coordinates (x : (R1 × R2) ⊗[F] E) :
    p1 R1 R2 x = (crd R1).symm (fun k => (crd (R1 × R2) x k).1) := by
  conv_lhs => rw [← (crd (E := E) (R1 × R2)).symm_apply_apply x]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [crd_symm, crd_symm, map_sum]
  rfl

theorem snd_coordinates (x : (R1 × R2) ⊗[F] E) :
    p2 R1 R2 x = (crd R2).symm (fun k => (crd (R1 × R2) x k).2) := by
  conv_lhs => rw [← (crd (E := E) (R1 × R2)).symm_apply_apply x]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [crd_symm, crd_symm, map_sum]
  rfl

def qq (a : R1 ⊗[F] E) (b : R2 ⊗[F] E) : (R1 × R2) ⊗[F] E :=
  (crd (R1 × R2)).symm (fun k => (crd R1 a k, crd R2 b k))

theorem fst_pair (a : R1 ⊗[F] E) (b : R2 ⊗[F] E) : p1 R1 R2 (qq R1 R2 a b) = a := by
  unfold qq
  rw [fst_coordinates, LinearEquiv.apply_symm_apply]
  exact (crd R1).symm_apply_apply a

theorem snd_pair (a : R1 ⊗[F] E) (b : R2 ⊗[F] E) : p2 R1 R2 (qq R1 R2 a b) = b := by
  unfold qq
  rw [snd_coordinates, LinearEquiv.apply_symm_apply]
  exact (crd R2).symm_apply_apply b

theorem qq_p (x : (R1 × R2) ⊗[F] E) : qq R1 R2 (p1 R1 R2 x) (p2 R1 R2 x) = x := by
  apply (crd (E := E) (R1 × R2)).injective
  unfold qq
  rw [LinearEquiv.apply_symm_apply, fst_coordinates, snd_coordinates, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem ext_p {x y : (R1 × R2) ⊗[F] E} (h1 : p1 R1 R2 x = p1 R1 R2 y)
    (h2 : p2 R1 R2 x = p2 R1 R2 y) : x = y := by
  rw [← qq_p R1 R2 x, ← qq_p R1 R2 y, h1, h2]

variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem fst_conj_bis (x : (R1 × R2) ⊗[F] E) :
    p1 R1 R2 (sigR (R1 × R2) σ x) = sigR R1 σ (p1 R1 R2 x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem snd_conj_alt (x : (R1 × R2) ⊗[F] E) :
    p2 R1 R2 (sigR (R1 × R2) σ x) = sigR R2 σ (p2 R1 R2 x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem fst_inclusion (e : E) : p1 R1 R2 (inclR (F := F) (R1 × R2) e) = inclR (F := F) R1 e := rfl

theorem snd_inclusion (e : E) : p2 R1 R2 (inclR (F := F) (R1 × R2) e) = inclR (F := F) R2 e := rfl

theorem map_fst_conj_transpose (P : Matrix (Fin M) (Fin M) ((R1 × R2) ⊗[F] E)) :
    (Formalism.UG.cT (sigR (R1 × R2) σ) P).map (p1 R1 R2) =
      Formalism.UG.cT (sigR R1 σ) (P.map (p1 R1 R2)) := by
  ext i j
  simp [Formalism.UG.cT, fst_conj_bis]

theorem map_snd_conj_transpose (P : Matrix (Fin M) (Fin M) ((R1 × R2) ⊗[F] E)) :
    (Formalism.UG.cT (sigR (R1 × R2) σ) P).map (p2 R1 R2) =
      Formalism.UG.cT (sigR R2 σ) (P.map (p2 R1 R2)) := by
  ext i j
  simp [Formalism.UG.cT, snd_conj_alt]

theorem map_fst_form : (JR (F := F) (R1 × R2) J).map (p1 R1 R2) = JR (F := F) R1 J := by
  ext i j
  exact fst_inclusion R1 R2 (J i j)

theorem map_snd_form : (JR (F := F) (R1 × R2) J).map (p2 R1 R2) = JR (F := F) R2 J := by
  ext i j
  exact snd_inclusion R1 R2 (J i j)

def mlift (m : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)) : Matrix (Fin M) (Fin M) ((R1 × R2) ⊗[F] E) :=
  Matrix.of fun i j => qq R1 R2 ((1 : Matrix (Fin M) (Fin M) (R1 ⊗[F] E)) i j) (m i j)

theorem matrix_lift_fst (m : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)) : (mlift R1 R2 m).map (p1 R1 R2) = 1 := by
  ext i j
  exact fst_pair R1 R2 _ _

theorem matrix_lift_snd (m : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)) : (mlift R1 R2 m).map (p2 R1 R2) = m := by
  ext i j
  exact snd_pair R1 R2 _ _

theorem mext {P Q : Matrix (Fin M) (Fin M) ((R1 × R2) ⊗[F] E)} (h1 : P.map (p1 R1 R2) = Q.map (p1 R1 R2))
    (h2 : P.map (p2 R1 R2) = Q.map (p2 R1 R2)) : P = Q := by
  ext i j
  exact ext_p R1 R2 (congrArg (· i j) h1) (congrArg (· i j) h2)

theorem mlift_mul (m m' : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)) :
    mlift R1 R2 m * mlift R1 R2 m' = mlift R1 R2 (m * m') := by
  apply mext
  · rw [Matrix.map_mul, matrix_lift_fst, matrix_lift_fst, matrix_lift_fst, one_mul]
  · rw [Matrix.map_mul, matrix_lift_snd, matrix_lift_snd, matrix_lift_snd]

theorem mlift_one : mlift R1 R2 (1 : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)) = 1 := by
  apply mext
  · rw [matrix_lift_fst, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [matrix_lift_snd, Matrix.map_one _ (map_zero _) (map_one _)]

def glift (u : GL (Fin M) (R2 ⊗[F] E)) : GL (Fin M) ((R1 × R2) ⊗[F] E) :=
  ⟨mlift R1 R2 (u : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)), mlift R1 R2 (↑u⁻¹ : Matrix (Fin M) (Fin M) _),
    by rw [mlift_mul, u.mul_inv, mlift_one], by rw [mlift_mul, u.inv_mul, mlift_one]⟩

theorem glift_mem (g : HA R2 σ J) : glift R1 R2 (HA.mat R2 σ J g) ∈ HR (R1 × R2) σ J := by
  have hg : HA.mat R2 σ J g ∈ HR R2 σ J := g.2
  change Formalism.UG.cT (sigR R2 σ) ((HA.mat R2 σ J g : Matrix (Fin M) (Fin M) (R2 ⊗[F] E))) * JR (F := F) R2 J *
    (HA.mat R2 σ J g : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)) = JR (F := F) R2 J at hg
  change Formalism.UG.cT (sigR (R1 × R2) σ) (mlift R1 R2 (HA.mat R2 σ J g : Matrix (Fin M) (Fin M) (R2 ⊗[F] E))) *
    JR (F := F) (R1 × R2) J * mlift R1 R2 (HA.mat R2 σ J g : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)) = JR (F := F) (R1 × R2) J
  apply mext
  · rw [Matrix.map_mul, Matrix.map_mul, map_fst_conj_transpose, map_fst_form, matrix_lift_fst]
    ext i j
    simp [Formalism.UG.cT, Matrix.one_apply]
  · rw [Matrix.map_mul, Matrix.map_mul, map_snd_conj_transpose, map_snd_form, matrix_lift_snd]
    exact hg

def lift (g : HA R2 σ J) : HA (R1 × R2) σ J :=
  (⟨glift R1 R2 (HA.mat R2 σ J g), glift_mem R1 R2 σ J g⟩ : ↥(HR (R1 × R2) σ J))

def psiE : (Fin M → (R1 × R2) ⊗[F] E) ≃+ (Fin M → R1 ⊗[F] E) × (Fin M → R2 ⊗[F] E) where
  toFun x := (fun i => p1 R1 R2 (x i), fun i => p2 R1 R2 (x i))
  invFun y := fun i => qq R1 R2 (y.1 i) (y.2 i)
  left_inv x := funext fun i => qq_p R1 R2 (x i)
  right_inv y := Prod.ext (funext fun i => fst_pair R1 R2 _ _) (funext fun i => snd_pair R1 R2 _ _)
  map_add' x y := by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp

theorem psi_lin (g : HA R2 σ J) (x : Fin M → (R1 × R2) ⊗[F] E) :
    psiE R1 R2 (lin (R1 × R2) σ J (lift R1 R2 σ J g) x) =
      ((psiE R1 R2 x).1, lin R2 σ J g (psiE R1 R2 x).2) := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · show p1 R1 R2 (Matrix.mulVec (mlift R1 R2 (HA.mat R2 σ J g : Matrix (Fin M) (Fin M) (R2 ⊗[F] E))) x i) = p1 R1 R2 (x i)
    rw [RingHom.map_mulVec, matrix_lift_fst, Matrix.one_mulVec]
    rfl
  · show p2 R1 R2 (Matrix.mulVec (mlift R1 R2 (HA.mat R2 σ J g : Matrix (Fin M) (Fin M) (R2 ⊗[F] E))) x i) =
      Matrix.mulVec (HA.mat R2 σ J g : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)) (fun k => p2 R1 R2 (x k)) i
    rw [RingHom.map_mulVec, matrix_lift_snd]
    rfl

end Ring

end PI.LevelKSplit.W.MVA
end
end

noncomputable section

namespace PI.LevelKSplit.W.MVA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

theorem cancel_prod {X Y : Type} [TopologicalSpace X] [AddGroup X] [IsTopologicalAddGroup X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y]
    (ν : Measure X) [ν.IsAddHaarMeasure] [SFinite ν] (a b : Measure Y) [SFinite a] [SFinite b]
    (h : ν.prod a = ν.prod b) : a = b := by
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (0 : X)
  have h0 : ν K ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hKn).ne'
  have hinf : ν K ≠ ⊤ := hK.measure_lt_top.ne
  ext s hs
  have h1 := congrArg (fun m => m (K ×ˢ s)) h
  simp only [Measure.prod_prod] at h1
  exact (ENNReal.mul_right_inj h0 hinf).1 h1

section Top

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

theorem continuous_crd (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] : Continuous (crd (F := F) (E := E) R) := by
  first
  | exact continuous_induced_dom
  | exact IsModuleTopology.continuous_of_linearMap (crd (F := F) (E := E) R).toLinearMap
  | fun_prop
  | (delta crd; exact LinearMap.continuous_of_finiteDimensional _)

theorem continuous_crd_symm (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] : Continuous (crd (F := F) (E := E) R).symm := by
  first
  | exact continuous_induced_rng.2 (by simpa [Function.comp_def] using continuous_id)
  | exact IsModuleTopology.continuous_of_linearMap (crd (F := F) (E := E) R).symm.toLinearMap
  | fun_prop

variable (R1 R2 : Type) [CommRing R1] [Algebra F R1] [CommRing R2] [Algebra F R2]
  [TopologicalSpace R1] [IsTopologicalRing R1] [TopologicalSpace R2] [IsTopologicalRing R2]

theorem continuous_first_orbit_map : Continuous (p1 (F := F) (E := E) R1 R2) := by
  have key : ∀ x, p1 (F := F) (E := E) R1 R2 x =
      (crd (F := F) (E := E) R1).symm (fun i => (crd (F := F) (E := E) (R1 × R2) x i).1) := by
    intro x
    apply (crd (F := F) (E := E) R1).injective
    rw [LinearEquiv.apply_symm_apply]
    funext i
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
      simp [crd, p1, Algebra.TensorProduct.basis_repr_tmul]
    | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, Prod.fst_add, hx, hy]
  rw [show p1 (F := F) (E := E) R1 R2 = fun x =>
      (crd (F := F) (E := E) R1).symm (fun i => (crd (F := F) (E := E) (R1 × R2) x i).1) from funext key]
  exact (continuous_crd_symm R1).comp
    (continuous_pi fun i => continuous_fst.comp ((continuous_apply i).comp (continuous_crd (R1 × R2))))

theorem continuous_p2 : Continuous (p2 (F := F) (E := E) R1 R2) := by
  have key : ∀ x, p2 (F := F) (E := E) R1 R2 x =
      (crd (F := F) (E := E) R2).symm (fun i => (crd (F := F) (E := E) (R1 × R2) x i).2) := by
    intro x
    apply (crd (F := F) (E := E) R2).injective
    rw [LinearEquiv.apply_symm_apply]
    funext i
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
      simp [crd, p2, Algebra.TensorProduct.basis_repr_tmul]
    | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, Prod.snd_add, hx, hy]
  rw [show p2 (F := F) (E := E) R1 R2 = fun x =>
      (crd (F := F) (E := E) R2).symm (fun i => (crd (F := F) (E := E) (R1 × R2) x i).2) from funext key]
  exact (continuous_crd_symm R2).comp
    (continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_crd (R1 × R2))))

theorem continuous_qq :
    Continuous (fun y : (R1 ⊗[F] E) × (R2 ⊗[F] E) => qq R1 R2 y.1 y.2) := by
  delta qq
  exact (continuous_crd_symm (R1 × R2)).comp (continuous_pi fun k =>
    (((continuous_apply k).comp (continuous_crd R1)).comp continuous_fst).prodMk
      (((continuous_apply k).comp (continuous_crd R2)).comp continuous_snd))

variable {M : ℕ}

theorem continuous_psiE : Continuous (psiE (F := F) (E := E) (M := M) R1 R2) := by
  show Continuous (fun x : Fin M → (R1 × R2) ⊗[F] E =>
    (fun i => p1 (F := F) (E := E) R1 R2 (x i), fun i => p2 (F := F) (E := E) R1 R2 (x i)))
  exact (continuous_pi fun i => (continuous_first_orbit_map R1 R2).comp (continuous_apply i)).prodMk
    (continuous_pi fun i => (continuous_p2 R1 R2).comp (continuous_apply i))


set_option maxHeartbeats 800000 in
theorem continuous_qqv :
    Continuous (fun y : (Fin M → R1 ⊗[F] E) × (Fin M → R2 ⊗[F] E) => fun i => qq R1 R2 (y.1 i) (y.2 i)) := by
  refine continuous_pi fun i => ?_
  have h1 : Continuous (fun y : (Fin M → R1 ⊗[F] E) × (Fin M → R2 ⊗[F] E) => (y.1 i, y.2 i)) :=
    ((continuous_apply i).comp continuous_fst).prodMk ((continuous_apply i).comp continuous_snd)
  have h2 := (continuous_qq R1 R2).comp h1
  simpa only [Function.comp_def] using h2

set_option maxHeartbeats 1000000 in
theorem continuous_psiE_symm : Continuous (psiE (F := F) (E := E) (M := M) R1 R2).symm := by
  show Continuous (fun y : (Fin M → R1 ⊗[F] E) × (Fin M → R2 ⊗[F] E) =>
    fun i => qq R1 R2 (y.1 i) (y.2 i))
  exact continuous_qqv R1 R2

theorem continuous_lin (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (g : HA R σ J) :
    Continuous (lin R σ J g) := by
  first
  | exact IsModuleTopology.continuous_of_linearMap ((lin R σ J g).restrictScalars R)
  | exact Continuous.matrix_mulVec continuous_const continuous_id
  | (delta lin; fun_prop)

end Top

section Meas

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R1 R2 : Type) [CommRing R1] [Algebra F R1] [CommRing R2] [Algebra F R2]
  [TopologicalSpace R1] [IsTopologicalRing R1] [LocallyCompactSpace R1] [T2Space R1]
  [SecondCountableTopology R1]
  [TopologicalSpace R2] [IsTopologicalRing R2] [LocallyCompactSpace R2] [T2Space R2]
  [SecondCountableTopology R2]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem pres_snd
    (hV : ∀ (g : HA (R1 × R2) σ J) (ν : Measure (Fin M → (R1 × R2) ⊗[F] E)),
      ν.IsAddHaarMeasure → ν.map (lin (R1 × R2) σ J g) = ν)
    (g : HA R2 σ J) (μ : Measure (Fin M → R2 ⊗[F] E)) (hμ : μ.IsAddHaarMeasure) :
    μ.map (lin R2 σ J g) = μ := by
  let ν1 : Measure (Fin M → R1 ⊗[F] E) := Measure.addHaar
  let e := psiE (F := F) (E := E) (M := M) R1 R2
  have hc : Continuous e := continuous_psiE R1 R2
  have hcs : Continuous e.symm := continuous_psiE_symm R1 R2
  let P0 : Measure ((Fin M → R1 ⊗[F] E) × (Fin M → R2 ⊗[F] E)) := ν1.prod μ
  have : P0.IsAddHaarMeasure := inferInstance
  let P : Measure (Fin M → (R1 × R2) ⊗[F] E) := P0.map e.symm
  have : P.IsAddHaarMeasure := e.symm.isAddHaarMeasure_map P0 hcs hc
  have hP := hV (lift R1 R2 σ J g) P inferInstance
  have hl1 := continuous_lin (R1 × R2) σ J (lift R1 R2 σ J g)
  have hl2 := continuous_lin R2 σ J g
  have hPe : P.map e = P0 := by
    rw [Measure.map_map hc.measurable hcs.measurable]
    have : (e ∘ e.symm) = id := funext e.apply_symm_apply
    rw [this, Measure.map_id]
  have key : P0.map (Prod.map id (lin R2 σ J g)) = P0 := by
    have h1 : (Prod.map id (lin R2 σ J g)) ∘ e = e ∘ (lin (R1 × R2) σ J (lift R1 R2 σ J g)) := by
      funext x
      exact (psi_lin R1 R2 σ J g x).symm
    calc P0.map (Prod.map id (lin R2 σ J g))
        = (P.map e).map (Prod.map id (lin R2 σ J g)) := by rw [hPe]
      _ = P.map ((Prod.map id (lin R2 σ J g)) ∘ e) :=
          Measure.map_map (measurable_id.prodMap hl2.measurable) hc.measurable
      _ = P.map (e ∘ (lin (R1 × R2) σ J (lift R1 R2 σ J g))) := by rw [h1]
      _ = (P.map (lin (R1 × R2) σ J (lift R1 R2 σ J g))).map e :=
          (Measure.map_map hc.measurable hl1.measurable).symm
      _ = P0 := by rw [hP, hPe]
  rw [← Measure.map_prod_map ν1 μ measurable_id hl2.measurable, Measure.map_id] at key
  exact (cancel_prod ν1 _ _ key).symm ▸ rfl

end Meas

end PI.LevelKSplit.W.MVA
end
end

noncomputable section

namespace PI.LevelKSplit.W.MVA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

theorem modVAll_of_vmod (h : PI.VolSemiDirect.W.Cj.VMod) : PI.LevelKSplit.W.CD.ModVAll := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  intro _ _ g μ hμ
  exact pres_snd (InfiniteAdeleRing F) (Af F) σ J
    (fun g' ν hν => h F E σ hσ M J hJ g' ν hν) g μ hμ

theorem modulus_all_extensions : PI.LevelKSplit.W.CD.ModVAll :=
  modVAll_of_vmod PI.VolSemiDirect.W.Cj.unipotent_modulus_holds

end PI.LevelKSplit.W.MVA
