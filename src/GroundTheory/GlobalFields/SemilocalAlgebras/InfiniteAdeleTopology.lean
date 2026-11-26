module

public import GroundTheory.GlobalFields.SemilocalAlgebras.ContinuousCompletionMap

@[expose] public section

section -- merged from GroundTheory.GlobalFields.SemilocalAlgebras.InfiniteAdele
noncomputable section

namespace GroundTheory.Global

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.LiesOver TensorProduct

namespace InfinitePlace

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

instance liesOver_comap (w : InfinitePlace L) : w.LiesOver (w.comap (algebraMap K L)) :=
  (liesOver_iff_comap_eq _ w).2 rfl

def piPlacesOverEquiv :
    ((v : InfinitePlace K) → PiPlacesOver (L := L) v) ≃ₐ[L] InfiniteAdeleRing L where
  toFun x w := x (w.comap (algebraMap K L)) ⟨w, liesOver_comap w⟩
  invFun y v w := y w
  left_inv x := by
    funext v w
    obtain ⟨w, hw⟩ := w
    have h : w.comap (algebraMap K L) = v := (liesOver_iff_comap_eq v w).1 hw
    subst h
    rfl
  right_inv y := rfl
  map_mul' x y := rfl
  map_add' x y := rfl
  commutes' l := rfl

variable [NumberField K] [NumberField L]


open scoped Classical in
def tensorInfiniteAdeleRingEquiv :
    L ⊗[K] InfiniteAdeleRing K ≃ₐ[L] InfiniteAdeleRing L :=
  by
    classical
    exact (Algebra.TensorProduct.piRight K L L (fun v : InfinitePlace K => v.Completion)).trans <|
      (AlgEquiv.piCongrRight fun v => tensorPiEquivLeft (L := L) v).trans piPlacesOverEquiv

theorem tensorInfiniteAdeleRingEquiv_tmul (l : L) (x : InfiniteAdeleRing K)
    (w : InfinitePlace L) :
    tensorInfiniteAdeleRingEquiv (l ⊗ₜ x) w =
      (l : w.Completion) * algebraMap (w.comap (algebraMap K L)).Completion w.Completion
        (x (w.comap (algebraMap K L))) := by
  change tensorPiEquivLeft (L := L) (w.comap (algebraMap K L))
    (l ⊗ₜ x (w.comap (algebraMap K L))) ⟨w, liesOver_comap w⟩ = _
  rw [tensorPiEquivLeft_tmul]


omit [NumberField K] [NumberField L] in
def infiniteAdeleRingMap : InfiniteAdeleRing K →+* InfiniteAdeleRing L :=
  by classical
  exact RingHom.pi fun w : InfinitePlace L =>
    (algebraMap (w.comap (algebraMap K L)).Completion w.Completion).comp
      (Pi.evalRingHom (fun v : InfinitePlace K => v.Completion) (w.comap (algebraMap K L)))

omit [NumberField K] [NumberField L] in
@[simp]
theorem infiniteAdeleRingMap_apply (x : InfiniteAdeleRing K) (w : InfinitePlace L) :
    infiniteAdeleRingMap x w =
      algebraMap (w.comap (algebraMap K L)).Completion w.Completion
        (x (w.comap (algebraMap K L))) := rfl


omit [NumberField K] [NumberField L] in
theorem continuous_infiniteAdeleRingMap :
    Continuous (infiniteAdeleRingMap (K := K) (L := L)) :=
  continuous_pi fun w =>
    (continuous_algebraMap (w.comap (algebraMap K L)).Completion w.Completion).comp
      (continuous_apply (w.comap (algebraMap K L)))


omit [NumberField K] [NumberField L] in
theorem infiniteAdeleRingMap_algebraMap (k : K) :
    infiniteAdeleRingMap (algebraMap K (InfiniteAdeleRing K) k) =
      algebraMap L (InfiniteAdeleRing L) (algebraMap K L k) := by
  funext w
  rw [infiniteAdeleRingMap_apply, InfiniteAdeleRing.algebraMap_apply,
    InfiniteAdeleRing.algebraMap_apply]
  have h₁ : algebraMap K (w.comap (algebraMap K L)).Completion k =
      (WithAbs.toAbs (w.comap (algebraMap K L)).1 k : (w.comap (algebraMap K L)).Completion) := by
    rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
      Algebra.algebraMap_self_apply]
  have h₂ : algebraMap L w.Completion (algebraMap K L k) =
      (WithAbs.toAbs w.1 (algebraMap K L k) : w.Completion) := by
    rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
      Algebra.algebraMap_self_apply]
  rw [← h₁, ← h₂]
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K L]

theorem tensorInfiniteAdeleRingEquiv_tmul' (l : L) (x : InfiniteAdeleRing K) :
    tensorInfiniteAdeleRingEquiv (l ⊗ₜ x) =
      algebraMap L (InfiniteAdeleRing L) l * infiniteAdeleRingMap x := by
  funext w
  rw [tensorInfiniteAdeleRingEquiv_tmul]
  rw [Pi.mul_apply, InfiniteAdeleRing.algebraMap_apply, infiniteAdeleRingMap_apply]

end InfinitePlace

end GroundTheory.Global
end
end

noncomputable section

namespace GroundTheory.Global

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.LiesOver TensorProduct

namespace InfinitePlace

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [NumberField K] [NumberField L]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

def piPlacesOverCoord {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K L)
    (v : InfinitePlace K) (i : ι) : PiPlacesOver (L := L) v →ₗ[v.Completion] v.Completion :=
  ((Algebra.TensorProduct.basis v.Completion b).coord i).comp
    (tensorPiEquiv (L := L) v).symm.toLinearMap

theorem continuous_piPlacesOverCoord {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (v : InfinitePlace K) (i : ι) :
    Continuous (piPlacesOverCoord b v i) :=
  LinearMap.continuous_of_finiteDimensional _

theorem sum_piPlacesOverCoord {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K L)
    (v : InfinitePlace K) (y : PiPlacesOver (L := L) v) (w : v.placesOver L) :
    ∑ i, algebraMap v.Completion _ (piPlacesOverCoord b v i y) *
      (b i : (w : InfinitePlace L).Completion) = y w := by
  have h := (Algebra.TensorProduct.basis v.Completion b).sum_repr
    ((tensorPiEquiv (L := L) v).symm y)
  have h2 := congrArg (fun z => tensorPiEquiv (L := L) v z w) h
  simp only [AlgEquiv.apply_symm_apply] at h2
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h2, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, map_smul, Pi.smul_apply, tensorPiEquiv_apply,
    tensorPiHom_tmul, map_one, one_mul, Algebra.smul_def]
  rfl

def adeleCoord {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K L) (i : ι)
    (y : InfiniteAdeleRing L) : InfiniteAdeleRing K :=
  fun v => piPlacesOverCoord b v i (fun w => y w)

theorem continuous_adeleCoord {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K L)
    (i : ι) : Continuous (adeleCoord b i) :=
  continuous_pi fun v => (continuous_piPlacesOverCoord b v i).comp
    (continuous_pi fun w => continuous_apply (w : InfinitePlace L))

theorem tensorInfiniteAdeleRingEquiv_sum_adeleCoord {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (y : InfiniteAdeleRing L) :
    tensorInfiniteAdeleRingEquiv (∑ i, b i ⊗ₜ[K] adeleCoord b i y) = y := by
  funext w
  have ev : ∀ f : ι → InfiniteAdeleRing L, (∑ i, f i) w = ∑ i, f i w := fun f =>
    map_sum (Pi.evalAddMonoidHom (fun w : InfinitePlace L => w.Completion) w) f Finset.univ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ev]
  simp_rw [tensorInfiniteAdeleRingEquiv_tmul]
  have := sum_piPlacesOverCoord b (w.comap (algebraMap K L)) (fun w' => y w') ⟨w, liesOver_comap w⟩
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
  rfl

def tmulLeft (l : L) : InfiniteAdeleRing K →ₗ[InfiniteAdeleRing K] L ⊗[K] InfiniteAdeleRing K where
  toFun x := l ⊗ₜ x
  map_add' x y := TensorProduct.tmul_add _ _ _
  map_smul' c x := by
    change l ⊗ₜ (c * x) = (1 ⊗ₜ c) * (l ⊗ₜ x)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

def tensorInfiniteAdeleRingHomeomorph :
    letI := moduleTopology (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)
    L ⊗[K] InfiniteAdeleRing K ≃ₜ InfiniteAdeleRing L :=
  letI := moduleTopology (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)
  haveI : IsModuleTopology (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)
  let b := Module.finBasis K L
  { toEquiv := (tensorInfiniteAdeleRingEquiv (K := K) (L := L)).toEquiv
    continuous_toFun := by
      let φ : L ⊗[K] InfiniteAdeleRing K →ₛₗ[infiniteAdeleRingMap (K := K) (L := L)]
          InfiniteAdeleRing L :=
        { toFun := tensorInfiniteAdeleRingEquiv
          map_add' := map_add _
          map_smul' := fun c t => by
            change tensorInfiniteAdeleRingEquiv ((1 ⊗ₜ c) * t) = infiniteAdeleRingMap c * _
            rw [map_mul, tensorInfiniteAdeleRingEquiv_tmul', map_one, one_mul] }
      exact IsModuleTopology.continuous_of_linearMapₛₗ continuous_infiniteAdeleRingMap φ
    continuous_invFun := by
      have h : ∀ y, (tensorInfiniteAdeleRingEquiv (K := K) (L := L)).symm y =
          ∑ i, tmulLeft (b i) (adeleCoord b i y) := fun y => by
        rw [AlgEquiv.symm_apply_eq]
        exact (tensorInfiniteAdeleRingEquiv_sum_adeleCoord b y).symm
      change Continuous fun y => (tensorInfiniteAdeleRingEquiv (K := K) (L := L)).symm y
      simp_rw [h]
      exact continuous_finsetSum _ fun i _ =>
        (IsModuleTopology.continuous_of_linearMap (tmulLeft (b i))).comp
          (continuous_adeleCoord b i) }

end InfinitePlace

end GroundTheory.Global
