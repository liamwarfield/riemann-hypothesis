module

public import GroundTheory.GlobalFields.Adele.BaseChange.FiniteTensor
public import GroundTheory.GlobalFields.SemilocalAlgebras.InfiniteAdeleTopology

@[expose] public section

section -- merged from GroundTheory.GlobalFields.Adele.BaseChange.AdeleEquiv
namespace GroundTheory.Global

open IsDedekindDomain NumberField TensorProduct Module Topology
open scoped NumberField.AdeleRing

noncomputable section

namespace AdeleBaseChange

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable (K L) in
def adeleMap : 𝔸[K] →+* 𝔸[L] :=
  RingHom.prodMap (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := K) (L := L))
    (finiteAdeleMap K L)

theorem adeleMap_apply (x : 𝔸[K]) :
    adeleMap K L x =
      (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap x.1, finiteAdeleMap K L x.2) :=
  rfl

theorem continuous_adeleMap : Continuous (adeleMap K L) :=
  GroundTheory.Global.InfinitePlace.continuous_infiniteAdeleRingMap.prodMap continuous_finiteAdeleMap

theorem adeleMap_algebraMap (k : K) :
    adeleMap K L (algebraMap K 𝔸[K] k) = algebraMap L 𝔸[L] (algebraMap K L k) :=
  Prod.ext (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_algebraMap k)
    (finiteAdeleMap_algebraMap k)

variable (K L) in
def adeleTensorEquiv : L ⊗[K] 𝔸[K] ≃ₐ[L] 𝔸[L] :=
  (Algebra.TensorProduct.prodRight K L L (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).trans
    (AlgEquiv.prodCongr GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv
      (finiteTensorEquiv K L))

theorem adeleTensorEquiv_tmul (l : L) (a : 𝔸[K]) :
    adeleTensorEquiv K L (l ⊗ₜ a) = algebraMap L 𝔸[L] l * adeleMap K L a :=
  Prod.ext (GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_tmul' l a.1)
    (finiteTensorEquiv_tmul l a.2)

theorem adeleTensorEquiv_tmul_snd (l : L) (a : 𝔸[K]) (w : HeightOneSpectrum (𝓞 L)) :
    (adeleTensorEquiv K L (l ⊗ₜ a)).2 w =
      SemiLocal.tensorEquiv' L (below K w) (l ⊗ₜ a.2 (below K w)) ⟨w, liesOver_below w⟩ :=
  finiteTensorEquiv_tmul_apply l a.2 w

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)

def coord (i : ι) (y : 𝔸[L]) : 𝔸[K] :=
  (GroundTheory.Global.InfinitePlace.adeleCoord b i y.1, finiteCoord b i y.2)

theorem continuous_coord (i : ι) : Continuous (coord b i) :=
  ((GroundTheory.Global.InfinitePlace.continuous_adeleCoord b i).comp continuous_fst).prodMk
    ((continuous_finiteCoord b i).comp continuous_snd)

def fstAddHom : 𝔸[L] →+ InfiniteAdeleRing L where
  toFun := Prod.fst
  map_zero' := rfl
  map_add' _ _ := rfl

def sndAddHom : 𝔸[L] →+ FiniteAdeleRing (𝓞 L) L where
  toFun := Prod.snd
  map_zero' := rfl
  map_add' _ _ := rfl

theorem adeleTensorEquiv_sum_coord (y : 𝔸[L]) :
    adeleTensorEquiv K L (∑ i, b i ⊗ₜ coord b i y) = y := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp_rw [adeleTensorEquiv_tmul]
  refine Prod.ext ?_ ?_
  · change fstAddHom (∑ i, algebraMap L 𝔸[L] (b i) * adeleMap K L (coord b i y)) = y.1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    conv_rhs => rw [← GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_sum_adeleCoord b y.1]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp_rw [GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_tmul']
    rfl
  · change sndAddHom (∑ i, algebraMap L 𝔸[L] (b i) * adeleMap K L (coord b i y)) = y.2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    conv_rhs => rw [← finiteTensorMap_sum_finiteCoord b y.2]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp_rw [finiteTensorMap_tmul]
    rfl

theorem adeleTensorEquiv_symm_apply (y : 𝔸[L]) :
    (adeleTensorEquiv K L).symm y = ∑ i, b i ⊗ₜ coord b i y := by
  rw [AlgEquiv.symm_apply_eq]
  exact (adeleTensorEquiv_sum_coord b y).symm

end AdeleBaseChange

end

end GroundTheory.Global
end

namespace GroundTheory.Global

open IsDedekindDomain NumberField TensorProduct Module Topology
open scoped NumberField.AdeleRing RestrictedProduct

noncomputable section

namespace AdeleBaseChange

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

def tmulLeft (l : L) : 𝔸[K] →ₗ[𝔸[K]] L ⊗[K] 𝔸[K] where
  toFun x := l ⊗ₜ x
  map_add' x y := TensorProduct.tmul_add _ _ _
  map_smul' c x := by
    change l ⊗ₜ (c * x) = (1 ⊗ₜ c) * (l ⊗ₜ x)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem adeleTensorEquiv_one_tmul_mul (a : 𝔸[K]) (t : L ⊗[K] 𝔸[K]) :
    adeleTensorEquiv K L ((1 ⊗ₜ a) * t) = adeleMap K L a * adeleTensorEquiv K L t := by
  rw [map_mul, adeleTensorEquiv_tmul, map_one, one_mul]


variable (K L) in
def adeleTensorSemilinear : L ⊗[K] 𝔸[K] →ₛₗ[adeleMap K L] 𝔸[L] where
  toFun := adeleTensorEquiv K L
  map_add' := map_add _
  map_smul' c t := adeleTensorEquiv_one_tmul_mul c t


variable (K L) in
def adeleTensorHomeomorph :
    letI := moduleTopology 𝔸[K] (L ⊗[K] 𝔸[K])
    L ⊗[K] 𝔸[K] ≃ₜ 𝔸[L] :=
  letI := moduleTopology 𝔸[K] (L ⊗[K] 𝔸[K])
  haveI : IsModuleTopology 𝔸[K] (L ⊗[K] 𝔸[K]) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd 𝔸[K] (L ⊗[K] 𝔸[K])
  { toEquiv := (adeleTensorEquiv K L).toEquiv
    continuous_toFun :=
      IsModuleTopology.continuous_of_linearMapₛₗ continuous_adeleMap (adeleTensorSemilinear K L)
    continuous_invFun := by
      have h : ∀ y, (adeleTensorEquiv K L).symm y =
          ∑ i, tmulLeft (Module.finBasis K L i) (coord (Module.finBasis K L) i y) :=
        adeleTensorEquiv_symm_apply (Module.finBasis K L)
      change Continuous fun y ↦ (adeleTensorEquiv K L).symm y
      simp_rw [h]
      exact continuous_finsetSum _ fun i _ ↦
        (IsModuleTopology.continuous_of_linearMap (tmulLeft (Module.finBasis K L i))).comp
          (continuous_coord _ i) }


scoped instance algebraAdeleRing : Algebra 𝔸[K] 𝔸[L] :=
  (adeleMap K L).toAlgebra

theorem algebraMap_adeleRing : algebraMap 𝔸[K] 𝔸[L] = adeleMap K L :=
  rfl

scoped instance continuousSMul_adeleRing : ContinuousSMul 𝔸[K] 𝔸[L] :=
  continuousSMul_of_algebraMap _ _ continuous_adeleMap


variable (K L) in
def adeleTensorAlgEquivAdele : L ⊗[K] 𝔸[K] ≃ₐ[𝔸[K]] 𝔸[L] :=
  AlgEquiv.ofRingEquiv (f := (adeleTensorEquiv K L).toRingEquiv) fun a ↦ by
    change adeleTensorEquiv K L (1 ⊗ₜ a) = adeleMap K L a
    rw [adeleTensorEquiv_tmul, map_one, one_mul]


theorem isModuleTopology_adeleRing : IsModuleTopology 𝔸[K] 𝔸[L] := by
  let := moduleTopology 𝔸[K] (L ⊗[K] 𝔸[K])
  have : IsModuleTopology 𝔸[K] (L ⊗[K] 𝔸[K]) := ⟨rfl⟩
  exact IsModuleTopology.iso
    { (adeleTensorAlgEquivAdele K L).toLinearEquiv with
      continuous_toFun := (adeleTensorHomeomorph K L).continuous_toFun
      continuous_invFun := (adeleTensorHomeomorph K L).continuous_invFun }


variable (K L) in
def normalizedTrace : L →ₗ[K] K :=
  (finrank K L : K)⁻¹ • Algebra.trace K L

theorem normalizedTrace_one : normalizedTrace K L 1 = 1 := by
  rw [normalizedTrace, LinearMap.smul_apply, ← map_one (algebraMap K L), Algebra.trace_algebraMap,
    nsmul_eq_mul, mul_one, smul_eq_mul, inv_mul_cancel₀]
  exact Nat.cast_ne_zero.2 Module.finrank_pos.ne'


variable (K L) in
def traceRetraction : L ⊗[K] 𝔸[K] →ₗ[𝔸[K]] 𝔸[K] where
  toFun t := TensorProduct.lid K 𝔸[K] (LinearMap.rTensor 𝔸[K] (normalizedTrace K L) t)
  map_add' s t := by simp only [map_add (f := _)]
  map_smul' c t := by
    change _ = c * _
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul l a =>
      change TensorProduct.lid K 𝔸[K] (LinearMap.rTensor 𝔸[K] (normalizedTrace K L)
        ((1 ⊗ₜ c) * (l ⊗ₜ a))) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, LinearMap.rTensor_tmul,
        LinearMap.rTensor_tmul, TensorProduct.lid_tmul, TensorProduct.lid_tmul, mul_smul_comm]
    | add s t hs ht => simp only [smul_add, map_add (f := _), hs, ht, mul_add]

theorem traceRetraction_one_tmul (a : 𝔸[K]) : traceRetraction K L (1 ⊗ₜ a) = a := by
  change TensorProduct.lid K 𝔸[K] (LinearMap.rTensor 𝔸[K] (normalizedTrace K L) (1 ⊗ₜ a)) = a
  rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, normalizedTrace_one, one_smul]


variable (K L) in
def adeleRetraction (y : 𝔸[L]) : 𝔸[K] :=
  traceRetraction K L ((adeleTensorEquiv K L).symm y)

theorem adeleRetraction_adeleMap (a : 𝔸[K]) : adeleRetraction K L (adeleMap K L a) = a := by
  have : (adeleTensorEquiv K L).symm (adeleMap K L a) = 1 ⊗ₜ a := by
    rw [AlgEquiv.symm_apply_eq, adeleTensorEquiv_tmul, map_one, one_mul]
  rw [adeleRetraction, this, traceRetraction_one_tmul]

theorem continuous_adeleRetraction : Continuous (adeleRetraction K L) := by
  let := moduleTopology 𝔸[K] (L ⊗[K] 𝔸[K])
  have : IsModuleTopology 𝔸[K] (L ⊗[K] 𝔸[K]) := ⟨rfl⟩
  exact (IsModuleTopology.continuous_of_linearMap (traceRetraction K L)).comp
    (adeleTensorHomeomorph K L).symm.continuous

theorem adeleMap_injective : Function.Injective (adeleMap K L) :=
  Function.LeftInverse.injective (g := adeleRetraction K L) adeleRetraction_adeleMap


end AdeleBaseChange

end

end GroundTheory.Global
