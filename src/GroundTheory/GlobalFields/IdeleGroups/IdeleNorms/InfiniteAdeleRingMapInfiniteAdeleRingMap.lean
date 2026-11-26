module

public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange

@[expose] public section

section -- merged from GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.InfiniteAdeleRingMapInfiniteAdeleRingMap
namespace GroundTheory.Global

open IsDedekindDomain NumberField
open scoped NumberField.AdeleRing NumberField.LiesOver

noncomputable section

namespace AdeleBaseChange

open SemiLocal

variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]

theorem completionMap_completionMap (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    (u : HeightOneSpectrum (𝓞 M)) [w.asIdeal.LiesOver v.asIdeal] [u.asIdeal.LiesOver w.asIdeal]
    [u.asIdeal.LiesOver v.asIdeal] (a : v.adicCompletion K) :
    completionMap w u (completionMap v w a) = completionMap v u a := by
  have h := (HeightOneSpectrum.denseRange_algebraMap K v).equalizer
    ((continuous_completionMap w u).comp (continuous_completionMap v w))
    (continuous_completionMap v u) (funext fun k ↦ ?_)
  · exact congrFun h a
  · simp only [Function.comp_apply]
    rw [completionMap_algebraMap, completionMap_algebraMap,
      IsScalarTower.algebraMap_apply K L (w.adicCompletion L), completionMap_algebraMap,
      IsScalarTower.algebraMap_apply L M (u.adicCompletion M),
      IsScalarTower.algebraMap_apply K M (u.adicCompletion M), ← IsScalarTower.algebraMap_apply K L M]


omit [NumberField K] [NumberField L] [NumberField M] in
theorem below_below (u : HeightOneSpectrum (𝓞 M)) : below K (below L u) = below K u :=
  HeightOneSpectrum.ext (Ideal.under_under (A := 𝓞 K) (B := 𝓞 L) u.asIdeal)

theorem finiteAdeleMap_finiteAdeleMap (x : FiniteAdeleRing (𝓞 K) K) :
    finiteAdeleMap L M (finiteAdeleMap K L x) = finiteAdeleMap K M x := by
  refine FiniteAdeleRing.ext (K := M) fun u ↦ ?_
  have hb := below_below (K := K) (L := L) u
  have : u.asIdeal.LiesOver (below K (below L u)).asIdeal := by rw [hb]; infer_instance
  rw [finiteAdeleMap_apply, finiteAdeleMap_apply, finiteAdeleMap_apply,
    completionMap_completionMap (below K (below L u)) (below L u) u]
  exact completionMap_congr hb u x


omit [NumberField K] [NumberField L] [NumberField M] in
theorem algebraMap_completion_algebraMap (v : InfinitePlace K) (w : InfinitePlace L)
    (u : InfinitePlace M) [w.LiesOver v] [u.LiesOver w] [u.LiesOver v] (a : v.Completion) :
    algebraMap w.Completion u.Completion (algebraMap v.Completion w.Completion a) =
      algebraMap v.Completion u.Completion a := by
  have h := (InfinitePlace.Completion.denseRange_coe v).equalizer
    ((continuous_algebraMap w.Completion u.Completion).comp
      (continuous_algebraMap v.Completion w.Completion))
    (continuous_algebraMap v.Completion u.Completion) (funext fun y ↦ ?_)
  · exact congrFun h a
  · simp only [Function.comp_apply]
    have hy : (y : v.Completion) = algebraMap K v.Completion y.ofAbs := by
      simp [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]
    rw [hy]
    change algebraMap w.Completion u.Completion
        (algebraMap v.Completion w.Completion (algebraMap K v.Completion y.ofAbs)) =
      algebraMap v.Completion u.Completion (algebraMap K v.Completion y.ofAbs)
    rw [← IsScalarTower.algebraMap_apply K v.Completion w.Completion,
      ← IsScalarTower.algebraMap_apply K v.Completion u.Completion,
      IsScalarTower.algebraMap_apply K L w.Completion,
      ← IsScalarTower.algebraMap_apply L w.Completion u.Completion,
      IsScalarTower.algebraMap_apply L M u.Completion,
      IsScalarTower.algebraMap_apply K M u.Completion, ← IsScalarTower.algebraMap_apply K L M]

omit [NumberField K] [NumberField L] [NumberField M] [Algebra L M] [IsScalarTower K L M] in
theorem algebraMap_completion_congr {v v' : InfinitePlace K} (h : v = v') (u : InfinitePlace M)
    [u.LiesOver v] [u.LiesOver v'] (x : InfiniteAdeleRing K) :
    algebraMap v.Completion u.Completion (x v) = algebraMap v'.Completion u.Completion (x v') := by
  subst h
  rfl


omit [NumberField K] [NumberField L] [NumberField M] in
theorem infiniteAdeleRingMap_infiniteAdeleRingMap (x : InfiniteAdeleRing K) :
    GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := L) (L := M)
        (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := K) (L := L) x) =
      GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := K) (L := M) x := by
  funext u
  have hv : (u.comap (algebraMap L M)).comap (algebraMap K L) = u.comap (algebraMap K M) := by
    rw [IsScalarTower.algebraMap_eq K L M]
    rfl
  have : u.LiesOver ((u.comap (algebraMap L M)).comap (algebraMap K L)) := by
    rw [hv]; infer_instance
  rw [GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_apply,
    GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_apply,
    GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_apply,
    algebraMap_completion_algebraMap _ (u.comap (algebraMap L M)) u]
  exact algebraMap_completion_congr hv u x

theorem adeleMap_adeleMap (x : 𝔸[K]) : adeleMap L M (adeleMap K L x) = adeleMap K M x :=
  Prod.ext (infiniteAdeleRingMap_infiniteAdeleRingMap x.1) (finiteAdeleMap_finiteAdeleMap x.2)

scoped instance isScalarTower_adeleRing : IsScalarTower 𝔸[K] 𝔸[L] 𝔸[M] :=
  .of_algebraMap_eq fun x ↦ (adeleMap_adeleMap x).symm

theorem norm_adeleRing_norm (y : 𝔸[M]) :
    Algebra.norm 𝔸[K] (Algebra.norm 𝔸[L] y) = Algebra.norm 𝔸[K] y :=
  Algebra.norm_norm

end AdeleBaseChange

open AdeleBaseChange

variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]

theorem ideleEmbedding_ideleEmbedding (x : IdeleGroup K) :
    ideleEmbedding L M (ideleEmbedding K L x) = ideleEmbedding K M x :=
  Units.ext (adeleMap_adeleMap (x : 𝔸[K]))

theorem ideleNorm_ideleNorm (x : IdeleGroup M) :
    ideleNorm K L (ideleNorm L M x) = ideleNorm K M x :=
  Units.ext (norm_adeleRing_norm (K := K) (L := L) (x : 𝔸[M]))

theorem ideleClassMap_ideleClassMap (c : IdeleClassGroup K) :
    ideleClassMap L M (ideleClassMap K L c) = ideleClassMap K M c := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
  rw [ideleClassMap_mk, ideleClassMap_mk, ideleClassMap_mk, ideleEmbedding_ideleEmbedding]

theorem ideleClassNorm_ideleClassNorm (c : IdeleClassGroup M) :
    ideleClassNorm K L (ideleClassNorm L M c) = ideleClassNorm K M c := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective M c
  rw [ideleClassNorm_mk, ideleClassNorm_mk, ideleClassNorm_mk, ideleNorm_ideleNorm]

end

end GroundTheory.Global
end

section -- merged from GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.CompletionsOverBasisRepr
namespace GroundTheory.Global

open IsDedekindDomain NumberField TensorProduct Module
open scoped NumberField.AdeleRing NumberField.LiesOver

noncomputable section

namespace AdeleBaseChange

open SemiLocal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]


variable (K) in
def finiteEval (v : HeightOneSpectrum (𝓞 K)) : 𝔸[K] →+* v.adicCompletion K where
  toFun a := a.2 v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl


variable (L) in
def finiteRestrict (v : HeightOneSpectrum (𝓞 K)) : 𝔸[L] →+* CompletionsOver L v where
  toFun y w := y.2 w.1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)

def completionsOverBasis (v : HeightOneSpectrum (𝓞 K)) :
    Basis ι (v.adicCompletion K) (CompletionsOver L v) :=
  (Algebra.TensorProduct.basis (v.adicCompletion K) b).map (tensorEquiv L v).toLinearEquiv

omit [Fintype ι] [DecidableEq ι] in
theorem completionsOverBasis_repr (v : HeightOneSpectrum (𝓞 K)) (z : CompletionsOver L v)
    (i : ι) : (completionsOverBasis b v).repr z i = localCoord b v i z :=
  rfl

theorem finiteEval_norm (v : HeightOneSpectrum (𝓞 K)) (y : 𝔸[L]) :
    finiteEval K v (Algebra.norm 𝔸[K] y) =
      Algebra.norm (v.adicCompletion K) (finiteRestrict L v y) := by
  classical
  refine (norm_map_of_repr (finiteEval K v) (finiteRestrict L v) (adeleBasis (Module.finBasis K L))
    (completionsOverBasis (Module.finBasis K L) v) (fun y i ↦ ?_) y).symm
  rw [completionsOverBasis_repr, adeleBasis_repr]
  rfl

theorem norm_adeleRing_snd (v : HeightOneSpectrum (𝓞 K)) (y : 𝔸[L]) :
    (Algebra.norm 𝔸[K] y).2 v =
      ∏ w : PlacesOver L v, Algebra.norm (v.adicCompletion K) (y.2 w.1) :=
  (finiteEval_norm v y).trans (norm_pi _)


variable (K) in
def infiniteEval (v : InfinitePlace K) : 𝔸[K] →+* v.Completion where
  toFun a := a.1 v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl


variable (L) in
def infiniteRestrict (v : InfinitePlace K) :
    𝔸[L] →+* GroundTheory.Global.InfinitePlace.PiPlacesOver (L := L) v where
  toFun y w := y.1 w
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def piPlacesOverBasis (v : InfinitePlace K) :
    Basis ι v.Completion (GroundTheory.Global.InfinitePlace.PiPlacesOver (L := L) v) :=
  (Algebra.TensorProduct.basis v.Completion b).map
    (GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := L) v).toLinearEquiv

theorem piPlacesOverBasis_repr (v : InfinitePlace K)
    (z : GroundTheory.Global.InfinitePlace.PiPlacesOver (L := L) v) (i : ι) :
    (piPlacesOverBasis b v).repr z i = GroundTheory.Global.InfinitePlace.piPlacesOverCoord b v i z :=
  rfl

theorem infiniteEval_norm (v : InfinitePlace K) (y : 𝔸[L]) :
    infiniteEval K v (Algebra.norm 𝔸[K] y) =
      Algebra.norm v.Completion (infiniteRestrict L v y) := by
  classical
  refine (norm_map_of_repr (infiniteEval K v) (infiniteRestrict L v)
    (adeleBasis (Module.finBasis K L)) (piPlacesOverBasis (Module.finBasis K L) v)
    (fun y i ↦ ?_) y).symm
  rw [piPlacesOverBasis_repr, adeleBasis_repr]
  rfl


open scoped Classical in
theorem norm_adeleRing_fst (v : InfinitePlace K) (y : 𝔸[L]) :
    (Algebra.norm 𝔸[K] y).1 v =
      ∏ w : v.placesOver L, Algebra.norm v.Completion (y.1 w) :=
  by
    letI : ∀ w : v.placesOver L, Module.Finite v.Completion (w : InfinitePlace L).Completion :=
      fun w => GroundTheory.Global.InfinitePlace.finiteDimensional_completion v
        (w : InfinitePlace L)
    exact (infiniteEval_norm v y).trans (GroundTheory.Global.Algebra.norm_pi _)

end AdeleBaseChange

open AdeleBaseChange SemiLocal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem ideleNorm_snd (x : IdeleGroup L) (v : HeightOneSpectrum (𝓞 K)) :
    ((ideleNorm K L x : IdeleGroup K) : 𝔸[K]).2 v =
      ∏ w : PlacesOver L v, Algebra.norm (v.adicCompletion K) ((x : 𝔸[L]).2 w.1) :=
  norm_adeleRing_snd (K := K) v (x : 𝔸[L])


open scoped Classical in
theorem ideleNorm_fst (x : IdeleGroup L) (v : InfinitePlace K) :
    ((ideleNorm K L x : IdeleGroup K) : 𝔸[K]).1 v =
      ∏ w : v.placesOver L, Algebra.norm v.Completion ((x : 𝔸[L]).1 w) :=
  norm_adeleRing_fst (K := K) v (x : 𝔸[L])

end

end GroundTheory.Global
end
