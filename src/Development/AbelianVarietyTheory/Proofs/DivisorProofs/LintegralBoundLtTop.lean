module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexifiedDerivedActionIsLieAction
public import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugatesSeparableMatrixCompactModCentralizer
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbstractCompleteReducibility
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralBoundLtTop
open scoped TensorProduct NNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes (AF Af Ainf)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (AE)
open scoped GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

attribute [local instance] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.topTens

noncomputable section

namespace GlobalTheory.TateConv

open GroundTheory.Global GroundTheory.Global.AdeleBaseChange
open scoped NumberField.LiesOver nonZeroDivisors
open GroundTheory.Global.IdeleGroup

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def tens : AE F E ≃ₐ[AF F] AdeleRing (𝓞 E) E := adeleTensorAlgEquivLeft F E

theorem continuous_tens : Continuous (tens F E) := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  exact IsModuleTopology.continuous_of_linearMap (tens F E).toLinearMap

theorem continuous_tens_symm : Continuous (tens F E).symm := by
  haveI := isModuleTopology_adeleRing (K := F) (L := E)
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  exact IsModuleTopology.continuous_of_linearMap (tens F E).symm.toLinearMap

def idl : (AE F E)ˣ ≃ₜ* IdeleGroup E where
  toMulEquiv := Units.mapEquiv (tens F E).toMulEquiv
  continuous_toFun := Continuous.units_map (tens F E).toMulEquiv.toMonoidHom (continuous_tens F E)
  continuous_invFun := Continuous.units_map (tens F E).symm.toMulEquiv.toMonoidHom (continuous_tens_symm F E)

theorem idl_val (l : (AE F E)ˣ) : ((idl F E l : IdeleGroup E) : AdeleRing (𝓞 E) E) = tens F E l := rfl

theorem absE_eq (l : (AE F E)ˣ) :
    (absE F E l : ℝ) = (IdeleGroup.ideleModule E (idl F E l) : ℝ) := by
  rw [← GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := F) (idl F E l),
    IdeleGroup.ideleModule_apply]
  have hN : ((ideleNorm F E (idl F E l) : IdeleGroup F) : AF F) = Algebra.norm (AF F) (l : AE F E) := by
    rw [coe_ideleNorm, idl_val]
    exact Algebra.norm_eq_of_algEquiv (tens F E) _
  have hf : ((∏ᶠ v, GlobalTheory.Doubling.absEv F E v (GlobalTheory.Doubling.unitFin F E v l) : ℝ≥0) : ℝ) =
      ∏ᶠ v, ((GlobalTheory.Doubling.absEv F E v (GlobalTheory.Doubling.unitFin F E v l) : ℝ≥0) : ℝ) :=
    NNReal.toRealHom.toMonoidHom.map_finprod (GlobalTheory.Doubling.finite_mulSupport_absEv l)
  rw [GlobalTheory.Doubling.absE_apply, NNReal.coe_mul, NNReal.coe_prod, hf]
  simp only [IdeleGroup.infiniteModule, IdeleGroup.finiteModule, hN]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [GlobalTheory.Doubling.absEw_unitInf, NNReal.coe_pow, coe_nnnorm]
    rfl
  · refine finprod_congr fun v => ?_
    rw [GlobalTheory.Doubling.absEv_unitFin, coe_nnnorm]
    rfl

theorem crd_eq (x : AE F E) (i : Fin (Module.finrank F E)) :
    GlobalTheory.XTermMaj.crd F E x i = coord (Module.finBasis F E) i (tens F E x) := by
  rw [← adeleBasis_repr]
  simp [GlobalTheory.XTermMaj.crd, adeleBasis, tens]

theorem eq_sum (y : AdeleRing (𝓞 E) E) :
    y = ∑ i, algebraMap E (AdeleRing (𝓞 E) E) (Module.finBasis F E i) *
      adeleMap F E (coord (Module.finBasis F E) i y) := by
  conv_lhs => rw [← adeleTensorEquiv_sum_coord (Module.finBasis F E) y]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp_rw [adeleTensorEquiv_tmul]

def gfin (c : Fin (Module.finrank F E) → Af F) : FiniteAdeleRing (𝓞 E) E :=
  ∑ i, algebraMap E (FiniteAdeleRing (𝓞 E) E) (Module.finBasis F E i) * finiteAdeleMap F E (c i)

theorem continuous_gfin : Continuous (gfin F E) :=
  continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_finiteAdeleMap.comp (continuous_apply i))

theorem snd_eq (y : AdeleRing (𝓞 E) E) :
    y.2 = gfin F E (fun i => (coord (Module.finBasis F E) i y).2) := by
  conv_lhs => rw [eq_sum F E y]
  change sndAddHom (∑ i, _) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  rfl

def infPart {K : Type} [Field K] [NumberField K] (y : AdeleRing (𝓞 K) K) : InfiniteAdeleRing K := y.1

theorem fst_apply (y : AdeleRing (𝓞 E) E) (w : InfinitePlace E) :
    infPart y w = ∑ i, (algebraMap E (InfiniteAdeleRing E) (Module.finBasis F E i)) w *
      algebraMap (w.comap (algebraMap F E)).Completion w.Completion
        ((coord (Module.finBasis F E) i y).1 (w.comap (algebraMap F E))) := by
  conv_lhs => rw [eq_sum F E y]
  change ((fstAddHom (L := E)) (∑ i, _)) w = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine (map_sum (Pi.evalAddMonoidHom (fun v : InfinitePlace E => v.Completion) w) _ (Finset.univ : Finset (Fin (Module.finrank F E)))).trans ?_
  rfl

theorem norm_alg (w : InfinitePlace E) (x : (w.comap (algebraMap F E)).Completion) :
    ‖algebraMap (w.comap (algebraMap F E)).Completion w.Completion x‖ = ‖x‖ := by
  refine NumberField.InfinitePlace.Completion.induction_on _ x ?_ ?_
  · exact isClosed_eq (continuous_norm.comp (continuous_algebraMap _ _)) continuous_norm
  · intro a
    rw [NumberField.InfinitePlace.Completion.algebraMap_coe, NumberField.InfinitePlace.Completion.norm_coe,
      NumberField.InfinitePlace.Completion.norm_coe]
    exact (NumberField.InfinitePlace.LiesOver.isometry_algebraMap w _).norm_map_of_map_zero (map_zero _) a

def bc : ℝ := ∑ w : InfinitePlace E, ∑ i, ‖(algebraMap E (InfiniteAdeleRing E) (Module.finBasis F E i)) w‖

theorem bc_nonneg : 0 ≤ bc F E := by unfold bc; positivity

theorem norm_fst_le (x : AE F E) (y : AdeleRing (𝓞 E) E) (hy : y = tens F E x) (w : InfinitePlace E) :
    ‖infPart y w‖ ≤ bc F E * ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E x i).1 v‖ := by
  set S := ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E x i).1 v‖
  have hS : 0 ≤ S := by positivity
  have hx : ∀ i, ‖(coord (Module.finBasis F E) i (tens F E x)).1 (w.comap (algebraMap F E))‖ ≤ S := by
    intro i
    rw [← crd_eq]
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E x i).1 v‖)
      (fun _ _ => by positivity) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun v : InfinitePlace F => ‖(GlobalTheory.XTermMaj.crd F E x i).1 v‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ _)
  rw [fst_apply F E, hy]
  calc _ ≤ ∑ i, ‖(algebraMap E (InfiniteAdeleRing E) (Module.finBasis F E i)) w *
        algebraMap (w.comap (algebraMap F E)).Completion w.Completion
          ((coord (Module.finBasis F E) i (tens F E x)).1 (w.comap (algebraMap F E)))‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖(algebraMap E (InfiniteAdeleRing E) (Module.finBasis F E i)) w‖ * S := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul, norm_alg]
        exact mul_le_mul_of_nonneg_left (hx i) (norm_nonneg _)
    _ = (∑ i, ‖(algebraMap E (InfiniteAdeleRing E) (Module.finBasis F E i)) w‖) * S := (Finset.sum_mul _ _ _).symm
    _ ≤ bc F E * S := by
        refine mul_le_mul_of_nonneg_right ?_ hS
        exact Finset.single_le_sum (f := fun w : InfinitePlace E =>
          ∑ i, ‖(algebraMap E (InfiniteAdeleRing E) (Module.finBasis F E i)) w‖) (fun _ _ => by positivity) (Finset.mem_univ w)

theorem bound {s : ℝ} (hs : 1 < s) {U : Set (Fin (Module.finrank F E) → Af F)} (hU : IsCompact U) :
    ∃ (N k : ℕ) (L : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (C : ℝ), 2 * s + 2 < k ∧ ∀ l : (AE F E)ˣ,
      GlobalTheory.XTermMaj.maj F E N U (l : AE F E) * ENNReal.ofReal ((absE F E l : ℝ) ^ s) ≤
        ENNReal.ofReal (C * (infiniteZetaBound s k (IdeleGroup.toInfinite E (idl F E l)) *
          finiteZetaBound L s (IdeleGroup.toFinite E (idl F E l)))) := by
  classical
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 2 * s + 2 < k := exists_nat_gt _
  obtain ⟨L, hL⟩ := exists_subset_idealFiniteAdeles (hU.image (continuous_gfin F E))
  set r := Fintype.card (InfinitePlace E)
  have hB := bc_nonneg F E
  refine ⟨k * r, k, L, (1 + bc F E) ^ (k * r), hk, fun l => ?_⟩
  set S := ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖ with hSdef
  have hS : 0 ≤ S := by positivity
  by_cases hU' : (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∈ U
  · rw [GlobalTheory.XTermMaj.maj, Set.indicator_of_mem hU', ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    set y : AdeleRing (𝓞 E) E := tens F E (l : AE F E) with hy
    have hfin : y.2 ∈ idealFiniteAdeles L := by
      rw [snd_eq F E]
      apply hL
      refine ⟨_, hU', ?_⟩
      simp only [hy, crd_eq]
    have hfz : finiteZetaBound L s (IdeleGroup.toFinite E (idl F E l)) =
        finiteModule (ofFinite (IdeleGroup.toFinite E (idl F E l))) ^ s := by
      rw [finiteZetaBound, if_pos]
      exact hfin
    rw [hfz, absE_eq, ideleModule_rpow_eq]
    set fm := finiteModule (ofFinite (IdeleGroup.toFinite E (idl F E l))) ^ s
    have hfm : 0 ≤ fm := Real.rpow_nonneg (finiteModule_pos _).le _
    set a : InfiniteAdeleRing E := ((IdeleGroup.toInfinite E (idl F E l) : (InfiniteAdeleRing E)ˣ) : InfiniteAdeleRing E)
    have ha : ∀ w, 1 + ‖a w‖ ≤ (1 + bc F E) * (1 + S) := fun w => by
      have h1 := norm_fst_le F E (l : AE F E) y hy w
      have e : a w = infPart y w := rfl
      rw [e]
      nlinarith
    have key : (1 + S) ^ (-((k * r : ℕ) : ℝ)) * ∏ w, ‖a w‖ ^ ((w.mult : ℝ) * s) ≤
        (1 + bc F E) ^ (k * r) * ∏ w, ‖a w‖ ^ ((w.mult : ℝ) * s) / (1 + ‖a w‖) ^ k := by
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
      have e1 : (1 + S) ^ (k * r) = ∏ _w : InfinitePlace E, (1 + S) ^ k := by
        rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
      have e2 : (1 + bc F E) ^ (k * r) = ∏ _w : InfinitePlace E, (1 + bc F E) ^ k := by
        rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
      rw [e1, e2, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod₀ (fun w _ => by positivity) (fun w _ => ?_)
      have h2 : (1 + ‖a w‖) ^ k ≤ (1 + bc F E) ^ k * (1 + S) ^ k := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (ha w) k
      have hP : 0 ≤ ‖a w‖ ^ ((w.mult : ℝ) * s) := by positivity
      have h1S : 0 < (1 + S) ^ k := by positivity
      have h1a : 0 < (1 + ‖a w‖) ^ k := by positivity
      rw [mul_div_assoc', le_div_iff₀ h1a]
      calc ((1 + S) ^ k)⁻¹ * ‖a w‖ ^ ((w.mult : ℝ) * s) * (1 + ‖a w‖) ^ k
          ≤ ((1 + S) ^ k)⁻¹ * ‖a w‖ ^ ((w.mult : ℝ) * s) * ((1 + bc F E) ^ k * (1 + S) ^ k) := by gcongr
        _ = (1 + bc F E) ^ k * ‖a w‖ ^ ((w.mult : ℝ) * s) := by field_simp
    calc (1 + S) ^ (-((k * r : ℕ) : ℝ)) * ((∏ w, ‖a w‖ ^ ((w.mult : ℝ) * s)) * fm)
        = ((1 + S) ^ (-((k * r : ℕ) : ℝ)) * ∏ w, ‖a w‖ ^ ((w.mult : ℝ) * s)) * fm := by ring
      _ ≤ ((1 + bc F E) ^ (k * r) * ∏ w, ‖a w‖ ^ ((w.mult : ℝ) * s) / (1 + ‖a w‖) ^ k) * fm :=
          mul_le_mul_of_nonneg_right key hfm
      _ = _ := by rw [infiniteZetaBound]; ring
  · rw [GlobalTheory.XTermMaj.maj, Set.indicator_of_notMem hU', zero_mul]
    exact zero_le

theorem lintegral_bound_lt_top (ν : Measure (AE F E)ˣ) [ν.IsHaarMeasure] {s : ℝ} (hs : 1 < s) {k : ℕ}
    (hk : 2 * s + 2 < k) (L : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (C : ℝ) :
    ∫⁻ l, ENNReal.ofReal (C * (infiniteZetaBound s k (IdeleGroup.toInfinite E (idl F E l)) *
      finiteZetaBound L s (IdeleGroup.toFinite E (idl F E l)))) ∂ν < ⊤ := by
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  set G : IdeleGroup E → ENNReal := fun x => ENNReal.ofReal (C * (infiniteZetaBound s k
    (IdeleGroup.toInfinite E x) * finiteZetaBound L s (IdeleGroup.toFinite E x))) with hG
  have hm : ∫⁻ l, G (idl F E l) ∂ν = ∫⁻ x, G x ∂(ν.map (idl F E)) :=
    (lintegral_map_equiv G (idl F E).toHomeomorph.toMeasurableEquiv (μ := ν)).symm
  rw [hm]
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : (ν.map (idl F E)).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map ν (idl F E)
  rw [Measure.isMulLeftInvariant_eq_smul (ν.map (idl F E)) (ideleMeasure E), lintegral_smul_measure]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (((integrable_zetaBound hs hk L).const_mul C).lintegral_lt_top)

end GlobalTheory.TateConv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorModuliWithSymplecticLevelRepresentab
noncomputable section

namespace GlobalTheory.UPel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

variable {F : Type} [Field F] [NumberField F] [IsCMField F]

def IsLevelStructureOfLevel {D : Datum F} {p N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp (D.OEp p)} (o : Obj D p N s) (N₁ : ℕ)
    (α : D.La → (𝟙_ (Over S) ⟶ o.A)) : Prop :=
  (∀ a c, α (a + c) = α a * α c) ∧ (∀ a, α (N₁ • a) = 1) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S),
      (∀ a, toUnit (Over.mk x) ≫ α a = 1 ↔ ∃ b, a = N₁ • b) ∧
      (∀ g : Over.mk x ⟶ o.A, g ^ N₁ = 1 → ∃ a, toUnit _ ≫ α a = g) ∧
      ∃ z : kˣ, IsPrimitiveRoot z N₁ ∧
        ∀ a b, Out.WeilIs o.A o.PP.L N₁ (toUnit (Over.mk x) ≫ α a) (toUnit _ ≫ α b) (unitOn (z ^ D.EF a b))

def LevelStructurePullback {D : Datum F} {p N : ℕ} {S S' : Scheme.{0}} {s : S ⟶ Sp (D.OEp p)} {s' : S' ⟶ Sp (D.OEp p)}
    {o' : Obj D p N s'} {o : Obj D p N s} {f : S' ⟶ S} (m : ObjMap o' o f) (α' : D.La → (𝟙_ (Over S') ⟶ o'.A))
    (α : D.La → (𝟙_ (Over S) ⟶ o.A)) : Prop :=
  ∀ a, (α' a).left ≫ m.φ = f ≫ (α a).left

def HasLevelStructureOfLevel {D : Datum F} {p N : ℕ} {X₁ : Scheme.{0}} {s₁ : X₁ ⟶ Sp (D.OEp p)} (o₁ : Obj D p N s₁) (N₁ : ℕ)
    (α₁ : D.La → (𝟙_ (Over X₁) ⟶ o₁.A)) : Prop :=
  ∀ (S : Scheme.{0}) (s : S ⟶ Sp (D.OEp p)) (o : Obj D p N s) (α : D.La → (𝟙_ (Over S) ⟶ o.A)), IsLevelStructureOfLevel o N₁ α →
    ∃! f : S ⟶ X₁, f ≫ s₁ = s ∧ ∃ m : ObjMap o o₁ f, LevelStructurePullback m α α₁

end GlobalTheory.UPel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitCompactModCentralizerSeparableLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitCompactModCentralizerSeparableLocal
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.OrbitCptW

theorem orbit_cpt_w : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (N : GLw n w), N.val.charpoly.Separable → ∀ C : Set (GLw n w), IsCompact C → ∃ D : Set (GLw n w), IsCompact D ∧ ∀ x : GLw n w, x⁻¹ * N * x ∈ C → ∃ z : GLw n w, z * N = N * z ∧ ∃ d ∈ D, x = z * d := by
  intro E _ _ _ _ n w N hN C hC
  letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
  obtain ⟨C', hC', hC'g⟩ := GlobalTheory.OrbCpt.gl_orbit_cpt (k := w.adicCompletion E) N.val hN
    ((fun y : GLw n w => (y : Matrix (Fin n) (Fin n) (w.adicCompletion E))) '' C)
    (hC.image Units.continuous_val)
  refine ⟨(fun y => y⁻¹) '' C', hC'.image continuous_inv, fun x hx => ?_⟩
  obtain ⟨c, hc, t, ht, hxt⟩ := hC'g x⁻¹ ⟨_, hx, by simp [mul_assoc]⟩
  refine ⟨t⁻¹, ?_, c⁻¹, ⟨c, hc, rfl⟩, ?_⟩
  · have h1 : t * N = N * t := Units.ext ht
    calc t⁻¹ * N = t⁻¹ * (N * t) * t⁻¹ := by group
      _ = t⁻¹ * (t * N) * t⁻¹ := by rw [h1]
      _ = N * t⁻¹ := by group
  · rw [← _root_.mul_inv_rev, ← hxt, inv_inv]

end GlobalTheory.OrbitCptW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitCompactModCentralizerSeparableLocalStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_compact_mod_centralizer_separable_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (N : GLw n w), N.val.charpoly.Separable → ∀ C : Set (GLw n w), IsCompact C → ∃ D : Set (GLw n w), IsCompact D ∧ ∀ x : GLw n w, x⁻¹ * N * x ∈ C → ∃ z : GLw n w, z * N = N * z ∧ ∃ d ∈ D, x = z * d := by
  first | exact @GlobalTheory.OrbitCptW.orbit_cpt_w | exact GlobalTheory.OrbitCptW.orbit_cpt_w | (intros; apply GlobalTheory.OrbitCptW.orbit_cpt_w <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMapExists
open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpFrame.LevelMap

variable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ}

theorem grpA_mul (O : Type) [CommRing O] (lam : ι → ℕ → ℕ) (g h : ι → GL (Fin N) O) :
    grpA O N lam (g * h) = grpA O N lam g * grpA O N lam h := by
  apply Subtype.ext
  show grp O N lam (g * h) = grp O N lam g * grp O N lam h
  unfold grp
  exact map_mul _ g h

theorem grpA_one (O : Type) [CommRing O] (lam : ι → ℕ → ℕ) :
    grpA O N lam 1 = 1 := by
  apply Subtype.ext
  show grp O N lam 1 = 1
  unfold grp
  exact map_one _

def jK (F : Frame l ι N) (lam : ι → ℕ → ℕ) : F.K →* alg F.O N lam where
  toFun κ := (F.chi κ : F.O) • grpA F.O N lam (F.kap κ)
  map_one' := by simp [grpA_one]
  map_mul' a b := by
    rw [map_mul, map_mul, grpA_mul, Units.val_mul, smul_mul_smul_comm]

end GlobalTheory.ExpFrame.LevelMap

theorem GlobalTheory.ExpFrame.levelMap_exists : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ), ∃ (jK : F.K →* alg F.O N lam), F.IsJ lam jK := by
  intro l _ ι _ _ N F lam
  exact ⟨GlobalTheory.ExpFrame.LevelMap.jK F lam, fun κ => rfl⟩

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreeLeOfColW
open NumberField IsDedekindDomain GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

set_option autoImplicit false

open MvPolynomial

namespace GlobalTheory.NablaFin

theorem totalDegree_le_of_colW {O : Type} [CommRing O] (N : ℕ) (ν : Fin N → ℕ)
    (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ weightedHomogeneousSubmodule O (Formalism.GradedWeylDivisibility.colW N N) ν) :
    f.totalDegree ≤ ∑ t, ν t := by
  rw [mem_weightedHomogeneousSubmodule] at hf
  unfold totalDegree
  refine Finset.sup_le fun s hs => ?_
  have hw := hf (mem_support_iff.1 hs)
  rw [← hw, Finsupp.weight_apply]
  refine le_of_eq ?_
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [Formalism.GradedWeylDivisibility.colW, Pi.single_apply]

theorem dualWeyl_finite (O : Type) [CommRing O] [IsNoetherianRing O] (N : ℕ) (ν : Fin N → ℕ) :
    Module.Finite O (Formalism.GradedWeylDivisibility.dualWeyl O N N ν) := by
  have hle : Formalism.GradedWeylDivisibility.dualWeyl O N N ν ≤ restrictTotalDegree (Fin N × Fin N) O (∑ t, ν t) := by
    intro f hf
    rw [mem_restrictTotalDegree]
    exact totalDegree_le_of_colW N ν f (by unfold Formalism.GradedWeylDivisibility.dualWeyl at hf; exact hf.1)
  haveI : IsNoetherian O (Formalism.GradedWeylDivisibility.dualWeyl O N N ν) := isNoetherian_of_le hle
  infer_instance

theorem nablaT_finite : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (N : ℕ) (ι : Type) [Fintype ι]
    (lam : ι → ℕ → ℕ), Module.Finite O (NablaT O N lam) := by
  intro O _ _ N ι _ lam
  haveI : ∀ τ, Module.Finite O (Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ))) := fun τ => dualWeyl_finite O N _
  exact PiTensorProduct.finite

end GlobalTheory.NablaFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexProd
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.BCT.LevOpTmul

theorem finite_supp {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K : Subgroup G}
    (hK : IsOpen (K : Set G)) {f : G → ℂ} (hf : HasCompactSupport f) : {q : G ⧸ K | f q.out ≠ 0}.Finite := by
  have hc : IsCompact (tsupport f) := hf
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun x : G => (fun y : G => x⁻¹ * y) ⁻¹' (K : Set G))
    (fun x => hK.preimage (continuous_const.mul continuous_id))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp [K.one_mem]⟩)
  refine (t.finite_toSet.image (fun x : G => (x : G ⧸ K))).subset ?_
  intro q hq
  have hmem : q.out ∈ tsupport f := subset_tsupport f hq
  obtain ⟨x, hx, hqx⟩ := Set.mem_iUnion₂.1 (ht hmem)
  refine ⟨x, hx, ?_⟩
  conv_rhs => rw [← QuotientGroup.out_eq' q]
  exact QuotientGroup.eq.2 hqx

theorem levOp_apply {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K K₁ : Subgroup G) (f : G → ℂ) (A : V →ₗ[ℂ] V) (S : Finset (G ⧸ K₁)) (hS : ∀ q : G ⧸ K₁, f q.out ≠ 0 → q ∈ S)
    (v : V) : levOp ρ K K₁ f A v = ((K₁.relIndex K : ℕ) : ℂ)⁻¹ • ∑ q ∈ S, f q.out • ρ q.out (A v) := by
  unfold levOp
  rw [finsum_eq_sum_of_support_subset (s := S)]
  · simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply]
  · intro q hq
    rw [Function.mem_support] at hq
    apply hS
    intro h0
    apply hq
    rw [h0, zero_smul]

theorem term_mk {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K₁ : Subgroup G) (f : G → ℂ) (hf : ∀ k ∈ K₁, ∀ x, f (x * k) = f x) (w : V) (hw : ∀ k ∈ K₁, ρ k w = w) (g : G) :
    f (g : G ⧸ K₁).out = f g ∧ ρ (g : G ⧸ K₁).out w = ρ g w := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K₁ g
  rw [hk]
  exact ⟨hf k k.2 g, by rw [map_mul, Module.End.mul_apply, hw k k.2]⟩

end GlobalTheory.BCT.LevOpTmul
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesOnOpenRestrictAffineOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesOnOpenRestrictAffineOpen
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

theorem isEtCoord_res : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (U W : X.Opens) (h : W ≤ U) (d : ℕ) (t : Fin d → Γ(X, U)), IsAffineOpen U → IsAffineOpen W → IsEtCoord f U t → IsEtCoord f W (fun a => resG X h (t a)) := by
  intro R _ X f U W h d t hU hW ht
  have h1 : (resG X h).Etale := GlobalTheory.TopForm.etale_resG hU hW h
  have h2 : ((resG X h).comp (MvPolynomial.eval₂Hom (cstOn f U) t)).Etale :=
    RingHom.Etale.stableUnderComposition _ _ ht h1
  have h3 : MvPolynomial.eval₂Hom (cstOn f W) (fun a => resG X h (t a)) =
      (resG X h).comp (MvPolynomial.eval₂Hom (cstOn f U) t) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      have hc : cstOn f W = (resG X h).comp (cstOn f U) := by
        unfold cstOn resG
        rw [← CommRingCat.hom_comp]
        have e := Scheme.Hom.appLE_map f (U := ⊤) (V := U) (by simp) (homOfLE h).op
        exact congrArg (fun g => ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g).hom) e.symm
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, hc]
    · intro i
      simp
  unfold IsEtCoord
  rw [h3]
  exact h2

end GlobalTheory.LogPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesOnOpenRestrictAffineOpenStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEtaleCoordinatesOnOpen_restrict_affineOpen : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (U W : X.Opens) (h : W ≤ U) (d : ℕ) (t : Fin d → Γ(X, U)), IsAffineOpen U → IsAffineOpen W → IsEtCoord f U t → IsEtCoord f W (fun a => resG X h (t a)) := by
  first | exact @GlobalTheory.LogPair.isEtCoord_res | exact GlobalTheory.LogPair.isEtCoord_res | (intros; apply GlobalTheory.LogPair.isEtCoord_res <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidLineBundleIsoDescentAlongGaloisCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidLineBundleIsoDescentAlongGaloisCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GaloisLBDescent

theorem lbIso_of_galoisCover : ∀ (S S₁ Y : Scheme.{0}) (π₁ : S₁ ⟶ S) (Ga : Type) [Group Ga] (ρ₁ : Ga → (S₁ ⟶ S₁)) (f : S ⟶ Y) (A' : Over S₁) (A : Over S) (B : Over Y) [GrpObj A'] [GrpObj A] [IsCommMonObj A] [GrpObj B] (φ₁ : A'.left ⟶ A.left) (φ : A.left ⟶ B.left) (PA : RigLB A) (PB : RigLB B) (L' : LB A'.left), IsAbelianScheme A → GlobalTheory.ZM.IsGaloisCover Ga ρ₁ π₁ → IsGrpPullback A' A π₁ φ₁ → IsGrpPullback A B f φ → L'.IsLB → LBIso L' (PA.L.pull φ₁) → LBIso L' (PB.L.pull (φ₁ ≫ φ)) → LBIso PA.L (PB.L.pull φ) := by
  intro S S₁ Y π₁ Ga _ ρ₁ f A' A B _ _ _ _ φ₁ φ PA PB L' hA hG h₁ h hL' i₁ i₂
  have := hG.fin
  have := hG.etale
  have := hG.onto
  have hPA := PA.isLB
  have h₂ := pull_isLB PB.isLB φ
  have hN := LB.isLB_div h₂ hPA
  have cN : CechPic.cls _ hN = CechPic.pull φ (CechPic.cls _ PB.isLB) - CechPic.cls _ hPA :=
    CechPic.cls_div h₂ hPA hN
  have zA : CechPic.pull (eSec A) (CechPic.cls _ PA.isLB) = 0 :=
    (CechPic.cls_eq_zero_iff (pull_isLB PA.isLB _)).2 ⟨_, PA.rigGen⟩
  have zB : CechPic.pull (eSec B) (CechPic.cls _ PB.isLB) = 0 :=
    (CechPic.cls_eq_zero_iff (pull_isLB PB.isLB _)).2 ⟨_, PB.rigGen⟩
  have c₁ : CechPic.cls _ hL' = CechPic.pull φ₁ (CechPic.cls _ PA.isLB) :=
    (CechPic.cls_eq_iff hL' (pull_isLB PA.isLB _)).2 i₁
  have c₂ : CechPic.cls _ hL' = CechPic.pull (φ₁ ≫ φ) (CechPic.cls _ PB.isLB) :=
    (CechPic.cls_eq_iff hL' (pull_isLB PB.isLB _)).2 i₂
  refine GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange GlobalTheory.SemiRigid.globalFns S S₁ π₁ A _ hA hN
    inferInstance inferInstance inferInstance ((CechPic.cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
    ((CechPic.cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
  · have he : eSec A ≫ φ = f ≫ eSec B := GlobalTheory.PolBaseChange.eSec_comm h
    rw [CechPic.cls_pull hN, cN, map_sub, ← CechPic.pull_comp, zA, he, CechPic.pull_comp, zB, map_zero,
      sub_zero]
  · rw [CechPic.cls_pull hN, cN, ← h₁.1.isoPullback_inv_fst, CechPic.pull_comp, map_sub,
      ← CechPic.pull_comp φ₁ φ, ← c₁, ← c₂, sub_self, map_zero]

end GlobalTheory.GaloisLBDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidLineBundleIsoDescentAlongGaloisCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidLineBundleIso_descent_along_galoisCover : ∀ (S S₁ Y : Scheme.{0}) (π₁ : S₁ ⟶ S) (Ga : Type) [Group Ga] (ρ₁ : Ga → (S₁ ⟶ S₁)) (f : S ⟶ Y) (A' : Over S₁) (A : Over S) (B : Over Y) [GrpObj A'] [GrpObj A] [IsCommMonObj A] [GrpObj B] (φ₁ : A'.left ⟶ A.left) (φ : A.left ⟶ B.left) (PA : RigLB A) (PB : RigLB B) (L' : LB A'.left), IsAbelianScheme A → GlobalTheory.ZM.IsGaloisCover Ga ρ₁ π₁ → IsGrpPullback A' A π₁ φ₁ → IsGrpPullback A B f φ → L'.IsLB → LBIso L' (PA.L.pull φ₁) → LBIso L' (PB.L.pull (φ₁ ≫ φ)) → LBIso PA.L (PB.L.pull φ) := by
  first | exact @GlobalTheory.GaloisLBDescent.lbIso_of_galoisCover | exact GlobalTheory.GaloisLBDescent.lbIso_of_galoisCover | (intros; apply GlobalTheory.GaloisLBDescent.lbIso_of_galoisCover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnitaryCountableDiscrete
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom

namespace GlobalTheory.RatUDisc

theorem countable_ratU (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) : Countable (ratU σ J) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  haveI : Countable (GL (Fin n) E) := Units.val_injective.countable
  refine Function.Injective.countable (f := fun x : ratU σ J =>
    (Classical.choose (Subgroup.mem_subgroupOf.1 x.2) : GL (Fin n) E)) ?_
  intro x y h
  have hx := Classical.choose_spec (Subgroup.mem_subgroupOf.1 x.2)
  have hy := Classical.choose_spec (Subgroup.mem_subgroupOf.1 y.2)
  apply Subtype.ext; apply Subtype.ext
  rw [← hx, ← hy]
  exact congrArg _ h

theorem discrete_ratU (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) : DiscreteTopology (ratU σ J) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := F) (E := E)
  obtain ⟨U, hU, h⟩ := GlobalTheory.RationalDiscrete.exists_nhds_zero_inclR (F := F) (E := E)
  refine discreteTopology_of_isOpen_singleton_one ?_
  let f : ratU σ J → Matrix (Fin n) (Fin n) (AF F ⊗[F] E) :=
    fun g => ((g.1.1 : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) - 1
  have hf : Continuous f :=
    (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).sub
      continuous_const
  have hf1 : f 1 = 0 := sub_self _
  rw [isOpen_singleton_iff_nhds_eq_pure]
  refine le_antisymm (fun s hs => Filter.mem_of_superset (x := {1}) ?_ (Set.singleton_subset_iff.2 hs)) (pure_le_nhds _)
  have hW : (⋂ i, ⋂ j, (fun g => f g i j) ⁻¹' U) ∈ 𝓝 (1 : ratU σ J) :=
    Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j =>
      (hf.matrix_elem i j).continuousAt.preimage_mem_nhds (by
        show U ∈ 𝓝 (f 1 i j)
        rw [hf1]; exact hU)
  refine Filter.mem_of_superset hW fun g hg => ?_
  obtain ⟨γ, hγ⟩ := Subgroup.mem_subgroupOf.1 g.2
  have hfg : ∀ i j, f g i j =
      inclR (F := F) (AF F) (((γ : Matrix (Fin n) (Fin n) E) - 1 : Matrix (Fin n) (Fin n) E) i j) := by
    intro i j
    show (((g.1.1 : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) - 1) i j = _
    rw [← hγ, Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.one_apply, Matrix.one_apply,
      apply_ite (inclR (F := F) (AF F)), map_one, map_zero]
    rfl
  have hγ1 : γ = 1 := by
    refine Units.ext (sub_eq_zero.1 (Matrix.ext fun i j => h _ ?_))
    rw [Units.val_one, ← hfg]
    exact Set.mem_iInter.1 (Set.mem_iInter.1 hg i) j
  refine Subtype.ext (Subtype.ext ?_)
  rw [← hγ, hγ1, map_one]
  rfl

theorem countable_discrete_ratU : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), Countable (ratU σ J) ∧ DiscreteTopology (ratU σ J) :=
  fun F E _ _ _ _ _ σ n J => ⟨countable_ratU F E σ n J, discrete_ratU F E σ n J⟩

end GlobalTheory.RatUDisc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareIntegrableSmoothSubmoduleGL
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep.CuspidalL2GL
open scoped InnerProductSpace

namespace GlobalTheory.SqIntGL

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

variable (μ : Measure (GA E a)) [μ.IsHaarMeasure]

theorem memL2_iff_std {f : GA E a → ℂ} : MemL2Quotient (latticeGL E a) μ f ↔
    LeftInv (latticeGL E a) f ∧ MemLp f 2 (μ.restrict (stdDom (latticeGL E a))) :=
  memL2_iff_fundamental_domain (isFundamentalDomain_stdDom _ μ)

def squareIntegrableSmoothSubmoduleGL : Submodule ℂ (Sm E a) where
  carrier := {ψ | MemL2Quotient (latticeGL E a) μ ψ.1}
  zero_mem' := (memL2_iff_std μ).2 ⟨fun _ _ _ => rfl, MemLp.zero⟩
  add_mem' {x y} hx hy := by
    rw [Set.mem_setOf_eq, memL2_iff_std] at hx hy ⊢
    exact ⟨fun γ hγ g => by simp [hx.1 γ hγ g, hy.1 γ hγ g], hx.2.add hy.2⟩
  smul_mem' c x hx := by
    rw [Set.mem_setOf_eq, memL2_iff_std] at hx ⊢
    exact ⟨fun γ hγ g => by simp [hx.1 γ hγ g], hx.2.const_smul c⟩

theorem mem_l2Sub {ψ : Sm E a} : ψ ∈ squareIntegrableSmoothSubmoduleGL μ ↔ MemL2Quotient (latticeGL E a) μ ψ.1 := Iff.rfl

def l2Map : Sm E a →ₗ[ℂ] L2 (latticeGL E a) μ :=
  toL2ₗ μ (squareIntegrableSmoothSubmoduleGL μ) (fun _ h => (mem_l2Sub μ).1 h) ∘ₗ
    Submodule.linearProjOfIsCompl (squareIntegrableSmoothSubmoduleGL μ) _ (Classical.choose_spec (Submodule.exists_isCompl (squareIntegrableSmoothSubmoduleGL μ)))

theorem l2Map_apply {ψ : Sm E a} (h : ψ ∈ squareIntegrableSmoothSubmoduleGL μ) : l2Map μ ψ = ((mem_l2Sub μ).1 h).toL2 := by
  unfold l2Map
  rw [LinearMap.comp_apply]
  have e := Submodule.linearProjOfIsCompl_apply_left (Classical.choose_spec (Submodule.exists_isCompl (squareIntegrableSmoothSubmoduleGL μ))) ⟨ψ, h⟩
  erw [e]
  rfl

def l2Form : Sm E a →ₗ⋆[ℂ] Sm E a →ₗ[ℂ] ℂ := ((innerₛₗ ℂ).comp (l2Map μ)).compl₂ (l2Map μ)

theorem l2Form_apply {x y : Sm E a} (hx : x ∈ squareIntegrableSmoothSubmoduleGL μ) (hy : y ∈ squareIntegrableSmoothSubmoduleGL μ) :
    l2Form μ x y = ⟪((mem_l2Sub μ).1 hx).toL2, ((mem_l2Sub μ).1 hy).toL2⟫_ℂ := by
  simp only [l2Form, LinearMap.compl₂_apply, LinearMap.comp_apply, l2Map_apply μ hx, l2Map_apply μ hy]
  rfl

theorem re_l2Form_pos {x : Sm E a} (hx : x ∈ squareIntegrableSmoothSubmoduleGL μ) (hc : Continuous x.1) (h0 : x ≠ 0) : 0 < (l2Form μ x x).re := by
  rw [l2Form_apply μ hx hx]
  have : ((mem_l2Sub μ).1 hx).toL2 ≠ 0 := toL2_ne_zero _ hc fun e => h0 (Subtype.ext e)
  first
    | exact (re_inner_self_pos (𝕜 := ℂ)).2 this
    | exact inner_self_pos.2 this
    | exact (RCLike.inner_self_pos).2 this
    | (rw [inner_self_eq_norm_sq_to_K]; norm_cast; simpa using this)

theorem mem_l2Sub_of_isAutForm {ψ : Sm E a} (h : IsAutForm ψ) (h' : IsSqInt ψ.1) : ψ ∈ squareIntegrableSmoothSubmoduleGL μ :=
  memL2_of_isAutForm h h'

end GlobalTheory.SqIntGL

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasInfCharGL
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ResW.IrrInfChar

theorem cap_commute_act' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (τ : E →+* ℂ) (u : ℂ)
    (o : Op E a) : Commute (cap (a := a) τ u) (act o) := by
  cases o with
  | fin k => exact commute_cap_finRep τ u k
  | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
  | lie X => exact commute_cap_lie τ u X

theorem exists_scalar {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {V : Submodule ℂ (Sm E a)}
    (hV : IsDiscrete V) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a)
    (hc : ∀ o : Op E a, Commute z (act o)) : ∃ c : ℂ, ∀ φ ∈ V, z φ = c • φ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  set U := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) with hU
  have hfin : FiniteDimensional ℂ U := (hV.aut φ hφ).zfin
  have hle : U ≤ V := Submodule.span_le.2 (by
    rintro _ ⟨y, hy, rfl⟩
    exact Zalg_stable (fun X => hV.stable (.lie X)) hy φ hφ)
  have hst : ∀ x ∈ U, z x ∈ U := fun x hx => by
    have : U ≤ U.comap z := Submodule.span_le.2 (by
      rintro _ ⟨y, hy, rfl⟩
      exact Submodule.subset_span ⟨z * y, mul_mem hz hy, rfl⟩)
    exact this hx
  have hφU : φ ∈ U := Submodule.subset_span ⟨1, one_mem _, rfl⟩
  have : Nontrivial U := ⟨⟨φ, hφU⟩, 0, fun h => h0 (congrArg Subtype.val h)⟩
  obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue (z.restrict hst)
  obtain ⟨v, hv⟩ := hc'.exists_hasEigenvector
  have hv1 : z v.1 = c • v.1 := congrArg Subtype.val hv.apply_eq_smul
  refine ⟨c, fun ψ hψ => ?_⟩
  rcases hV.irred (V ⊓ z.eigenspace c) inf_le_left (fun o x hx => ⟨hV.stable o x hx.1, by
    have h1 : z x = c • x := Module.End.mem_eigenspace_iff.1 hx.2
    refine Module.End.mem_eigenspace_iff.2 ?_
    rw [← map_smul, ← h1]
    exact LinearMap.congr_fun (hc o).eq x⟩) with h | h
  · have : v.1 ∈ V ⊓ z.eigenspace c := ⟨hle v.2, Module.End.mem_eigenspace_iff.2 hv1⟩
    rw [h] at this
    exact absurd (Subtype.ext ((Submodule.mem_bot ℂ).1 this)) hv.2
  · rw [← h] at hψ
    exact Module.End.mem_eigenspace_iff.1 hψ.2

theorem exists_hasInfCharGL {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}
    {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) (τ : E →+* ℂ) : ∃ μ, HasInfCharGL V τ μ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ h0
  obtain ⟨m, hm, h⟩ := exists_multiset_qdet (Eop (a := N) τ) (((N : ℂ) - 1) / 2) φ f hf
  refine ⟨m, hm, fun u ψ hψ => ?_⟩
  obtain ⟨c, h1⟩ := exists_scalar hV (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩)
    (fun o => cap_commute_act' τ u o)
  have h2 : f (cap τ u φ) = _ := h u
  rw [h1 φ hφ, map_smul, hf, smul_eq_mul, mul_one] at h2
  rw [h1 ψ hψ, h2]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (τ : E →+* ℂ), (∀ x : CuspSub E N, ∃ μ, x.HasInfChar τ μ) ∧ ∀ (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∃ μ, HasInfCharGL V τ μ := by
  intro E _ _ _ N τ
  refine ⟨fun x => ⟨(CG.mk x).infChar τ, ?_⟩, fun V hV => exists_hasInfCharGL hV τ⟩
  exact hasInfChar_infChar_of_commute E N (fun τ u o => cap_commute_act' τ u o) (CG.mk x) τ

end GlobalTheory.ResW.IrrInfChar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralBlock
set_option autoImplicit false

noncomputable section

open NumberField PowerSeries Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
open Neutral.B1 hiding G
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.ExpFrame Formalism.CohomologicalDescent.FrobeniusPeriodChange

namespace GlobalTheory.WachBlock

section Galois

variable (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]

def ofOL (LL : FinExt l) : ↥(OL LL) →+* PadicAlgCl l :=
  (LL.1.val.toRingHom).comp ((OL LL).val.toRingHom)

def IntegralBlock (n t : ℕ) (J : (E →+* PadicAlgCl l) → Fin n → ℤ) (bot : (E →+* PadicAlgCl l) → ℤ) : Prop :=
  ∃ (LL : FinExt l) (r : G E Ω →* GL (Fin n) ↥(OL LL)) (ψ : Fin t → G E Ω →* (↥(OL LL))ˣ) (ϖ : ↥(OL LL))
    (R : ℕ) (M : Fin (R + 1) → Submodule ↥(OL LL) (Fin n → ↥(OL LL))) (rs : Fin t → Fin R),
    (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) ∧ (∀ (τ : E →+* PadicAlgCl l) (x : E), τ x ∈ LL.1) ∧
    CrysWith ((Matrix.GeneralLinearGroup.map (ofOL l LL)).comp r) (fun τ => Finset.univ.val.map (J τ)) ∧
    (∀ s, CrysWith (GlobalTheory.TripleGal.rk1 ((Units.map (ofOL l LL).toMonoidHom).comp (ψ s)))
      fun τ => {bot τ + ((s : ℕ) : ℤ)}) ∧
    Irreducible ϖ ∧ (∀ x, x ∈ M 0 ↔ ∃ y : Fin n → ↥(OL LL), x = fun a => ϖ * y a) ∧ M (Fin.last R) = ⊤ ∧ Monotone M ∧
    (∀ g k x, x ∈ M k → (r g : Matrix (Fin n) (Fin n) ↥(OL LL)).mulVec x ∈ M k) ∧
    Function.Injective rs ∧
    ∀ s, ∃ x ∈ M (rs s).succ, x ∉ M (rs s).castSucc ∧
      M (rs s).succ = M (rs s).castSucc ⊔ Submodule.span ↥(OL LL) {x} ∧
      ∀ g, (r g : Matrix (Fin n) (Fin n) ↥(OL LL)).mulVec x - (fun a => ((ψ s g : (↥(OL LL))ˣ) : ↥(OL LL)) * x a) ∈
        M (rs s).castSucc

end Galois

section Reduced

variable {F : Type} [Field F] {n : ℕ}

def lau (y : Fin n → F⟦X⟧) : Fin n → LaurentSeries F := fun a => ((y a : F⟦X⟧) : LaurentSeries F)

def phiV (l : ℕ) (P : Matrix (Fin n) (Fin n) F⟦X⟧) (y : Fin n → F⟦X⟧) : Fin n → F⟦X⟧ :=
  P.mulVec fun a => frob0 l (y a)

def gamV (un : F⟦X⟧) (D : Matrix (Fin n) (Fin n) F⟦X⟧) (y : Fin n → F⟦X⟧) : Fin n → F⟦X⟧ :=
  (1 + (X : F⟦X⟧) • D).mulVec fun a => gam0 0 un (y a)

def RedFilt {ι : Type} (σ : Equiv.Perm ι) (l : ℕ) {t : ℕ} (un : F⟦X⟧) (P D : ι → Matrix (Fin n) (Fin n) F⟦X⟧)
    (Pψ Dψ : Fin t → ι → F⟦X⟧) : Prop :=
  ∃ (R : ℕ) (V : ι → Fin (R + 1) → Submodule (LaurentSeries F) (Fin n → LaurentSeries F)) (rs : Fin t → Fin R)
    (e : ι → Fin t → Fin n → F⟦X⟧) (m : ι → Fin t → ℤ),
    Function.Injective rs ∧
    (∀ i, V i 0 = ⊥ ∧ V i (Fin.last R) = ⊤ ∧ Monotone (V i)) ∧
    (∀ k i j, Module.finrank (LaurentSeries F) (V i k) = Module.finrank (LaurentSeries F) (V j k)) ∧
    (∀ i k y, lau y ∈ V (σ i) k → lau (phiV l (P i) y) ∈ V i k) ∧
    (∀ i k y, lau y ∈ V i k → lau (gamV un (D i) y) ∈ V i k) ∧
    (∀ i s, lau (e i s) ∉ V i (rs s).castSucc ∧
      V i (rs s).succ = V i (rs s).castSucc ⊔ Submodule.span (LaurentSeries F) {lau (e i s)}) ∧
    (∀ i s, (((X : F⟦X⟧) : LaurentSeries F) ^ m i s) • lau (phiV l (P i) (e (σ i) s)) -
        (((X : F⟦X⟧) : LaurentSeries F) ^ ((l : ℤ) * m (σ i) s) * ((Pψ s i : F⟦X⟧) : LaurentSeries F)) •
          lau (e i s) ∈ V i (rs s).castSucc) ∧
    ∀ i s, (((X : F⟦X⟧) : LaurentSeries F) ^ m i s) • lau (gamV un (D i) (e i s)) -
        (((gamSer 0 un : F⟦X⟧) : LaurentSeries F) ^ m i s *
          ((1 + X * Dψ s i : F⟦X⟧) : LaurentSeries F)) • lau (e i s) ∈ V i (rs s).castSucc

end Reduced

end GlobalTheory.WachBlock

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologySubsingletonOfCechPicardClassEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologySubsingletonOfCechPicardClassEq
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.Div

theorem coh_subsingleton_of_cls_eq : ∀ (X : Scheme.{0}) (M N : LB X) (hM : M.IsLB) (hN : N.IsLB),
    cls M hM = cls N hN → ∀ q : ℕ, Subsingleton (coh (LB.toMod M) q) →
      Subsingleton (coh (LB.toMod N) q) := by
  intro X M N hM hN e q h
  obtain ⟨i⟩ := nonempty_twist_iso_of_cls_eq (structureModule X) hM hN e
  exact (cohOn.mapIso Γ(X, ⊤) ⊤ q
    ((Twist.unitTwistIso M).symm ≪≫ i ≪≫ Twist.unitTwistIso N)).toEquiv.subsingleton_congr.1 h

end GlobalTheory.Div
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologySubsingletonOfCechPicardClassEqStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomology_subsingleton_of_cechPicardClass_eq : ∀ (X : Scheme.{0}) (M N : LB X) (hM : M.IsLB) (hN : N.IsLB), cls M hM = cls N hN → ∀ q : ℕ, Subsingleton (coh (LB.toMod M) q) → Subsingleton (coh (LB.toMod N) q) := by
  first | exact @GlobalTheory.Div.coh_subsingleton_of_cls_eq | exact GlobalTheory.Div.coh_subsingleton_of_cls_eq | (intros; apply GlobalTheory.Div.coh_subsingleton_of_cls_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecFockCore
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.VecFockCore
open GlobalTheory.AdTh.VecFock

open scoped ComplexOrder

theorem vec_fock_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T0), VStd D i → IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) ∧ (∀ τ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i (sg0 D A)) τ)) (R.vP i t)) ∧ (∀ τ, IsCartanInv (gramAt D (Wc D i) τ) (cart (R.MW i (sg0 D A)) τ)) ∧ (∀ τ, IsCartanInv (gramAt D (Vc D i) τ) 1) ∧ ∀ τ, IsONBasis (gramAt D (Wc D i) τ) (cart (R.MW i (sg0 D A)) τ) (onb (R.MW i (sg0 D A)) τ) ((Wc D i).sig (tauE D τ)).1 := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F h i t hV
  have hθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := h.thP.pt_theta i t 1
    unfold RealDat.ptP pureTensorO at this
    rwa [pureTensorL_one] at this
  refine ⟨hθ, GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ (fun _ => 1) _ _ _ _ _ _ _ _ _ _ (h.thP.vP i t) hθ,
    isCartanInv_cart _, fun τ => ?_, fun τ => isONBasis_onb _ τ _ (h.models.order i τ)⟩
  have : gramAt D (Vc D i) τ = 1 := by
    unfold gramAt
    rw [hV.1]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [this]
  exact ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩

end GlobalTheory.AdTh.VecFockCore
end
