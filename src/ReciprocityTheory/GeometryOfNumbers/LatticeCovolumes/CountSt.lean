module

public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily

@[expose] public section

section -- merged from ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountStC
section -- merged from ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountStB
namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module MeasureTheory Set
open scoped Classical ComplexOrder

section Crd

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

noncomputable def crd {r : ℕ} {v : Fin r → V} (hli : LinearIndependent K v) :
    V →ₗ[K] (Fin r → K) :=
  (Basis.span hli).equivFun.toLinearMap ∘ₗ
    (LinearMap.exists_leftInverse_of_injective (Submodule.span K (Set.range v)).subtype
      (Submodule.ker_subtype _)).choose

theorem crd_of_mem {r : ℕ} {v : Fin r → V} (hli : LinearIndependent K v) {x : V}
    (hx : x ∈ Submodule.span K (Set.range v)) :
    crd hli x = (Basis.span hli).equivFun ⟨x, hx⟩ := by
  unfold crd
  have h := (LinearMap.exists_leftInverse_of_injective (Submodule.span K (Set.range v)).subtype
      (Submodule.ker_subtype _)).choose_spec
  have h2 : (LinearMap.exists_leftInverse_of_injective (Submodule.span K (Set.range v)).subtype
      (Submodule.ker_subtype _)).choose x = ⟨x, hx⟩ := by
    have := congrArg (fun f => f ⟨x, hx⟩) h
    simpa using this
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, h2]

theorem sum_crd {r : ℕ} {v : Fin r → V} (hli : LinearIndependent K v) {x : V}
    (hx : x ∈ Submodule.span K (Set.range v)) : ∑ i, crd hli x i • v i = x := by
  rw [crd_of_mem hli hx]
  have h := (Basis.span hli).sum_equivFun ⟨x, hx⟩
  have h2 := congrArg Subtype.val h
  simp only [Submodule.coe_sum, Submodule.coe_smul, Basis.span_apply] at h2
  exact h2

theorem sum_mem_span {r : ℕ} (v : Fin r → V) (c : Fin r → K) :
    ∑ i, c i • v i ∈ Submodule.span K (Set.range v) := Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem crd_sum {r : ℕ} {v : Fin r → V} (hli : LinearIndependent K v) (c : Fin r → K) :
    crd hli (∑ i, c i • v i) = c := by
  rw [crd_of_mem hli (sum_mem_span v c)]
  have h : (⟨∑ i, c i • v i, sum_mem_span v c⟩ : Submodule.span K (Set.range v)) = ∑ i, c i • (Basis.span hli) i := by
    ext
    simp [Basis.span_apply]
  rw [h, Basis.equivFun_apply, Basis.repr_sum_self]

end Crd

section Lat

variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]

noncomputable def crdEmb {r : ℕ} {v : Fin r → V} (hli : LinearIndependent K v) :
    V →+ (Fin r → mixedEmbedding.mixedSpace K) where
  toFun x i := mixedEmbedding K (crd hli x i)
  map_zero' := by ext1 i; simp
  map_add' x y := by ext1 i; simp

theorem crdEmb_apply {r : ℕ} {v : Fin r → V} (hli : LinearIndependent K v) (x : V) (i : Fin r) :
    crdEmb hli x i = mixedEmbedding K (crd hli x i) := rfl

variable (K) in
noncomputable def latB (r : ℕ) :
    Basis (Σ _ : Fin r, Free.ChooseBasisIndex ℤ (𝓞 K)) ℝ (Fin r → mixedEmbedding.mixedSpace K) :=
  Pi.basis fun _ => mixedEmbedding.latticeBasis K

variable (K) in
noncomputable def lat0 (r : ℕ) : Submodule ℤ (Fin r → mixedEmbedding.mixedSpace K) :=
  Submodule.span ℤ (Set.range (latB K r))

theorem heckeAlgebra_mapsTo_localisationLatticeSpan {r : ℕ} {y : Fin r → mixedEmbedding.mixedSpace K} :
    y ∈ lat0 K r ↔ ∀ i, ∃ a : 𝓞 K, mixedEmbedding K (a : K) = y i := by
  rw [lat0, Basis.mem_span_iff_repr_mem ℤ (latB K r)]
  simp only [latB, Pi.basis_repr, Sigma.forall]
  refine forall_congr' fun i => ?_
  rw [← Basis.mem_span_iff_repr_mem ℤ (mixedEmbedding.latticeBasis K),
    mixedEmbedding.mem_span_latticeBasis]
  simp [LinearMap.mem_range]

end Lat

end ReciprocityTheory.GeometryOfNumbersTheory

namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module MeasureTheory Set
open scoped Classical ComplexOrder

variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

instance instMeasurableAddMixed : MeasurableAdd (mixedEmbedding.mixedSpace K) :=
  MeasurableAdd₂.toMeasurableAdd

instance instHaarPiMixed (r : ℕ) :
    (volume : Measure (Fin r → mixedEmbedding.mixedSpace K)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure _

instance instBorelPiMixed (r : ℕ) :
    @BorelSpace (Fin r → mixedEmbedding.mixedSpace K) _ MeasureSpace.toMeasurableSpace :=
  Pi.borelSpace

instance (r : ℕ) : DiscreteTopology (lat0 K r) := by unfold lat0; infer_instance

instance (r : ℕ) : IsZLattice ℝ (lat0 K r) := by unfold lat0; infer_instance

theorem sum_ooK_smul {r : ℕ} (v : Fin r → V) (c : Fin r → 𝓞 K) :
    ∑ i, ((c i : K)) • v i = ∑ i, c i • v i := Finset.sum_congr rfl fun i _ => algebraMap_smul K (c i) (v i)

theorem map_span_crdEmb {r : ℕ} {v : Fin r → V} (hli : LinearIndependent K v) :
    (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.map (crdEmb hli) =
      (lat0 K r).toAddSubgroup := by
  ext y
  simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, heckeAlgebra_mapsTo_localisationLatticeSpan]
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hx
    refine ⟨c i, ?_⟩
    rw [crdEmb_apply, ← sum_ooK_smul, crd_sum]
  · intro h
    choose a ha using h
    refine ⟨∑ i, ((a i : K)) • v i, ?_, ?_⟩
    · rw [sum_ooK_smul]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self i))
    · ext1 i; rw [crdEmb_apply, crd_sum, ha]

noncomputable def latE {r : ℕ} {v : Fin r → V} (hli : LinearIndependent K v)
    (E : Submodule (𝓞 K) V) : Submodule ℤ (Fin r → mixedEmbedding.mixedSpace K) :=
  (E.toAddSubgroup.map (crdEmb hli)).toIntSubmodule

theorem crdEmb_injOn {r : ℕ} {v : Fin r → V} (hli : LinearIndependent K v) {x y : V}
    (hx : x ∈ Submodule.span K (Set.range v)) (hy : y ∈ Submodule.span K (Set.range v))
    (h : crdEmb hli x = crdEmb hli y) : x = y := by
  have h1 : crd hli x = crd hli y := by
    funext i
    have h2 := congrFun h i
    simp only [crdEmb_apply] at h2
    exact mixedEmbedding_injective K h2
  rw [← sum_crd hli hx, ← sum_crd hli hy, h1]

theorem span_le_E {E : Submodule (𝓞 K) V} {r : ℕ} {v : Fin r → V} (hv : IsFrame K E v) :
    Submodule.span (𝓞 K) (Set.range v) ≤ E := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hv.1 i)

theorem standardLattice_le_frameLattice {E : Submodule (𝓞 K) V} {r : ℕ} {v : Fin r → V} (hv : IsFrame K E v) :
    lat0 K r ≤ latE hv.2.1 E := by
  intro y hy
  have : y ∈ (lat0 K r).toAddSubgroup := hy
  rw [← map_span_crdEmb hv.2.1] at this
  exact AddSubgroup.map_mono (f := crdEmb hv.2.1) (fun x hx => span_le_E hv hx) this

theorem relIndex_lat {E : Submodule (𝓞 K) V} {r : ℕ} {v : Fin r → V} (hv : IsFrame K E v) :
    (lat0 K r).toAddSubgroup.relIndex (latE hv.2.1 E).toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup := by
  let P : AddSubgroup V := (Submodule.span K (Set.range v)).toAddSubgroup
  have hEP : E.toAddSubgroup ≤ P := fun x hx => hv.2.2 hx
  have hHP : (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup ≤ P :=
    fun x hx => hEP (span_le_E hv hx)
  let f := (crdEmb hv.2.1).comp P.subtype
  have hf : Function.Injective f := fun a b hab =>
    Subtype.ext (crdEmb_injOn hv.2.1 a.2 b.2 hab)
  have key : ∀ X : AddSubgroup V, X ≤ P → X.map (crdEmb hv.2.1) = (X.addSubgroupOf P).map f := by
    intro X hX
    rw [← AddSubgroup.map_map, AddSubgroup.addSubgroupOf_map_subtype, inf_of_le_left hX]
  rw [← map_span_crdEmb hv.2.1]
  change ((Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.map (crdEmb hv.2.1)).relIndex
    (E.toAddSubgroup.map (crdEmb hv.2.1)) = _
  rw [key _ hHP, key _ hEP, AddSubgroup.relIndex_map_map_of_injective _ _ hf,
    AddSubgroup.relIndex_addSubgroupOf hEP]

theorem discrete_latE {E : Submodule (𝓞 K) V} (hE : E.FG) {r : ℕ} {v : Fin r → V}
    (hv : IsFrame K E v) : DiscreteTopology (latE hv.2.1 E) := by
  set n := (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup with hn_def
  have hn : n ≠ 0 := hv.relIndex_ne_zero hE
  have hmem : ∀ y ∈ latE hv.2.1 E, n • y ∈ lat0 K r := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have h1 : n • x ∈ (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup :=
      AddSubgroup.nsmul_relIndex_mem _ hx
    have : (lat0 K r).toAddSubgroup = _ := (map_span_crdEmb hv.2.1).symm
    change n • crdEmb hv.2.1 x ∈ (lat0 K r).toAddSubgroup
    rw [this, ← map_nsmul]
    exact AddSubgroup.mem_map_of_mem _ h1
  let g : latE hv.2.1 E → lat0 K r := fun y => ⟨n • (y : Fin r → mixedEmbedding.mixedSpace K), hmem y y.2⟩
  refine DiscreteTopology.of_continuous_injective (f := g) ?_ ?_
  · exact Continuous.subtype_mk ((continuous_const_smul n).comp continuous_subtype_val) _
  · intro a b hab
    have h1 : n • (a : Fin r → mixedEmbedding.mixedSpace K) = n • (b : Fin r → mixedEmbedding.mixedSpace K) :=
      congrArg Subtype.val hab
    have h2 : (n : ℝ) • (a : Fin r → mixedEmbedding.mixedSpace K) = (n : ℝ) • (b : Fin r → mixedEmbedding.mixedSpace K) := by
      simpa only [Nat.cast_smul_eq_nsmul] using h1
    exact Subtype.ext (smul_right_injective _ (Nat.cast_ne_zero.mpr hn) h2)

theorem isZLattice_latE {E : Submodule (𝓞 K) V} (hE : E.FG) {r : ℕ} {v : Fin r → V}
    (hv : IsFrame K E v) :
    letI := discrete_latE hE hv
    IsZLattice ℝ (latE hv.2.1 E) := by
  have := discrete_latE hE hv
  refine ⟨?_⟩
  rw [eq_top_iff, ← IsZLattice.span_top (L := lat0 K r)]
  exact Submodule.span_mono (standardLattice_le_frameLattice hv)

theorem covolume_standardLattice (r : ℕ) :
    ZLattice.covolume (lat0 K r) = (ZLattice.covolume (mixedEmbedding.integerLattice K)) ^ r := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain (lat0 K r) volume
      (ZSpan.isAddFundamentalDomain (latB K r) volume),
    ZLattice.covolume_eq_measure_fundamentalDomain _ volume
      (mixedEmbedding.fundamentalDomain_integerLattice K)]
  have : ZSpan.fundamentalDomain (latB K r) =
      Set.pi univ fun _ => ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis K) := by
    ext y
    simp only [ZSpan.mem_fundamentalDomain, latB, Pi.basis_repr, Sigma.forall, mem_pi, mem_univ,
      true_implies]
  rw [this, measureReal_def, volume_pi_pi, ENNReal.toReal_prod, measureReal_def]
  simp

theorem covolume_latE {E : Submodule (𝓞 K) V} (hE : E.FG) {r : ℕ} {v : Fin r → V}
    (hv : IsFrame K E v) :
    ZLattice.covolume (latE hv.2.1 E) = ZLattice.covolume (lat0 K r) /
      ((Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup : ℝ) := by
  have := discrete_latE hE hv
  have := isZLattice_latE hE hv
  have h := covol_div_covol_eq_relIndex volume (lat0 K r) (latE hv.2.1 E) (standardLattice_le_frameLattice hv)
  rw [relIndex_lat hv] at h
  have hn : ((Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (hv.relIndex_ne_zero hE)
  have hpos := ZLattice.covolume_pos (latE hv.2.1 E) volume
  rw [← h, div_div_cancel₀ (ZLattice.covolume_pos _ _).ne']

end ReciprocityTheory.GeometryOfNumbersTheory
end

namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module MeasureTheory Set
open scoped Classical ComplexOrder

variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]

noncomputable def gramR (h : HermFam K V) {r : ℕ} (v : Fin r → V)
    (w : {w : InfinitePlace K // w.IsReal}) : Matrix (Fin r) (Fin r) ℝ :=
  (h.gram w.1.embedding v).map Complex.re

def ellS (h : HermFam K V) {r : ℕ} (v : Fin r → V) (R : ℝ) :
    Set (Fin r → mixedEmbedding.mixedSpace K) :=
  {y | (∀ w, qR (gramR h v w) (fun i => (y i).1 w) ≤ R ^ 2) ∧
    ∀ w : {w : InfinitePlace K // w.IsComplex}, qC (h.gram w.1.embedding v) (fun i => (y i).2 w) ≤ R ^ 2}

theorem gram_posDef (h : HermFam K V) (σ : K →+* ℂ) {r : ℕ} {v : Fin r → V}
    (hli : LinearIndependent K v) : (h.gram σ v).PosDef := h.posDef σ r v hli

private lemma finsupp_sum_sum_star_mul_eq_qR {r : ℕ} (M : Matrix (Fin r) (Fin r) ℝ) (y : Fin r →₀ ℝ) :
    (y.sum fun i xi => y.sum fun j xj => star xi * M i j * xj) = qR M y := by
  unfold qR
  rw [Finsupp.sum_fintype]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finsupp.sum_fintype]
    · simp only [star_trivial]
    · intro j
      simp
  · intro i
    simp

private lemma finsupp_sum_sum_star_mul_re_eq_qC {r : ℕ} (G : Matrix (Fin r) (Fin r) ℂ) (z : Fin r →₀ ℂ) :
    (z.sum fun i xi => z.sum fun j xj => star xi * G i j * xj).re = qC G z := by
  unfold qC
  rw [Finsupp.sum_fintype]
  · congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finsupp.sum_fintype]
    · simp only [Complex.star_def]
    · intro j
      simp
  · intro i
    simp

private lemma qR_map_re_eq_qC_ofReal {r : ℕ} (G : Matrix (Fin r) (Fin r) ℂ) (y : Fin r → ℝ) :
    qR (G.map Complex.re) y = qC G (fun i => (y i : ℂ)) := by
  unfold qR qC
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.re_ofReal_mul, Complex.re_mul_ofReal, Matrix.map_apply] <;> ring

theorem gramR_posDef (h : HermFam K V) {r : ℕ} {v : Fin r → V} (hli : LinearIndependent K v)
    (w : {w : InfinitePlace K // w.IsReal}) : (gramR h v w).PosDef := by
  have hG := gram_posDef h w.1.embedding hli
  refine ⟨Matrix.IsHermitian.ext fun i j => ?_, fun y hy => ?_⟩
  · simp only [gramR, Matrix.map_apply, star_trivial]
    rw [← hG.1.apply i j]
    simp [Complex.star_def]
  · have hz : Finsupp.mapRange (fun a : ℝ => (a : ℂ)) Complex.ofReal_zero y ≠ 0 := by
      intro h0
      apply hy
      ext i
      simpa using DFunLike.congr_fun h0 i
    have h1 := (Complex.lt_def.mp (hG.2 hz)).1
    rw [finsupp_sum_sum_star_mul_re_eq_qC] at h1
    have h2 : (⇑(Finsupp.mapRange (fun a : ℝ => (a : ℂ)) Complex.ofReal_zero y)) =
        fun i => (y i : ℂ) := by
      funext i
      simp
    rw [h2, ← qR_map_re_eq_qC_ofReal] at h1
    rw [finsupp_sum_sum_star_mul_eq_qR]
    simpa [gramR] using h1

def psi (K : Type*) [Field K] [NumberField K] (r : ℕ) (y : Fin r → mixedEmbedding.mixedSpace K) :
    ({w : InfinitePlace K // w.IsReal} → Fin r → ℝ) × ({w : InfinitePlace K // w.IsComplex} → Fin r → ℂ) :=
  (fun w i => (y i).1 w, fun w i => (y i).2 w)

private lemma measurePreserving_pi_pi_swap {ι κ X : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] :
    MeasurePreserving (fun (f : ι → κ → X) (j : κ) (i : ι) => f i j)
      (Measure.pi fun _ => Measure.pi fun _ => μ) (Measure.pi fun _ => Measure.pi fun _ => μ) := by
  classical
  have h1 : MeasurePreserving (fun (f : ι → κ → X) (p : ι × κ) => f p.1 p.2)
      (Measure.pi fun _ => Measure.pi fun _ => μ) (Measure.pi fun _ => μ) := by
    have hm : Measurable (fun (f : ι → κ → X) (p : ι × κ) => f p.1 p.2) :=
      Measurable.of_eval fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
    refine ⟨hm, (Measure.pi_eq fun s hs => ?_).symm⟩
    rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
    have he : (fun (f : ι → κ → X) (p : ι × κ) => f p.1 p.2) ⁻¹' Set.univ.pi s =
        Set.univ.pi fun i => Set.univ.pi fun j => s (i, j) := by
      ext f
      simp only [Set.mem_preimage, Set.mem_univ_pi]
      exact ⟨fun H i j => H (i, j), fun H p => H p.1 p.2⟩
    rw [he, Measure.pi_pi, Fintype.prod_prod_type]
    exact Finset.prod_congr rfl fun i _ => by rw [Measure.pi_pi]
  let e : (κ → ι → X) ≃ᵐ (ι × κ → X) :=
    { toFun := fun g p => g p.2 p.1
      invFun := fun g j i => g (i, j)
      left_inv := fun g => rfl
      right_inv := fun g => rfl
      measurable_toFun :=
        Measurable.of_eval fun p => (measurable_pi_apply p.1).comp (measurable_pi_apply p.2)
      measurable_invFun :=
        Measurable.of_eval fun j => Measurable.of_eval fun i => measurable_pi_apply (i, j) }
  have h2 : MeasurePreserving e (Measure.pi fun _ => Measure.pi fun _ => μ)
      (Measure.pi fun _ => μ) := by
    refine ⟨e.measurable, (Measure.pi_eq fun s hs => ?_).symm⟩
    rw [e.map_apply]
    have he : e ⁻¹' Set.univ.pi s = Set.univ.pi fun j => Set.univ.pi fun i => s (i, j) := by
      ext g
      simp only [Set.mem_preimage, Set.mem_univ_pi]
      exact ⟨fun H j i => H (i, j), fun H p => H p.2 p.1⟩
    rw [he, Measure.pi_pi, Fintype.prod_prod_type, Finset.prod_comm]
    exact Finset.prod_congr rfl fun j _ => by rw [Measure.pi_pi]
  exact (h2.symm e).comp h1

theorem measurePreserving_psi (r : ℕ) :
    MeasurePreserving (psi K r) volume
      ((Measure.pi fun _ => Measure.pi fun _ => volume).prod
        (Measure.pi fun _ => Measure.pi fun _ => volume)) := by
  have hA := measurePreserving_arrowProdEquivProdArrow ({w : InfinitePlace K // w.IsReal} → ℝ)
    ({w : InfinitePlace K // w.IsComplex} → ℂ) (Fin r) (fun _ => volume) (fun _ => volume)
  exact ((measurePreserving_pi_pi_swap (ι := Fin r) (κ := {w : InfinitePlace K // w.IsReal})
    (volume : Measure ℝ)).prod (measurePreserving_pi_pi_swap (ι := Fin r) (κ := {w : InfinitePlace K // w.IsComplex})
    (volume : Measure ℂ))).comp hA

theorem ellS_eq (h : HermFam K V) {r : ℕ} (v : Fin r → V) (R : ℝ) :
    ellS h v R = psi K r ⁻¹' ((Set.pi univ fun w => {u | qR (gramR h v w) u ≤ R ^ 2}) ×ˢ
      (Set.pi univ fun w : {w : InfinitePlace K // w.IsComplex} =>
        {u | qC (h.gram w.1.embedding v) u ≤ R ^ 2})) := by
  ext y
  simp [ellS, psi, Set.mem_pi]

end ReciprocityTheory.GeometryOfNumbersTheory

namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module MeasureTheory Set
open scoped Classical ComplexOrder

variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]

def ellT (h : HermFam K V) {r : ℕ} (v : Fin r → V) (R : ℝ) :
    Set (({w : InfinitePlace K // w.IsReal} → Fin r → ℝ) ×
      ({w : InfinitePlace K // w.IsComplex} → Fin r → ℂ)) :=
  (Set.pi univ fun w => {u | qR (gramR h v w) u ≤ R ^ 2}) ×ˢ
    (Set.pi univ fun w : {w : InfinitePlace K // w.IsComplex} =>
      {u | qC (h.gram w.1.embedding v) u ≤ R ^ 2})

theorem ellT_props (h : HermFam K V) {r : ℕ} {v : Fin r → V} (hli : LinearIndependent K v)
    (R : ℝ) : Convex ℝ (ellT h v R) ∧ Bornology.IsBounded (ellT h v R) ∧
      MeasurableSet (ellT h v R) := by
  have hR := fun w => ellipsoidR_props (gramR_posDef h hli w) R
  have hC := fun w : {w : InfinitePlace K // w.IsComplex} =>
    ellipsoidC_props (gram_posDef h w.1.embedding hli) R
  refine ⟨?_, ?_, ?_⟩
  · exact (convex_pi fun w _ => (hR w).1).prod (convex_pi fun w _ => (hC w).1)
  · exact (Bornology.IsBounded.pi fun w => (hR w).2.2.1).prod
      (Bornology.IsBounded.pi fun w => (hC w).2.2.1)
  · exact (MeasurableSet.univ_pi fun w => (hR w).2.2.2).prod
      (MeasurableSet.univ_pi fun w => (hC w).2.2.2)

def psiL (K : Type*) [Field K] [NumberField K] (r : ℕ) :
    (Fin r → mixedEmbedding.mixedSpace K) →ₗ[ℝ]
      (({w : InfinitePlace K // w.IsReal} → Fin r → ℝ) ×
        ({w : InfinitePlace K // w.IsComplex} → Fin r → ℂ)) where
  toFun := psi K r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem norm_le_norm_psi {r : ℕ} (y : Fin r → mixedEmbedding.mixedSpace K) :
    ‖y‖ ≤ ‖psi K r y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  refine norm_prod_le_iff.2 ⟨?_, ?_⟩
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun w => ?_
    calc ‖(y i).1 w‖ = ‖(psi K r y).1 w i‖ := rfl
      _ ≤ ‖(psi K r y).1 w‖ := norm_le_pi_norm _ i
      _ ≤ ‖(psi K r y).1‖ := norm_le_pi_norm _ w
      _ ≤ ‖psi K r y‖ := norm_fst_le _
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun w => ?_
    calc ‖(y i).2 w‖ = ‖(psi K r y).2 w i‖ := rfl
      _ ≤ ‖(psi K r y).2 w‖ := norm_le_pi_norm _ i
      _ ≤ ‖(psi K r y).2‖ := norm_le_pi_norm _ w
      _ ≤ ‖psi K r y‖ := norm_snd_le _

theorem ellS_props (h : HermFam K V) {r : ℕ} {v : Fin r → V} (hli : LinearIndependent K v)
    (R : ℝ) : Convex ℝ (ellS h v R) ∧ (∀ y ∈ ellS h v R, -y ∈ ellS h v R) ∧
      Bornology.IsBounded (ellS h v R) ∧ MeasurableSet (ellS h v R) := by
  obtain ⟨hcv, hbd, hms⟩ := ellT_props h hli R
  have he : ellS h v R = psi K r ⁻¹' ellT h v R := ellS_eq h v R
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [he]
    exact hcv.linear_preimage (psiL K r)
  · intro y hy
    refine ⟨fun w => ?_, fun w => ?_⟩
    · exact (ellipsoidR_props (gramR_posDef h hli w) R).2.1 _ (hy.1 w)
    · exact (ellipsoidC_props (gram_posDef h w.1.embedding hli) R).2.1 _ (hy.2 w)
  · obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hbd
    refine isBounded_iff_forall_norm_le.2 ⟨C, fun y hy => ?_⟩
    rw [he] at hy
    exact (norm_le_norm_psi y).trans (hC _ hy)
  · rw [he]
    exact hms.preimage (measurePreserving_psi (K := K) r).measurable

theorem volume_ellS (h : HermFam K V) {r : ℕ} {v : Fin r → V} (hli : LinearIndependent K v)
    (R : ℝ) : (volume (ellS h v R)).toReal =
      (∏ w, (volume {u : Fin r → ℝ | qR (gramR h v w) u ≤ R ^ 2}).toReal) *
        ∏ w : {w : InfinitePlace K // w.IsComplex},
          (volume {u : Fin r → ℂ | qC (h.gram w.1.embedding v) u ≤ R ^ 2}).toReal := by
  rw [show ellS h v R = psi K r ⁻¹' ellT h v R from ellS_eq h v R,
    (measurePreserving_psi r).measure_preimage (ellT_props h hli R).2.2.nullMeasurableSet, ellT,
    Measure.prod_prod, Measure.pi_pi,
    Measure.pi_pi, ENNReal.toReal_mul, ENNReal.toReal_prod, ENNReal.toReal_prod]
  all_goals rfl

end ReciprocityTheory.GeometryOfNumbersTheory
end

section -- merged from ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountZSt
namespace ReciprocityTheory.GeometryOfNumbersTheory

open MeasureTheory Module
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem finite_inter_lattice (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (S : Set E)
    (hb : Bornology.IsBounded S) : (S ∩ (L : Set E)).Finite := by
  haveI : ProperSpace E := FiniteDimensional.proper_real E
  haveI : DiscreteTopology L.toAddSubgroup := ‹DiscreteTopology L›
  have hc : IsClosed (L : Set E) := (L.toAddSubgroup).isClosed_of_discreteTopology
  exact Metric.finite_isBounded_inter_isClosed ⟨(‹DiscreteTopology L› : DiscreteTopology L)⟩ hb hc

theorem fiber_count_le_ncard_inter_lattice (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (S : Set E) (hconv : Convex ℝ S) (hsymm : ∀ x ∈ S, -x ∈ S) (hb : Bornology.IsBounded S)
    (x : E) :
    ∑' g : L, ((g +ᵥ ((2⁻¹ : ℝ) • S)).indicator 1 x : ENNReal) ≤ ((S ∩ (L : Set E)).ncard : ENNReal) := by
  classical
  by_cases hx : ∃ g0 : L, x ∈ g0 +ᵥ ((2⁻¹ : ℝ) • S)
  swap
  · push_neg at hx
    simp [Set.indicator_of_notMem (hx _)]
  obtain ⟨g0, hg0⟩ := hx

  have key : ∀ g : L, x ∈ g +ᵥ ((2⁻¹ : ℝ) • S) → ((g : E) - g0) ∈ S := by
    intro g hg
    rw [Set.mem_vadd_set] at hg hg0
    obtain ⟨a, ha, hax⟩ := hg
    obtain ⟨c, hc, hcx⟩ := hg0
    rw [Set.mem_smul_set] at ha hc
    obtain ⟨s1, hs1, rfl⟩ := ha
    obtain ⟨s2, hs2, rfl⟩ := hc
    rw [Submodule.vadd_def, vadd_eq_add] at hax hcx
    have e : (g : E) - g0 = (2⁻¹ : ℝ) • s2 + (2⁻¹ : ℝ) • (-s1) := by
      rw [smul_neg, eq_sub_of_add_eq hax, eq_sub_of_add_eq hcx]; abel
    rw [e]
    exact hconv hs2 (hsymm s1 hs1) (by norm_num) (by norm_num) (by norm_num)
  have hfin : {g : L | ((g : E) - g0) ∈ S}.Finite := by
    have hinj : Function.Injective (fun g : L => (g : E) - g0) :=
      fun a b h => Subtype.ext (sub_left_injective h)
    refine ((finite_inter_lattice L S hb).preimage hinj.injOn).subset ?_
    intro g hg
    exact Set.mem_inter hg (sub_mem g.2 g0.2)
  rw [tsum_eq_sum (s := hfin.toFinset) (fun g hg => Set.indicator_of_notMem
    (fun h => hg (hfin.mem_toFinset.2 (key g h))) _)]
  calc ∑ g ∈ hfin.toFinset, ((g +ᵥ ((2⁻¹ : ℝ) • S)).indicator 1 x : ENNReal)
      ≤ ∑ g ∈ hfin.toFinset, (1 : ENNReal) := by
        refine Finset.sum_le_sum fun g _ => ?_
        unfold Set.indicator; split_ifs <;> simp
    _ = (hfin.toFinset.card : ENNReal) := by simp
    _ ≤ ((S ∩ (L : Set E)).ncard : ENNReal) := by
        rw [← Set.ncard_eq_toFinset_card _ hfin]
        have hh := Set.ncard_le_ncard_of_injOn (s := {g : L | ((g : E) - g0) ∈ S})
          (t := S ∩ (L : Set E)) (fun g : L => (g : E) - g0)
          (fun g hg => Set.mem_inter hg (sub_mem g.2 g0.2))
          (fun a _ b _ h => Subtype.ext (sub_left_injective h)) (finite_inter_lattice L S hb)
        exact_mod_cast hh

theorem measure_div_le_ncard_inter_lattice (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (S : Set E)
    (hconv : Convex ℝ S) (hsymm : ∀ x ∈ S, -x ∈ S) (hb : Bornology.IsBounded S)
    (hm : MeasurableSet S) :
    (μ S).toReal / (2 ^ finrank ℝ E * ZLattice.covolume L μ) ≤ ((S ∩ (L : Set E)).ncard : ℝ) := by
  classical
  haveI : MeasureTheory.VAddInvariantMeasure L E μ :=
    ⟨fun g s _ => by simp only [Submodule.vadd_def, vadd_eq_add]; exact measure_preimage_add μ (g : E) s⟩
  have hF : MeasureTheory.IsAddFundamentalDomain L
      (ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)) μ :=
    ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ L) μ
  have hcov := ZLattice.covolume_eq_measure_fundamentalDomain L μ hF
  have hpos : 0 < ZLattice.covolume L μ := ZLattice.covolume_pos L μ
  have hTm : MeasurableSet ((2⁻¹ : ℝ) • S) := hm.const_smul₀ _
  have hle : μ ((2⁻¹ : ℝ) • S) ≤ ((S ∩ (L : Set E)).ncard : ENNReal)
      * μ (ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)) := by
    rw [hF.measure_eq_tsum ((2⁻¹ : ℝ) • S)]
    calc ∑' g : L, μ ((g +ᵥ (2⁻¹ : ℝ) • S)
          ∩ ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L))
        = ∑' g : L, ∫⁻ y in ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L),
            ((g +ᵥ (2⁻¹ : ℝ) • S).indicator 1 y : ENNReal) ∂μ := by
          congr 1; funext g
          rw [lintegral_indicator_one (hTm.const_vadd g), Measure.restrict_apply (hTm.const_vadd g)]
      _ = ∫⁻ y in ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L),
            ∑' g : L, ((g +ᵥ (2⁻¹ : ℝ) • S).indicator 1 y : ENNReal) ∂μ :=
          (lintegral_tsum fun g => (measurable_one.indicator (hTm.const_vadd g)).aemeasurable).symm
      _ ≤ ∫⁻ _ in ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L),
            ((S ∩ (L : Set E)).ncard : ENNReal) ∂μ :=
          lintegral_mono fun y => fiber_count_le_ncard_inter_lattice L S hconv hsymm hb y
      _ = _ := setLIntegral_const _ _
  have hFfin : μ (ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)) ≠ ⊤ := by
    intro h
    rw [hcov, Measure.real, h] at hpos
    simp at hpos
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hFfin) hle
  rw [Measure.addHaar_smul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
    abs_of_nonneg (by positivity), inv_pow, ENNReal.toReal_natCast] at hreal
  have h2 : (0 : ℝ) < 2 ^ finrank ℝ E := by positivity
  rw [inv_mul_le_iff₀ h2] at hreal
  rw [div_le_iff₀ (mul_pos h2 hpos), hcov, Measure.real]
  calc (μ S).toReal ≤ _ := hreal
    _ = _ := by ring

end ReciprocityTheory.GeometryOfNumbersTheory
end

namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module
open scoped ComplexOrder
open MeasureTheory

variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def HermFam.IsConjInv (h : HermFam K V) : Prop :=
  ∀ (σ : K →+* ℂ) (x y : V),
    h.form (ComplexEmbedding.conjugate σ) x y = starRingEnd ℂ (h.form σ x y)

def smallVec (h : HermFam K V) (E : Submodule (𝓞 K) V) (R : ℝ) : Set V :=
  {x | x ∈ E ∧ ∀ σ, h.nrm σ x ≤ R}

theorem nrm_conj (h : HermFam K V) (hinv : h.IsConjInv) (σ : K →+* ℂ) (x : V) :
    h.nrm (ComplexEmbedding.conjugate σ) x = h.nrm σ x := by
  unfold HermFam.nrm
  rw [hinv σ x x, Complex.conj_re]

theorem nrm_eq_nrm_embedding (h : HermFam K V) (hinv : h.IsConjInv) (σ : K →+* ℂ) (x : V) :
    h.nrm σ x = h.nrm (InfinitePlace.mk σ).embedding x := by
  rcases InfinitePlace.embedding_mk_eq σ with h1 | h1 <;> rw [h1]
  exact (nrm_conj h hinv σ x).symm

open scoped Classical in
theorem mem_image_of_mem_ellS (h : HermFam K V) (hinv : h.IsConjInv) {E : Submodule (𝓞 K) V}
    {r : ℕ} {v : Fin r → V} (hv : IsFrame K E v) {R : ℝ} (hR : 0 ≤ R) {y}
    (hy : y ∈ ellS h v R ∩ (latE hv.2.1 E : Set _)) :
    y ∈ crdEmb hv.2.1 '' smallVec h E R := by
  obtain ⟨⟨hyR, hyC⟩, hyL⟩ := hy
  have hyL' : y ∈ E.toAddSubgroup.map (crdEmb hv.2.1) := hyL
  obtain ⟨x, hxE, rfl⟩ := AddSubgroup.mem_map.1 hyL'
  have hxs : x ∈ Submodule.span K (Set.range v) := hv.2.2 hxE

  have hexp : ∀ (σ : K →+* ℂ) (c : Fin r → K), h.form σ (∑ i, c i • v i) (∑ j, c j • v j) =
      ∑ i, ∑ j, starRingEnd ℂ (σ (c i)) * h.form σ (v i) (v j) * σ (c j) := by
    intro σ c
    have hr : ∀ y, h.form σ y (∑ j, c j • v j) = ∑ j, σ (c j) * h.form σ y (v j) := by
      intro y
      have e := map_sum (AddMonoidHom.mk' (h.form σ y) (h.add_right σ y)) (fun j => c j • v j)
        Finset.univ
      simp only [AddMonoidHom.mk'_apply, h.smul_right] at e
      exact e
    have hl : ∀ y, h.form σ (∑ i, c i • v i) y =
        ∑ i, starRingEnd ℂ (σ (c i)) * h.form σ (v i) y := by
      intro y
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← h.conj_symm σ y, hr y, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, h.conj_symm]
    rw [hl]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hr, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hreal : ∀ w : {w : InfinitePlace K // w.IsReal},
      qR (gramR h v w) (fun i => (crdEmb hv.2.1 x i).1 w) = (h.form w.1.embedding x x).re := by
    intro w
    have hy : ∀ a : K, (((mixedEmbedding K a).1 w : ℝ) : ℂ) = w.1.embedding a := fun a => by
      simp [mixedEmbedding]
    symm
    conv_lhs => rw [← sum_crd hv.2.1 hxs]
    rw [hexp, Complex.re_sum]
    unfold qR
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [crdEmb, AddMonoidHom.coe_mk, ZeroHom.coe_mk, gramR, HermFam.gram, Matrix.map_apply,
      Matrix.of_apply]
    rw [← hy, ← hy, Complex.conj_ofReal]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im]
    ring
  have hcplx : ∀ w : {w : InfinitePlace K // w.IsComplex},
      qC (h.gram w.1.embedding v) (fun i => (crdEmb hv.2.1 x i).2 w) =
        (h.form w.1.embedding x x).re := by
    intro w
    symm
    conv_lhs => rw [← sum_crd hv.2.1 hxs]
    rw [hexp]
    unfold qC
    congr 1
  refine ⟨x, ⟨hxE, fun σ => ?_⟩, rfl⟩
  rw [nrm_eq_nrm_embedding h hinv σ x]
  have hre : (h.form (InfinitePlace.mk σ).embedding x x).re ≤ R ^ 2 := by
    rcases (InfinitePlace.mk σ).isReal_or_isComplex with hw | hw
    · exact (hreal ⟨_, hw⟩).symm.trans_le (hyR ⟨_, hw⟩)
    · exact (hcplx ⟨_, hw⟩).symm.trans_le (hyC ⟨_, hw⟩)
  unfold HermFam.nrm
  calc Real.sqrt (h.form (InfinitePlace.mk σ).embedding x x).re ≤ Real.sqrt (R ^ 2) :=
        Real.sqrt_le_sqrt hre
    _ = R := Real.sqrt_sq hR

theorem det_gram_conj_re (h : HermFam K V) (hinv : h.IsConjInv) (σ : K →+* ℂ) {r : ℕ}
    (v : Fin r → V) :
    (h.gram (ComplexEmbedding.conjugate σ) v).det.re = (h.gram σ v).det.re := by
  have hg : h.gram (ComplexEmbedding.conjugate σ) v = (h.gram σ v).map (starRingEnd ℂ) := by
    ext i j
    simp only [HermFam.gram, Matrix.map_apply, Matrix.of_apply]
    exact hinv σ (v i) (v j)
  rw [hg, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Complex.conj_re]

end ReciprocityTheory.GeometryOfNumbersTheory
