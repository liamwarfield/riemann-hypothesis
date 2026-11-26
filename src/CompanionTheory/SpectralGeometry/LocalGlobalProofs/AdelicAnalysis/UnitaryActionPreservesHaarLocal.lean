module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitProductClosureProperties
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MapMulVecEqSmul
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MatrixTransvectionDiagonalDecomposition
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MatrixTransvectionDiagonalDecomposition
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.ArtinElem

variable {K K' : Type*} [CommRing K] [CommRing K'] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {M : Type*} [DecidableEq M] {F : M → Type*} [∀ m, CommRing (F m)]

noncomputable def coord (e : K ≃+* ∀ m, F m) (m : M) : K →+* F m :=
  (Pi.evalRingHom F m).comp e.toRingHom

noncomputable def liftT (e : K ≃+* ∀ m, F m) (m : M) (t : TransvectionStruct ι (F m)) :
    TransvectionStruct ι K :=
  ⟨t.i, t.j, t.hij, e.symm (Pi.single m t.c)⟩

lemma coord_symm_single (e : K ≃+* ∀ m, F m) (m m' : M) (c : F m) :
    coord e m' (e.symm (Pi.single m c)) = (Pi.single m c : ∀ m, F m) m' := by
  simp [coord]

lemma mapMatrix_single (f : K →+* K') (a b : ι) (c : K) :
    f.mapMatrix (single a b c) = single a b (f c) := by
  ext x y
  simp only [RingHom.mapMatrix_apply, map_apply, single_apply]
  split_ifs <;> simp

lemma liftT_toMatrix (e : K ≃+* ∀ m, F m) (m : M) (t : TransvectionStruct ι (F m)) :
    (liftT e m t).toMatrix = 1 + single t.i t.j (e.symm (Pi.single m t.c)) := rfl

lemma mapMatrix_liftT_same (e : K ≃+* ∀ m, F m) (m : M) (t : TransvectionStruct ι (F m)) :
    (coord e m).mapMatrix (liftT e m t).toMatrix = t.toMatrix := by
  rw [liftT_toMatrix, map_add (f := _), map_one, mapMatrix_single, coord_symm_single, Pi.single_eq_same]
  rfl

lemma mapMatrix_liftT_ne (e : K ≃+* ∀ m, F m) {m m' : M} (h : m' ≠ m)
    (t : TransvectionStruct ι (F m)) :
    (coord e m').mapMatrix (liftT e m t).toMatrix = 1 := by
  rw [liftT_toMatrix, map_add (f := _), map_one, mapMatrix_single, coord_symm_single,
    Pi.single_eq_of_ne h, single_zero, add_zero]

lemma mapMatrix_prod_same (e : K ≃+* ∀ m, F m) (m : M) (T : List (TransvectionStruct ι (F m))) :
    (coord e m).mapMatrix (((T.map (liftT e m)).map TransvectionStruct.toMatrix).prod) =
      (T.map TransvectionStruct.toMatrix).prod := by
  induction T with
  | nil => simp
  | cons t T ih => simp only [List.map_cons, List.prod_cons, map_mul, ih, mapMatrix_liftT_same]

lemma mapMatrix_prod_ne (e : K ≃+* ∀ m, F m) {m m' : M} (h : m' ≠ m)
    (T : List (TransvectionStruct ι (F m))) :
    (coord e m').mapMatrix (((T.map (liftT e m)).map TransvectionStruct.toMatrix).prod) = 1 := by
  induction T with
  | nil => simp
  | cons t T ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, ih, mapMatrix_liftT_ne e h, mul_one]

noncomputable def big (e : K ≃+* ∀ m, F m) (T : ∀ m, List (TransvectionStruct ι (F m))) (l : List M) :
    List (TransvectionStruct ι K) :=
  l.flatMap fun m => (T m).map (liftT e m)

lemma mapMatrix_big (e : K ≃+* ∀ m, F m) (T : ∀ m, List (TransvectionStruct ι (F m)))
    (m' : M) (l : List M) (hl : l.Nodup) :
    (coord e m').mapMatrix (((big e T l).map TransvectionStruct.toMatrix).prod) =
      if m' ∈ l then ((T m').map TransvectionStruct.toMatrix).prod else 1 := by
  induction l with
  | nil => simp [big]
  | cons m l ih =>
    have ih' := ih (List.nodup_cons.mp hl).2
    have hm : m ∉ l := (List.nodup_cons.mp hl).1
    have hb : big e T (m :: l) = (T m).map (liftT e m) ++ big e T l := by simp [big]
    rw [hb, List.map_append, List.prod_append, map_mul, ih']
    by_cases h : m' = m
    · subst h
      rw [mapMatrix_prod_same]
      simp [hm]
    · rw [mapMatrix_prod_ne e h, one_mul]
      simp [h]

lemma matrix_ext_coord (e : K ≃+* ∀ m, F m) {A B : Matrix ι ι K}
    (h : ∀ m, (coord e m).mapMatrix A = (coord e m).mapMatrix B) : A = B := by
  ext a b
  apply e.injective
  funext m
  have := congrFun (congrFun (h m) a) b
  simpa [coord] using this

theorem factor_of_pi [Fintype M] (e : K ≃+* ∀ m, F m)
    (hF : ∀ (m : M) (A : Matrix ι ι (F m)),
      ∃ (L L' : List (TransvectionStruct ι (F m))) (D : ι → F m),
        A = (L.map TransvectionStruct.toMatrix).prod * diagonal D *
          (L'.map TransvectionStruct.toMatrix).prod)
    (A : Matrix ι ι K) :
    ∃ (L L' : List (TransvectionStruct ι K)) (D : ι → K),
      A = (L.map TransvectionStruct.toMatrix).prod * diagonal D *
        (L'.map TransvectionStruct.toMatrix).prod := by
  choose L L' D hD using fun m => hF m ((coord e m).mapMatrix A)
  refine ⟨big e L Finset.univ.toList, big e L' Finset.univ.toList,
    fun i => e.symm (fun m => D m i), matrix_ext_coord e fun m => ?_⟩
  have hnd := Finset.nodup_toList (Finset.univ : Finset M)
  have hdiag : (coord e m).mapMatrix (diagonal fun i => e.symm (fun m => D m i)) =
      diagonal (D m) := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp [coord]
    · simp [hab]
  rw [map_mul, map_mul, mapMatrix_big e L m _ hnd, mapMatrix_big e L' m _ hnd, hdiag]
  simpa using hD m

end GlobalTheory.CompanionTheory.SW.ArtinElem

namespace GlobalTheory.CompanionTheory.SW

theorem artinian_reduced_list_transvec_mul_diagonal_mul_list_transvec
    (K : Type) [CommRing K] [IsArtinianRing K] [IsReduced K] (ι : Type) [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι K) :
    ∃ (L L' : List (Matrix.TransvectionStruct ι K)) (D : ι → K),
      A = (L.map Matrix.TransvectionStruct.toMatrix).prod * Matrix.diagonal D *
        (L'.map Matrix.TransvectionStruct.toMatrix).prod := by
  classical
  letI : Fintype (MaximalSpectrum K) := Fintype.ofFinite _
  refine ArtinElem.factor_of_pi (F := fun m : MaximalSpectrum K => K ⧸ m.asIdeal)
    (IsArtinianRing.equivPi K).toRingEquiv (fun m B => ?_) A
  letI : Field (K ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  exact Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec B

end GlobalTheory.CompanionTheory.SW
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MatrixTransvectionDiagonalDecompositionStatement
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_transvection_diagonal_decomposition : ∀ (K : Type) [CommRing K] [IsArtinianRing K] [IsReduced K] (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K), ∃ (L L' : List (Matrix.TransvectionStruct ι K)) (D : ι → K), A = (L.map Matrix.TransvectionStruct.toMatrix).prod * Matrix.diagonal D * (L'.map Matrix.TransvectionStruct.toMatrix).prod := by
  first | exact @GlobalTheory.CompanionTheory.SW.artinian_reduced_list_transvec_mul_diagonal_mul_list_transvec | exact GlobalTheory.CompanionTheory.SW.artinian_reduced_list_transvec_mul_diagonal_mul_list_transvec | (intros; apply GlobalTheory.CompanionTheory.SW.artinian_reduced_list_transvec_mul_diagonal_mul_list_transvec <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarInvariantUnderTransvection
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarInvariantUnderTransvection
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.Transv

theorem toMatrix_mulVec_apply {K ι : Type} [CommRing K] [Fintype ι] [DecidableEq ι]
    (t : Matrix.TransvectionStruct ι K) (x : ι → K) (k : ι) :
    (t.toMatrix *ᵥ x) k = if k = t.i then x k + t.c * x t.j else x k := by
  have h : t.toMatrix = 1 + Matrix.single t.i t.j t.c := rfl
  rw [h, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
  by_cases hk : k = t.i
  · subst hk
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
  · have : ∀ l, (Matrix.single t.i t.j t.c) k l = 0 := by
      intro l
      simp [Matrix.single_apply, Ne.symm hk]
    simp [Matrix.mulVec, dotProduct, this, hk]

theorem measurePreserving_pi {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
    {ι : Type} [Fintype ι] [DecidableEq ι] (ν : Measure K) [SigmaFinite ν]
    [ν.IsAddLeftInvariant] (t : Matrix.TransvectionStruct ι K) :
    MeasurePreserving (fun x : ι → K => t.toMatrix *ᵥ x)
      (Measure.pi fun _ : ι => ν) (Measure.pi fun _ : ι => ν) := by
  classical
  have hj : t.j ≠ t.i := t.hij.symm
  let p : ι → Prop := fun k => k ≠ t.i
  let B : Measure ({k // p k} → K) := Measure.pi fun _ => ν
  let A : Measure ({k // ¬ p k} → K) := Measure.pi fun _ => ν
  have hmp := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => ν) p
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => K) p
  let g : ({k // p k} → K) → ({k // ¬ p k} → K) → ({k // ¬ p k} → K) :=
    fun b a => (fun _ => t.c * b ⟨t.j, hj⟩) + a
  have hgm : Measurable (Function.uncurry g) := by
    refine measurable_pi_iff.2 fun k => ?_
    have h1 : Measurable fun q : ({k // p k} → K) × ({k // ¬ p k} → K) =>
        q.1 ⟨t.j, hj⟩ := (measurable_pi_apply _).comp measurable_fst
    have h2 : Measurable fun q : ({k // p k} → K) × ({k // ¬ p k} → K) =>
        q.2 k := (measurable_pi_apply _).comp measurable_snd
    exact (h1.const_mul t.c).add h2
  have hsk : MeasurePreserving (fun q : ({k // p k} → K) × ({k // ¬ p k} → K) => (id q.1, g q.1 q.2))
      (B.prod A) (B.prod A) := by
    refine (MeasurePreserving.id B).skew_product hgm (Filter.Eventually.of_forall fun b => ?_)
    exact map_add_left_eq_self A _
  have hall := hmp.symm.comp (hsk.comp hmp)
  have hfun : (fun x : ι → K => t.toMatrix *ᵥ x) =
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => K) p).symm ∘
        (fun q : ({k // p k} → K) × ({k // ¬ p k} → K) => (id q.1, g q.1 q.2)) ∘
          (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => K) p) := by
    funext x k
    rw [toMatrix_mulVec_apply]
    by_cases hk : k = t.i
    · subst hk
      have hnp : ¬ p t.i := fun h => h rfl
      simp [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, g, hnp, add_comm]
    · have hp : p k := hk
      simp [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hp, hk]
  rw [hfun]
  exact hall

theorem map_toMatrix_mulVec (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [LocallyCompactSpace K] [SecondCountableTopology K] [T2Space K] [MeasurableSpace K]
    [BorelSpace K] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : Measure (ι → K))
    [μ.IsAddHaarMeasure] (t : Matrix.TransvectionStruct ι K) :
    μ.map (fun x => t.toMatrix *ᵥ x) = μ := by
  let ν : Measure K := Measure.addHaar
  let P : Measure (ι → K) := Measure.pi fun _ : ι => ν
  haveI : P.IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hμ : μ = Measure.addHaarScalarFactor μ P • P := Measure.isAddLeftInvariant_eq_smul μ P
  have hP : MeasurePreserving (fun x => t.toMatrix *ᵥ x) P P := measurePreserving_pi ν t
  generalize Measure.addHaarScalarFactor μ P = c at hμ
  rw [hμ, Measure.map_smul c hP.measurable.aemeasurable, hP.map_eq]

end GlobalTheory.CompanionTheory.SW.Transv

theorem GlobalTheory.CompanionTheory.SW.transvection_map_addHaar : ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : Measure (ι → K)) [μ.IsAddHaarMeasure] (t : Matrix.TransvectionStruct ι K), μ.map (fun x => t.toMatrix *ᵥ x) = μ := by
  intro K _ _ _ _ _ _ _ _ ι _ _ μ _ t
  exact GlobalTheory.CompanionTheory.SW.Transv.map_toMatrix_mulVec K ι μ t
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarInvariantUnderTransvectionStatement
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_invariant_under_transvection : ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : Measure (ι → K)) [μ.IsAddHaarMeasure] (t : Matrix.TransvectionStruct ι K), μ.map (fun x => t.toMatrix *ᵥ x) = μ := by
  first | exact @GlobalTheory.CompanionTheory.SW.transvection_map_addHaar | exact GlobalTheory.CompanionTheory.SW.transvection_map_addHaar | (intros; apply GlobalTheory.CompanionTheory.SW.transvection_map_addHaar <;> assumption)
end
end

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.ModDet

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  [LocallyCompactSpace K] [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K]

theorem map_mul_unit (lam : Measure K) [lam.IsAddHaarMeasure] (u : Kˣ) :
    lam.map (fun y => (u : K) * y) = (distribHaarChar K u)⁻¹ • lam := by
  have hm : Measurable (fun y : K => (u : K) * y) :=
    (continuous_const.mul continuous_id).measurable
  ext s hs
  rw [Measure.map_apply hm hs, Measure.smul_apply, Measure.nnreal_smul_coe_apply, ← map_inv,
    distribHaarChar_mul lam u⁻¹ s]
  congr 1
  ext y
  simp [Set.mem_inv_smul_set_iff, Units.smul_def]

theorem pi_smul_const {ι : Type} [Fintype ι] (lam : Measure K) [SigmaFinite lam] (c : ι → ℝ≥0) :
    Measure.pi (fun i => c i • lam) = (∏ i, c i) • Measure.pi (fun _ : ι => lam) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
    ENNReal.ofNNReal_finsetProd]

theorem pi_map_diag {ι : Type} [Fintype ι] (lam : Measure K) [lam.IsAddHaarMeasure] (D : ι → Kˣ) :
    (Measure.pi fun _ : ι => lam).map (fun x i => (D i : K) * x i) =
      (∏ i, (distribHaarChar K (D i))⁻¹) • Measure.pi fun _ : ι => lam := by
  have hm : ∀ i, Measurable (fun y : K => (D i : K) * y) := fun i =>
    (continuous_const.mul continuous_id).measurable
  have hs : ∀ i, SigmaFinite (lam.map (fun y : K => (D i : K) * y)) := fun i => by
    rw [map_mul_unit]; infer_instance
  rw [Measure.pi_map_pi (fun i => (hm i).aemeasurable)]
  simp_rw [map_mul_unit]
  exact pi_smul_const lam _

theorem smul_cancel (lam : Measure K) [lam.IsAddHaarMeasure] {a b : ℝ≥0}
    (h : a • lam = b • lam) : a = b := by
  obtain ⟨C, hC, hn⟩ := exists_compact_mem_nhds (0 : K)
  have h0 : lam C ≠ 0 := (Measure.measure_pos_of_mem_nhds lam hn).ne'
  have h1 : lam C ≠ ∞ := hC.measure_lt_top.ne
  have e := congrArg (fun m : Measure K => m C) h
  simp only [Measure.smul_apply, Measure.nnreal_smul_coe_apply] at e
  exact ENNReal.coe_injective ((ENNReal.mul_left_inj h0 h1).1 e)

theorem map_transvections {ι : Type} [Fintype ι] [DecidableEq ι] (μ : Measure (ι → K))
    [μ.IsAddHaarMeasure] (L : List (Matrix.TransvectionStruct ι K)) :
    μ.map (fun x => (L.map Matrix.TransvectionStruct.toMatrix).prod *ᵥ x) = μ := by
  induction L with
  | nil => simp
  | cons t L ih =>
    have hm : ∀ M : Matrix ι ι K, Measurable (fun x : ι → K => M *ᵥ x) := fun M =>
      (continuous_const.matrix_mulVec continuous_id).measurable
    have e : (fun x : ι → K => ((t :: L).map Matrix.TransvectionStruct.toMatrix).prod *ᵥ x) =
        (fun x => t.toMatrix *ᵥ x) ∘
          (fun x => (L.map Matrix.TransvectionStruct.toMatrix).prod *ᵥ x) := by
      funext x
      simp [Matrix.mulVec_mulVec]
    rw [e, ← Measure.map_map (hm _) (hm _), ih]
    exact GlobalTheory.T.haar_invariant_under_transvection K ι μ t

theorem det_transvections {ι : Type} [Fintype ι] [DecidableEq ι]
    (L : List (Matrix.TransvectionStruct ι K)) :
    ((L.map Matrix.TransvectionStruct.toMatrix).prod).det = 1 := by
  induction L with
  | nil => simp
  | cons t L ih => simp [Matrix.det_mul, ih, Matrix.TransvectionStruct.det]

theorem map_mulVec_eq_smul : ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [LocallyCompactSpace K] [SecondCountableTopology K] [T2Space K] [MeasurableSpace K]
    [BorelSpace K] [IsArtinianRing K] [IsReduced K] (ι : Type) [Fintype ι] [DecidableEq ι]
    (μ : Measure (ι → K)) [μ.IsAddHaarMeasure] (lam : Measure K) [lam.IsAddHaarMeasure]
    (A : Matrix ι ι K), IsUnit A.det → ∀ c : ℝ≥0,
      lam.map (fun y => A.det * y) = c • lam → μ.map (fun x => A *ᵥ x) = c • μ := by
  intro K _ _ _ _ _ _ _ _ _ _ ι _ _ μ _ lam _ A hA c hc
  obtain ⟨L, L', D, hAeq⟩ := GlobalTheory.T.matrix_transvection_diagonal_decomposition K ι A
  have hdet : A.det = ∏ i, D i := by
    rw [hAeq, Matrix.det_mul, Matrix.det_mul, det_transvections, det_transvections,
      Matrix.det_diagonal, one_mul, mul_one]
  have hu : ∀ i, IsUnit (D i) := fun i => by
    have h := hA
    rw [hdet, ← Finset.mul_prod_erase Finset.univ D (Finset.mem_univ i)] at h
    exact isUnit_of_mul_isUnit_left h
  obtain ⟨Du, hDu⟩ : ∃ Du : ι → Kˣ, ∀ i, (Du i : K) = D i :=
    ⟨fun i => (hu i).unit, fun i => (hu i).unit_spec⟩
  have hcc : (∏ i, (distribHaarChar K (Du i))⁻¹) = c := by
    refine smul_cancel lam ?_
    rw [← hc, hdet]
    have e : (∏ i, D i) = ((∏ i, Du i : Kˣ) : K) := by
      simp [Units.coe_prod, hDu]
    rw [e, map_mul_unit, map_prod, Finset.prod_inv_distrib]
  have hμ := Measure.isAddLeftInvariant_eq_smul μ (Measure.pi fun _ : ι => lam)
  have hmd : Measurable (fun (x : ι → K) i => (Du i : K) * x i) :=
    (continuous_pi fun i => continuous_const.mul (continuous_apply i)).measurable
  have hdiag : μ.map (fun (x : ι → K) i => (Du i : K) * x i) = c • μ := by
    rw [hμ, Measure.map_smul, pi_map_diag, hcc, smul_comm]
    exact hmd.aemeasurable
  have hm : ∀ M : Matrix ι ι K, Measurable (fun x : ι → K => M *ᵥ x) := fun M =>
    (continuous_const.matrix_mulVec continuous_id).measurable
  have e : (fun x : ι → K => A *ᵥ x) =
      (fun x => (L.map Matrix.TransvectionStruct.toMatrix).prod *ᵥ x) ∘
        (fun (x : ι → K) i => (Du i : K) * x i) ∘
          (fun x => (L'.map Matrix.TransvectionStruct.toMatrix).prod *ᵥ x) := by
    funext x
    have hd : ∀ y : ι → K, (fun i => (Du i : K) * y i) = Matrix.diagonal D *ᵥ y := fun y => by
      funext i
      simp [Matrix.mulVec_diagonal, hDu]
    simp only [Function.comp_apply, hd, Matrix.mulVec_mulVec]
    rw [hAeq, Matrix.mul_assoc]
  rw [e, ← Measure.map_map (hm _) (hmd.comp (hm _)), ← Measure.map_map hmd (hm _),
    map_transvections μ L', hdiag, Measure.map_smul, map_transvections μ L]
  exact (hm _).aemeasurable

end GlobalTheory.CompanionTheory.SW.ModDet
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MapMulEqOfNormOne
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.NormOneHaar

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

def mulEquiv (u v : K) (h : u * v = 1) : K ≃ₜ+ K where
  toFun y := u * y
  invFun y := v * y
  left_inv y := by
    show v * (u * y) = y
    rw [← mul_assoc, mul_comm v u, h, one_mul]
  right_inv y := by
    show u * (v * y) = y
    rw [← mul_assoc, h, one_mul]
  map_add' x y := mul_add u x y
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

def invEquiv (σ : K →+* K) (hc : Continuous σ) (hi : ∀ y, σ (σ y) = y) : K ≃ₜ+ K where
  toFun := σ
  invFun := σ
  left_inv := hi
  right_inv := hi
  map_add' := map_add σ
  continuous_toFun := hc
  continuous_invFun := hc

variable [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]

theorem char_conj (σ : K →+* K) (hc : Continuous σ) (hi : ∀ y, σ (σ y) = y) (u v : K)
    (h : u * v = 1) (h' : σ u * σ v = 1) :
    addEquivAddHaarChar (mulEquiv (σ u) (σ v) h') = addEquivAddHaarChar (mulEquiv u v h) := by
  set s := invEquiv σ hc hi
  have e : mulEquiv (σ u) (σ v) h' = (s.trans (mulEquiv u v h)).trans s.symm := by
    ext y
    show σ u * y = σ (u * σ y)
    rw [map_mul, hi]
  rw [e, addEquivAddHaarChar_trans, addEquivAddHaarChar_trans, addEquivAddHaarChar_symm,
    mul_comm (addEquivAddHaarChar s), mul_assoc,
    mul_inv_cancel₀ (addEquivAddHaarChar_pos s).ne', mul_one]

theorem char_mul_eq_one (u v : K) (h : u * v = 1) (h' : v * u = 1) :
    addEquivAddHaarChar (mulEquiv u v h) * addEquivAddHaarChar (mulEquiv v u h') = 1 := by
  have e : (mulEquiv u v h).trans (mulEquiv v u h') = ContinuousAddEquiv.refl K := by
    ext y
    show v * (u * y) = y
    rw [← mul_assoc, h', one_mul]
  rw [← addEquivAddHaarChar_trans, e, addEquivAddHaarChar_refl]

theorem map_mul_eq_of_norm_one :
    ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
      [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K] (σ : K →+* K),
      Continuous σ → (∀ y, σ (σ y) = y) → ∀ (lam : Measure K) [lam.IsAddHaarMeasure] (u : K),
      u * σ u = 1 → lam.map (fun y => u * y) = lam := by
  intro K _ _ _ _ _ _ _ _ σ hc hi lam _ u hu
  have hu' : σ u * σ (σ u) = 1 := by rw [← map_mul, hu, map_one]
  have hu2 : σ u * u = 1 := by rw [mul_comm, hu]
  have hconj := char_conj σ hc hi u (σ u) hu hu'
  have hprod := char_mul_eq_one u (σ u) hu hu2
  have hsame : mulEquiv (σ u) u hu2 = mulEquiv (σ u) (σ (σ u)) hu' := by
    ext y
    rfl
  rw [hsame, hconj] at hprod
  have hone : addEquivAddHaarChar (mulEquiv u (σ u) hu) = 1 := by
    have h2 : addEquivAddHaarChar (mulEquiv u (σ u) hu) ^ 2 = 1 := by rw [sq, hprod]
    exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 h2
  have hmap := addEquivAddHaarChar_smul_map lam (mulEquiv u (σ u) hu)
  rw [hone, one_smul] at hmap
  exact hmap

end GlobalTheory.CompanionTheory.SW.NormOneHaar
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryActionPreservesHaarLocal
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.HInv

theorem det_mul_conj_eq_one {A : Type} [CommRing A] {m : Type} [Fintype m] [DecidableEq m]
    (τ : A →+* A) (g J : Matrix m m A) (hg : cT τ g * J * g = J) (hJ : IsUnit J.det) :
    g.det * τ g.det = 1 := by
  have hc : (cT τ g).det = τ g.det := by
    rw [cT, Matrix.det_transpose, RingHom.map_det, RingHom.mapMatrix_apply]
  have h := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, hc] at h
  apply hJ.mul_left_cancel
  linear_combination h

theorem map_tuple_eq {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [LocallyCompactSpace K] [SecondCountableTopology K] [T2Space K] [MeasurableSpace K]
    [BorelSpace K] [IsArtinianRing K] [IsReduced K] (τ : K →+* K) (hc : Continuous τ)
    (hi : ∀ y, τ (τ y) = y) {M n : ℕ} (A : Matrix (Fin M) (Fin M) K)
    (hA : A.det * τ A.det = 1) (μ : Measure (Fin n → Fin M → K)) [μ.IsAddHaarMeasure] :
    μ.map (fun X a => A *ᵥ X a) = μ := by
  let lam : Measure K := Measure.addHaar
  have hl : lam.map (fun y => A.det * y) = lam :=
    NormOneHaar.map_mul_eq_of_norm_one K τ hc hi lam _ hA
  let μ0 : Measure (Fin M → K) := Measure.pi fun _ => lam
  have hdet : IsUnit A.det := IsUnit.of_mul_eq_one _ hA
  have h0 : μ0.map (fun x => A *ᵥ x) = μ0 := by
    have := ModDet.map_mulVec_eq_smul K (Fin M) μ0 lam A hdet 1 (by simpa using hl)
    simpa using this
  let P : Measure (Fin n → Fin M → K) := Measure.pi fun _ => μ0
  have hmeas : Measurable (fun x : Fin M → K => A *ᵥ x) :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  haveI hs : SigmaFinite (μ0.map (fun x => A *ᵥ x)) := by
    rw [h0]; infer_instance
  have hP : P.map (fun X a => A *ᵥ X a) = P := by
    have := Measure.pi_map_pi (μ := fun _ : Fin n => μ0) (f := fun _ x => A *ᵥ x)
      (fun _ => hmeas.aemeasurable)
    simpa only [h0] using this
  have e := Measure.isAddLeftInvariant_eq_smul μ P
  have htuple : Measurable (fun (X : Fin n → Fin M → K) a => A *ᵥ X a) :=
    Measurable.of_eval fun a => hmeas.comp (measurable_pi_apply a)
  rw [e, Measure.map_smul _ htuple.aemeasurable, hP]

theorem map_actW_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R],
    IsLocR R → ∀ (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure →
    ∀ h : HA R σ J, μ.map (actW R σ J h) = μ := by
  intro F E _ _ _ _ _ σ hCM M J hJ R _ _ _ _ _ hR n μ hμ h
  obtain ⟨r1, r2, r3, r4, r5, r6, -, -⟩ := hR
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI := r5
  haveI := r6
  obtain ⟨t1, t2, t3, t4, tc, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  obtain ⟨a1, a2, -, ai, -⟩ := KAlg.algebra_tensor_invol F E σ hCM R
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := a1
  haveI := a2
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hJu : IsUnit (JR (F := F) R J).det := by
    have e : (JR (F := F) R J).det = inclR (F := F) R J.det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, JR]
    rw [e]
    exact (IsUnit.mk0 _ hJ.2).map (inclR (F := F) R)
  have hg : cT (sigR R σ) ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *
      JR (F := F) R J * ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR (F := F) R J :=
    (show (h : HR R σ J).1 ∈ HR R σ J from (h : HR R σ J).2)
  exact map_tuple_eq (sigR R σ) tc ai _ (det_mul_conj_eq_one _ _ _ hg hJu) μ

end GlobalTheory.CompanionTheory.SW.HInv
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryActionPreservesHaarLocalStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_action_preserves_haar_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ∀ h : HA R σ J, μ.map (actW R σ J h) = μ := by
  first | exact @GlobalTheory.CompanionTheory.SW.HInv.map_actW_eq | exact GlobalTheory.CompanionTheory.SW.HInv.map_actW_eq | (intros; apply GlobalTheory.CompanionTheory.SW.HInv.map_actW_eq <;> assumption)
end
