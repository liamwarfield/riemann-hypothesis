module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeUNuInv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsLv
noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open Formalism.UG (cT bc)
open scoped TensorProduct NNReal

namespace GlobalTheory.SphEis.Inhabitant

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n j m : ℕ} {J : Matrix (Fin n) (Fin n) E} {C D : Matrix (Fin n) (Fin j) E}
  {Z : Matrix (Fin n) (Fin m) E} {J₀ : Matrix (Fin m) (Fin m) E}

theorem existsUnique_isLv (f : Fr σ J C D Z J₀) :
    ∃ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv ∧ Function.Injective lv ∧
      ∀ lv', IsLv σ J C D Z lv' → lv' = lv :=
  ⟨SphEisModel.lv f, SphEisModel.isLv_lv f, SphEisModel.isLv_injective f (SphEisModel.isLv_lv f),
    fun _ h => SphEisModel.isLv_unique f h (SphEisModel.isLv_lv f)⟩

end GlobalTheory.SphEis.Inhabitant

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneAdelicGLLocallyCompactDiscreteFiniteCovol
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogTensorIdeleAbsDetExpScalarCentreEqMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogTensorIdeleAbsDetExpScalarCentreEqMul
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.GLOneVol

open GroundTheory.Global GroundTheory.Global.AdeleBaseChange GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele GlobalTheory.IdeleCovolume GlobalTheory.OneRep.SplitTwist

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem idl_det_eq (k : ℕ) (g : GL (Fin k) (AF F ⊗[F] E)) :
    GlobalTheory.TateConv.idl F E (Matrix.GeneralLinearGroup.det g) = Matrix.GeneralLinearGroup.det (glTens F E k g) := by
  ext
  change GlobalTheory.TateConv.tens F E (g : Matrix (Fin k) (Fin k) (AF F ⊗[F] E)).det =
    ((GlobalTheory.TateConv.tens F E).toRingEquiv.toRingHom.mapMatrix (g : Matrix (Fin k) (Fin k) (AF F ⊗[F] E))).det
  exact RingHom.map_det (GlobalTheory.TateConv.tens F E).toRingEquiv.toRingHom _

variable [_root_.NumberField.IsTotallyComplex E]

theorem absE_det_cR (k : ℕ) (t : ℝ) :
    ((absE F E (Matrix.GeneralLinearGroup.det (cR F E k t)) : ℝ≥0) : ℝ) =
      ideleNorm (E := E) (Matrix.GeneralLinearGroup.det (GlobalTheory.UnitaryBC.splitCentre E k t)) := by
  rw [GlobalTheory.TateConv.absE_eq, idl_det_eq, glTens_cR]
  rfl

end GlobalTheory.GLOneVol

theorem GlobalTheory.GLOneVol.log_absE_det_cR : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [_root_.NumberField.IsTotallyComplex E] (k : ℕ), 1 ≤ k → ∃ a : ℝ, a ≠ 0 ∧ ∀ t : ℝ,
      Real.log ((absE F E (Matrix.GeneralLinearGroup.det (GlobalTheory.GLOneVol.cR F E k t)) : ℝ≥0) : ℝ) = a * t := by
  intro F E _ _ _ _ _ _ k hk
  let D : ℝ →+ ℝ := AddMonoidHom.mk'
    (fun t => Real.log (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm (E := E)
      (Matrix.GeneralLinearGroup.det (GlobalTheory.UnitaryBC.splitCentre E k t)))) fun x y => by
      rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_add, map_mul, map_mul,
        Real.log_mul (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm_ne_zero _) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm_ne_zero _)]
  have hD : Continuous D :=
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_ideleNorm.comp (Matrix.GeneralLinearGroup.continuous_det.comp
      GlobalTheory.OneRep.SplitTwist.continuous_splitCentre)).log fun _ => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm_ne_zero _
  have hDt : ∀ t, D t = t * D 1 := fun t => by simpa using map_real_smul D hD t 1
  have hD1 : 0 < D 1 := by
    change 0 < Real.log (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm (E := E)
      (Matrix.GeneralLinearGroup.det (GlobalTheory.UnitaryBC.splitCentre E k 1)))
    rw [GlobalTheory.CuspRep.CuspidalL2GL.det_splitCentre_one, map_pow, Real.log_pow]
    exact mul_pos (by exact_mod_cast hk) (Real.log_pos (GlobalTheory.IdeleCovolume.one_lt_ideleNorm_eIdele E))
  refine ⟨D 1, hD1.ne', fun t => ?_⟩
  rw [GlobalTheory.GLOneVol.absE_det_cR, mul_comm]
  exact hDt t
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogTensorIdeleAbsDetExpScalarCentreEqMulStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_tensorIdeleAbs_det_expScalarCentre_eq_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex E] (k : ℕ), 1 ≤ k → ∃ a : ℝ, a ≠ 0 ∧ ∀ t : ℝ, Real.log ((absE F E (Matrix.GeneralLinearGroup.det (GlobalTheory.GLOneVol.cR F E k t)) : ℝ≥0) : ℝ) = a * t := by
  first | exact @GlobalTheory.GLOneVol.log_absE_det_cR | exact GlobalTheory.GLOneVol.log_absE_det_cR | (intros; apply GlobalTheory.GLOneVol.log_absE_det_cR <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeGLAdelicTensorRationalTimesExpInt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeGLAdelicTensorRationalTimesExpInt
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.GLOneVol

open GroundTheory.Global GroundTheory.Global.AdeleBaseChange GlobalTheory.CuspRep.CuspidalL2GL

theorem symm_mem_latR {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [_root_.NumberField.IsTotallyComplex E] {k : ℕ} {g : GlobalTheory.CuspRep.GA E k} (hg : g ∈ GlobalTheory.UnitaryBC.latticeGL E k) :
    (glTens F E k).symm g ∈ latR F E k := by
  obtain ⟨γ, n, rfl⟩ := mem_latticeGL_iff.1 hg
  rw [map_mul, map_zpow]
  refine mul_mem (Subgroup.mem_sup_left ⟨γ, ?_⟩) (zpow_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) n)
  apply (glTens F E k).injective
  rw [glTens_bc, ContinuousMulEquiv.apply_symm_apply]

def latEquiv (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [_root_.NumberField.IsTotallyComplex E] (k : ℕ) : GlobalTheory.UnitaryBC.latticeGL E k ≃ latR F E k where
  toFun g := ⟨(glTens F E k).symm g, symm_mem_latR g.2⟩
  invFun x := ⟨glTens F E k x, latR_le k x.2⟩
  left_inv g := Subtype.ext ((glTens F E k).apply_symm_apply _)
  right_inv x := Subtype.ext ((glTens F E k).symm_apply_apply _)

theorem finvol_tens : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [_root_.NumberField.IsTotallyComplex E] (k : ℕ) [MeasurableSpace (GL (Fin k) (AF F ⊗[F] E))]
    [BorelSpace (GL (Fin k) (AF F ⊗[F] E))] (ν : Measure (GL (Fin k) (AF F ⊗[F] E)))
    (D : Set (GL (Fin k) (AF F ⊗[F] E))), ν.IsHaarMeasure → IsFundamentalDomain (latR F E k) D ν → ν D ≠ ⊤ := by
  intro F E _ _ _ _ _ _ k _ _ ν D hν hD
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  let f := (glTens F E k).toHomeomorph.toMeasurableEquiv
  let μ : Measure (GlobalTheory.CuspRep.GA E k) := ν.map f
  haveI : μ.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map ν (glTens F E k)
  have hq : Measure.QuasiMeasurePreserving f.symm μ ν :=
    (MeasurePreserving.mk f.symm.measurable (f.map_symm_map)).quasiMeasurePreserving
  have hD' : IsFundamentalDomain (GlobalTheory.UnitaryBC.latticeGL E k) (f '' D) μ :=
    hD.image_of_equiv f.toEquiv hq (latEquiv F E k) fun g x => by
      change glTens F E k ((glTens F E k).symm g * x) = g * glTens F E k x
      rw [map_mul, ContinuousMulEquiv.apply_symm_apply]
  have h1 : ν D = μ (f '' D) := by
    rw [f.map_apply, f.preimage_image]
  rw [h1, ← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hD']
  haveI := (GlobalTheory.CovolGL.finvol E k μ).1
  exact measure_ne_top _ _

end GlobalTheory.GLOneVol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeGLAdelicTensorRationalTimesExpIntStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_covolume_GL_adelicTensor_rationalTimesExpInt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex E] (k : ℕ) [MeasurableSpace (GL (Fin k) (AF F ⊗[F] E))] [BorelSpace (GL (Fin k) (AF F ⊗[F] E))] (ν : Measure (GL (Fin k) (AF F ⊗[F] E))) (D : Set (GL (Fin k) (AF F ⊗[F] E))), ν.IsHaarMeasure → IsFundamentalDomain (GlobalTheory.GLOneVol.latR F E k) D ν → ν D ≠ ⊤ := by
  first | exact @GlobalTheory.GLOneVol.finvol_tens | exact GlobalTheory.GLOneVol.finvol_tens | (intros; apply GlobalTheory.GLOneVol.finvol_tens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeKernelOfSplitCentralOneParam
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeKernelOfSplitCentralOneParam
open MeasureTheory Topology

namespace GlobalTheory.KernelCovolume

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

lemma c_zero {c : ℝ → G} (hca : ∀ x y, c (x + y) = c x * c y) : c 0 = 1 :=
  mul_left_cancel (a := c 0) (by rw [mul_one, ← hca, add_zero])

lemma c_neg {c : ℝ → G} (hca : ∀ x y, c (x + y) = c x * c y) (r : ℝ) : (c r)⁻¹ = c (-r) :=
  inv_eq_of_mul_eq_one_right (by rw [← hca, add_neg_cancel, c_zero hca])

def cHom (c : ℝ → G) (hca : ∀ x y, c (x + y) = c x * c y) : Multiplicative ℝ →* G where
  toFun x := c (Multiplicative.toAdd x)
  map_one' := c_zero hca
  map_mul' x y := hca _ _

lemma c_int {c : ℝ → G} (hca : ∀ x y, c (x + y) = c x * c y) (n : ℤ) : c n = c 1 ^ n := by
  have h := map_zpow (cHom c hca) (Multiplicative.ofAdd (1:ℝ)) n
  rw [← ofAdd_zsmul, zsmul_one] at h
  exact h

lemma mem_of_split {H : Subgroup G} {s : G → ℝ} {c : ℝ → G}
    (hsa : ∀ g h, s (g * h) = s g + s h) (hsc : ∀ t, s (c t) = t) (hH : ∀ g, g ∈ H ↔ s g = 0)
    (g : G) : g * c (-s g) ∈ H := by
  rw [hH, hsa, hsc]; ring

def splitHomeo {H : Subgroup G} {s : G → ℝ} {c : ℝ → G} (hs : Continuous s)
    (hsa : ∀ g h, s (g * h) = s g + s h) (hc : Continuous c)
    (hca : ∀ x y, c (x + y) = c x * c y) (hsc : ∀ t, s (c t) = t) (hH : ∀ g, g ∈ H ↔ s g = 0) :
    H × ℝ ≃ₜ G where
  toFun p := (p.1 : G) * c p.2
  invFun g := (⟨g * c (-s g), mem_of_split hsa hsc hH g⟩, s g)
  left_inv p := by
    rcases p with ⟨⟨h, hh⟩, t⟩
    have h0 : s h = 0 := (hH h).1 hh
    have e : s (h * c t) = t := by rw [hsa, hsc, h0, zero_add]
    refine Prod.ext (Subtype.ext ?_) ?_
    · show h * c t * c (-s (h * c t)) = h
      rw [e, mul_assoc, ← hca, add_neg_cancel, c_zero hca, mul_one]
    · exact e
  right_inv g := by
    show g * c (-s g) * c (s g) = g
    rw [mul_assoc, ← hca, neg_add_cancel, c_zero hca, mul_one]
  continuous_toFun := (continuous_subtype_val.comp continuous_fst).mul (hc.comp continuous_snd)
  continuous_invFun := (Continuous.subtype_mk (continuous_id.mul (hc.comp hs.neg)) _).prodMk hs

end GlobalTheory.KernelCovolume

open scoped Pointwise

open GlobalTheory.KernelCovolume in
theorem GlobalTheory.finiteCovolume_kernel : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (H Γ Λ : Subgroup G) (s : G → ℝ) (c : ℝ → G), Continuous s → (∀ g h, s (g * h) = s g + s h) → Continuous c → (∀ x y, c (x + y) = c x * c y) → (∀ t g, c t * g = g * c t) → (∀ t, s (c t) = t) → (∀ g, g ∈ H ↔ s g = 0) → Γ ≤ H → Λ = Γ ⊔ Subgroup.zpowers (c 1) → DiscreteTopology Λ → (∀ (ν : Measure G) (D : Set G), ν.IsHaarMeasure → IsFundamentalDomain Λ D ν → ν D ≠ ⊤) → ∀ (π : Measure H) (D : Set H), π.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf H) D π → π D ≠ ⊤ := by
  intro G _ _ _ _ _ _ _ _ H Γ Λ s c hs hsa hc hca hcc hsc hH hΓ hΛ _hdisc hfin π D hπ hD
  have hcl : IsClosed (H : Set G) := by
    have : (H : Set G) = s ⁻¹' {0} := by ext g; exact hH g
    rw [this]; exact isClosed_singleton.preimage hs
  haveI : LocallyCompactSpace H := hcl.locallyCompactSpace
  haveI : SigmaCompactSpace H := hcl.sigmaCompactSpace
  haveI : SigmaFinite π := inferInstance
  set φ : H × ℝ ≃ₜ G := GlobalTheory.KernelCovolume.splitHomeo hs hsa hc hca hsc hH with hφdef
  have hφ : ∀ p : H × ℝ, φ p = (p.1 : G) * c p.2 := fun p => rfl
  set μ0 : Measure (H × ℝ) := π.prod volume with hμ0
  set ν : Measure G := μ0.map φ with hνdef
  have hνapp : ∀ A, ν A = μ0 (φ ⁻¹' A) := fun A => φ.toMeasurableEquiv.map_apply A
  have hmulφ : ∀ (γ : H) (r : ℝ) (p : H × ℝ), (γ : G) * c r * φ p = φ (γ * p.1, r + p.2) := by
    intro γ r p
    simp only [hφ, Subgroup.coe_mul, hca, mul_assoc]
    rw [← mul_assoc (c r) (p.1 : G), hcc r, mul_assoc]

  haveI : (Subgroup.zpowers (c 1)).Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hcomm : Commute ((c 1) ^ k) g := (Commute.zpow_left (hcc 1 g) k)
    rw [hcomm.symm.eq, mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.zpow_mem_zpowers _ _⟩
  have hdec : ∀ l ∈ Λ, ∃ γ ∈ Γ, ∃ n : ℤ, l = γ * c n := by
    intro l hl
    rw [hΛ] at hl
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hl
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact ⟨y, hy, n, by rw [GlobalTheory.KernelCovolume.c_int hca]⟩
  have hmemΛ : ∀ γ ∈ Γ, ∀ n : ℤ, γ * c n ∈ Λ := by
    intro γ hγ n
    rw [hΛ, GlobalTheory.KernelCovolume.c_int hca]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hγ)
      (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ _))

  have hνHaar : ν.IsHaarMeasure := by
    haveI : IsFiniteMeasureOnCompacts ν := Measure.IsFiniteMeasureOnCompacts.map μ0 φ
    haveI : ν.IsOpenPosMeasure := φ.continuous.isOpenPosMeasure_map φ.surjective
    haveI : ν.IsMulLeftInvariant := ⟨fun g => by
      obtain ⟨p0, rfl⟩ := φ.surjective g
      ext A hA
      rw [Measure.map_apply (measurable_const_mul _) hA, hνapp, hνapp]
      have hpre : φ ⁻¹' ((fun x => φ p0 * x) ⁻¹' A) =
          (Prod.map (fun h : H => p0.1 * h) (fun t : ℝ => p0.2 + t)) ⁻¹' (φ ⁻¹' A) := by
        ext p
        simp only [Set.mem_preimage, Prod.map]
        rw [show φ p0 = (p0.1 : G) * c p0.2 from rfl, hmulφ]
      have hT : μ0.map (Prod.map (fun h : H => p0.1 * h) (fun t : ℝ => p0.2 + t)) = μ0 := by
        rw [hμ0, ← Measure.map_prod_map π volume (measurable_const_mul _) (measurable_const_add _),
          map_mul_left_eq_self, map_add_left_eq_self]
      rw [hpre, ← Measure.map_apply ((measurable_const_mul _).prodMap (measurable_const_add _))
        (φ.measurable hA), hT]⟩
    exact ⟨⟩

  set S : Set (H × ℝ) := D ×ˢ Set.Ico (0:ℝ) 1 with hS
  set D' : Set G := φ.symm ⁻¹' S with hD'
  have hφD' : φ ⁻¹' D' = S := by ext p; simp [hD']
  have hsub : ∀ (l : Λ) (γ : G) (hγ : γ ∈ Γ) (n : ℤ), (l : G) = γ * c n → ∀ p : H × ℝ,
      φ p ∈ l • D' → (⟨γ, hΓ hγ⟩ : H)⁻¹ * p.1 ∈ D ∧ ((-n : ℤ) : ℝ) + p.2 ∈ Set.Ico (0:ℝ) 1 := by
    intro l γ hγ n e p hp
    rw [Set.mem_smul_set_iff_inv_smul_mem] at hp
    have hx : l⁻¹ • φ p = φ ((⟨γ, hΓ hγ⟩ : H)⁻¹ * p.1, ((-n : ℤ) : ℝ) + p.2) := by
      rw [← hmulφ, Subgroup.smul_def, smul_eq_mul]
      congr 1
      simp only [Subgroup.coe_inv, e, mul_inv_rev, GlobalTheory.KernelCovolume.c_neg hca, Int.cast_neg]
      exact hcc _ _
    rw [hx] at hp
    simpa [hD', hS] using hp
  have hFD : IsFundamentalDomain Λ D' ν := by
    refine { nullMeasurableSet := ?_, ae_covers := ?_, aedisjoint := ?_ }
    · exact (hD.nullMeasurableSet.prod measurableSet_Ico.nullMeasurableSet).preimage
        (φ.toMeasurableEquiv.quasiMeasurePreserving_symm μ0)
    · rw [hνdef, show (⇑φ : H × ℝ → G) = ⇑φ.toMeasurableEquiv from rfl,
        φ.toMeasurableEquiv.measurableEmbedding.ae_map_iff]
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae hD.ae_covers] with p hp
      obtain ⟨γ, hγ⟩ := hp
      have hγΓ : ((γ : H) : G) ∈ Γ := Subgroup.mem_subgroupOf.1 γ.2
      refine ⟨⟨((γ : H) : G) * c ((-⌊p.2⌋ : ℤ) : ℝ), hmemΛ _ hγΓ _⟩, ?_⟩
      rw [Subgroup.smul_def, smul_eq_mul]
      show _ ∈ φ.symm ⁻¹' S
      rw [Set.mem_preimage, show (φ.toMeasurableEquiv p) = φ p from rfl, hmulφ, φ.symm_apply_apply]
      have hfr : ((-⌊p.2⌋ : ℤ) : ℝ) + p.2 = Int.fract p.2 := by
        rw [Int.cast_neg, Int.fract]; ring
      rw [hfr]
      exact Set.mk_mem_prod hγ ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    · intro l1 l2 hne
      obtain ⟨γ1, hγ1, n1, e1⟩ := hdec l1 l1.2
      obtain ⟨γ2, hγ2, n2, e2⟩ := hdec l2 l2.2
      show ν ((l1 • D') ∩ (l2 • D')) = 0
      rw [hνapp]
      by_cases hn : n1 = n2
      · subst hn
        have hγne : γ1 ≠ γ2 := by
          rintro rfl; exact hne (Subtype.ext (e1.trans e2.symm))
        let g1 : Γ.subgroupOf H := ⟨⟨γ1, hΓ hγ1⟩, Subgroup.mem_subgroupOf.2 hγ1⟩
        let g2 : Γ.subgroupOf H := ⟨⟨γ2, hΓ hγ2⟩, Subgroup.mem_subgroupOf.2 hγ2⟩
        have hg : g1 ≠ g2 := fun h => hγne (congrArg (fun x : Γ.subgroupOf H => ((x : H) : G)) h)
        have h0 : π (g1 • D ∩ g2 • D) = 0 := hD.aedisjoint hg
        refine measure_mono_null (t := (g1 • D ∩ g2 • D) ×ˢ Set.univ) ?_ ?_
        · rintro p ⟨hp1, hp2⟩
          refine Set.mk_mem_prod ⟨?_, ?_⟩ (Set.mem_univ _)
          · rw [Set.mem_smul_set_iff_inv_smul_mem]; exact (hsub l1 γ1 hγ1 n1 e1 p hp1).1
          · rw [Set.mem_smul_set_iff_inv_smul_mem]; exact (hsub l2 γ2 hγ2 n1 e2 p hp2).1
        · rw [hμ0, Measure.prod_prod, h0, zero_mul]
      · refine measure_mono_null (t := ∅) ?_ measure_empty
        rintro p ⟨hp1, hp2⟩
        have a1 := (hsub l1 γ1 hγ1 n1 e1 p hp1).2
        have a2 := (hsub l2 γ2 hγ2 n2 e2 p hp2).2
        simp only [Set.mem_Ico, Int.cast_neg] at a1 a2
        have b1 : (n1 : ℝ) < n2 + 1 := by linarith
        have b2 : (n2 : ℝ) < n1 + 1 := by linarith
        have c1 : n1 < n2 + 1 := by exact_mod_cast b1
        have c2 : n2 < n1 + 1 := by exact_mod_cast b2
        exact absurd (by omega : n1 = n2) hn
  have hfinν := hfin ν D' hνHaar hFD
  have hνD' : ν D' = π D := by
    rw [hνapp, hφD', hS, hμ0, Measure.prod_prod, Real.volume_Ico, sub_zero, ENNReal.ofReal_one,
      mul_one]
  rwa [hνD'] at hfinν
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeKernelOfSplitCentralOneParamStatement
open MeasureTheory Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteCovolume_kernel_of_split_central_oneParam : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (H Γ Λ : Subgroup G) (s : G → ℝ) (c : ℝ → G), Continuous s → (∀ g h, s (g * h) = s g + s h) → Continuous c → (∀ x y, c (x + y) = c x * c y) → (∀ t g, c t * g = g * c t) → (∀ t, s (c t) = t) → (∀ g, g ∈ H ↔ s g = 0) → Γ ≤ H → Λ = Γ ⊔ Subgroup.zpowers (c 1) → DiscreteTopology Λ → (∀ (ν : Measure G) (D : Set G), ν.IsHaarMeasure → IsFundamentalDomain Λ D ν → ν D ≠ ⊤) → ∀ (π : Measure H) (D : Set H), π.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf H) D π → π D ≠ ⊤ := by
  first | exact @GlobalTheory.finiteCovolume_kernel | exact GlobalTheory.finiteCovolume_kernel | (intros; apply GlobalTheory.finiteCovolume_kernel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneAdelicGLLocallyCompactDiscreteFiniteCovol
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

noncomputable section

open GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.GLOneVol

namespace GlobalTheory.GLOneVol

section Help

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_bc {k : ℕ} (γ : GL (Fin k) E) :
    Matrix.GeneralLinearGroup.det (bc (inclR (F := F) (AF F)) γ : GL (Fin k) (AF F ⊗[F] E)) =
      Units.map (inclR (F := F) (AF F)).toMonoidHom (Matrix.GeneralLinearGroup.det γ) :=
  Units.ext (RingHom.map_det _ _).symm

theorem absE_pos (x : (AF F ⊗[F] E)ˣ) : 0 < (absE F E x : ℝ) := by
  have h : absE F E x * absE F E x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have : absE F E x ≠ 0 := fun h0 => by rw [h0, zero_mul] at h; exact zero_ne_one h
  exact_mod_cast pos_iff_ne_zero.2 this

end Help

theorem glOne_finvol : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (k : ℕ), LocallyCompactSpace ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker ∧ SecondCountableTopology ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker ∧ DiscreteTopology ((bc (inclR (F := F) (AF F)) : GL (Fin k) E →* GL (Fin k) (AF F ⊗[F] E)).range.subgroupOf ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker) ∧ ∀ [MeasurableSpace (GL (Fin k) (AF F ⊗[F] E))] [BorelSpace (GL (Fin k) (AF F ⊗[F] E))] (π : Measure ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker) (DM : Set ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker), π.IsHaarMeasure → IsFundamentalDomain ((bc (inclR (F := F) (AF F)) : GL (Fin k) E →* GL (Fin k) (AF F ⊗[F] E)).range.subgroupOf ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker) DM π → π DM ≠ ⊤ := by
  intro F E _ _ _ _ _ σ hCM k
  haveI : IsTotallyComplex E := hCM.2.1
  obtain ⟨hTR, hT2⟩ := GlobalTheory.StdPar.ring_facts (F := F) (E := E)
  set H := ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker with hHdef
  set Γ := (bc (inclR (F := F) (AF F)) : GL (Fin k) E →* GL (Fin k) (AF F ⊗[F] E)).range with hΓdef
  have hemb := (glTens F E k).toHomeomorph.isClosedEmbedding
  haveI : LocallyCompactSpace (GL (Fin k) (AF F ⊗[F] E)) := hemb.locallyCompactSpace
  haveI : SecondCountableTopology (GL (Fin k) (AF F ⊗[F] E)) := hemb.isEmbedding.secondCountableTopology
  haveI : T2Space (GL (Fin k) (AF F ⊗[F] E)) := hemb.isEmbedding.t2Space
  have hcont : Continuous fun g : GL (Fin k) (AF F ⊗[F] E) => absE F E (Matrix.GeneralLinearGroup.det g) :=
    GlobalTheory.Doubling.continuous_absE.comp Matrix.GeneralLinearGroup.continuous_det
  have hcl : IsClosed (H : Set (GL (Fin k) (AF F ⊗[F] E))) := isClosed_eq hcont continuous_const
  haveI : LocallyCompactSpace H := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hΓH : Γ ≤ H := by
    rintro _ ⟨γ, rfl⟩
    change absE F E (Matrix.GeneralLinearGroup.det _) = 1
    rw [det_bc]
    exact GlobalTheory.Doubling.absE_inclR _
  have hΓΛ : Γ ≤ latR F E k := le_sup_left
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · exact DiscreteTopology.of_continuous_injective
      (f := fun x : Γ.subgroupOf H => (⟨x.1.1, hΓΛ x.2⟩ : latR F E k))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      (fun x y h => by
        apply Subtype.ext; apply Subtype.ext
        exact congrArg (fun z : latR F E k => (z : GL (Fin k) (AF F ⊗[F] E))) h)
  · intro _ _ π DM hπ hDM
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · haveI : Subsingleton H := inferInstance
      haveI : CompactSpace H := inferInstance
      exact ((measure_mono (Set.subset_univ DM)).trans_lt (isCompact_univ.measure_lt_top)).ne
    obtain ⟨a, ha, hs⟩ := GlobalTheory.T.log_tensorIdeleAbs_det_expScalarCentre_eq_mul F E k hk
    let s : GL (Fin k) (AF F ⊗[F] E) → ℝ := fun g => Real.log (absE F E (Matrix.GeneralLinearGroup.det g) : ℝ) / a
    refine GlobalTheory.T.finiteCovolume_kernel_of_split_central_oneParam _ H Γ (latR F E k) s (cR F E k) ?_ ?_ (continuous_cR k) (cR_add k) (cR_comm k) ?_ ?_ hΓH rfl
      inferInstance (fun ν D hν hD => GlobalTheory.T.finite_covolume_GL_adelicTensor_rationalTimesExpInt F E k ν D hν hD) π DM hπ hDM
    · exact ((NNReal.continuous_coe.comp hcont).log fun g => (absE_pos _).ne').div_const _
    · intro g h
      simp only [s, map_mul, NNReal.coe_mul]
      rw [Real.log_mul (absE_pos _).ne' (absE_pos _).ne', add_div]
    · intro t
      simp only [s, hs t]
      field_simp
    · intro g
      simp only [s, div_eq_zero_iff, ha, or_false, hHdef, MonoidHom.mem_ker, MonoidHom.comp_apply]
      rw [Real.log_eq_zero]
      have := absE_pos (Matrix.GeneralLinearGroup.det g)
      constructor
      · intro h; right; left; rw [h]; rfl
      · rintro (h | h | h)
        · linarith
        · exact_mod_cast h
        · linarith

end GlobalTheory.GLOneVol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneAdelicGLLocallyCompactDiscreteFiniteCovolStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normOneAdelicGL_locallyCompact_discrete_finiteCovolume : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (k : ℕ), LocallyCompactSpace ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker ∧ SecondCountableTopology ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker ∧ DiscreteTopology ((bc (inclR (F := F) (AF F)) : GL (Fin k) E →* GL (Fin k) (AF F ⊗[F] E)).range.subgroupOf ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker) ∧ ∀ [MeasurableSpace (GL (Fin k) (AF F ⊗[F] E))] [BorelSpace (GL (Fin k) (AF F ⊗[F] E))] (π : Measure ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker) (DM : Set ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker), π.IsHaarMeasure → IsFundamentalDomain ((bc (inclR (F := F) (AF F)) : GL (Fin k) E →* GL (Fin k) (AF F ⊗[F] E)).range.subgroupOf ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker) DM π → π DM ≠ ⊤ := by
  first | exact @GlobalTheory.GLOneVol.glOne_finvol | exact GlobalTheory.GLOneVol.glOne_finvol | (intros; apply GlobalTheory.GLOneVol.glOne_finvol <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicFrameDecompositionOfWittFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicFrameDecompositionOfWittFrame
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

namespace GlobalTheory.FrameExt

theorem idem_factor {K : Type} [Field K] {n : ℕ} (Q : Matrix (Fin n) (Fin n) K) (hQ : Q * Q = Q) :
    ∃ (m : ℕ) (Z : Matrix (Fin n) (Fin m) K) (C : Matrix (Fin m) (Fin n) K), Z * C = Q ∧ C * Z = 1 := by
  let W := LinearMap.range Q.mulVecLin
  let b := Module.finBasis K W
  have key : ∀ w : W, Q.mulVecLin.rangeRestrict (w : Fin n → K) = w := by
    rintro ⟨w, v, rfl⟩
    apply Subtype.ext
    simp [Matrix.mulVec_mulVec, hQ]
  refine ⟨Module.finrank K W, LinearMap.toMatrix' (W.subtype ∘ₗ b.equivFun.symm.toLinearMap),
    LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ Q.mulVecLin.rangeRestrict), ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp]
    have : (W.subtype ∘ₗ b.equivFun.symm.toLinearMap) ∘ₗ (b.equivFun.toLinearMap ∘ₗ Q.mulVecLin.rangeRestrict)
        = Q.mulVecLin := LinearMap.ext fun v => by simp
    rw [this, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
  · rw [← LinearMap.toMatrix'_comp]
    have : (b.equivFun.toLinearMap ∘ₗ Q.mulVecLin.rangeRestrict) ∘ₗ (W.subtype ∘ₗ b.equivFun.symm.toLinearMap)
        = LinearMap.id := LinearMap.ext fun c => by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Submodule.coe_subtype, key,
        LinearEquiv.apply_symm_apply, LinearMap.id_apply]
    rw [this, LinearMap.toMatrix'_id]

end GlobalTheory.FrameExt

theorem GlobalTheory.FrameExt.exists_fr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E),
    IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    ∃ (m : ℕ) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J X Y Z J₀ := by
  intro F E _ _ _ _ _ σ n J r X Y hcm hJ hW
  have hσ : ∀ e, σ (σ e) = e := fun e => GlobalTheory.SiegelSet.sigma_sigma (σ := σ) hcm e
  have ccT : ∀ {p q : ℕ} (M : Matrix (Fin p) (Fin q) E), cT (σ : E →+* E) (cT (σ : E →+* E) M) = M :=
    fun M => Matrix.ext fun i j => by simp [Formalism.UG.cT, hσ]
  have cT0 : ∀ {p q : ℕ}, cT (σ : E →+* E) (0 : Matrix (Fin p) (Fin q) E) = 0 :=
    Matrix.ext fun i j => by simp [Formalism.UG.cT]
  have hJJ : cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j
  have hBX : cT (σ : E →+* E) Y * J * X = 1 := GlobalTheory.StdPar.yx hcm hJ hW
  obtain ⟨A, hA⟩ : ∃ A, A = cT (σ : E →+* E) X * J := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = cT (σ : E →+* E) Y * J := ⟨_, rfl⟩
  have hAX : A * X = 0 := by rw [hA]; exact hW.xx
  have hAY : A * Y = 1 := by rw [hA]; exact hW.xy
  have hBY : B * Y = 0 := by rw [hB]; exact hW.yy
  have hBX' : B * X = 1 := by rw [hB]; exact hBX
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 1 - X * B - Y * A := ⟨_, rfl⟩
  have hAQ : A * Q = 0 := by
    rw [hQ, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hAX, hAY]
    simp
  have hBQ : B * Q = 0 := by
    rw [hQ, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hBX', hBY]
    simp
  have hQQ : Q * Q = Q := by
    calc Q * Q = (1 - X * B - Y * A) * Q := by rw [← hQ]
      _ = Q - X * (B * Q) - Y * (A * Q) := by
        rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = Q := by rw [hBQ, hAQ]; simp
  obtain ⟨m, Z, C, hZC, hCZ⟩ := GlobalTheory.FrameExt.idem_factor Q hQQ
  have hQZ : Q * Z = Z := by rw [← hZC, Matrix.mul_assoc, hCZ, Matrix.mul_one]
  have hAZ : A * Z = 0 := by rw [← hQZ, ← Matrix.mul_assoc, hAQ, Matrix.zero_mul]
  have hBZ : B * Z = 0 := by rw [← hQZ, ← Matrix.mul_assoc, hBQ, Matrix.zero_mul]

  have hzc : cT (σ : E →+* E) Z * J * X = 0 := by
    have := congrArg (cT (σ : E →+* E)) hAZ
    rwa [hA, Formalism.UG.cT_mul, Formalism.UG.cT_mul, ccT, hJJ, cT0, ← Matrix.mul_assoc] at this
  have hzd : cT (σ : E →+* E) Z * J * Y = 0 := by
    have := congrArg (cT (σ : E →+* E)) hBZ
    rwa [hB, Formalism.UG.cT_mul, Formalism.UG.cT_mul, ccT, hJJ, cT0, ← Matrix.mul_assoc] at this
  obtain ⟨J₀, hJ₀⟩ : ∃ J₀, J₀ = cT (σ : E →+* E) Z * J * Z := ⟨_, rfl⟩
  have hJ₀h : cT (σ : E →+* E) J₀ = J₀ := by
    rw [hJ₀, Formalism.UG.cT_mul, Formalism.UG.cT_mul, ccT, hJJ, Matrix.mul_assoc]
  have key : cT (σ : E →+* E) Z * J = J₀ * C := by
    calc cT (σ : E →+* E) Z * J = cT (σ : E →+* E) Z * J * (X * B + Y * A + Z * C) := by
          rw [hZC, hQ]; simp
      _ = cT (σ : E →+* E) Z * J * X * B + cT (σ : E →+* E) Z * J * Y * A + J₀ * C := by
          rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ₀]
      _ = J₀ * C := by rw [hzc, hzd]; simp
  have hJZ : J * Z = cT (σ : E →+* E) C * J₀ := by
    have := congrArg (cT (σ : E →+* E)) key
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, ccT, hJJ, hJ₀h] at this
  have hJu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ.2
  have hZ : Z = J⁻¹ * (cT (σ : E →+* E) C * J₀) := by
    rw [← hJZ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJu, Matrix.one_mul]
  have hdet₀ : J₀.det ≠ 0 := by
    refine Matrix.det_ne_zero_of_left_inverse (B := C * J⁻¹ * cT (σ : E →+* E) C) ?_
    rw [← hCZ, hZ]; simp only [Matrix.mul_assoc]
  have hJ₀u : IsUnit J₀.det := isUnit_iff_ne_zero.mpr hdet₀
  refine ⟨m, Z, J₀, ⟨hcm, hJ, ⟨fun i j => ?_, hdet₀⟩, hW.xx, hW.yy, hW.xy, hBX, ?_, ?_, hzc, hzd, hJ₀.symm, ?_, ?_⟩⟩
  · have := congrFun (congrFun hJ₀h i) j
    simpa [Formalism.UG.cT] using this
  · rw [← hA]; exact hAZ
  · rw [← hB]; exact hBZ
  · rw [← hA, ← hB, key, ← Matrix.mul_assoc J₀⁻¹, Matrix.nonsing_inv_mul _ hJ₀u, Matrix.one_mul, hZC, hQ]
    abel
  · have htr : (1 : Matrix (Fin n) (Fin n) E).trace = (X * B).trace + (Y * A).trace + (Z * C).trace := by
      rw [← Matrix.trace_add, ← Matrix.trace_add, hZC, hQ]; congr 1; abel
    rw [Matrix.trace_mul_comm X B, hBX', Matrix.trace_mul_comm Y A, hAY, Matrix.trace_mul_comm Z C, hCZ] at htr
    simp only [Matrix.trace_one, Fintype.card_fin] at htr
    have h3 : ((m + 2 * (r + 1) : ℕ) : E) = ((n : ℕ) : E) := by push_cast at htr ⊢; rw [htr]; ring
    exact Nat.cast_injective h3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicFrameDecompositionOfWittFrameStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropicFrameDecomposition_of_wittFrame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∃ (m : ℕ) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J X Y Z J₀ := by
  first | exact @GlobalTheory.FrameExt.exists_fr | exact GlobalTheory.FrameExt.exists_fr | (intros; apply GlobalTheory.FrameExt.exists_fr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundamentalDomainProdLtTop
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundamentalDomainProdLtTop
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

namespace GlobalTheory

theorem isFundamentalDomain_stdDom_prod {G₁ G₂ : Type} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
    [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂]
    [IsTopologicalGroup G₂] [SecondCountableTopology G₂] [MeasurableSpace G₂] [BorelSpace G₂]
    (Γ₁ : Subgroup G₁) (Γ₂ : Subgroup G₂) [DiscreteTopology Γ₁] [DiscreteTopology Γ₂] (μ : Measure (G₁ × G₂)) :
    IsFundamentalDomain (Γ₁.prod Γ₂) (GlobalTheory.AutomorphicL2Unitary.stdDom Γ₁ ×ˢ GlobalTheory.AutomorphicL2Unitary.stdDom Γ₂) μ := by
  refine .mk' ((GlobalTheory.AutomorphicL2Unitary.measurableSet_stdDom Γ₁).prod (GlobalTheory.AutomorphicL2Unitary.measurableSet_stdDom Γ₂)).nullMeasurableSet ?_
  rintro ⟨a, b⟩
  obtain ⟨γ₁, h₁, u₁⟩ := GlobalTheory.AutomorphicL2Unitary.existsUnique_stdDom Γ₁ a
  obtain ⟨γ₂, h₂, u₂⟩ := GlobalTheory.AutomorphicL2Unitary.existsUnique_stdDom Γ₂ b
  refine ⟨⟨((γ₁ : G₁), (γ₂ : G₂)), Subgroup.mem_prod.2 ⟨γ₁.2, γ₂.2⟩⟩, ⟨h₁, h₂⟩, ?_⟩
  rintro ⟨⟨c, d⟩, hcd⟩ ⟨hc, hd⟩
  have e₁ := u₁ ⟨c, (Subgroup.mem_prod.1 hcd).1⟩ hc
  have e₂ := u₂ ⟨d, (Subgroup.mem_prod.1 hcd).2⟩ hd
  ext <;> simp [← e₁, ← e₂]

theorem measure_fundamentalDomain_prod_lt_top : ∀ (G₁ G₂ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂] [SecondCountableTopology G₂] [T2Space G₂] [MeasurableSpace G₂] [BorelSpace G₂] (Γ₁ : Subgroup G₁) (Γ₂ : Subgroup G₂) [DiscreteTopology Γ₁] [DiscreteTopology Γ₂], (∀ μ : Measure G₁, μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain Γ₁ 𝓕 μ → μ 𝓕 ≠ ⊤) → (∀ μ : Measure G₂, μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain Γ₂ 𝓕 μ → μ 𝓕 ≠ ⊤) → ∀ μ : Measure (G₁ × G₂), μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain (Γ₁.prod Γ₂) 𝓕 μ → μ 𝓕 < ⊤ := by
  intro G₁ G₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Γ₁ Γ₂ _ _ h₁ h₂ μ hμ 𝓕 h𝓕
  have hd := GlobalTheory.isFundamentalDomain_stdDom_prod Γ₁ Γ₂ μ
  haveI : Countable (Γ₁.prod Γ₂) := by
    have : Function.Injective (fun γ : Γ₁.prod Γ₂ => ((⟨(γ : G₁ × G₂).1, (Subgroup.mem_prod.1 γ.2).1⟩ : Γ₁),
      (⟨(γ : G₁ × G₂).2, (Subgroup.mem_prod.1 γ.2).2⟩ : Γ₂))) := by
      rintro ⟨⟨a, b⟩, _⟩ ⟨⟨c, d⟩, _⟩ h
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      ext <;> simp [h.1, h.2]
    exact this.countable
  rw [h𝓕.measure_eq hd]
  have hp : (Measure.haar : Measure G₁).prod (Measure.haar : Measure G₂) |>.IsHaarMeasure := inferInstance
  rw [Measure.isMulLeftInvariant_eq_smul μ ((Measure.haar : Measure G₁).prod (Measure.haar : Measure G₂)),
    Measure.smul_apply, Measure.prod_prod, ENNReal.smul_def, smul_eq_mul]
  have a₁ := h₁ Measure.haar inferInstance _ (GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom Γ₁ Measure.haar)
  have a₂ := h₂ Measure.haar inferInstance _ (GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom Γ₂ Measure.haar)
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top a₁.lt_top a₂.lt_top)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundamentalDomainProdLtTopStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_fundamentalDomain_prod_lt_infty : ∀ (G₁ G₂ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂] [SecondCountableTopology G₂] [T2Space G₂] [MeasurableSpace G₂] [BorelSpace G₂] (Γ₁ : Subgroup G₁) (Γ₂ : Subgroup G₂) [DiscreteTopology Γ₁] [DiscreteTopology Γ₂], (∀ μ : Measure G₁, μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain Γ₁ 𝓕 μ → μ 𝓕 ≠ ⊤) → (∀ μ : Measure G₂, μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain Γ₂ 𝓕 μ → μ 𝓕 ≠ ⊤) → ∀ μ : Measure (G₁ × G₂), μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain (Γ₁.prod Γ₂) 𝓕 μ → μ 𝓕 < ⊤ := by
  first | exact @GlobalTheory.measure_fundamentalDomain_prod_lt_top | exact GlobalTheory.measure_fundamentalDomain_prod_lt_top | (intros; apply GlobalTheory.measure_fundamentalDomain_prod_lt_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicLeviNormOneLastColumnProdEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicLeviNormOneLastColumnProdEquiv
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis.LeviLast

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

theorem cT_mul_sq {R : Type} [CommRing R] (s : R →+* R) {k : ℕ} (A B : Matrix (Fin k) (Fin k) R) :
    cT s (A * B) = cT s B * cT s A := by
  simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one_sq {R : Type} [CommRing R] (s : R →+* R) {k : ℕ} : cT s (1 : Matrix (Fin k) (Fin k) R) = 1 := by
  simp only [Formalism.UG.cT, Matrix.map_one _ (map_zero s) (map_one s), Matrix.transpose_one]

def cTUnit {R : Type} [CommRing R] (s : R →+* R) {k : ℕ} (β : GL (Fin k) R) : GL (Fin k) R where
  val := cT s (β⁻¹).1
  inv := cT s β.1
  val_inv := by rw [← cT_mul_sq, Units.mul_inv, cT_one_sq]
  inv_val := by rw [← cT_mul_sq, Units.inv_mul, cT_one_sq]

theorem adMat_mul' {a b c : ℕ} (A : Matrix (Fin a) (Fin b) E) (B : Matrix (Fin b) (Fin c) E) :
    adMat F (A * B) = adMat F A * adMat F B := Matrix.map_mul

theorem adMat_one' {a : ℕ} : adMat F (1 : Matrix (Fin a) (Fin a) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

def blk {k : ℕ} (P : Matrix (Fin k) (Fin n) E) (X : Matrix (Fin n) (Fin k) E) (g : GAd σ J) :
    Matrix (Fin k) (Fin k) (AF F ⊗[F] E) :=
  adMat F P * (matHom _ σ J g).1 * adMat F X

theorem blk_of {k : ℕ} {P : Matrix (Fin k) (Fin n) E} {X : Matrix (Fin n) (Fin k) E} (hPX : P * X = 1) {g : GAd σ J}
    {B : Matrix (Fin k) (Fin k) (AF F ⊗[F] E)} (h : (matHom _ σ J g).1 * adMat F X = adMat F X * B) : blk P X g = B := by
  rw [blk, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ← adMat_mul', hPX, adMat_one', Matrix.one_mul]

theorem blk_mul {k : ℕ} {P : Matrix (Fin k) (Fin n) E} {X : Matrix (Fin n) (Fin k) E} (hPX : P * X = 1) (a : GAd σ J)
    {b : GAd σ J} {B : Matrix (Fin k) (Fin k) (AF F ⊗[F] E)} (h : (matHom _ σ J b).1 * adMat F X = adMat F X * B) :
    blk P X (a * b) = blk P X a * blk P X b := by
  rw [blk_of hPX h, blk, blk, map_mul, Units.val_mul]
  simp only [Matrix.mul_assoc]
  rw [h]

variable {r : ℕ}

theorem mem_leviOne_last {X Y : Matrix (Fin n) (Fin (r + 1)) E} {g : GAd σ J} :
    g ∈ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} ↔
      (∃ B : GL (Fin (r + 1)) (AF F ⊗[F] E), (matHom _ σ J g).1 * adMat F X = adMat F X * B.1) ∧
      (∃ B : GL (Fin (r + 1)) (AF F ⊗[F] E), (matHom _ σ J g).1 * adMat F Y = adMat F Y * B.1) ∧
      (∃ B ∈ ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin (r + 1)) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker,
        (matHom _ σ J g).1 * adMat F X = adMat F X * B.1) := by
  have hmem : g ∈ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} ↔ ∀ k ∈ ({Fin.last r} : Finset (Fin (r + 1))),
      g ∈ GlobalTheory.StdPar.frameStab σ J (GlobalTheory.StdPar.initCols X k) ((⊤ : Subgroup (AF F ⊗[F] E)ˣ).comap Matrix.GeneralLinearGroup.det) ∧
      g ∈ GlobalTheory.StdPar.frameStab σ J (GlobalTheory.StdPar.initCols Y k) ((⊤ : Subgroup (AF F ⊗[F] E)ˣ).comap Matrix.GeneralLinearGroup.det) ∧
      g ∈ GlobalTheory.StdPar.frameStab σ J (GlobalTheory.StdPar.initCols X k) ((absE F E).ker.comap Matrix.GeneralLinearGroup.det) := by
    simp only [GlobalTheory.StdPar.leviOne, GlobalTheory.StdPar.levi, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.comap_top, MonoidHom.comap_ker]
    exact ⟨fun h k hk => ⟨(h.1 k hk).1, (h.1 k hk).2, h.2 k hk⟩, fun h => ⟨fun k hk => ⟨(h k hk).1, (h k hk).2.1⟩, fun k hk => (h k hk).2.2⟩⟩
  rw [hmem]
  simp only [Finset.mem_singleton, forall_eq]
  constructor
  · rintro ⟨⟨B, -, h⟩, ⟨B', -, h'⟩, ⟨B'', h2, h''⟩⟩
    exact ⟨⟨B, h⟩, ⟨B', h'⟩, ⟨B'', h2, h''⟩⟩
  · rintro ⟨⟨B, h⟩, ⟨B', h'⟩, ⟨B'', h2, h''⟩⟩
    exact ⟨⟨B, Subgroup.mem_top _, h⟩, ⟨B', Subgroup.mem_top _, h'⟩, ⟨B'', h2, h''⟩⟩


set_option maxHeartbeats 1000000 in
open GlobalTheory.UAut GlobalTheory.EisLine in
theorem leviOne_last_prod : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r m : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J X Y Z J₀ → ∃ φ : (GlobalTheory.SphEis.fixG σ J X ⊓ GlobalTheory.SphEis.fixG σ J Y : Subgroup (GAd σ J)) × ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin (r + 1)) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker ≃ₜ* GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}, ∀ p, ((φ p : GAd σ J) ∈ ratPts σ J ↔ (p.1 : GAd σ J) ∈ ratPts σ J ∧ (p.2 : GL (Fin (r + 1)) (AF F ⊗[F] E)) ∈ (bc (inclR (F := F) (AF F)) : GL (Fin (r + 1)) E →* GL (Fin (r + 1)) (AF F ⊗[F] E)).range) := by
  intro F E _ _ _ _ _ σ n J r m X Y Z J₀ hF
  obtain ⟨_, _⟩ := GlobalTheory.StdPar.ring_facts (F := F) (E := E)
  obtain ⟨lv, hlv, -, -⟩ := GlobalTheory.SphEis.Inhabitant.existsUnique_isLv hF
  set K := ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin (r + 1)) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker with hK
  set A := GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} with hA
  set T := (GlobalTheory.SphEis.fixG σ J X ⊓ GlobalTheory.SphEis.fixG σ J Y : Subgroup (GAd σ J)) with hT
  set P : Matrix (Fin (r + 1)) (Fin n) E := cT (σ : E →+* E) Y * J with hP
  set Q : Matrix (Fin (r + 1)) (Fin n) E := cT (σ : E →+* E) X * J with hQ
  have hPX : P * X = 1 := hF.dc
  have hQY : Q * Y = 1 := hF.cd
  have h1X : ∀ g : GAd σ J, (matHom _ σ J g).1 * adMat F X = adMat F X →
      (matHom _ σ J g).1 * adMat F X = adMat F X * (1 : GL (Fin (r + 1)) (AF F ⊗[F] E)).1 := fun g h => by
    rw [Units.val_one, Matrix.mul_one]; exact h
  have hinv : ∀ a : A, blk P X (a : GAd σ J) * blk P X ((a⁻¹ : A) : GAd σ J) = 1 ∧
      blk P X ((a⁻¹ : A) : GAd σ J) * blk P X (a : GAd σ J) = 1 := by
    intro a
    obtain ⟨⟨B, hB⟩, -, -⟩ := mem_leviOne_last.1 a.2
    obtain ⟨⟨B', hB'⟩, -, -⟩ := mem_leviOne_last.1 (a⁻¹).2
    have e1 : blk P X (1 : GAd σ J) = 1 := by
      have := blk_of hPX (h1X 1 (by rw [map_one, Units.val_one, Matrix.one_mul]))
      rw [this, Units.val_one]
    refine ⟨?_, ?_⟩
    · rw [← blk_mul hPX _ hB', ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, e1]
    · rw [← blk_mul hPX _ hB, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, e1]
  let πu : A → GL (Fin (r + 1)) (AF F ⊗[F] E) := fun a =>
    ⟨blk P X (a : GAd σ J), blk P X ((a⁻¹ : A) : GAd σ J), (hinv a).1, (hinv a).2⟩
  have hπK : ∀ a : A, πu a ∈ K := by
    intro a
    obtain ⟨-, -, ⟨B, hBK, hB⟩⟩ := mem_leviOne_last.1 a.2
    have : πu a = B := Units.ext (blk_of hPX hB)
    rw [this]; exact hBK
  let π : A → K := fun a => ⟨πu a, hπK a⟩
  have hlvA : ∀ β : K, lv β ∈ A := fun β =>
    mem_leviOne_last.2 ⟨⟨β, hlv.onC β⟩, ⟨cTUnit (sigR (AF F) σ) (β : GL (Fin (r + 1)) (AF F ⊗[F] E)), hlv.onD β⟩,
      ⟨β, β.2, hlv.onC β⟩⟩
  let mm : K → A := fun β => ⟨lv β, hlvA β⟩
  have hTA : T ≤ A := by
    intro x hx
    obtain ⟨hxX, hxY⟩ := Subgroup.mem_inf.1 hx
    have hX' : (matHom _ σ J x).1 * adMat F X = adMat F X := hxX
    have hY' : (matHom _ σ J x).1 * adMat F Y = adMat F Y := hxY
    exact mem_leviOne_last.2 ⟨⟨1, by rw [hX', Units.val_one, Matrix.mul_one]⟩, ⟨1, by rw [hY', Units.val_one, Matrix.mul_one]⟩,
      ⟨1, one_mem _, by rw [hX', Units.val_one, Matrix.mul_one]⟩⟩
  have hTiff : ∀ a : A, (a : GAd σ J) ∈ T ↔ π a = 1 := by
    intro a
    constructor
    · intro hx
      exact Subtype.ext (Units.ext (blk_of hPX (h1X _ (Subgroup.mem_inf.1 hx).1)))
    · intro h1
      have hb : blk P X (a : GAd σ J) = 1 := by
        have := congrArg (fun x : K => (x : GL (Fin (r + 1)) (AF F ⊗[F] E)).1) h1
        exact this
      obtain ⟨⟨B, hB⟩, ⟨B', hB'⟩, -⟩ := mem_leviOne_last.1 a.2
      have hB1 : B.1 = 1 := (blk_of hPX hB).symm.trans hb
      have hfX : (matHom _ σ J (a : GAd σ J)).1 * adMat F X = adMat F X := by rw [hB, hB1, Matrix.mul_one]
      have hfXi : (a : GAd σ J)⁻¹ ∈ GlobalTheory.SphEis.fixG σ J X :=
        inv_mem (show (a : GAd σ J) ∈ GlobalTheory.SphEis.fixG σ J X from hfX)
      have hform := form_mul_of_mul_cols (B := 1)
        (show (matHom _ σ J (a : GAd σ J)⁻¹).1 * adMat F X = adMat F X * 1 by rw [Matrix.mul_one]; exact hfXi)
      rw [inv_inv, cT_one_sq, Matrix.one_mul] at hform
      have e1 : blk Q Y (a : GAd σ J) = B'.1 := blk_of hQY hB'
      rw [blk, hform, ← adMat_mul', hQY, adMat_one'] at e1
      have hfY : (matHom _ σ J (a : GAd σ J)).1 * adMat F Y = adMat F Y := by rw [hB', ← e1, Matrix.mul_one]
      exact Subgroup.mem_inf.2 ⟨hfX, hfY⟩
  have hπc : Continuous π := by
    refine Continuous.subtype_mk ?_ _
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · show Continuous fun a : A => adMat F P * (matHom _ σ J (a : GAd σ J)).1 * adMat F X
      exact (continuous_const.matrix_mul (GlobalTheory.StdPar.continuous_mat.comp continuous_subtype_val)).matrix_mul continuous_const
    · show Continuous fun a : A => adMat F P * (matHom _ σ J ((a⁻¹ : A) : GAd σ J)).1 * adMat F X
      exact (continuous_const.matrix_mul (GlobalTheory.StdPar.continuous_mat.comp (continuous_subtype_val.comp continuous_inv))).matrix_mul
        continuous_const
  have hmc : Continuous mm := (hlv.cont.comp continuous_subtype_val).subtype_mk _
  have hmm : ∀ a b, mm (a * b) = mm a * mm b := fun a b => Subtype.ext (map_mul lv _ _)
  have hππ : ∀ a b, π (a * b) = π a * π b := by
    intro a b
    obtain ⟨⟨B, hB⟩, -, -⟩ := mem_leviOne_last.1 b.2
    exact Subtype.ext (Units.ext (blk_mul hPX (a : GAd σ J) hB))
  have hπm : ∀ β, π (mm β) = β := fun β => Subtype.ext (Units.ext (blk_of hPX (hlv.onC β)))
  have hc : ∀ τ ∈ T, ∀ β, τ * (mm β : GAd σ J) = mm β * τ := fun τ hτ β =>
    (GlobalTheory.SphEis.lv_comm_of_fix_cols F E σ n J (r + 1) m X Y Z J₀ hF lv hlv β τ hτ).symm
  obtain ⟨φ, hφ⟩ := GlobalTheory.LeviSplit.exists_prod_equiv A T mm π hmc hπc hmm hππ hπm hTA hTiff hc
  refine ⟨φ, fun p => ?_⟩
  rw [hφ p]
  change (p.1 : GAd σ J) * lv p.2 ∈ ratPts σ J ↔ _
  constructor
  · intro h
    have hp1 : (matHom _ σ J (p.1 : GAd σ J)).1 * adMat F X = adMat F X := (Subgroup.mem_inf.1 p.1.2).1
    have hg : (matHom _ σ J ((p.1 : GAd σ J) * lv p.2)).1 * adMat F X =
        adMat F X * (p.2 : GL (Fin (r + 1)) (AF F ⊗[F] E)).1 := by
      rw [map_mul, Units.val_mul, Matrix.mul_assoc, hlv.onC, ← Matrix.mul_assoc, hp1]
    have hb := blk_of hPX hg
    obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 h)
    have hM : (matHom _ σ J ((p.1 : GAd σ J) * lv p.2)).1 = adMat F γ.1 := (congrArg Units.val hγ).symm
    rw [blk, hM, ← adMat_mul', ← adMat_mul'] at hb
    have hrng : (p.2 : GL (Fin (r + 1)) (AF F ⊗[F] E)) ∈ (bc (inclR (F := F) (AF F)) :
        GL (Fin (r + 1)) E →* GL (Fin (r + 1)) (AF F ⊗[F] E)).range := by
      rcases subsingleton_or_nontrivial (AF F ⊗[F] E) with _ | _
      · exact ⟨1, Units.ext (Subsingleton.elim _ _)⟩
      · have hd : (P * γ.1 * X).det ≠ 0 := fun h0 => by
          have hu : IsUnit (p.2 : GL (Fin (r + 1)) (AF F ⊗[F] E)).1.det :=
            (Matrix.isUnit_iff_isUnit_det _).1 (p.2 : GL (Fin (r + 1)) (AF F ⊗[F] E)).isUnit
          rw [← hb, show (adMat F (P * γ.1 * X)).det = inclR (F := F) (AF F) (P * γ.1 * X).det from
            (RingHom.map_det _ _).symm, h0, map_zero] at hu
          exact not_isUnit_zero hu
        exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, Units.ext hb⟩
    obtain ⟨δ, hδ⟩ := hrng
    refine ⟨?_, ⟨δ, hδ⟩⟩
    have h2 : lv p.2 ∈ ratPts σ J := by rw [← hδ]; exact hlv.rat δ
    have := mul_mem h (inv_mem h2)
    rwa [mul_inv_cancel_right] at this
  · rintro ⟨h1, ⟨δ, hδ⟩⟩
    refine mul_mem h1 ?_
    rw [← hδ]; exact hlv.rat δ

end GlobalTheory.SphEis.LeviLast
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicLeviNormOneLastColumnProdEquivStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardParabolicLeviNormOne_lastColumn_prodEquiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r m : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J X Y Z J₀ → ∃ φ : (GlobalTheory.SphEis.fixG σ J X ⊓ GlobalTheory.SphEis.fixG σ J Y : Subgroup (GAd σ J)) × ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin (r + 1)) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker ≃ₜ* GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}, ∀ p, ((φ p : GAd σ J) ∈ ratPts σ J ↔ (p.1 : GAd σ J) ∈ ratPts σ J ∧ (p.2 : GL (Fin (r + 1)) (AF F ⊗[F] E)) ∈ (bc (inclR (F := F) (AF F)) : GL (Fin (r + 1)) E →* GL (Fin (r + 1)) (AF F ⊗[F] E)).range) := by
  first | exact @GlobalTheory.SphEis.LeviLast.leviOne_last_prod | exact GlobalTheory.SphEis.LeviLast.leviOne_last_prod | (intros; apply GlobalTheory.SphEis.LeviLast.leviOne_last_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeNormOneLeviWittFrameStabilizer
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

namespace GlobalTheory.ResidueEisenstein

theorem finCovol_leviOne_last : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (π : Measure (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})) (DM : Set (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})), π.IsHaarMeasure → IsFundamentalDomain ((ratPts σ J).subgroupOf (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})) DM π → π DM ≠ ⊤ := by
  intro F E _ _ _ _ _ σ n J r X Y hcm hJ hW π DM hπ hDM
  obtain ⟨m, Z, J₀, hF⟩ := GlobalTheory.T.exists_isotropicFrameDecomposition_of_wittFrame F E σ n J r X Y hcm hJ hW
  letI : MeasurableSpace (GL (Fin (r + 1)) (AF F ⊗[F] E)) := borel _
  haveI : BorelSpace (GL (Fin (r + 1)) (AF F ⊗[F] E)) := ⟨rfl⟩
  obtain ⟨_, _⟩ := GlobalTheory.StdPar.ring_facts (F := F) (E := E)
  set A := (GlobalTheory.SphEis.fixG σ J X ⊓ GlobalTheory.SphEis.fixG σ J Y : Subgroup (GAd σ J)) with hA
  set G₁ := ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin (r + 1)) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker
  set ΓA := (ratPts σ J).subgroupOf A
  set ΓG := (bc (inclR (F := F) (AF F)) : GL (Fin (r + 1)) E →* GL (Fin (r + 1)) (AF F ⊗[F] E)).range.subgroupOf G₁
  obtain ⟨hlc, hsc, hdisc, hfinGL⟩ := GlobalTheory.T.normOneAdelicGL_locallyCompact_discrete_finiteCovolume F E σ hcm (r + 1)
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.standardParabolicLeviNormOne_lastColumn_prodEquiv F E σ n J r m X Y Z J₀ hF
  have hclA : IsClosed (A : Set (GAd σ J)) :=
    (isClosed_eq (GlobalTheory.StdPar.continuous_mat.matrix_mul continuous_const) continuous_const).inter
      (isClosed_eq (GlobalTheory.StdPar.continuous_mat.matrix_mul continuous_const) continuous_const)
  haveI : LocallyCompactSpace A := hclA.locallyCompactSpace
  haveI : LocallyCompactSpace (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}) :=
    (GlobalTheory.StdPar.isClosed_levi _ hcm hJ hW).2.locallyCompactSpace
  haveI := hlc
  haveI := hsc
  haveI := hdisc
  haveI : DiscreteTopology ΓA := DiscreteTopology.of_continuous_injective
    (f := fun x : ΓA => (⟨(x.1 : GAd σ J), x.2⟩ : ratPts σ J))
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    (fun a b h => by
      apply Subtype.ext; apply Subtype.ext
      exact congrArg (fun y : ratPts σ J => (y : GAd σ J)) h)
  haveI : Countable (ΓA.prod ΓG) := by
    haveI : Countable ΓA := inferInstance
    haveI : Countable ΓG := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
    exact Function.Injective.countable (f := fun x : ΓA.prod ΓG => ((⟨x.1.1, x.2.1⟩ : ΓA), (⟨x.1.2, x.2.2⟩ : ΓG)))
      (fun a b h => Subtype.ext (Prod.ext (congrArg (fun q => (q.1 : A)) h) (congrArg (fun q => (q.2 : G₁)) h)))
  refine GlobalTheory.SphEis.covolume_ne_top_of_continuousMulEquiv (A × G₁) _ φ (ΓA.prod ΓG) _ (fun g => ?_)
    (fun μ hμ 𝓕 h𝓕 => GlobalTheory.T.measure_fundamentalDomain_prod_lt_infty A G₁ ΓA ΓG
      (fun μ hμ 𝓕 h𝓕 => GlobalTheory.T.finiteCovolume_common_adelicFixatorOfColumns F E σ n J (r + 1) m X Y Z J₀ hF μ 𝓕 hμ h𝓕) (fun μ hμ 𝓕 h𝓕 => hfinGL μ 𝓕 hμ h𝓕)
      μ hμ 𝓕 h𝓕) π DM hπ hDM
  rw [Subgroup.mem_prod, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hφ g]

end GlobalTheory.ResidueEisenstein
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeNormOneLeviWittFrameStabilizerStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteCovolume_normOneLevi_wittFrameStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (π : Measure (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})) (DM : Set (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})), π.IsHaarMeasure → IsFundamentalDomain ((ratPts σ J).subgroupOf (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})) DM π → π DM ≠ ⊤ := by
  first | exact @GlobalTheory.ResidueEisenstein.finCovol_leviOne_last | exact GlobalTheory.ResidueEisenstein.finCovol_leviOne_last | (intros; apply GlobalTheory.ResidueEisenstein.finCovol_leviOne_last <;> assumption)
end
