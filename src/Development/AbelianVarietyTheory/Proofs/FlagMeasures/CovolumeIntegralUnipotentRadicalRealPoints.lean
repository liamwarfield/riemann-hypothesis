module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitQuotientTopology.IsClosedRStab
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrictFundamentalDomainMeasureEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasFlagDepthAtLeastOfFreeEntriesVanish
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureUnipotentTuplesFreeEntryBlocks
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentMemModelUnipotentAtPlace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryDatumLevelPrimeSplitDegreeGramFacts
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeSeenInDefiniteSpaceDetRankIndex
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LiftRowMiddleSpaceIntegralPoint
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SkewLatticeInverseDifferentPowCovolumeStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeMiddleLatticeHomLatticeIdeal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentModelProductActionMeasurePreserving
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentModelProductActionMeasurePreserving
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem actM_measurePreserving (E : Type) [Field E] [NumberField E] (k r : ℕ)
    (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (hN : ∀ w, gM A γ w ∈ Nset k r) :
    MeasurePreserving (actM A γ) (Measure.pi fun _ : InfinitePlace E => haarLie (Nset k r) 1)
      (Measure.pi fun _ : InfinitePlace E => haarLie (Nset k r) 1) := by
  have hH := (GlobalTheory.T.haar_lie_nilpotent_coordinates k r).1
  haveI : SigmaFinite (haarLie (Nset k r) 1) := hH.1
  have hf : ∀ w, MeasurePreserving (lmulM (gM A γ w)) (haarLie (Nset k r) 1) (haarLie (Nset k r) 1) :=
    fun w => ⟨GlobalTheory.Amp.StabMeas.meas_lmul _, hH.2.2.2 _ (hN w)⟩
  exact measurePreserving_pi (fun _ : InfinitePlace E => haarLie (Nset k r) 1) (fun _ => haarLie (Nset k r) 1) hf

end GlobalTheory.SnMass.VolN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentModelProductActionMeasurePreservingStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentModelProductAction_measurePreserving : ∀ (E : Type) [Field E] [NumberField E] (k r : ℕ) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E), (∀ w, gM A γ w ∈ Nset k r) → MeasurePreserving (actM A γ) (Measure.pi fun _ : InfinitePlace E => haarLie (Nset k r) 1) (Measure.pi fun _ : InfinitePlace E => haarLie (Nset k r) 1) := by
  first | exact @GlobalTheory.SnMass.VolN.actM_measurePreserving | exact GlobalTheory.SnMass.VolN.actM_measurePreserving | (intros; apply GlobalTheory.SnMass.VolN.actM_measurePreserving <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentRadicalFormsUnitSubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentRadicalFormsUnitSubgroup
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.VolN.GNGroup

variable {E : Type} [Field E]

theorem cT_mul (σ : E →+* E) {n : ℕ} (A B : Matrix (Fin n) (Fin n) E) :
    cT σ (A * B) = cT σ B * cT σ A := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_mul' (σ : E →+* E) {n a : ℕ} (A : Matrix (Fin n) (Fin n) E) (B : Matrix (Fin n) (Fin a) E) :
    cT σ (A * B) = cT σ B * cT σ A := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_mul'' (σ : E →+* E) {n a : ℕ} (A : Matrix (Fin n) (Fin a) E) (B : Matrix (Fin a) (Fin a) E) :
    cT σ (A * B) = cT σ B * cT σ A := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one (σ : E →+* E) {n : ℕ} : cT σ (1 : Matrix (Fin n) (Fin n) E) = 1 := by
  simp [cT]

theorem isUp_iff_bt {m : ℕ} (u : Matrix (Fin m) (Fin m) E) :
    IsUp u ↔ u.BlockTriangular id ∧ ∀ i, u i i = 1 := by
  constructor
  · intro h
    exact ⟨fun i j hij => (h i j).1 hij, fun i => (h i i).2 rfl⟩
  · rintro ⟨h1, h2⟩ i j
    exact ⟨fun hij => h1 hij, fun hij => hij ▸ h2 i⟩

theorem diag_mul_of_bt {m : ℕ} {A B : Matrix (Fin m) (Fin m) E} (hA : A.BlockTriangular id)
    (hB : B.BlockTriangular id) (i : Fin m) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with hl | hl
    · rw [hA hl, zero_mul]
    · rw [hB hl, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem isUp_mul {m : ℕ} {u u' : Matrix (Fin m) (Fin m) E} (h : IsUp u) (h' : IsUp u') : IsUp (u * u') := by
  rw [isUp_iff_bt] at h h' ⊢
  refine ⟨h.1.mul h'.1, fun i => ?_⟩
  rw [diag_mul_of_bt h.1 h'.1, h.2, h'.2, one_mul]

theorem isUp_inv {m : ℕ} {u : Matrix (Fin m) (Fin m) E} (h : IsUp u) : IsUp u⁻¹ ∧ u * u⁻¹ = 1 := by
  rw [isUp_iff_bt] at h
  have hdet : u.det = 1 := by
    rw [Matrix.det_of_upperTriangular h.1]
    exact Finset.prod_eq_one fun i _ => h.2 i
  letI : Invertible u.det := { invOf := 1, invOf_mul_self := by simp [hdet], mul_invOf_self := by simp [hdet] }
  letI : Invertible u := Matrix.invertibleOfDetInvertible u
  have hbt : u⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular h.1
  have hui : u⁻¹ * u = 1 := Matrix.nonsing_inv_mul u (by rw [hdet]; exact isUnit_one)
  refine ⟨(isUp_iff_bt _).2 ⟨hbt, fun i => ?_⟩, Matrix.mul_nonsing_inv u (by rw [hdet]; exact isUnit_one)⟩
  have := congrFun (congrFun hui i) i
  rw [diag_mul_of_bt hbt h.1, h.2, mul_one] at this
  simpa using this

variable [NumberField E]

theorem latMap_mul {n : ℕ} (g g' : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) :
    latMap (g * g') Λ = latMap g (latMap g' Λ) := by
  ext x
  simp only [latMap, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g' *ᵥ y, ⟨y, hy, rfl⟩, by rw [Matrix.mulVec_mulVec]⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, by rw [Matrix.mulVec_mulVec]⟩

theorem latMap_one {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) : latMap 1 Λ = Λ := by
  ext x
  simp [latMap, Submodule.mem_map]

omit [NumberField E] in
theorem isUnit_of_isUn (σ : E →+* E) {n : ℕ} {J g : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0)
    (h : IsUn σ J g) : IsUnit g := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have := congrArg Matrix.det h
  rw [cT, Matrix.det_mul, Matrix.det_mul] at this
  refine isUnit_iff_ne_zero.2 fun h0 => hJ ?_
  rw [h0, mul_zero] at this
  exact this.symm

omit [NumberField E] in
theorem isUn_mul (σ : E →+* E) {n : ℕ} {J g g' : Matrix (Fin n) (Fin n) E} (h : IsUn σ J g)
    (h' : IsUn σ J g') : IsUn σ J (g * g') := by
  unfold IsUn at *
  calc cT σ (g * g') * J * (g * g') = cT σ g' * (cT σ g * J * g) * g' := by
        rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = J := by rw [h, h']

omit [NumberField E] in
theorem isUn_inv (σ : E →+* E) {n : ℕ} {J a b : Matrix (Fin n) (Fin n) E} (h : IsUn σ J a)
    (hab : a * b = 1) : IsUn σ J b := by
  unfold IsUn at *
  calc cT σ b * J * b = cT σ b * (cT σ a * J * a) * b := by rw [h]
    _ = cT σ (a * b) * J * (a * b) := by rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = J := by rw [hab, cT_one, Matrix.one_mul, Matrix.mul_one]

omit [NumberField E] in
theorem inN_one (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E) :
    InN σ J P 1 := by
  refine ⟨by simp [IsUn, cT_one], ⟨1, ?_, ?_⟩, fun v _ => ⟨0, by simp⟩⟩
  · intro i j
    exact ⟨fun h => Matrix.one_apply_ne (ne_of_lt h).symm, fun h => by subst h; exact Matrix.one_apply_eq i⟩
  · have key : (1 : Matrix (Fin n) (Fin n) E) * eOf P = eOf P * (1 : Matrix (Fin r) (Fin r) E) := by
      rw [Matrix.one_mul, Matrix.mul_one]
    exact key

omit [NumberField E] in
theorem inN_mul (σ : E →+* E) {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {P : Matrix (Fin n) (Fin (r + 1)) E}
    {g g' : Matrix (Fin n) (Fin n) E} (h : InN σ J P g) (h' : InN σ J P g') : InN σ J P (g * g') := by
  obtain ⟨hu, ⟨ν, hν, he⟩, hp⟩ := h
  obtain ⟨hu', ⟨ν', hν', he'⟩, hp'⟩ := h'
  replace he : g * eOf P = eOf P * ν := he
  replace he' : g' * eOf P = eOf P * ν' := he'
  refine ⟨isUn_mul σ hu hu', ⟨ν * ν', isUp_mul hν hν', ?_⟩, fun v hv => ?_⟩
  · have key : (g * g') * eOf P = eOf P * (ν * ν') := by
      rw [Matrix.mul_assoc, he', ← Matrix.mul_assoc, he, Matrix.mul_assoc]
    exact key
  · obtain ⟨c, hc⟩ := hp v hv
    obtain ⟨c', hc'⟩ := hp' v hv
    refine ⟨ν *ᵥ c' + c, ?_⟩
    have e1 : (g * g') *ᵥ v - v = g *ᵥ (g' *ᵥ v - v) + (g *ᵥ v - v) := by
      rw [← Matrix.mulVec_mulVec, Matrix.mulVec_sub]; abel
    rw [e1, hc', hc, Matrix.mulVec_mulVec, he, ← Matrix.mulVec_mulVec, Matrix.mulVec_add]

omit [NumberField E] in
theorem inN_inv (σ : E →+* E) {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {P : Matrix (Fin n) (Fin (r + 1)) E}
    {a b : Matrix (Fin n) (Fin n) E} (h : InN σ J P a) (hab : a * b = 1) (hba : b * a = 1) :
    InN σ J P b := by
  obtain ⟨hu, ⟨ν, hν, he⟩, hp⟩ := h
  replace he : a * eOf P = eOf P * ν := he
  obtain ⟨hνi, hνν⟩ := isUp_inv hν
  have hJ : cT σ a * J = J * b := by
    calc cT σ a * J = cT σ a * J * (a * b) := by rw [hab, Matrix.mul_one]
      _ = J * b := by rw [← Matrix.mul_assoc, hu]
  refine ⟨isUn_inv σ hu hab, ⟨ν⁻¹, hνi, ?_⟩, fun v hv => ?_⟩
  · have key : b * eOf P = eOf P * ν⁻¹ := by
      calc b * eOf P = (b * (eOf P * ν)) * ν⁻¹ := by
            rw [Matrix.mul_assoc b, Matrix.mul_assoc, hνν, Matrix.mul_one]
        _ = (b * (a * eOf P)) * ν⁻¹ := by rw [he]
        _ = eOf P * ν⁻¹ := by rw [← Matrix.mul_assoc b, hba, Matrix.one_mul]
    exact key
  · have e2 : cT σ (eOf P) * J * b = cT σ ν * (cT σ (eOf P) * J) := by
      rw [Matrix.mul_assoc, ← hJ, ← Matrix.mul_assoc, ← cT_mul', he, cT_mul'', Matrix.mul_assoc]
    have hw : (cT σ (eOf P) * J) *ᵥ (b *ᵥ v) = 0 := by
      rw [Matrix.mulVec_mulVec, e2, ← Matrix.mulVec_mulVec]
      have hv' : (cT σ (eOf P) * J) *ᵥ v = 0 := hv
      rw [hv', Matrix.mulVec_zero]
    obtain ⟨c, hc⟩ := hp _ hw
    refine ⟨-c, ?_⟩
    rw [Matrix.mulVec_mulVec, hab, Matrix.one_mulVec] at hc
    rw [Matrix.mulVec_neg, ← hc]
    abel

end GlobalTheory.SnMass.VolN.GNGroup

namespace GlobalTheory.SnMass.VolN

variable {E : Type} [Field E] [NumberField E]

def gNUnits (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (P : Matrix (Fin n) (Fin (r + 1)) E) : Subgroup (Matrix (Fin n) (Fin n) E)ˣ where
  carrier := {u | (u : Matrix (Fin n) (Fin n) E) ∈ GN σ J Λ P}
  one_mem' := by
    show ((1 : (Matrix (Fin n) (Fin n) E)ˣ) : Matrix (Fin n) (Fin n) E) ∈ GN σ J Λ P
    rw [Units.val_one]
    exact ⟨GNGroup.inN_one _ J P, GNGroup.latMap_one Λ⟩
  mul_mem' := by
    intro a b ha hb
    show ((a * b : (Matrix (Fin n) (Fin n) E)ˣ) : Matrix (Fin n) (Fin n) E) ∈ GN σ J Λ P
    rw [Units.val_mul]
    exact ⟨GNGroup.inN_mul _ ha.1 hb.1, by rw [GNGroup.latMap_mul, hb.2, ha.2]⟩
  inv_mem' := by
    intro a ha
    show ((a⁻¹ : (Matrix (Fin n) (Fin n) E)ˣ) : Matrix (Fin n) (Fin n) E) ∈ GN σ J Λ P
    refine ⟨GNGroup.inN_inv _ ha.1 a.mul_inv a.inv_mul, ?_⟩
    calc latMap ((a⁻¹ : (Matrix (Fin n) (Fin n) E)ˣ) : Matrix (Fin n) (Fin n) E) Λ
        = latMap ((a⁻¹ : (Matrix (Fin n) (Fin n) E)ˣ) : Matrix (Fin n) (Fin n) E)
            (latMap (a : Matrix (Fin n) (Fin n) E) Λ) := by rw [ha.2]
      _ = Λ := by rw [← GNGroup.latMap_mul, a.inv_mul, GNGroup.latMap_one]

theorem gN_subgroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → (∃ G : Subgroup (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)ˣ, ∀ u : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)ˣ, u ∈ G ↔ (u : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) ∈ GN (σ : E →+* E) J Λ P) ∧ ∀ γ ∈ GN (σ : E →+* E) J Λ P, IsUnit γ := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hV
  have hJ : J.det ≠ 0 := hV.2.2.1.2
  exact ⟨⟨gNUnits (σ : E →+* E) J Λ P, fun u => Iff.rfl⟩,
    fun γ hγ => GNGroup.isUnit_of_isUn (σ : E →+* E) hJ hγ.1.1⟩

end GlobalTheory.SnMass.VolN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentRadicalFormsUnitSubgroupStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralUnipotentRadical_forms_unit_subgroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → (∃ G : Subgroup (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)ˣ, ∀ u : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)ˣ, u ∈ G ↔ (u : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) ∈ GN (σ : E →+* E) J Λ P) ∧ ∀ γ ∈ GN (σ : E →+* E) J Λ P, IsUnit γ := by
  first | exact @GlobalTheory.SnMass.VolN.gN_subgroup | exact GlobalTheory.SnMass.VolN.gN_subgroup | (intros; apply GlobalTheory.SnMass.VolN.gN_subgroup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentModelActionIsActionAndFaithful
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentModelActionIsActionAndFaithful
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem det_embed_ne_zero {E : Type} [Field E] [NumberField E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : J.det ≠ 0)
    (w : InfinitePlace E) : (J.map w.embedding).det ≠ 0 := by
  rw [show J.map w.embedding = w.embedding.mapMatrix J from rfl, ← RingHom.map_det]
  exact (map_ne_zero _).mpr hJ

theorem A_isUnit_det {E : Type} [Field E] [NumberField E] {k r : ℕ}
    (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)
    (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hJ : J.det ≠ 0) (hA : IsModelAt J A) (w : InfinitePlace E) : IsUnit (A w).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have h : ((A w)ᴴ * Hpk k r * A w).det = (J.map w.embedding).det := congrArg Matrix.det (hA w)
  rw [det_mul, det_mul, h0, mul_zero] at h
  exact det_embed_ne_zero J hJ w h.symm

theorem actLaws (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ) :
    IsVolData σ J Λ P f T A s → (∀ x, actM A 1 x = x) ∧ (∀ γ γ' x, actM A (γ * γ') x = actM A γ (actM A γ' x)) ∧ ∀ γ, (∀ w, gM A γ w = 1) → γ = 1 := by
  intro h
  have hJ : J.det ≠ 0 := h.2.2.1.2
  have hA : IsModelAt J A := h.2.2.2.2.2.2.2.1
  have hu : ∀ w, IsUnit (A w).det := fun w => A_isUnit_det J A hJ hA w
  refine ⟨?_, ?_, ?_⟩
  · intro x
    funext w
    have e : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E).map w.embedding = 1 :=
      map_one w.embedding.mapMatrix
    simp only [actM, e, Matrix.mul_one, Matrix.mul_nonsing_inv _ (hu w), Matrix.one_mul]
    rfl
  · intro γ γ' x
    funext w
    have e : (γ * γ').map w.embedding = γ.map w.embedding * γ'.map w.embedding :=
      map_mul w.embedding.mapMatrix γ γ'
    have m : A w * (γ.map w.embedding * γ'.map w.embedding) * (A w)⁻¹ * Matrix.of (x w) =
        A w * γ.map w.embedding * (A w)⁻¹ * (A w * γ'.map w.embedding * (A w)⁻¹ * Matrix.of (x w)) := by
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (hu w)]
    show Matrix.of.symm (A w * (γ * γ').map w.embedding * (A w)⁻¹ * Matrix.of (x w)) =
      Matrix.of.symm (A w * γ.map w.embedding * (A w)⁻¹ *
        Matrix.of (Matrix.of.symm (A w * γ'.map w.embedding * (A w)⁻¹ * Matrix.of (x w))))
    rw [Equiv.apply_symm_apply, e, m]
  · intro γ hγ
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    have hi : (A w)⁻¹ * A w = 1 := Matrix.nonsing_inv_mul _ (hu w)
    have h1 : γ.map w.embedding = 1 := by
      have e : A w * γ.map w.embedding * (A w)⁻¹ = 1 := hγ w
      calc γ.map w.embedding = (A w)⁻¹ * (A w * γ.map w.embedding * (A w)⁻¹) * A w := by
            simp only [Matrix.mul_assoc, hi, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left _ _ (hu w)]
        _ = 1 := by rw [e, Matrix.mul_one, hi]
    ext i j
    apply w.embedding.injective
    have := congrArg (fun M => M i j) h1
    simpa [Matrix.one_apply, apply_ite] using this

end GlobalTheory.SnMass.VolN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentModelActionIsActionAndFaithfulStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentModelAction_isAction_and_faithful : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → (∀ x, actM A 1 x = x) ∧ (∀ γ γ' x, actM A (γ * γ') x = actM A γ (actM A γ' x)) ∧ ∀ γ, (∀ w, gM A γ w = 1) → γ = 1 := by
  first | exact @GlobalTheory.SnMass.VolN.actLaws | exact GlobalTheory.SnMass.VolN.actLaws | (intros; apply GlobalTheory.SnMass.VolN.actLaws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalBlockCovolumesProd
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalBlockCovolumesProd
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.VolN.Covol

theorem sum_UTr_fst (r : ℕ) (u : Fin r → ℝ) :
    ∑ p : UTr r, u p.1.1 = ∑ a : Fin r, ((r - 1 - (a : ℕ) : ℕ) : ℝ) * u a := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun x : Fin r × Fin r => x.1 < x.2)) (by simp)
    (fun x => u x.1)]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_filter]
  dsimp only
  rw [Finset.sum_const, nsmul_eq_mul, ← Fin.card_Ioi]
  congr 3
  ext b; simp

theorem sum_UTr_snd (r : ℕ) (v : Fin r → ℝ) :
    ∑ p : UTr r, v p.1.2 = ∑ b : Fin r, ((b : ℕ) : ℝ) * v b := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun x : Fin r × Fin r => x.1 < x.2)) (by simp)
    (fun x => v x.2)]
  rw [Finset.sum_filter, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_filter]
  dsimp only
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 2
  rw [← Fin.card_Iio b]; congr 1; ext a; simp

theorem sum_UTr (r : ℕ) (u v : Fin r → ℝ) :
    ∑ p : UTr r, (u p.1.1 + v p.1.2) =
      ∑ a : Fin r, (((r - 1 - (a : ℕ) : ℕ) : ℝ) * u a + ((a : ℕ) : ℝ) * v a) := by
  rw [Finset.sum_add_distrib, sum_UTr_fst, sum_UTr_snd, ← Finset.sum_add_distrib]

theorem sum_fin_quad (r : ℕ) (c₀ c₁ c₂ : ℝ) :
    ∑ a : Fin r, (c₀ + c₁ * ((a : ℕ) : ℝ) + c₂ * ((a : ℕ) : ℝ) ^ 2) =
      c₀ * r + c₁ * (r * (r - 1) / 2) + c₂ * ((r - 1) * r * (2 * r - 1) / 6) := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => c₀ + c₁ * (i : ℝ) + c₂ * (i : ℝ) ^ 2) r]
  induction r with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

end GlobalTheory.SnMass.VolN.Covol

namespace GlobalTheory.SnMass.VolN


open Covol in
theorem covol_blocks_prod : ∀ (d : ℝ) (f k r : ℕ) (s : Fin r → ℝ), 0 < d → (∀ a, 0 < s a) → (2 : ℝ) ^ (f * (r * (r - 1) + r * (k + 1))) * ((∏ p : UTr r, (2⁻¹ : ℝ) ^ f * d ^ (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ) + 2 * ((r - p.1.2.val : ℕ) : ℝ)) * (s p.1.1 / s p.1.2) ^ (2 * f)) * (∏ a : Fin r, ((2⁻¹ : ℝ) ^ f * d ^ (1 - 2 * ((r - a.val : ℕ) : ℝ)) * s a ^ (2 * f)) ^ (k + 1)) * (∏ p : UTr r, (2⁻¹ : ℝ) ^ f * d ^ (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ) - 2 * ((r - p.1.2.val : ℕ) : ℝ)) * (s p.1.1 * s p.1.2) ^ (2 * f)) * ∏ a : Fin r, d ^ (1 / 2 - 2 * ((r - a.val : ℕ) : ℝ)) * (s a ^ 2) ^ f) = d ^ (-(((k : ℝ) + 1) * (r : ℝ) ^ 2) - 4 * ((r : ℝ) ^ 3 - r) / 3 - 3 * (r : ℝ) / 2) * (∏ a : Fin r, s a ^ (4 * (r - (a : ℕ)) + 2 * k)) ^ f := by
  intro d f k r s hd hs
  obtain ⟨δ, rfl⟩ : ∃ δ, d = Real.exp δ := ⟨Real.log d, (Real.exp_log hd).symm⟩
  obtain ⟨σ, rfl⟩ : ∃ σ : Fin r → ℝ, s = fun a => Real.exp (σ a) :=
    ⟨fun a => Real.log (s a), funext fun a => (Real.exp_log (hs a)).symm⟩
  beta_reduce
  have h2i : (2⁻¹ : ℝ) = Real.exp (-Real.log 2) := by rw [Real.exp_neg, Real.exp_log two_pos]
  have e1 : ∀ p : UTr r, (2⁻¹ : ℝ) ^ f * Real.exp δ ^ (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ) +
      2 * ((r - p.1.2.val : ℕ) : ℝ)) * (Real.exp (σ p.1.1) / Real.exp (σ p.1.2)) ^ (2 * f) =
      Real.exp ((-(f : ℝ) * Real.log 2 + δ * (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ)) + 2 * f * σ p.1.1) +
        (2 * δ * ((r - p.1.2.val : ℕ) : ℝ) - 2 * f * σ p.1.2)) := by
    intro p
    rw [h2i]
    simp only [← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_sub, ← Real.exp_add]
    congr 1; push_cast; ring
  have e3 : ∀ p : UTr r, (2⁻¹ : ℝ) ^ f * Real.exp δ ^ (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ) -
      2 * ((r - p.1.2.val : ℕ) : ℝ)) * (Real.exp (σ p.1.1) * Real.exp (σ p.1.2)) ^ (2 * f) =
      Real.exp ((-(f : ℝ) * Real.log 2 + δ * (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ)) + 2 * f * σ p.1.1) +
        (-(2 * δ * ((r - p.1.2.val : ℕ) : ℝ)) + 2 * f * σ p.1.2)) := by
    intro p
    rw [h2i]
    simp only [← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1; push_cast; ring
  have e2 : ∀ a : Fin r, ((2⁻¹ : ℝ) ^ f * Real.exp δ ^ (1 - 2 * ((r - a.val : ℕ) : ℝ)) *
      Real.exp (σ a) ^ (2 * f)) ^ (k + 1) =
      Real.exp (((k : ℝ) + 1) * (-(f : ℝ) * Real.log 2 + δ * (1 - 2 * ((r - a.val : ℕ) : ℝ)) + 2 * f * σ a)) := by
    intro a
    rw [h2i]
    simp only [← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1; push_cast; ring
  have e4 : ∀ a : Fin r, Real.exp δ ^ (1 / 2 - 2 * ((r - a.val : ℕ) : ℝ)) * (Real.exp (σ a) ^ 2) ^ f =
      Real.exp (δ * (1 / 2 - 2 * ((r - a.val : ℕ) : ℝ)) + 2 * f * σ a) := by
    intro a
    simp only [← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1; push_cast; ring
  have e5 : ∀ a : Fin r, Real.exp (σ a) ^ (4 * (r - (a : ℕ)) + 2 * k) =
      Real.exp (((4 * (r - (a : ℕ)) + 2 * k : ℕ) : ℝ) * σ a) := fun a => (Real.exp_nat_mul _ _).symm
  rw [Finset.prod_congr rfl (fun p _ => e1 p), Finset.prod_congr rfl (fun a _ => e2 a),
    Finset.prod_congr rfl (fun p _ => e3 p), Finset.prod_congr rfl (fun a _ => e4 a),
    Finset.prod_congr rfl (fun a _ => e5 a)]
  have hu1 := sum_UTr r
    (fun a => -(f : ℝ) * Real.log 2 + δ * (1 - 2 * ((r - a.val : ℕ) : ℝ)) + 2 * f * σ a)
    (fun b => 2 * δ * ((r - b.val : ℕ) : ℝ) - 2 * f * σ b)
  have hu3 := sum_UTr r
    (fun a => -(f : ℝ) * Real.log 2 + δ * (1 - 2 * ((r - a.val : ℕ) : ℝ)) + 2 * f * σ a)
    (fun b => -(2 * δ * ((r - b.val : ℕ) : ℝ)) + 2 * f * σ b)
  beta_reduce at hu1 hu3
  rw [← Real.exp_sum, ← Real.exp_sum, ← Real.exp_sum, ← Real.exp_sum, ← Real.exp_sum, hu1, hu3]
  rw [show (2 : ℝ) ^ (f * (r * (r - 1) + r * (k + 1))) =
      Real.exp (((f * (r * (r - 1) + r * (k + 1)) : ℕ) : ℝ) * Real.log 2) by
    rw [Real.exp_nat_mul, Real.exp_log two_pos]]
  simp only [← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_add]
  rw [Real.exp_eq_exp]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← sub_eq_zero, show ∀ x y z w : ℝ, x + y - (z + w) = (y - w) + (x - z) from fun _ _ _ _ => by ring,
    ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (g := fun a : Fin r =>
      (δ * (2 * ((r : ℝ) - 1) * (1 - 2 * r) + ((k : ℝ) + 1) * (1 - 2 * r) + 1 / 2 - 2 * r) -
        Real.log 2 * f * (2 * r + k - 1)) +
      (δ * (8 * r + 2 * k - 2) + 2 * f * Real.log 2) * ((a : ℕ) : ℝ) + (-4 * δ) * ((a : ℕ) : ℝ) ^ 2) ?hc,
    sum_fin_quad]
  · have hN : ((f * (r * (r - 1) + r * (k + 1)) : ℕ) : ℝ) = f * (r * ((r : ℝ) - 1) + r * (k + 1)) := by
      rcases r with _ | n
      · simp
      · push_cast [Nat.add_sub_cancel]; ring
    rw [hN]; ring
  · intro a _
    have ha := a.isLt
    have h1 : ((r - (a : ℕ) : ℕ) : ℝ) = r - (a : ℕ) := by rw [Nat.cast_sub ha.le]
    have h2 : ((r - 1 - (a : ℕ) : ℕ) : ℝ) = r - 1 - (a : ℕ) := by
      rw [Nat.sub_sub, Nat.cast_sub (by omega)]; push_cast; ring
    have h3 : ((4 * (r - (a : ℕ)) + 2 * k : ℕ) : ℝ) = 4 * ((r : ℝ) - (a : ℕ)) + 2 * k := by
      push_cast [Nat.cast_sub ha.le]; ring
    rw [h3, h2, h1]; ring

end GlobalTheory.SnMass.VolN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalBlockCovolumesProdStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentRadical_blockCovolumes_prod : ∀ (d : ℝ) (f k r : ℕ) (s : Fin r → ℝ), 0 < d → (∀ a, 0 < s a) → (2 : ℝ) ^ (f * (r * (r - 1) + r * (k + 1))) * ((∏ p : UTr r, (2⁻¹ : ℝ) ^ f * d ^ (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ) + 2 * ((r - p.1.2.val : ℕ) : ℝ)) * (s p.1.1 / s p.1.2) ^ (2 * f)) * (∏ a : Fin r, ((2⁻¹ : ℝ) ^ f * d ^ (1 - 2 * ((r - a.val : ℕ) : ℝ)) * s a ^ (2 * f)) ^ (k + 1)) * (∏ p : UTr r, (2⁻¹ : ℝ) ^ f * d ^ (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ) - 2 * ((r - p.1.2.val : ℕ) : ℝ)) * (s p.1.1 * s p.1.2) ^ (2 * f)) * ∏ a : Fin r, d ^ (1 / 2 - 2 * ((r - a.val : ℕ) : ℝ)) * (s a ^ 2) ^ f) = d ^ (-(((k : ℝ) + 1) * (r : ℝ) ^ 2) - 4 * ((r : ℝ) ^ 3 - r) / 3 - 3 * (r : ℝ) / 2) * (∏ a : Fin r, s a ^ (4 * (r - (a : ℕ)) + 2 * k)) ^ f := by
  first | exact @GlobalTheory.SnMass.VolN.covol_blocks_prod | exact GlobalTheory.SnMass.VolN.covol_blocks_prod | (intros; apply GlobalTheory.SnMass.VolN.covol_blocks_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentBlockEntriesMulOfHasFlagDepthAtLeast
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentBlockEntriesMulOfHasFlagDepthAtLeast
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN.LeftMul

theorem pos_eI (k r : ℕ) (a : Fin r) : pos k r (eI k r a) = a.val := by
  have := a.isLt
  unfold pos eI
  dsimp only
  split_ifs <;> omega

theorem pos_wI (k r : ℕ) (j : Fin (k + 1)) : pos k r (wI k r j) = r := by
  have := j.isLt
  unfold pos wI
  dsimp only
  split_ifs <;> omega

theorem pos_esI (k r : ℕ) (a : Fin r) : pos k r (esI k r a) = 2 * r - a.val := by
  have := a.isLt
  unfold pos esI
  dsimp only
  split_ifs <;> omega

theorem mul_apply_of_dep (k r d : ℕ) (g x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hg : Dep k r d (g - 1)) (hx : Dep k r 1 (x - 1)) (i j : Fin (2 * r + k + 1)) (hij : i ≠ j)
    (hp : pos k r j ≤ pos k r i + d) : (g * x) i j = g i j + x i j := by
  have h1 : g * x = (g - 1) * (x - 1) + (g - 1) + (x - 1) + 1 := by noncomm_ring
  have h2 : ((g - 1) * (x - 1)) i j = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : pos k r l < pos k r i + d
    · rw [hg i l hl, zero_mul]
    · rw [hx l j (by omega), mul_zero]
  rw [h1, Matrix.add_apply, Matrix.add_apply, Matrix.add_apply, h2, Matrix.sub_apply, Matrix.sub_apply,
    Matrix.one_apply_ne hij]
  ring

end GlobalTheory.SnMass.VolN.LeftMul

namespace GlobalTheory.SnMass.VolN


open GlobalTheory.SnMass.VolN.LeftMul in
theorem cM_mul_of_dep : ∀ (k r : ℕ) (g x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (d : ℕ),
    Dep k r d (g - 1) → Dep k r 1 (x - 1) → ∀ β : Bk r, degB r β ≤ d →
      cM k r β (Matrix.of.symm (g * x)) = cM k r β (Matrix.of.symm x) + cM k r β (Matrix.of.symm g) := by
  intro k r g x d hg hx β hβ
  rcases β with p | a | p | a
  · have hlt : p.1.1.val < p.1.2.val := p.2
    simp only [degB] at hβ
    show (g * x) (eI k r p.1.1) (eI k r p.1.2) = x (eI k r p.1.1) (eI k r p.1.2) + g (eI k r p.1.1) (eI k r p.1.2)
    rw [mul_apply_of_dep k r d g x hg hx _ _ ?_ ?_, add_comm]
    · intro h; have := congrArg Fin.val h; simp only [eI] at this; omega
    · rw [pos_eI, pos_eI]; omega
  · simp only [degB] at hβ
    have ha := a.isLt
    show (fun j => (g * x) (eI k r a) (wI k r j)) = (fun j => x (eI k r a) (wI k r j)) + (fun j => g (eI k r a) (wI k r j))
    funext l
    rw [Pi.add_apply, mul_apply_of_dep k r d g x hg hx _ _ ?_ ?_, add_comm]
    · intro h; have := congrArg Fin.val h; simp only [eI, wI] at this; omega
    · rw [pos_eI, pos_wI]; omega
  · have hlt : p.1.1.val < p.1.2.val := p.2
    have hb := p.1.2.isLt
    simp only [degB] at hβ
    show (g * x) (eI k r p.1.1) (esI k r p.1.2) = x (eI k r p.1.1) (esI k r p.1.2) + g (eI k r p.1.1) (esI k r p.1.2)
    rw [mul_apply_of_dep k r d g x hg hx _ _ ?_ ?_, add_comm]
    · intro h; have := congrArg Fin.val h; simp only [eI, esI] at this; omega
    · rw [pos_eI, pos_esI]; omega
  · simp only [degB] at hβ
    have ha := a.isLt
    show ((g * x) (eI k r a) (esI k r a)).im = (x (eI k r a) (esI k r a)).im + (g (eI k r a) (esI k r a)).im
    rw [mul_apply_of_dep k r d g x hg hx _ _ ?_ ?_, Complex.add_im, add_comm]
    · intro h; have := congrArg Fin.val h; simp only [eI, esI] at this; omega
    · rw [pos_eI, pos_esI]; omega

end GlobalTheory.SnMass.VolN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentBlockEntriesMulOfHasFlagDepthAtLeastStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentBlockEntries_mul_of_hasFlagDepthAtLeast : ∀ (k r : ℕ) (g x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (d : ℕ), Dep k r d (g - 1) → Dep k r 1 (x - 1) → ∀ β : Bk r, degB r β ≤ d → cM k r β (Matrix.of.symm (g * x)) = cM k r β (Matrix.of.symm x) + cM k r β (Matrix.of.symm g) := by
  first | exact @GlobalTheory.SnMass.VolN.cM_mul_of_dep | exact GlobalTheory.SnMass.VolN.cM_mul_of_dep | (intros; apply GlobalTheory.SnMass.VolN.cM_mul_of_dep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ReAntidiagonalEntryEqZeroOfFlagDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ReAntidiagonalEntryEqZeroOfFlagDepth
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem re_corner_eq_zero (k r : ℕ) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r)
    (hx : x ∈ Nset k r) (hd : Dep k r (2 * r - 2 * a.val) (x - 1)) :
    (x (eI k r a) (esI k r a)).re = 0 := by
  have hsv : (esI k r a).val = 2 * r + k - a.val := rfl
  have hev : (eI k r a).val = a.val := rfl
  generalize esI k r a = s at *
  generalize eI k r a = e at *
  have ha := a.isLt

  have hcol : ∀ i : Fin (2 * r + k + 1), a.val < i.val → i ≠ s → x i s = 0 := by
    intro i hi hne
    have h0 := hd i s (by
      simp only [pos]
      split_ifs <;> first | rfl | omega | (exfalso; omega))
    rw [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero] at h0; exact h0
  have hss : x s s = 1 := by
    have h0 := hd s s (by simp only [pos]; split_ifs <;> first | rfl | omega | (exfalso; omega))
    rw [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at h0; exact h0
  have hU := congrFun (congrFun hx.1 s) s
  have hH : Hpk k r s s = 0 := by
    simp only [Hpk, Fin.ext_iff, and_true]
    split_ifs <;> first | rfl | omega | (exfalso; omega)
  rw [hH] at hU
  have key : ∀ i j : Fin (2 * r + k + 1), star (x i s) * Hpk k r i j * x j s =
      (if i = s ∧ j = e then x j s else 0) + (if i = e ∧ j = s then star (x i s) else 0) := by
    intro i j
    by_cases h1 : i = s ∧ j = e
    · rw [h1.1, h1.2]
      have hes : e ≠ s := fun h => by have := congrArg Fin.val h; omega
      have : Hpk k r s e = 1 := by simp only [Hpk, Fin.ext_iff, and_true]; split_ifs <;> first | rfl | omega | (exfalso; omega)
      simp [hes, hes.symm, this, hss]
    by_cases h2 : i = e ∧ j = s
    · rw [h2.1, h2.2]
      have hes : e ≠ s := fun h => by have := congrArg Fin.val h; omega
      have : Hpk k r e s = 1 := by simp only [Hpk, Fin.ext_iff, and_true]; split_ifs <;> first | rfl | omega | (exfalso; omega)
      simp [hes, hes.symm, this, hss]
    rw [if_neg h1, if_neg h2, add_zero]
    have hi : i = s ∨ i.val ≤ a.val ∨ x i s = 0 := by
      by_cases h : i = s
      · exact Or.inl h
      by_cases h' : i.val ≤ a.val
      · exact Or.inr (Or.inl h')
      exact Or.inr (Or.inr (hcol i (by omega) h))
    have hj : j = s ∨ j.val ≤ a.val ∨ x j s = 0 := by
      by_cases h : j = s
      · exact Or.inl h
      by_cases h' : j.val ≤ a.val
      · exact Or.inr (Or.inl h')
      exact Or.inr (Or.inr (hcol j (by omega) h))
    have hI : ∀ i : Fin (2 * r + k + 1), i = s ↔ i.val = 2 * r + k - a.val := fun i =>
      ⟨fun h => h ▸ hsv, fun h => Fin.ext (h.trans hsv.symm)⟩
    have hE : ∀ i : Fin (2 * r + k + 1), i = e ↔ i.val = a.val := fun i =>
      ⟨fun h => h ▸ hev, fun h => Fin.ext (h.trans hev.symm)⟩
    rw [hI, hE] at h1 h2
    rcases hi with hi | hi | hi
    · rcases hj with hj | hj | hj
      · subst hi; subst hj; simp [hH]
      · have : Hpk k r i j = 0 := by
          rw [hI] at hi
          simp only [Hpk, Fin.ext_iff, and_true]; split_ifs <;> first | rfl | omega | (exfalso; omega)
        simp [this]
      · simp [hj]
    · rcases hj with hj | hj | hj
      · have : Hpk k r i j = 0 := by
          rw [hI] at hj
          simp only [Hpk, Fin.ext_iff, and_true]; split_ifs <;> first | rfl | omega | (exfalso; omega)
        simp [this]
      · have : Hpk k r i j = 0 := by
          simp only [Hpk, Fin.ext_iff, and_true]; split_ifs <;> first | rfl | omega | (exfalso; omega)
        simp [this]
      · simp [hj]
    · simp [hi]
  have hsum : (xᴴ * Hpk k r * x) s s = x e s + star (x e s) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [key, Finset.sum_add_distrib]
    simp [ite_and, hss]
  rw [hsum] at hU
  have := congrArg Complex.re hU
  simp at this
  linarith

end GlobalTheory.SnMass.VolN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ReAntidiagonalEntryEqZeroOfFlagDepthStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.re_antidiagonal_entry_eq_zero_of_flagDepth : ∀ (k r : ℕ) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r), x ∈ Nset k r → Dep k r (2 * r - 2 * a.val) (x - 1) → (x (eI k r a) (esI k r a)).re = 0 := by
  first | exact @GlobalTheory.SnMass.VolN.re_corner_eq_zero | exact GlobalTheory.SnMass.VolN.re_corner_eq_zero | (intros; apply GlobalTheory.SnMass.VolN.re_corner_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeIntegralUnipotentRadicalRealPoints
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem cM_one (k r : ℕ) (β : Bk r) : cM k r β (Matrix.of.symm 1) = 0 := by
  rcases β with p | a | p | a
  · show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (eI k r p.1.1) (eI k r p.1.2) = 0
    exact Matrix.one_apply_ne (fun h => p.2.ne (by simpa [eI, Fin.ext_iff] using h))
  · funext j
    show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (eI k r a) (wI k r j) = 0
    refine Matrix.one_apply_ne (fun h => ?_)
    have h' := congrArg Fin.val h
    simp only [eI, wI] at h'
    have := a.isLt
    omega
  · show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (eI k r p.1.1) (esI k r p.1.2) = 0
    refine Matrix.one_apply_ne (fun h => ?_)
    have h' := congrArg Fin.val h
    simp only [eI, esI] at h'
    have := p.1.1.isLt
    have := p.1.2.isLt
    omega
  · show ((1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (eI k r a) (esI k r a)).im = 0
    rw [Matrix.one_apply]
    split_ifs <;> simp

theorem pos_le (k r : ℕ) (i : Fin (2 * r + k + 1)) : pos k r i ≤ 2 * r := by
  have := i.isLt
  unfold pos
  split_ifs <;> omega

theorem eq_one_of_dep {k r : ℕ} {x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (h : Dep k r (2 * r + 1) (x - 1)) : x = 1 := by
  refine sub_eq_zero.1 (Matrix.ext fun i j => ?_)
  exact h i j (by have := pos_le k r j; omega)

theorem countable_units (E : Type) [Field E] [NumberField E] (n : ℕ) :
    Countable (Matrix (Fin n) (Fin n) E)ˣ := by
  haveI : Countable E :=
    Function.Injective.countable (Module.finBasis ℚ E).equivFun.injective
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  exact Function.Injective.countable (f := fun u : (Matrix (Fin n) (Fin n) E)ˣ => (u : Matrix (Fin n) (Fin n) E))
    Units.val_injective

theorem ofReal_five (t u h c g : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (hh : 0 ≤ h) (hc : 0 ≤ c) (hg : 0 ≤ g) :
    ENNReal.ofReal (t * (u * h * c * g)) =
      ENNReal.ofReal t * (ENNReal.ofReal u * ENNReal.ofReal h * ENNReal.ofReal c * ENNReal.ofReal g) := by
  rw [ENNReal.ofReal_mul ht, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul hu]

abbrev MM (k r : ℕ) (E : Type) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E

theorem covolume_N : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → IsHermND σ J → GlobalTheory.SgGlob.SelfDual (σ : E →+* E) J Λ → IsFrame (σ : E →+* E) J (algebraMap F E T) P → IsDual (σ : E →+* E) J P f → tupLat (id1 E r) (sideM P f) ≤ Λ → IsModelAt J A → (∀ a, 0 < s a) → Adapted A P f s → AllSome (IsDomN (σ : E →+* E) J Λ P A) fun 𝓓 => Measure.pi (fun _ : InfinitePlace E => haarLie (Nset k r) 1) 𝓓 = ENNReal.ofReal (|(NumberField.discr F : ℝ)| ^ (-(((k : ℝ) + 1) * (r : ℝ) ^ 2) - 4 * ((r : ℝ) ^ 3 - r) / 3 - 3 * (r : ℝ) / 2) * (∏ a : Fin r, s a ^ (4 * (r - (a : ℕ)) + 2 * k)) ^ Fintype.card (InfinitePlace E)) := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hV : IsVolData σ J Λ P f T A s := ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  obtain ⟨⟨G, hG⟩, hGu⟩ := GlobalTheory.T.integralUnipotentRadical_forms_unit_subgroup F E σ k r J Λ P f T A s hV
  obtain ⟨ha1, ha2, ha3⟩ := GlobalTheory.T.unipotentModelAction_isAction_and_faithful F E σ k r J Λ P f T A s hV
  have hmem := GlobalTheory.T.integralUnipotent_mem_modelUnipotentAtPlace F E σ k r J Λ P f T A s hV
  choose DU hDUm hDUf hDUv using fun p : UTr r =>
    GlobalTheory.T.covolume_inverseDifferentPow_div_lattice F E σ h1 h2 (r - p.1.1.val) (r - p.1.2.val) (s p.1.1 / s p.1.2) (div_pos (h9 _) (h9 _))
  choose DC hDCm hDCf hDCv using fun p : UTr r =>
    GlobalTheory.T.covolume_inverseDifferentPow_mul_lattice F E σ h1 h2 (r - p.1.1.val) (r - p.1.2.val) (s p.1.1 * s p.1.2) (mul_pos (h9 _) (h9 _))
  choose DH hDHm hDHf hDHv using GlobalTheory.T.covolume_middleLattice_homLattice_ideal F E σ k r J Λ P f T A s hV
  choose DG hDGm hDGf hDGv using fun a : Fin r =>
    GlobalTheory.T.skewLattice_inverseDifferentPow_covolume F E σ h1 h2 (r - a.val) (s a ^ 2) (pow_pos (h9 _) 2)
  let LB := blkSet (InfinitePlace E) k r
    (fun p => (ideLat (dInv E (r - p.1.1.val) * (dInv E (r - p.1.2.val))⁻¹) (s p.1.1 / s p.1.2) : Set _))
    (fun a => homLat (σ : E →+* E) J Λ P f A (dInv E (r - a.val)) (s a))
    (fun p => (ideLat (dInv E (r - p.1.1.val) * dInv E (r - p.1.2.val)) (s p.1.1 * s p.1.2) : Set _))
    (fun a => (skewLat (σ : E →+* E) (dInv E (2 * (r - a.val))) (s a ^ 2) : Set _))
  let DB := blkSet (InfinitePlace E) k r DU DH DC DG
  let NN : Set (InfinitePlace E → Mt k r) := {x | ∀ w, Matrix.of (x w) ∈ Nset k r}
  let ρ : G → (InfinitePlace E → Mt k r) → (InfinitePlace E → Mt k r) :=
    fun g => actM A ((g : (MM k r E)ˣ) : MM k r E)
  let o : InfinitePlace E → Mt k r := fun _ => Matrix.of.symm 1
  let gm : G → InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
    fun g => gM A ((g : (MM k r E)ˣ) : MM k r E)
  have hρo : ∀ g w, ρ g o w = Matrix.of.symm (gm g w) := fun g w => by
    show Matrix.of.symm (gm g w * 1) = Matrix.of.symm (gm g w)
    rw [mul_one]
  have hgm : ∀ g w, gm g w ∈ Nset k r := fun g => hmem _ ((hG _).1 g.2)
  have hρ1 : ∀ x, ρ 1 x = x := fun x => by
    have e : (((1 : G) : (MM k r E)ˣ) : MM k r E) = 1 := rfl
    show actM A (((1 : G) : (MM k r E)ˣ) : MM k r E) x = x
    rw [e]; exact ha1 x
  have hρm : ∀ g h x, ρ (g * h) x = ρ g (ρ h x) := fun g h x => by
    have e : (((g * h : G) : (MM k r E)ˣ) : MM k r E) = ((g : (MM k r E)ˣ) : MM k r E) * ((h : (MM k r E)ˣ) : MM k r E) := rfl
    show actM A (((g * h : G) : (MM k r E)ˣ) : MM k r E) x = _
    rw [e]; exact ha2 _ _ x
  have hρN : ∀ g, ∀ x ∈ NN, ρ g x ∈ NN := fun g x hx w =>
    PI.AmpOrbQuot.nset_mul (hgm g w) (hx w)
  have hdep : ∀ (g : G) (d : ℕ), (∀ β : Bk r, degB r β < d →
      (fun w => cM k r β (ρ g o w)) = 0) → ∀ w, Dep k r d (gm g w - 1) := fun g d hg w =>
    GlobalTheory.T.hasFlagDepthAtLeast_of_free_entries_vanish k r _ d (hgm g w) fun β hβ => by
      have := congrFun (hg β hβ) w
      rwa [hρo] at this
  have tw := GlobalTheory.T.existsUnique_layered_strictFundamentalDomain (V := fun β : Bk r => InfinitePlace E → VM k r β) ρ NN o (degB r)
    (fun β x w => cM k r β (x w)) LB DB (fun w => by
      change Matrix.of (Matrix.of.symm 1) ∈ Nset k r
      rw [Equiv.apply_symm_apply]
      exact PI.AmpOrbQuot.nset_one) hρ1 hρm hρN
    (by
      rintro (p | a | p | a)
      · exact (ideLat _ _).zero_mem
      · exact ⟨0, ⟨fun a => by simp [form], fun c _ => by simp⟩, fun w l => by
          have e : (fun i => w.embedding ((0 : Fin (2 * r + k + 1) → E) i)) = 0 := by ext; simp
          rw [e, Matrix.mulVec_zero]
          simp [herm]
          rfl⟩
      · exact (ideLat _ _).zero_mem
      · exact (skewLat _ _ _).zero_mem)
    (by
      rintro (p | a | p | a) v
      · exact hDUf p v
      · exact hDHf a v
      · exact hDCf p v
      · exact hDGf a v)
    (fun β => funext fun w => cM_one k r β)
    (fun d g hg x hx β hβ => funext fun w => by
      have := GlobalTheory.T.unipotentBlockEntries_mul_of_hasFlagDepthAtLeast k r (gm g w) (Matrix.of (x w)) d (hdep g d hg w) (GlobalTheory.T.flagUnipotent_block_upper_unitriangular k r _ (hx w)) β hβ
      show cM k r β (ρ g x w) = cM k r β (x w) + cM k r β (ρ g o w)
      rw [hρo]
      exact this)
    (by
      intro g β hβ
      have hgN := (hG _).1 g.2
      have e : (fun w => cM k r β (ρ g o w)) = fun w => cM k r β (Matrix.of.symm (gm g w)) :=
        funext fun w => by rw [hρo]
      show (fun w => cM k r β (ρ g o w)) ∈ LB β
      rw [e]
      rcases β with p | a | p | a
      · exact GlobalTheory.T.integralUnipotent_entry_mem_inverseDifferentLattice F E σ k r J Λ P f T A s hV _ hgN p
      · exact GlobalTheory.T.integralUnipotent_middleRow_mem_homLattice F E σ k r J Λ P f T A s hV _ hgN a
      · exact GlobalTheory.T.integralUnipotent_corner_entry_mem_idealLattice F E σ k r J Λ P f T A s hV _ hgN p
      · exact GlobalTheory.T.integralUnipotent_antidiagonal_mem_skewLattice F E σ k r J Λ P f T A s hV _ hgN a fun w =>
          GlobalTheory.T.re_antidiagonal_entry_eq_zero_of_flagDepth k r _ a (hgm g w) (hdep g _ hβ w))
    (by
      have lift : ∀ (β : Bk r) (l : InfinitePlace E → VM k r β),
          (∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = l w) ∧
            ∀ β' : Bk r, β' ≠ β → degB r β' ≤ degB r β → ∀ w, cM k r β' (Matrix.of.symm (gM A γ w)) = 0) →
          ∃ g : G, (fun w => cM k r β (ρ g o w)) = l ∧ ∀ β', β' ≠ β → degB r β' ≤ degB r β →
            (fun w => cM k r β' (ρ g o w)) = 0 := by
        rintro β l ⟨γ, hγ, hl, h0⟩
        obtain ⟨u, rfl⟩ := hGu γ hγ
        refine ⟨⟨u, (hG u).2 hγ⟩, funext fun w => ?_, fun β' h h' => funext fun w => ?_⟩
        · rw [hρo]; exact hl w
        · rw [hρo]; exact h0 β' h h' w
      rintro (p | a | p | a) l hl
      · exact lift _ _ (GlobalTheory.T.exists_integral_unipotent_lift_entry F E σ k r J Λ P f T A s hV p l hl)
      · exact lift _ _ (GlobalTheory.T.lift_row_middleSpace_integralPoint F E σ k r J Λ P f T A s hV a l hl)
      · exact lift _ _ (GlobalTheory.T.exists_integral_unipotent_lift_corner F E σ k r J Λ P f T A s hV p l hl)
      · exact lift _ _ (GlobalTheory.T.exists_integral_unipotent_lift_antidiagonal F E σ k r J Λ P f T A s hV a l hl))
    (fun g hg => by
      have h1' : ∀ w, gm g w = 1 := fun w => eq_one_of_dep (hdep g _ (fun β _ => hg β) w)
      exact Subtype.ext (Units.ext (ha3 _ h1')))
  obtain ⟨hNm, hN0⟩ := GlobalTheory.T.pi_unipotentModel_measurable_full_measure (InfinitePlace E) k r
  obtain ⟨hDm, hDv⟩ := GlobalTheory.T.measure_unipotent_tuples_free_entry_blocks (InfinitePlace E) k r DU DH DC DG hDUm hDHm hDCm hDGm
  set Dset : Set (InfinitePlace E → Mt k r) := {x | (∀ w, Matrix.of (x w) ∈ Nset k r) ∧
    ∀ β : Bk r, (fun w => cM k r β (x w)) ∈ blkSet (InfinitePlace E) k r DU DH DC DG β} with hDset
  have hstrict : ∀ x ∈ NN, ∃! g : G, ρ g x ∈ Dset := fun x hx => by
    obtain ⟨g, hg, hu⟩ := tw x hx
    exact ⟨g, ⟨hρN g x hx, hg⟩, fun g' hg' => hu g' hg'.2⟩
  have conv : ∀ S : Set (InfinitePlace E → Mt k r), (∀ x ∈ NN, ∃! g : G, ρ g x ∈ S) ↔
      ∀ x ∈ NN, ∃! γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E,
        (InN (σ : E →+* E) J P γ ∧ latMap γ Λ = Λ) ∧ actM A γ x ∈ S := fun S => by
    refine forall₂_congr fun x hx => ?_
    constructor
    · rintro ⟨g, hg, hu⟩
      refine ⟨_, ⟨(hG _).1 g.2, hg⟩, fun γ hγ => ?_⟩
      obtain ⟨u, rfl⟩ := hGu γ hγ.1
      exact congrArg (fun g : G => ((g : (MM k r E)ˣ) : MM k r E)) (hu ⟨u, (hG u).2 hγ.1⟩ hγ.2)
    · rintro ⟨γ, hγ, hu⟩
      obtain ⟨u, rfl⟩ := hGu γ hγ.1
      refine ⟨⟨u, (hG u).2 hγ.1⟩, hγ.2, fun g hg => ?_⟩
      exact Subtype.ext (Units.ext (hu _ ⟨(hG _).1 g.2, hg⟩))
  haveI : Countable G := by
    haveI := countable_units E (2 * r + k + 1)
    infer_instance
  refine ⟨⟨Dset, hDm, (conv Dset).1 hstrict⟩, fun 𝓓 h𝓓 => ?_⟩
  have hEq := GlobalTheory.T.strictFundamentalDomain_measure_eq (G := G) _ ρ NN 𝓓 Dset hNm hN0 h𝓓.1 hDm hρ1 hρm hρN
    (fun g => GlobalTheory.T.unipotentModelProductAction_measurePreserving E k r A _ (hgm g)) ((conv 𝓓).2 h𝓓.2) hstrict
  beta_reduce
  rw [hEq, hDv]
  simp only [hDUv, hDHv, hDCv, hDGv]
  have hd : 0 < |(NumberField.discr F : ℝ)| := abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero F)
  rw [← GlobalTheory.T.unipotentRadical_blockCovolumes_prod _ (Fintype.card (InfinitePlace E)) k r s hd h9]
  have nnU : ∀ p : UTr r, 0 ≤ (2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ) + 2 * ((r - p.1.2.val : ℕ) : ℝ)) * (s p.1.1 / s p.1.2) ^ (2 * Fintype.card (InfinitePlace E)) := fun p => by
    have := h9 p.1.1; have := h9 p.1.2; positivity
  have nnC : ∀ p : UTr r, 0 ≤ (2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ) - 2 * ((r - p.1.2.val : ℕ) : ℝ)) * (s p.1.1 * s p.1.2) ^ (2 * Fintype.card (InfinitePlace E)) := fun p => by
    have := h9 p.1.1; have := h9 p.1.2; positivity
  have nnH : ∀ a : Fin r, 0 ≤ ((2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * ((r - a.val : ℕ) : ℝ)) * s a ^ (2 * Fintype.card (InfinitePlace E))) ^ (k + 1) := fun a => by
    have := h9 a; positivity
  have nnG : ∀ a : Fin r, 0 ≤ |(NumberField.discr F : ℝ)| ^ (1 / 2 - 2 * ((r - a.val : ℕ) : ℝ)) * (s a ^ 2) ^ Fintype.card (InfinitePlace E) := fun a => by
    have := h9 a; positivity
  rw [← ENNReal.ofReal_prod_of_nonneg fun p _ => nnU p, ← ENNReal.ofReal_prod_of_nonneg fun a _ => nnH a,
    ← ENNReal.ofReal_prod_of_nonneg fun p _ => nnC p, ← ENNReal.ofReal_prod_of_nonneg fun a _ => nnG a,
    ofReal_five _ _ _ _ _ (by positivity) (Finset.prod_nonneg fun p _ => nnU p) (Finset.prod_nonneg fun a _ => nnH a)
      (Finset.prod_nonneg fun p _ => nnC p) (Finset.prod_nonneg fun a _ => nnG a),
    ENNReal.ofReal_pow (by norm_num)]
  simp

end GlobalTheory.SnMass.VolN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeIntegralUnipotentRadicalRealPointsStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_integral_unipotentRadical_real_points : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → IsHermND σ J → GlobalTheory.SgGlob.SelfDual (σ : E →+* E) J Λ → IsFrame (σ : E →+* E) J (algebraMap F E T) P → IsDual (σ : E →+* E) J P f → tupLat (id1 E r) (sideM P f) ≤ Λ → IsModelAt J A → (∀ a, 0 < s a) → Adapted A P f s → AllSome (IsDomN (σ : E →+* E) J Λ P A) fun 𝓓 => Measure.pi (fun _ : InfinitePlace E => haarLie (Nset k r) 1) 𝓓 = ENNReal.ofReal (|(NumberField.discr F : ℝ)| ^ (-(((k : ℝ) + 1) * (r : ℝ) ^ 2) - 4 * ((r : ℝ) ^ 3 - r) / 3 - 3 * (r : ℝ) / 2) * (∏ a : Fin r, s a ^ (4 * (r - (a : ℕ)) + 2 * k)) ^ Fintype.card (InfinitePlace E)) := by
  first | exact @GlobalTheory.SnMass.VolN.covolume_N | exact GlobalTheory.SnMass.VolN.covolume_N | (intros; apply GlobalTheory.SnMass.VolN.covolume_N <;> assumption)
end
