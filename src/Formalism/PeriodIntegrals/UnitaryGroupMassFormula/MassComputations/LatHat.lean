module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.IsCompactStabGLHat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.ContinuousSplitA

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.LatHat
noncomputable section

namespace MassDataMassesW.KCptW

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures MeasureTheory NumberField IsDedekindDomain
  Topology PI.AdicCompletionValuation MassDataLevelSSteps.LatTop MassDataLevelSSteps Matrix

section Sand

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem tensMap_smul' {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (φ : R →ₐ[F] R')
    (c : R) (z : R ⊗[F] E) : tensMap (E := E) φ (c • z) = φ c • tensMap (E := E) φ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [tensMap, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem continuous_tensEval (v : HeightOneSpectrum (𝓞 F)) : Continuous (tensMap (E := E) (evalV F v)) := by
  let f : Af F ⊗[F] E →ₛₗ[(evalV F v : Af F →+* Fv F v)] Fv F v ⊗[F] E :=
    { toFun := tensMap (E := E) (evalV F v), map_add' := map_add _,
      map_smul' := fun c z => tensMap_smul' (evalV F v) c z }
  exact IsModuleTopology.continuous_of_linearMapₛₗ (R := Af F) (S := Fv F v)
    (σ := (evalV F v : Af F →+* Fv F v)) (by exact RestrictedProduct.continuous_eval v) f

theorem continuous_pv (v : HeightOneSpectrum (𝓞 F)) : Continuous (pv (E := E) (n := n) v) :=
  continuous_pi fun i => (continuous_tensEval v).comp (continuous_apply i)

theorem pv_add (v : HeightOneSpectrum (𝓞 F)) (x y : Fin n → Af F ⊗[F] E) : pv v (x + y) = pv v x + pv v y := by
  funext i; simp [pv]

theorem pv_zero (v : HeightOneSpectrum (𝓞 F)) : pv (E := E) (n := n) v 0 = 0 := by
  funext i; simp [pv]

theorem pv_neg (v : HeightOneSpectrum (𝓞 F)) (x : Fin n → Af F ⊗[F] E) : pv v (-x) = -pv v x := by
  funext i; simp [pv]

theorem pv_zsmul (v : HeightOneSpectrum (𝓞 F)) (N : ℤ) (x : Fin n → Af F ⊗[F] E) : pv v (N • x) = N • pv v x := by
  funext i; simp [pv]

theorem ratV_zsmul (v : HeightOneSpectrum (𝓞 F)) (N : ℤ) (x : Fin n → E) :
    ratV (F := F) (Fv F v) (N • x) = N • ratV (F := F) (Fv F v) x := by
  funext i; simp [ratV]

theorem zsmul_mem_latLoc_of (L0 L : Set (Fin n → E)) (N : ℤ) (h : ∀ μ ∈ L0, N • μ ∈ L)
    (v : HeightOneSpectrum (𝓞 F)) {y : Fin n → Fv F v ⊗[F] E} (hy : y ∈ latLoc (E := E) v L0) :
    N • y ∈ latLoc (E := E) v L := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨μ, hμ, rfl⟩ := hz
    rw [← ratV_zsmul]
    exact Submodule.subset_span ⟨_, h μ hμ, rfl⟩
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ c ha

theorem zsmul_mem_latHat (L0 L : Set (Fin n → E)) (N : ℤ) (h : ∀ μ ∈ L0, N • μ ∈ L)
    {x : Fin n → Af F ⊗[F] E} (hx : x ∈ latHat (F := F) L0) : N • x ∈ latHat (F := F) L := by
  intro v
  rw [pv_zsmul]
  exact zsmul_mem_latLoc_of L0 L N h v (hx v)

def stdSub : Submodule (𝓞 E) (Fin n → E) :=
  Submodule.pi Set.univ fun _ => LinearMap.range (Algebra.linearMap (𝓞 E) E)

theorem single_mem_std (j : Fin n) : (Pi.single j (1 : E) : Fin n → E) ∈ (stdSub : Submodule (𝓞 E) (Fin n → E)) := by
  classical
  rw [stdSub, Submodule.mem_pi]
  intro i _
  rw [Pi.single_apply]
  split_ifs
  · exact LinearMap.mem_range.2 ⟨1, by simp⟩
  · exact zero_mem _

theorem span_std : Submodule.span E ((stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) = ⊤ := by
  classical
  refine eq_top_iff.2 fun x _ => ?_
  rw [← Finset.univ_sum_single x]
  refine Submodule.sum_mem _ fun i _ => ?_
  have e : (Pi.single i (x i) : Fin n → E) = x i • (Pi.single i (1 : E) : Fin n → E) := by
    ext k
    by_cases h : k = i
    · subst h; simp
    · simp [h]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (single_mem_std i))

theorem std_mult (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ μ ∈ ((stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)), N • μ ∈ (L : Set (Fin n → E)) := by
  classical
  obtain ⟨N, hN0, hN⟩ := exists_common_mult L hL (fun j : Fin n => (Pi.single j (1 : E) : Fin n → E))
  refine ⟨N, hN0, fun μ hμ => ?_⟩
  have hμ' : ∀ j, ∃ a : 𝓞 E, Algebra.linearMap (𝓞 E) E a = μ j := fun j =>
    LinearMap.mem_range.1 ((Submodule.mem_pi.1 hμ) j (Set.mem_univ _))
  choose a ha using hμ'
  have e : N • μ = ∑ j, a j • (N • (Pi.single j (1 : E) : Fin n → E)) := by
    ext k
    simp only [Pi.smul_apply, Finset.sum_apply, Pi.single_apply, smul_ite, smul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← ha k, Algebra.linearMap_apply]
    simp only [Algebra.smul_def, mul_one, eq_intCast, zsmul_eq_mul]
    ring
  rw [e]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hN j)

theorem lat_mult (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ μ ∈ (L : Set (Fin n → E)), N • μ ∈ ((stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  classical
  obtain ⟨S, hS⟩ := hfg
  obtain ⟨N, hN0, hN⟩ := exists_common_mult (stdSub : Submodule (𝓞 E) (Fin n → E)) span_std
    (fun s : S => (s : Fin n → E))
  refine ⟨N, hN0, fun μ hμ => ?_⟩
  have hμ' : μ ∈ Submodule.span (𝓞 E) (S : Set (Fin n → E)) := by rw [hS]; exact hμ
  clear hμ
  induction hμ' using Submodule.span_induction with
  | mem z hz => exact hN ⟨z, hz⟩
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ c ha

end Sand

def StdHatOpen : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ},
    IsOpen (latHat (F := F) ((stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)))

def StdHatCompact : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ},
    IsCompact (latHat (F := F) ((stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)))

theorem zsmul_eq_cast_smul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} (N : ℤ)
    (x : Fin n → Af F ⊗[F] E) : N • x = (N : F) • x :=
  (Int.cast_smul_eq_zsmul F N x).symm

theorem latHatOpen_of (h0 : StdHatOpen) : LatHatOpen := by
  intro F E _ _ _ _ _ n L hL _
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  obtain ⟨N, hN0, hN⟩ := std_mult L hL
  have hNF : (N : F) ≠ 0 := Int.cast_ne_zero.mpr hN0
  let G : AddSubgroup (Fin n → Af F ⊗[F] E) :=
    { carrier := latHat (F := F) (L : Set (Fin n → E))
      add_mem' := fun {x y} hx hy v => by rw [pv_add]; exact add_mem (hx v) (hy v)
      zero_mem' := fun v => by rw [pv_zero]; exact zero_mem _
      neg_mem' := fun {x} hx v => by rw [pv_neg]; exact neg_mem (hx v) }
  let W : Set (Fin n → Af F ⊗[F] E) :=
    {x | (N : F)⁻¹ • x ∈ latHat (F := F) ((stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E))}
  have hWo : IsOpen W := (h0 (F := F) (E := E) (n := n)).preimage (continuous_const_smul _)
  have hW0 : (0 : Fin n → Af F ⊗[F] E) ∈ W := by
    have h00 : (N : F)⁻¹ • (0 : Fin n → Af F ⊗[F] E) = 0 := smul_zero _
    show (N : F)⁻¹ • (0 : Fin n → Af F ⊗[F] E) ∈ latHat (F := F) _
    rw [h00]
    intro v
    rw [pv_zero]
    exact zero_mem _
  have hWG : W ⊆ (G : Set (Fin n → Af F ⊗[F] E)) := by
    intro x hx
    have h := zsmul_mem_latHat _ _ N hN hx
    rwa [zsmul_eq_cast_smul, smul_smul, mul_inv_cancel₀ hNF, one_smul] at h
  exact G.isOpen_of_mem_nhds (Filter.mem_of_superset (hWo.mem_nhds hW0) hWG)

theorem latHatCompact_of (h0 : StdHatCompact) : LatHatCompact := by
  intro F E _ _ _ _ _ n L hL hfg
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  obtain ⟨N, hN0, hN⟩ := lat_mult L hfg
  have hNF : (N : F) ≠ 0 := Int.cast_ne_zero.mpr hN0
  have hcl : IsClosed (latHat (F := F) (L : Set (Fin n → E))) := by
    have e : latHat (F := F) (L : Set (Fin n → E)) =
        ⋂ v, pv v ⁻¹' (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) := by
      ext x
      simp [latHat]
    rw [e]
    exact isClosed_iInter fun v => (((latLoc (E := E) v (L : Set (Fin n → E))).toAddSubgroup.isClosed_of_isOpen
      (isOpen_latLoc v L hL))).preimage (continuous_pv v)
  refine ((h0 (F := F) (E := E) (n := n)).image (continuous_const_smul ((N : F)⁻¹))).of_isClosed_subset hcl ?_
  intro x hx
  refine ⟨N • x, zsmul_mem_latHat _ _ N hN hx, ?_⟩
  show (N : F)⁻¹ • (N • x) = x
  rw [zsmul_eq_cast_smul, smul_smul, inv_mul_cancel₀ hNF, one_smul]

end MassDataMassesW.KCptW

namespace MassDataMassesW

open KCptW

end MassDataMassesW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.MassHNonneg
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.CountableRatOf
noncomputable section

open MeasureTheory NumberField
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets

namespace MassDataMassesW

theorem countable_ratOf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (K : Subgroup (HA (AF F) σ J)) :
    Countable (ratOf (K := K)) := by
  haveI := PI.VolStabSW.um_countable_HFinIn F E σ M J
  refine Function.Injective.countable (f := fun x : ratOf (K := K) =>
    (⟨((x : K) : HA (AF F) σ J), Subgroup.mem_comap.1 x.2⟩ : HFinIn (AF F) σ J)) ?_
  intro x y hxy
  have e := congrArg Subtype.val hxy
  exact Subtype.ext (Subtype.ext e)

theorem smulInv_ratOf {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (K : Subgroup G)
    (Γ : Subgroup K) (μ : Measure K) [μ.IsMulLeftInvariant] : SMulInvariantMeasure Γ K μ := by
  first
  | exact inferInstance
  | exact ⟨fun c s _ => by
      show μ ((fun x : K => (c : K) * x) ⁻¹' s) = μ s
      exact measure_preimage_mul μ (c : K) s⟩

theorem covol_eq_of_fd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) [MeasurableMul (HA (AF F) σ J)]
    (K : Subgroup (HA (AF F) σ J)) (μ : Measure K) (hμ : μ.IsMulLeftInvariant) (𝓕 : Set K)
    (h𝓕 : IsFundamentalDomain (ratOf (K := K)) 𝓕 μ) : covol μ = (μ 𝓕).toReal := by
  haveI := hμ
  haveI := countable_ratOf σ J K
  haveI := smulInv_ratOf K (ratOf (K := K)) μ
  unfold covol
  split_ifs with h
  · congr 1
    exact h.choose_spec.measure_eq h𝓕
  · exact absurd ⟨𝓕, h𝓕⟩ h

theorem n4cov_holds : UnipotentCoveringCount := by
  intro D X u 𝓕 hN h𝓕
  exact covol_eq_of_fd _ _ _ _ hN.2.2.2.1.toIsMulLeftInvariant 𝓕 h𝓕

end MassDataMassesW
end
end

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets
open scoped TensorProduct

namespace MassDataMassesW

theorem massH_nonneg {D : D7} (X : HidaSetting D) (u : D.what₂.Word) :
    0 ≤ massH X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) (frameOf X u) :=
  finsum_nonneg fun _ => inv_nonneg.2 (Nat.cast_nonneg _)

theorem massAll_of (hH : HinfCompact) (hK : KCompactOpen) (hC : ClassFinite) : MassAll := by
  intro D X hb u hT
  have : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  have hN := X.measW_norm u
  have hcs := hH X u
  have hfin : MassFinite (G := ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) (GamH X u) (KH X u) :=
    ⟨hC X u, stabFinite_of hH hK X u⟩
  obtain ⟨𝓕, h𝓕⟩ := fdExistsH_holds X u
  have hKU : MeasurableSet ((KH X u : Subgroup ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) :
      Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) :=
    ((hK X).2.preimage continuous_subtype_val).measurableSet
  have hU := massUnfold_gen X.B.I.cm.sig X.B.I.J (frameOf X u) (isCMExt_of_cmData X.B.I.cm)
    (isHermND_of_setting X) (X.measW u) hN (KH X u) hKU hfin 𝓕 h𝓕
  have hcov : covol (X.measW u).μH = ((X.measW u).μH 𝓕).toReal :=
    covol_eq_of_fd X.B.I.cm.sig X.B.I.J _ (X.measW u).μH hN.1.toIsMulLeftInvariant 𝓕 h𝓕
  have hV : X.muH u Set.univ = (X.measW u).μHinf Set.univ := by
    have h := (hT.2.2.2 u).2
    have h1 := congrArg (fun m => m Set.univ) h
    have hm : Measurable (X.toInf hb) := by
      haveI : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
      unfold Formalism.L2.SG.HidaSetting.HidaSetting.toInf
      exact (continuous_fst.comp ((continuous_splitA _ _).comp
        ((Formalism.L2.SG.AdBridge.toHA X.B.I hb).continuous.comp (continuous_id.prodMk continuous_const)))).measurable
    rw [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ] at h1
    rw [← h1]
    unfold Formalism.L2.SG.Measures.amb
    rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, Set.preimage_univ]

  have h1 := hN.2.1
  have h2 := hN.2.2.1
  have ha0 : (X.measW u).μHinf Set.univ ≠ 0 :=
    (isOpen_univ.measure_pos _ Set.univ_nonempty).ne'
  have haT : (X.measW u).μHinf Set.univ ≠ ⊤ :=
    (h1.toIsFiniteMeasureOnCompacts.lt_top_of_isCompact (@isCompact_univ _ _ (hH X u))).ne
  have hKo : IsOpen (Subtype.val ⁻¹' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) :
      Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) :=
    (hK X).2.preimage continuous_subtype_val
  have hb0 : (X.measW u).μHf (Subtype.val ⁻¹' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))) ≠ 0 :=
    h2.toIsOpenPosMeasure.open_pos _ hKo ⟨1, (KX X).one_mem⟩
  have hcl : IsClosed ((Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) :
      Subgroup (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) :=
    isClosed_stabT' X.B.I.cm.sig X.B.I.J (Af X.B.I.F) (tupH (frameOf X u))
  have hbT : (X.measW u).μHf (Subtype.val ⁻¹' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))) ≠ ⊤ :=
    (h2.toIsFiniteMeasureOnCompacts.lt_top_of_isCompact
      (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage (hK X).1)).ne
  have ha : 0 < ((X.measW u).μHinf Set.univ).toReal := ENNReal.toReal_pos ha0 haT
  have hb' : 0 < ((X.measW u).μHf (Subtype.val ⁻¹' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))).toReal :=
    ENNReal.toReal_pos hb0 hbT
  unfold MassAt
  rw [hcov]
  unfold frameOf at hU ⊢
  rw [hU, hV, ENNReal.toReal_mul, ENNReal.toReal_mul]
  change massH _ _ _ (frameOf X u) =
    ((X.measW u).μHinf Set.univ).toReal *
      ((X.measW u).μHf (Subtype.val ⁻¹' (KX X : Set _))).toReal *
      (ENNReal.ofReal (massH _ _ _ (frameOf X u))).toReal / _
  rw [ENNReal.toReal_ofReal (massH_nonneg X u)]
  field_simp

end MassDataMassesW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.EllipticCentralizerQuotientCompact
noncomputable section

open MeasureTheory NumberField Set
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets
open scoped TensorProduct

namespace MassDataMassesW

theorem prod_rect_of_ne_zero {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (ν : Measure β) (h0 : μ.prod ν ≠ 0) {s : Set α} {t : Set β} (hs : MeasurableSet s)
    (ht : MeasurableSet t) : μ.prod ν (s ×ˢ t) = μ s * ν t := by
  have hν : SFinite ν := by
    by_contra hν
    exact h0 (Measure.prod_eq_zero_of_not_sfinite hν)
  letI : SFinite ν := hν
  exact Measure.prod_prod s t

theorem tauF_eq_comm {D : D7} (X : HidaSetting D) (y : AF X.B.I.F ⊗[X.B.I.F] X.B.I.E) :
    tauF X.B.I y = Algebra.TensorProduct.comm X.B.I.F (Af X.B.I.F) X.B.I.E
      (tensMap (E := X.B.I.E) (sndA X.B.I.F) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [tauF_tmul]
    rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem toHA_fin_one {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (s : X.B.I.Ginf) :
    (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (s, 1))).2 = 1 := by
  have hbr := ((toHA_isBridge X.B.I hb) (s, 1)).2
  apply Subtype.ext
  apply Units.ext
  ext i j
  have e := congrFun (congrFun hbr i) j
  simp only [ofHAFin, Matrix.map_apply] at e
  rw [tauF_eq_comm] at e
  have e2 := congrArg (Algebra.TensorProduct.comm X.B.I.F (Af X.B.I.F) X.B.I.E).symm e
  rw [AlgEquiv.symm_apply_apply] at e2
  show tensMap (E := X.B.I.E) (sndA X.B.I.F) _ = _
  rw [← e2]
  show _ = (1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)) i j
  simp only [Formalism.MainNotions.S.AutInst.fmat, OneMemClass.coe_one, Units.val_one, Matrix.one_apply]
  split_ifs <;> simp

section Split

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

theorem eq_one_of_toHA_fin {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (p : X.B.I.GA)
    (h : (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb p)).2 = 1) : p.2 = 1 := by
  have hbr := ((toHA_isBridge X.B.I hb) p).2
  apply Subtype.ext
  apply Units.ext
  ext i j
  have e := congrFun (congrFun hbr i) j
  simp only [ofHAFin, Matrix.map_apply] at e
  rw [tauF_eq_comm] at e
  have h2 : tensMap (E := X.B.I.E) (sndA X.B.I.F) (hmat X.B.I (toHA X.B.I hb p) i j) =
      (1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)) i j := by
    have := congrArg (fun g : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J =>
      (HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J g).val i j) h
    exact this
  rw [h2] at e
  rw [Formalism.MainNotions.S.AutInst.fmat] at e
  show _ = (1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) i j
  rw [e, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem split_unitary_infinite_one (s : X.B.I.Ginf) :
    splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (s, 1)) = (X.toInf hb s, 1) :=
  Prod.ext rfl (toHA_fin_one X hb s)

theorem toInf_injective (hS : SplitIso) : Function.Injective (X.toInf hb) := by
  intro s t hst
  obtain ⟨e, he⟩ := hS X.B.I.cm.sig X.B.I.J
  have h1 : e (toHA X.B.I hb (s, 1)) = e (toHA X.B.I hb (t, 1)) := by
    rw [he, split_unitary_infinite_one, split_unitary_infinite_one, hst]
  have h2 := (toHA X.B.I hb).injective (e.injective h1)
  exact congrArg Prod.fst h2

theorem continuous_toInf_of (hS : SplitIso) : Continuous (X.toInf hb) := by
  obtain ⟨e, he⟩ := hS X.B.I.cm.sig X.B.I.J
  have hc : Continuous (splitA X.B.I.cm.sig X.B.I.J) := by rw [← he]; exact e.continuous_toFun
  exact continuous_fst.comp (hc.comp ((toHA X.B.I hb).continuous_toFun.comp
    (continuous_id.prodMk continuous_const)))

theorem measurable_toInf_of (hS : SplitIso) : Measurable (X.toInf hb) := by
  haveI : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  exact (continuous_toInf_of X hb hS).measurable

theorem measurableSet_image_toInf (hS : SplitIso) {FdN : Set X.B.I.Ginf} (hF : MeasurableSet FdN) :
    MeasurableSet (X.toInf hb '' FdN) := by
  obtain ⟨e, he⟩ := hS X.B.I.cm.sig X.B.I.J
  let Φ : X.B.I.GA ≃ₜ* (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J × HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    (toHA X.B.I hb).trans e
  have hΦ : ∀ s, Φ (s, 1) = (X.toInf hb s, 1) := fun s => by
    show e (toHA X.B.I hb (s, 1)) = _
    rw [he]
    exact split_unitary_infinite_one X hb s
  let ψ : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J → X.B.I.GA := fun y => Φ.symm (y, 1)
  have hψc : Continuous ψ := Φ.symm.continuous_toFun.comp (continuous_id.prodMk continuous_const)
  have hset : X.toInf hb '' FdN = (fun y => (ψ y).1) ⁻¹' FdN := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      show (Φ.symm (X.toInf hb s, 1)).1 ∈ FdN
      rw [← hΦ, Φ.symm_apply_apply]
      exact hs
    · intro h1
      have h2 : (ψ y).2 = 1 := by
        apply eq_one_of_toHA_fin X hb
        have h3 : e (toHA X.B.I hb (ψ y)) = (y, 1) := Φ.apply_symm_apply _
        rw [he] at h3
        rw [h3]
      refine ⟨(ψ y).1, h1, ?_⟩
      have hp : ψ y = ((ψ y).1, 1) := Prod.ext rfl h2
      have := congrArg Φ hp
      rw [show Φ (ψ y) = (y, 1) from Φ.apply_symm_apply _, hΦ] at this
      exact (congrArg Prod.fst this).symm
  haveI : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  rw [hset]
  exact (continuous_fst.comp hψc).measurable hF

end Split

theorem elliptic_centralizer_quotient_compact (hKo : KCompactOpen) : N4 := by
  intro hS D X hb u FdN hT hTie hF
  haveI : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  haveI : BorelSpace (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  haveI : BorelSpace (HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  obtain ⟨e, he⟩ := hS X.B.I.cm.sig X.B.I.J
  have hc : Continuous (splitA X.B.I.cm.sig X.B.I.J) := by rw [← he]; exact e.continuous_toFun
  have hm : Measurable (splitA X.B.I.cm.sig X.B.I.J) :=
    (continuous_fst.comp hc).measurable.prodMk (continuous_snd.comp hc).measurable
  have hTm : MeasurableSet (X.toInf hb '' FdN) := measurableSet_image_toInf X hb hS hF.1
  have hKm : MeasurableSet (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) := (hKo X).2.measurableSet
  have hRm : MeasurableSet ((X.toInf hb '' FdN) ×ˢ (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))) :=
    hTm.prod hKm
  have hFd : FdA X hb u FdN = Subtype.val ⁻¹' (splitA X.B.I.cm.sig X.B.I.J ⁻¹'
      ((X.toInf hb '' FdN) ×ˢ (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))) := by
    ext n
    simp only [FdA, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, Set.mem_image]
    constructor
    · rintro ⟨s, hs, h1, h2⟩
      exact ⟨⟨s, hs, h1.symm⟩, h2⟩
    · rintro ⟨⟨s, hs, h1⟩, h2⟩
      exact ⟨s, hs, h1.symm, h2⟩
  have hN := hT.2.2.2.2.2.2.2.2.2.1
  have hHaar : (X.measW u).μN.IsHaarMeasure := hT.2.2.2.1
  have h0 : (amb (X.measW u).μNinf).prod (amb (X.measW u).μNf) ≠ 0 := by
    rw [← hN]
    intro h
    have h' := congrArg (fun μ => μ Set.univ) h
    simp only [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ,
      Measure.map_apply measurable_subtype_coe MeasurableSet.univ, Measure.coe_zero, Pi.zero_apply] at h'
    exact (isOpen_univ.measure_ne_zero (X.measW u).μN Set.univ_nonempty) h'
  rw [hFd]
  erw [← Measure.map_apply measurable_subtype_coe (hm hRm)]
  rw [← Measure.map_apply hm hRm]
  change ((amb (X.measW u).μN).map (splitA X.B.I.cm.sig X.B.I.J)) _ = _
  rw [hN, prod_rect_of_ne_zero _ _ h0 hTm hKm, (hTie.2.2.2 u).1,
    Measure.map_apply (measurable_toInf_of X hb hS) hTm, Set.preimage_image_eq _ (toInf_injective X hb hS),
    Measure.map_apply measurable_subtype_coe hKm]

end MassDataMassesW
end
end
