module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocMIterateDiag
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftInvSubtypeSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergLawApply
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCovariance
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanHaarScalingNorm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTwistedRankQuotient
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.DictKAOfParts

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

variable {D : D7} {n ρ p : ℕ} {hn : ρ + p = n}

abbrev rt (ξ : Matrix (Fin ρ) (Fin p) D.host.E) : Mx D ρ p := ξ.map (incA D)

def chv (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (x y : Mx D ρ p) : ℂ :=
  ψ (trA (Matrix.trace (pr b₀ x y)))

def jc (y x : Mx D ρ p) : hermA D ρ :=
  ⟨(HMul.hMul y (adj x) : Mx D ρ ρ) + (HMul.hMul x (adj y) : Mx D ρ ρ), by
    have key : ∀ a b : Mx D ρ p, adj (HMul.hMul a (adj b) : Mx D ρ ρ) = (HMul.hMul b (adj a) : Mx D ρ ρ) := by
      intro a b
      ext i j
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul,
        Formalism.L2.Theta.cA_cA]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    show adj _ = _
    have : adj ((HMul.hMul y (adj x) : Mx D ρ ρ) + (HMul.hMul x (adj y) : Mx D ρ ρ)) = adj (HMul.hMul y (adj x) : Mx D ρ ρ) + adj (HMul.hMul x (adj y) : Mx D ρ ρ) := by
      ext i j
      simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, map_add (f := _)]
    rw [this, key, key, add_comm]⟩

def dsum (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (Φ : Mx D ρ p → ℂ) (x y : Mx D ρ p) : ℂ :=
  ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, chv ψ b₀ x (rt ξ) * Φ (rt ξ + y)

def Ap (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (Φ φ : Mx D ρ p → ℂ) (v : Mx D ρ p × Mx D ρ p) : ℂ :=
  dsum ψ b₀ Φ v.2 v.1 * conj (dsum ψ b₀ φ v.2 v.1)

theorem th_zero (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (φ : Mx D ρ p → ℂ) (x y : Mx D ρ p) :
    th ψ b₀ φ 0 x y = dsum ψ b₀ φ x y := by
  have h0 : chz ψ b₀ (0 : hermA D ρ) = 1 := by
    have : (Matrix.trace (HMul.hMul (b₀.1.map (incA D)) (0 : hermA D ρ).1 : Mx D ρ ρ)) = 0 := by
      simp
    rw [chz, this]
    simp [halfTr, trA]
  rw [th, h0, one_mul]
  rfl

theorem tsum_meas {ι X : Type} [Countable ι] [MeasurableSpace X] {f : ι → X → ℂ}
    (hf : ∀ i, StronglyMeasurable (f i)) (hs : ∀ a, Summable fun i => f i a) :
    StronglyMeasurable fun a => ∑' i, f i a := by
  refine stronglyMeasurable_of_tendsto (u := (atTop : Filter (Finset ι)))
    (f := fun (s : Finset ι) a => ∑ i ∈ s, f i a) (fun s => ?_) ?_
  · exact Finset.stronglyMeasurable_fun_sum _ fun i _ => hf i
  · exact tendsto_pi_nhds.2 fun a => (hs a).hasSum

end GlobalTheory.CompanionTheory.FJE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSegmentRepresentation
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSegmentRepresentation
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegExists

theorem hasFiniteLength_prodIrr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL (k := k))
    (hd : ∑ a, (x a).1 = N) : HasFiniteLength (prodIrr x hd) :=
  GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k _ _ _ _ _ _ (isSmooth_piTensor fun a => (x a).2.rep.smooth)
    (hasFiniteLength_of_isIrreducible (GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA x))

theorem exists_isLSeg : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k), ∃ π : IrrRep (GL (Fin Δ.deg) k), IsLSeg Δ π.ρ := by
  intro k _ _ _ _ hA Δ
  have hd : ∑ a, (Δ.term a).1 = Δ.deg := Δ.sum_term_fst
  obtain ⟨hd', ⟨φ⟩⟩ := GlobalTheory.T.contragredient_segment_product_equiv hA Δ hd
  obtain ⟨τ', hτ'⟩ := GlobalTheory.T.exists_socle_segment_product hA (segDual Δ) hd'
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompanionTheory.CosocleContra.isCosocle_of_isSocle_contra hA (prodIrr Δ.term hd)
    (isSmooth_prodIrr _ _) (hasFiniteLength_prodIrr hA _ _) τ' (hτ'.of_equiv (.refl _) φ.symm)
  exact ⟨τ, hd, hτ⟩

end GlobalTheory.CompanionTheory.SegExists

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSegmentRepresentationStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_segment_representation : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k), ∃ π : IrrRep (GL (Fin Δ.deg) k), IsLSeg Δ π.ρ := by
  first | exact @GlobalTheory.CompanionTheory.SegExists.exists_isLSeg | exact GlobalTheory.CompanionTheory.SegExists.exists_isLSeg | (intros; apply GlobalTheory.CompanionTheory.SegExists.exists_isLSeg <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralContinuous
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralContinuous
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.BigCellJ

theorem integrable_schwartzA {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} {μ : Measure (Mx D m n)}
    {𝓕 : Set (Mx D m n)} (hμ : IsCovolOne (ratMx D m n) μ 𝓕) {φ : Mx D m n → ℂ}
    (hφ : φ ∈ schwartzA θ m n) : Integrable φ μ := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.TowerRestrict.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI := hμ.1
  haveI i6 : DiscreteTopology (ratMx D m n) := i5
  haveI : SecondCountableTopology (ratMx D m n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : Countable (ratMx D m n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hc : Continuous φ := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ φ hφ).1
  have hU : GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiAbs.UnifSummable (ratMx D m n).subtype φ := fun Q hQ => by
    obtain ⟨b, hb1, hb2⟩ := GlobalTheory.CompanionTheory.ThetaPoisson.translates_bound hθ ⟨φ, hφ⟩ Q hQ
    refine ⟨b, hb1, fun c x hx => ?_⟩
    have h := hb2 x hx c
    rwa [add_comm] at h
  exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiAbs.integrable_of_unif hc hU μ hK fun x => by
    obtain ⟨γ, hγ, h⟩ := hKc x
    refine ⟨⟨-γ, (ratMx D m n).neg_mem hγ⟩, ?_⟩
    simpa [sub_neg_eq_add, add_comm] using h

theorem continuous_halfTr {D : D7} : Continuous (halfTr : AE D → AF D.host.F) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have ht : Continuous (trA : AE D → AF D.host.F) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  unfold halfTr
  exact continuous_const.mul ht

theorem continuous_integral_twist {X Y : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {μ : Measure Y} {φ : Y → ℂ} {g : X → Y → ℂ} (hi : Integrable φ μ)
    (hj : Continuous fun p : X × Y => g p.1 p.2) (hn : ∀ b y, ‖g b y‖ = 1) :
    Continuous fun b => ∫ y, φ y * g b y ∂μ := by
  have hg1 : ∀ b, AEStronglyMeasurable (g b) μ := fun b =>
    (hj.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hg2 : ∀ y, Continuous fun b => g b y := fun y =>
    hj.comp (continuous_id.prodMk continuous_const)
  refine continuous_of_dominated (bound := fun y => ‖φ y‖) (fun b => ?_) (fun b => ?_) hi.norm ?_
  · exact hi.aestronglyMeasurable.mul (hg1 b)
  · refine Filter.Eventually.of_forall fun y => ?_
    rw [norm_mul, hn, mul_one]
  · refine Filter.Eventually.of_forall fun y => ?_
    exact (hg2 y).const_mul (φ y)

theorem continuous_inner_self {D : D7} (V : HSp D) (r : ℕ) :
    Continuous fun y : Mx D V.rank r => (GlobalTheory.StdUnn.inner V y y : Mx D r r) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  unfold GlobalTheory.StdUnn.inner
  exact GlobalTheory.MixModel.continuous_adj.matrix_mul (continuous_const.matrix_mul continuous_id)

theorem continuous_phase {D : D7} (V : HSp D) (r : ℕ) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsCharAF D.host.F ψ) :
    Continuous fun p : hermA D r × Mx D V.rank r =>
      ψ (halfTr (Matrix.trace (HMul.hMul p.1.1 (GlobalTheory.StdUnn.inner V p.2 p.2) : Mx D r r))) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact hψ.1.comp (continuous_halfTr.comp
    ((continuous_subtype_val.comp continuous_fst).matrix_mul
      ((continuous_inner_self V r).comp continuous_snd)).matrix_trace)

theorem jt_continuous : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (μ : Measure (Mx D V.rank r)) (φ : Mx D V.rank r → ℂ), IsCharAF D.host.F ψ → IsInfFam θ →
    (∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕) → φ ∈ schwartzA θ V.rank r → Continuous (Jt ψ V μ φ) := by
  intro D r V ψ θ μ φ hψ hθ ⟨𝓕, hμ⟩ hφ
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.TowerRestrict.lattice_Mx D V.rank r
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := GlobalTheory.TowerRestrict.lattice_Mx D r r
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  haveI : SecondCountableTopology (hermA D r) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : FirstCountableTopology (hermA D r) :=
    TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  exact continuous_integral_twist (g := fun (b : hermA D r) (y : Mx D V.rank r) =>
      ψ (halfTr (Matrix.trace (HMul.hMul b.1 (GlobalTheory.StdUnn.inner V y y) : Mx D r r))))
    (integrable_schwartzA hθ hμ hφ) (continuous_phase V r hψ) (fun b y => hψ.2.1 _)

end GlobalTheory.CompanionTheory.BigCellJ

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralContinuousStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_integral_continuous : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r)) (φ : Mx D V.rank r → ℂ), IsCharAF D.host.F ψ → IsInfFam θ → (∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕) → φ ∈ schwartzA θ V.rank r → Continuous (Jt ψ V μ φ) := by
  first | exact @GlobalTheory.CompanionTheory.BigCellJ.jt_continuous | exact GlobalTheory.CompanionTheory.BigCellJ.jt_continuous | (intros; apply GlobalTheory.CompanionTheory.BigCellJ.jt_continuous <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjugatePlacesFacts
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjugatePlacesFacts
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.ConjAtPlaces

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

abbrev cc : E ≃+* E := (IsCMField.complexConj E).toRingEquiv

def conjPerm : Equiv.Perm (HeightOneSpectrum (𝓞 E)) where
  toFun := conjSrc (cc E)
  invFun := conjSrc (cc E)
  left_inv := GlobalTheory.ThetaPull.conjSrc_conjSrc
  right_inv := GlobalTheory.ThetaPull.conjSrc_conjSrc

variable {E}

def conjCompl (w : HeightOneSpectrum (𝓞 E)) : (conjPerm E w).adicCompletion E ≃+* w.adicCompletion E :=
  RingEquiv.ofBijective (conjLoc (cc E) w)
    ⟨(conjLoc (cc E) w).injective, GlobalTheory.CuspRep.ParLaws.conjLoc_surjective (cc E) w⟩

theorem norm_conjCompl (w : HeightOneSpectrum (𝓞 E)) (y : (conjPerm E w).adicCompletion E) :
    ‖conjCompl w y‖ = ‖y‖ := by
  have key : ∀ (a b : NNReal) (ha : a ≠ 0) (hb : b ≠ 0), a = b → ∀ z,
      WithZeroMulInt.toNNReal ha z = WithZeroMulInt.toNNReal hb z := by
    rintro a _ ha hb rfl z
    rfl
  have hv : Valued.v (conjCompl w y) = Valued.v y := (conjLoc_spec (cc E) w).2.2 y
  have hN : (Ideal.absNorm w.asIdeal : NNReal) = Ideal.absNorm (conjPerm E w).asIdeal := by
    rw [show Ideal.absNorm (conjPerm E w).asIdeal = Ideal.absNorm w.asIdeal from
      GlobalTheory.UnrEuler.ConjFac.absNorm_conjSrc (cc E) w]
  rw [FinitePlace.norm_def, FinitePlace.norm_def, hv, key _ _ _ _ hN]

theorem conjPlaces : ConjPlaces := by
  intro E _ _ _
  refine ⟨fun v u => ?_, fun c => conjAd_algebraMap c, conjPerm E, conjCompl, norm_conjCompl, fun w u => ?_⟩
  · exact congrFun (GlobalTheory.ThetaPull.pInf_conjAd u) v
  · rfl

end GlobalTheory.CompanionTheory.ConjAtPlaces

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjugatePlacesFactsStatement
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_places_facts : ConjPlaces := by
  first | exact @GlobalTheory.CompanionTheory.ConjAtPlaces.conjPlaces | exact GlobalTheory.CompanionTheory.ConjAtPlaces.conjPlaces | (intros; apply GlobalTheory.CompanionTheory.ConjAtPlaces.conjPlaces <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralEqThetaPartNondegenerate
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralEqThetaPartNondegenerate
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.ThetaGlue

section Abstract

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct ENNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem meanC_thetaS_of_lintegral (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (μ : Measure (HA (AF F) σ J))
    (𝓕 : Set (HA (AF F) σ J)) (S : Set (Fin n → Fin M → E))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (hm : Measurable Φ)
    (hfin : ∫⁻ h in 𝓕, ∑' x : S, ‖Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (x : Fin n → Fin M → E)))‖ₑ ∂μ < ⊤) :
    meanC μ 𝓕 (thetaS F E σ M J Φ S) = ∫ X, Φ X ∂(thetaMeas σ J μ 𝓕 S) := by
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)
  have := hB n M
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ (AF F)
  have ha : ∀ X, Measurable fun h : HA (AF F) σ J => actW (AF F) σ J h⁻¹ X := fun X =>
    ((hact n).1.comp (continuous_inv.prodMk continuous_const)).measurable
  have : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.symm.toEquiv
  have hsum : ∑' X : S, ∫⁻ h in 𝓕, ‖Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) X.1))‖ₑ ∂μ ≠ ⊤ := by
    rw [← lintegral_tsum (f := fun (X : S) h => ‖Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) X.1))‖ₑ)
      fun X => (hm.enorm.comp (ha _)).aemeasurable]
    exact hfin.ne
  have hint : Integrable Φ (Measure.sum fun X : S =>
      (μ.restrict 𝓕).map fun h => actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    change ∫⁻ X, ‖Φ X‖ₑ ∂_ < ⊤
    rw [lintegral_sum_measure]
    simp only [lintegral_map hm.enorm (ha _)]
    exact hsum.lt_top
  rw [thetaMeas, integral_smul_measure, integral_sum_measure hint, meanC, ENNReal.toReal_inv]
  simp only [integral_map (ha _).aemeasurable hm.aestronglyMeasurable]
  exact congrArg _ (integral_tsum (fun X => (hm.comp (ha _)).aestronglyMeasurable) hsum)

end Abstract

end GlobalTheory.CompanionTheory.SiegelND.ThetaGlue

end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.ThetaGlue

variable {D : D7}

def colsOf {m r : ℕ} (X : Fin r → Fin m → D.host.E) : Matrix (Fin m) (Fin r) D.host.E :=
  Matrix.of fun i a => X a i

theorem gramQ_colsOf (V : HSp D) {r : ℕ} (X : Fin r → Fin V.rank → D.host.E) :
    gramQ V (colsOf X) = HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig V.gram X := by
  refine Matrix.ext fun a b => ?_
  change ∑ i, D.sp.cm.sig (X a i) * ∑ j, V.gram i j * X b j =
    ∑ i, ∑ j, D.sp.cm.sig (X a i) * V.gram i j * X b j
  simp only [Finset.mul_sum, mul_assoc]

theorem rank_eq_of_gramQ (V : HSp D) {r : ℕ} (x : Matrix (Fin V.rank) (Fin r) D.host.E)
    (h : (gramQ V x).det ≠ 0) : x.rank = r := by
  refine le_antisymm (Matrix.rank_le_width x) ?_
  have h1 : (gramQ V x).rank = r := by
    have := Matrix.rank_of_isUnit (gramQ V x) ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h))
    simpa using this
  have h2 : gramQ V x = ((x.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose * HSpace.gram V) * x := by
    rw [gramQ, Matrix.mul_assoc]
  calc r = (gramQ V x).rank := h1.symm
    _ ≤ x.rank := by
      rw [h2]
      exact Matrix.rank_mul_le_right _ _

def fibEquiv (V : HSp D) {r : ℕ} (β : HermE D r) (hβ : β.1.det ≠ 0) :
    {X : Fin r → Fin V.rank → D.host.E | HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig V.gram X = β.1} ≃
      {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1} where
  toFun X := ⟨colsOf X.1, rank_eq_of_gramQ V _ (by rw [gramQ_colsOf, X.2]; exact hβ),
    (gramQ_colsOf V X.1).trans X.2⟩
  invFun x := ⟨fun a i => x.1 i a, (gramQ_colsOf V _).symm.trans x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem tupOf_actW (V : HSp D) {r : ℕ} (h : GA D V) (X : Fin r → Fin V.rank → D.host.E) :
    tupOf (GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram h⁻¹ (HeckeCharacterZeroLocus.SiegelWeilU.ratTup (AF D.host.F) X)) =
      HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) ((colsOf X).map (incA D)) := by
  ext i a
  rfl

theorem average_eq_meanC (V : HSp D) (ν μH : Measure (GA D V)) (hν : ν.IsHaarMeasure) (hμ : μH.IsHaarMeasure)
    (𝓕 : Set (GA D V)) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μH) (f : GA D V → ℂ) (hf : LeftInv (GQ V) f) :
    ⨍ q, descend (GQ V) f q ∂autMeasure V ν = HeckeCharacterZeroLocus.SiegelWeilU.meanC μH 𝓕 f := by
  have : BorelSpace (GA D V) := ⟨rfl⟩
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V
  obtain ⟨h0, h1, -⟩ := GlobalTheory.Published.SiegelOneVector.normalise D.sp.cm.sig V.gram (GlobalTheory.DefiniteQuotient.cmExt D)
    (GlobalTheory.DefiniteQuotient.gram_hermND V) μH 𝓕 hμ h𝓕
  have e := Measure.isMulLeftInvariant_eq_smul μH ν
  set c := Measure.haarScalarFactor μH ν
  have e1 : autMeasure V μH = (c : ENNReal) • autMeasure V ν := by
    rw [← GlobalTheory.AutomorphicL2Unitary.quotMeasure_smul]
    exact congrArg _ e
  have e2 : μH 𝓕 = c * autMeasure V ν Set.univ := by
    rw [← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ h𝓕]
    exact congrArg (fun m : Measure (AutQ V) => m Set.univ) e1
  have hc0 : ((c : ℝ≥0∞)).toReal ≠ 0 := by
    intro h
    have : (c : ℝ≥0∞) = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).1 h with h | h
      · exact h
      · exact absurd h ENNReal.coe_ne_top
    rw [this, zero_mul] at e2
    exact h0 e2
  have e3 : ∫ g in 𝓕, f g ∂μH = (c : ℝ≥0∞).toReal • ∫ q, descend (GQ V) f q ∂autMeasure V ν := by
    have h3 := GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h𝓕 (descend (GQ V) f)
    simp only [hf.descend_mk] at h3
    rw [← h3]
    change ∫ q, descend (GQ V) f q ∂autMeasure V μH = _
    rw [e1, integral_smul_measure]
  rw [average_eq, HeckeCharacterZeroLocus.SiegelWeilU.meanC, e3, e2, ENNReal.toReal_mul, smul_smul, Measure.real,
    mul_inv, mul_comm ((c : ℝ≥0∞).toReal)⁻¹, mul_assoc, inv_mul_cancel₀ hc0, mul_one]

theorem setLIntegral_absTheta_lt_top (V : HSp D) (ν μH : Measure (GA D V)) (hν : ν.IsHaarMeasure)
    (hμ : μH.IsHaarMeasure) (𝓕 : Set (GA D V)) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μH) {r : ℕ}
    (φ : Mx D V.rank r → ℂ) (habs : GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤) :
    ∫⁻ h in 𝓕, GlobalTheory.SiegelFormula.absTheta V φ h ∂μH < ⊤ := by
  have : BorelSpace (GA D V) := ⟨rfl⟩
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V
  have e := Measure.isMulLeftInvariant_eq_smul μH ν
  set c := Measure.haarScalarFactor μH ν
  have e1 : autMeasure V μH = (c : ENNReal) • autMeasure V ν := by
    rw [← GlobalTheory.AutomorphicL2Unitary.quotMeasure_smul]
    exact congrArg _ e
  have hL := GlobalTheory.SiegelFormula.leftInv_absTheta V φ
  have h3 := GlobalTheory.AutomorphicL2Unitary.lintegral_quotMeasure h𝓕 (descend (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ))
  simp only [hL.descend_mk] at h3
  rw [← h3]
  change ∫⁻ q, descend (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ) q ∂autMeasure V μH < ⊤
  rw [e1, lintegral_smul_measure]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top habs


set_option maxHeartbeats 1000000 in
theorem ifrB_eq_thetaPartD : ∀ (D : D7) (r : ℕ) (V : HSp D) (θ : InfFam D), IsInfFam θ → ∀ ν : Measure (GA D V), ν.IsHaarMeasure →
    ∀ φ : Mx D V.rank r → ℂ, φ ∈ schwartzA θ V.rank r → GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤ →
    ∀ (μH : Measure (GA D V)) (𝓕 : Set (GA D V)), μH.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μH →
    ∀ β : HermE D r, β.1.det ≠ 0 → IfrB V ν φ β = thetaPartD V μH 𝓕 φ β := by
  intro D r V θ hθ ν hν φ hφ habs μH 𝓕 hμ h𝓕 β hβ
  have hcm := GlobalTheory.DefiniteQuotient.cmExt D
  have hJ := GlobalTheory.DefiniteQuotient.gram_hermND V
  have hcont : Continuous φ :=
    (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ φ hφ).1
  obtain ⟨⟨lcA, scA, t2A⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable D.host.F
  haveI := lcA
  haveI := scA
  haveI := t2A
  obtain ⟨-, -, sc, -, -, -, -, borelK, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring D.host.F D.host.E D.sp.cm.sig hcm (AF D.host.F)
  haveI := sc
  haveI := borelK r V.rank
  have hrank : ∀ (δ : GL (Fin V.rank) D.host.E) (ξ : Matrix (Fin V.rank) (Fin r) D.host.E),
      (δ.1 * ξ).rank = ξ.rank := fun δ ξ =>
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 δ.isUnit)
  have hL := GlobalTheory.CompanionTheory.SplitGram.leftInv_subtypeSum V φ
    (fun x : Matrix (Fin V.rank) (Fin r) D.host.E => x.rank = r ∧ gramQ V x = β.1)
    (fun δ hδ ξ h => ⟨(hrank δ ξ).trans h.1, (GlobalTheory.CompanionTheory.SplitGram.gramQ_mul V hδ ξ).trans h.2⟩)
  have hI := average_eq_meanC V ν μH hν hμ 𝓕 h𝓕 _ hL
  let Φ : (Fin r → Fin V.rank → AE D) → ℂ := fun X => φ (tupOf X)
  have hΦc : Continuous Φ := hcont.comp (continuous_matrix fun i a =>
    (continuous_apply i).comp (continuous_apply a))
  have hΦm : Measurable Φ := hΦc.measurable
  let S : Set (Fin r → Fin V.rank → D.host.E) :=
    {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig V.gram X = β.1}
  have hfin : ∫⁻ h in 𝓕, ∑' x : S, ‖Φ (GlobalTheory.CompanionTheory.SW.actW (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F) D.sp.cm.sig V.gram h⁻¹
      (HeckeCharacterZeroLocus.SiegelWeilU.ratTup (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F) (x : Fin r → Fin V.rank → D.host.E)))‖ₑ ∂μH < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun h => ?_)
      (setLIntegral_absTheta_lt_top V ν μH hν hμ 𝓕 h𝓕 φ habs)
    have hinj : Function.Injective fun X : S => colsOf X.1 := fun X Y e =>
      Subtype.ext (funext fun a => funext fun i => congrFun (congrFun e i) a)
    refine le_trans (le_of_eq (tsum_congr fun X => ?_))
      (ENNReal.tsum_comp_le_tsum_of_injective hinj fun ξ => ‖φ (GlobalTheory.SiegelFormula.invPt V h ξ)‖ₑ)
    exact congrArg (fun y => ‖φ y‖ₑ) (tupOf_actW V h X.1)
  have hS : HeckeCharacterZeroLocus.SiegelWeilU.thetaS D.host.F D.host.E D.sp.cm.sig V.rank V.gram Φ S =
      fun h => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
        φ (GlobalTheory.SiegelFormula.invPt V h x.1) := by
    funext h
    refine (tsum_congr fun X => ?_).trans ((fibEquiv V β hβ).tsum_eq
      fun x => φ (GlobalTheory.SiegelFormula.invPt V h x.1))
    exact congrArg φ (tupOf_actW V h X.1)
  have key := meanC_thetaS_of_lintegral D.sp.cm.sig hcm V.gram hJ μH 𝓕 S Φ hΦm hfin
  rw [hS] at key
  exact hI.trans key

end GlobalTheory.CompanionTheory.SiegelND.ThetaGlue

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralEqThetaPartNondegenerateStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_integral_eq_theta_part_nondegenerate : ∀ (D : D7) (r : ℕ) (V : HSp D) (θ : InfFam D), IsInfFam θ → ∀ ν : Measure (GA D V), ν.IsHaarMeasure →
  ∀ φ : Mx D V.rank r → ℂ, φ ∈ schwartzA θ V.rank r → GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤ →
  ∀ (μH : Measure (GA D V)) (𝓕 : Set (GA D V)), μH.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μH →
  ∀ β : HermE D r, β.1.det ≠ 0 → IfrB V ν φ β = thetaPartD V μH 𝓕 φ β := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.ThetaGlue.ifrB_eq_thetaPartD | exact GlobalTheory.CompanionTheory.SiegelND.ThetaGlue.ifrB_eq_thetaPartD | (intros; apply GlobalTheory.CompanionTheory.SiegelND.ThetaGlue.ifrB_eq_thetaPartD <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitScalingRankOneVolume
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitScalingRankOneVolume
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem GlobalTheory.CompanionTheory.SW.coordW_image_unit_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (u : (Fv F v ⊗[F] E)ˣ) (S : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)), MeasurableSet S → coordW (Fv F v) b lam 1 M ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' S) = ((‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ : ℝ≥0∞)) ^ M * coordW (Fv F v) b lam 1 M S := by
  intro F E _ _ _ _ _ σ hσ M d b v lam hlam u S hS
  have hR := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  obtain ⟨h1, h2, h3, h4, -⟩ := id hR
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, a8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 1 M
  obtain ⟨-, hW, -⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lam hlam.1
  haveI := hW 1 M
  haveI : (coordW (Fv F v) b lam 1 M).Regular := by
    let K : TopologicalSpace.PositiveCompacts (Fin 1 → Fin M → Fv F v ⊗[F] E) := Classical.choice inferInstance
    exact Measure.regular_of_isAddLeftInvariant K.isCompact K.interior_nonempty K.isCompact.measure_ne_top
  have hchar : distribHaarChar (Fv F v ⊗[F] E) u = ‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ := by
    haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
    haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
    let bE := Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)
    let e : (Fv F v ⊗[F] E) ≃ₜ+ (Fin (Module.finrank F E) → Fv F v) :=
      { bE.equivFun.toAddEquiv with
        continuous_toFun := IsModuleTopology.continuous_of_linearMap bE.equivFun.toLinearMap
        continuous_invFun := IsModuleTopology.continuous_of_linearMap bE.equivFun.symm.toLinearMap }
    borelize (Fv F v ⊗[F] E)
    set A := Algebra.leftMulMatrix bE (u : Fv F v ⊗[F] E)
    have hdet : A.det = Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E) := (Algebra.norm_eq_matrix_det bE _).symm
    have hA : IsUnit A.det := hdet ▸ u.isUnit.map (Algebra.norm (Fv F v))
    have hN : Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E) ≠ 0 := (hdet ▸ hA).ne_zero
    rw [GlobalTheory.ModuNorm.distribHaarChar_eq_addEquivAddHaarChar]
    have ht := GlobalTheory.ModuLR.addEquivAddHaarChar_transport e.symm (GlobalTheory.ModuLR.mulVecCE A hA)
    have hext : ((e.symm.symm.trans (GlobalTheory.ModuLR.mulVecCE A hA)).trans e.symm) = GlobalTheory.ModuNorm.mulUnitCE u := by
      ext x
      show bE.equivFun.symm (Matrix.mulVec A (bE.equivFun x)) = (u : Fv F v ⊗[F] E) * x
      rw [show Matrix.mulVec A (bE.equivFun x) = bE.equivFun ((u : Fv F v ⊗[F] E) * x) from Algebra.leftMulMatrix_mulVec_repr bE _ x, LinearEquiv.symm_apply_apply]
    rw [hext] at ht
    rw [ht, GlobalTheory.ModuArtin.addEquivAddHaarChar_mulVecCE _ inferInstance inferInstance, hdet, GlobalTheory.GaugeEx.modu, dite_eq_left (hdet ▸ hA)]
    convert GlobalTheory.CompanionTheory.SW.ProdFormula.distribHaarChar_eq_nnnorm v _ hN using 2
    exact Units.ext rfl
  let U1 : (Fin M → Fv F v ⊗[F] E)ˣ := Units.map (Pi.constRingHom (Fin M) (Fv F v ⊗[F] E)).toMonoidHom u
  let U : (Fin 1 → Fin M → Fv F v ⊗[F] E)ˣ :=
    Units.map (Pi.constRingHom (Fin 1) (Fin M → Fv F v ⊗[F] E)).toMonoidHom U1
  have hc1 : distribHaarChar (Fin M → Fv F v ⊗[F] E) U1 = ‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ ^ M := by
    rw [GlobalTheory.ModuPiLocal.distribHaarChar_pi (fun _ : Fin M => Fv F v ⊗[F] E) U1]
    have hU : ∀ i, Units.map (Pi.evalRingHom (fun _ : Fin M => Fv F v ⊗[F] E) i).toMonoidHom U1 = u :=
      fun i => Units.ext rfl
    simp only [hU, hchar, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hc : distribHaarChar (Fin 1 → Fin M → Fv F v ⊗[F] E) U = ‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ ^ M := by
    rw [GlobalTheory.ModuPiLocal.distribHaarChar_pi (fun _ : Fin 1 => Fin M → Fv F v ⊗[F] E) U]
    have hU : ∀ i, Units.map (Pi.evalRingHom (fun _ : Fin 1 => Fin M → Fv F v ⊗[F] E) i).toMonoidHom U = U1 :=
      fun i => Units.ext rfl
    simp only [hU, hc1, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one]
  have hm : coordW (Fv F v) b lam 1 M ((fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => U • X) '' S) =
      distribHaarChar (Fin 1 → Fin M → Fv F v ⊗[F] E) U * coordW (Fv F v) b lam 1 M S := by
    open scoped Pointwise in
    exact (distribHaarChar_mul (coordW (Fv F v) b lam 1 M) U S).symm
  have himg : (fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) =
      fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => U • X := rfl
  rw [himg, hm, hc]
  push_cast
  rfl
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitScalingRankOneVolumeStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_scaling_rank_one_volume : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (u : (Fv F v ⊗[F] E)ˣ) (S : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)), MeasurableSet S → coordW (Fv F v) b lam 1 M ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' S) = ((‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ : ℝ≥0∞)) ^ M * coordW (Fv F v) b lam 1 M S := by
  first | exact @GlobalTheory.CompanionTheory.SW.coordW_image_unit_mul | exact GlobalTheory.CompanionTheory.SW.coordW_image_unit_mul | (intros; apply GlobalTheory.CompanionTheory.SW.coordW_image_unit_mul <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockMatrixInjective
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.EisCovar PositivityTheory.GramSchwartzFunctions.EC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTw

variable {D : D7} {n ρ p : ℕ} {hn : ρ + p = n}

section Blocks

variable {R : Type} [CommRing R]

theorem block_mul₂ (hn : ρ + p = n) (a a' : Matrix (Fin ρ) (Fin ρ) R) (b b' : Matrix (Fin ρ) (Fin p) R)
    (c c' : Matrix (Fin p) (Fin ρ) R) (d d' : Matrix (Fin p) (Fin p) R) :
    bl hn a b c d * bl hn a' b' c' d' =
      bl hn (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [bl]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blockRowSubstitution_one (hn : ρ + p = n) : bl hn (1 : Matrix (Fin ρ) (Fin ρ) R) 0 0 (1 : Matrix (Fin p) (Fin p) R) = 1 := by
  simp only [bl, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem blockMatrix_zero (hn : ρ + p = n) :
    bl hn (0 : Matrix (Fin ρ) (Fin ρ) R) 0 0 (0 : Matrix (Fin p) (Fin p) R) = 0 := by
  simp only [bl, Matrix.fromBlocks_zero]
  rfl

theorem bl_add (hn : ρ + p = n) (a a' : Matrix (Fin ρ) (Fin ρ) R) (b b' : Matrix (Fin ρ) (Fin p) R)
    (c c' : Matrix (Fin p) (Fin ρ) R) (d d' : Matrix (Fin p) (Fin p) R) :
    bl hn a b c d + bl hn a' b' c' d' = bl hn (a + a') (b + b') (c + c') (d + d') := by
  simp only [bl]
  rw [← Matrix.fromBlocks_add]
  rfl

theorem blockMatrix_inj (hn : ρ + p = n) {a a' : Matrix (Fin ρ) (Fin ρ) R} {b b' : Matrix (Fin ρ) (Fin p) R}
    {c c' : Matrix (Fin p) (Fin ρ) R} {d d' : Matrix (Fin p) (Fin p) R}
    (h : bl hn a b c d = bl hn a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have h2 := congrArg (fun M => M.submatrix (finSumFinEquiv.trans (finCongr hn)) (finSumFinEquiv.trans (finCongr hn))) h
  simp only [bl, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] at h2
  exact Matrix.fromBlocks_inj.1 h2

theorem block_matrix_injective {a a' b b' c c' d d' : Matrix (Fin n) (Fin n) R}
    (h : blk4 a b c d = blk4 a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have h2 := congrArg (fun M => M.submatrix finSumFinEquiv finSumFinEquiv) h
  simp only [blk4, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] at h2
  exact Matrix.fromBlocks_inj.1 h2

end Blocks

theorem mat_nzx_sh (M : Maps D hn) (z : hermA D ρ) (x y : Mx D ρ p) :
    mat (M.nzx z x * M.sh y) = blk4 (bl hn 1 y 0 1) (bl hn (z.1 - x ⬝ adj y) x (adj x) 0) 0 (bl hn 1 0 (-adj y) 1) := by
  rw [mat_mul', M.nzx_mat, M.sh_mat, submatrix_fromBlocks_mul]
  congr 1
  · simp
  · rw [Matrix.mul_zero, zero_add, block_mul₂]
    simp [sub_eq_add_neg]
  · simp
  · simp

theorem nzx_sh_inj (M : Maps D hn) {z z' : hermA D ρ} {x x' y y' : Mx D ρ p}
    (h : M.nzx z x * M.sh y = M.nzx z' x' * M.sh y') : z = z' ∧ x = x' ∧ y = y' := by
  have h2 := congrArg mat h
  rw [mat_nzx_sh, mat_nzx_sh] at h2
  obtain ⟨h3, h4, -, -⟩ := block_matrix_injective h2
  obtain ⟨-, rfl, -, -⟩ := blockMatrix_inj hn h3
  obtain ⟨h5, rfl, -, -⟩ := blockMatrix_inj hn h4
  exact ⟨Subtype.ext (sub_left_injective h5), rfl, rfl⟩

set_option maxHeartbeats 1000000 in
theorem gl_levi (M : Maps D hn) (g : G D p) (a : GL (Fin p) (AE D)) (hg : mat g = blk4 a.1 0 0 (adj (a⁻¹).1))
    (z : hermA D ρ) (x y : Mx D ρ p) :
    M.emb g * (M.nzx z x * M.sh y) = M.nzx z (x ⬝ adj a.1) * M.sh (y ⬝ (a⁻¹).1) * M.emb g := by
  have h1 : (a⁻¹).1 * a.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : adj a.1 * adj (a⁻¹).1 = 1 := by
    have := adj_mul (a⁻¹).1 a.1
    rw [show HMul.hMul (a⁻¹).1 a.1 = (1 : Mx D p p) from h1, adj_one] at this
    exact this.symm
  have hE := M.emb_mat g _ _ _ _ hg
  apply mat_injective'
  rw [mat_mul' (M.emb g), mat_mul' _ (M.emb g), mat_nzx_sh, mat_nzx_sh, hE, blockMatrix_zero, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  have h3 : ∀ w : Mx D p ρ, adj a.1 ⬝ (adj (a⁻¹).1 ⬝ w) = w := fun w => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have h4 : ∀ w : Mx D ρ p, w ⬝ adj a.1 ⬝ adj (a⁻¹).1 = w := fun w => by
    rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  have h5 : ∀ w : Mx D ρ p, w ⬝ (a⁻¹).1 ⬝ a.1 = w := fun w => by
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, block_mul₂, adj_mul, adj_adj, Matrix.one_mul,
    Matrix.mul_one, h4, h5, Matrix.mul_assoc x, h3, Matrix.mul_neg, Matrix.neg_mul, neg_zero]

theorem adj_sub' {k l : ℕ} (u v : Mx D k l) : adj (u - v) = adj u - adj v := by
  rw [sub_eq_add_neg, adj_add, adj_neg, sub_eq_add_neg]

def zU (z : hermA D ρ) (y : Mx D ρ p) (b : Mx D p p) (hb : adj b = b) : hermA D ρ :=
  ⟨z.1 - y ⬝ (b ⬝ adj y), by
    show adj _ = _
    rw [adj_sub', adj_mul, adj_mul, adj_adj, hb, z.2, Matrix.mul_assoc]⟩

set_option maxHeartbeats 1000000 in
theorem gl_unip (M : Maps D hn) (g : G D p) (b : Mx D p p) (hb : adj b = b) (hg : mat g = blk4 1 b 0 1)
    (z : hermA D ρ) (x y : Mx D ρ p) :
    M.emb g * (M.nzx z x * M.sh y) = M.nzx (zU z y b hb) (x - y ⬝ b) * M.sh y * M.emb g := by
  have hE := M.emb_mat g _ _ _ _ hg
  apply mat_injective'
  rw [mat_mul' (M.emb g), mat_mul' _ (M.emb g), mat_nzx_sh, mat_nzx_sh, hE, blockMatrix_zero, blockRowSubstitution_one, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul, Matrix.mul_one, block_mul₂, bl_add, adj_sub', adj_mul, hb]
  have e1 : (zU z y b hb).1 - (x - y ⬝ b) ⬝ adj y = z.1 - x ⬝ adj y := by
    simp only [zU, Matrix.sub_mul, Matrix.mul_assoc]
    abel
  have e2 : y ⬝ b + (x - y ⬝ b) = x := by abel
  have e3 : adj x + b ⬝ -adj y = adj x - b ⬝ adj y := by rw [Matrix.mul_neg, sub_eq_add_neg]
  rw [e1, e2, e3]

def zW (z : hermA D ρ) (x y : Mx D ρ p) : hermA D ρ :=
  ⟨z.1 - x ⬝ adj y - y ⬝ adj x, by
    show adj _ = _
    rw [adj_sub', adj_sub', adj_mul, adj_mul, adj_adj, adj_adj, z.2]
    abel⟩

set_option maxHeartbeats 1000000 in
theorem gl_weyl (M : Maps D hn) (g : G D p) (hg : mat g = blk4 0 1 (-1) 0)
    (z : hermA D ρ) (x y : Mx D ρ p) :
    M.emb g * (M.nzx z x * M.sh y) = M.nzx (zW z x y) (-y) * M.sh x * M.emb g := by
  have hE := M.emb_mat g _ _ _ _ hg
  apply mat_injective'
  rw [mat_mul' (M.emb g), mat_mul' _ (M.emb g), mat_nzx_sh, mat_nzx_sh, hE, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  have e1 : (zW z x y).1 - -y ⬝ adj x = z.1 - x ⬝ adj y := by
    simp only [zW, Matrix.neg_mul]
    abel
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, block_mul₂, bl_add, adj_neg, Matrix.one_mul,
    Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, neg_neg, neg_zero]
  rw [show (zW z x y).1 - -(y ⬝ adj x) = z.1 - x ⬝ adj y by rw [← Matrix.neg_mul]; exact e1]

end GlobalTheory.CompanionTheory.ThTw
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HCoContinuousAddEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HCoContinuousAddEquiv
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

theorem hCo_continuousAddEquiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] (d : ℕ) (b : Module.Basis (Fin d) F E) (n : ℕ), ∃ e : HermR R σ n ≃ₜ+ (Idx n d → R), ∀ S, e S = hCo R σ b S := by
  intro F E _ _ _ _ _ σ hCM R _ _ _ _ _ _ _ d b n
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  obtain ⟨hinv, δ, hδ, hσδ⟩ := GlobalTheory.CompanionTheory.SW.HaarCoord.conj_facts hCM
  have hfin : Module.finrank F E = 2 := hCM.2.2.1
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R _
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
  let h1 : HermR R σ n ≃ₜ (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) :=
    (GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord_isHomeomorph R hinv hfin hδ hσδ n t5 t6).homeomorph _
  let h2 : (R ⊗[F] E) ≃ₜ (Fin d → R) := (t7 d b).homeomorph _
  have h2a : ∀ y k, h2 y k = (Algebra.TensorProduct.basis R b).repr y k := fun _ _ => rfl
  let G : ((Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E)) ≃ₜ (Idx n d → R) :=
    { toFun := fun x => Sum.elim x.1 (fun q => h2 (x.2 q.2) q.1)
      invFun := fun f => (fun i => f (Sum.inl i), fun p => h2.symm fun k => f (Sum.inr (k, p)))
      left_inv := by
        rintro ⟨x, y⟩
        refine Prod.ext rfl ?_
        funext p
        exact h2.symm_apply_apply (y p)
      right_inv := by
        intro f
        funext q
        rcases q with i | ⟨k, p⟩
        · rfl
        · simp
      continuous_toFun := by
        refine continuous_pi fun q => ?_
        rcases q with i | ⟨k, p⟩
        · exact (continuous_apply i).comp continuous_fst
        · exact (continuous_apply k).comp
            (h2.continuous.comp ((continuous_apply p).comp continuous_snd))
      continuous_invFun := by
        refine Continuous.prodMk (continuous_pi fun i => continuous_apply _) (continuous_pi fun p => ?_)
        exact h2.symm.continuous.comp (continuous_pi fun k => continuous_apply _) }
  let H : HermR R σ n ≃ₜ (Idx n d → R) := h1.trans G
  have hH : ∀ S, H S = hCo R σ b S := by
    intro S
    funext q
    rcases q with i | ⟨k, p⟩ <;> rfl
  refine ⟨{ toEquiv := H.toEquiv
            map_add' := ?_
            continuous_toFun := H.continuous
            continuous_invFun := H.symm.continuous }, hH⟩
  intro S T
  show H (S + T) = H S + H T
  rw [hH, hH, hH]
  funext q
  rcases q with i | ⟨k, p⟩
  · simp [hCo, map_add (f := _), mul_add]
  · simp [hCo, map_add (f := _)]

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HCoContinuousAddEquivStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homeomorph_hermR_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] (d : ℕ) (b : Module.Basis (Fin d) F E) (n : ℕ), ∃ e : HermR R σ n ≃ₜ+ (Idx n d → R), ∀ S, e S = hCo R σ b S := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.hCo_continuousAddEquiv | exact GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.hCo_continuousAddEquiv | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.hCo_continuousAddEquiv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousInvAddChar
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

namespace GlobalTheory.CompanionTheory.BZCuspPair

section Proofs
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nontrivial_of_irr {G : Type} [Group G] [TopologicalSpace G] (τ : IrrRep G) : Nontrivial τ.V := by
  have hi := τ.irr
  by_contra hs
  rw [not_nontrivial_iff_subsingleton] at hs
  apply (bot_ne_top : (⊥ : Subrepresentation τ.ρ) ≠ ⊤)
  apply Subrepresentation.ext
  ext x
  rw [Subsingleton.elim x 0]
  exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩

theorem continuous_inv_addChar (ψ : AddChar k Circle) (hc : Continuous ψ) : Continuous (ψ⁻¹ : AddChar k Circle) := by
  have : (⇑(ψ⁻¹ : AddChar k Circle)) = fun a => ψ (-a) := funext fun a => AddChar.inv_apply ψ a
  rw [this]
  exact hc.comp continuous_neg

end Proofs

end GlobalTheory.CompanionTheory.BZCuspPair
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DictionaryMaximalCompactParts
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DictionaryMaximalCompactParts
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SWDict

open PositivityTheory.PfSWUS GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd

theorem dictKA_of_parts : PositivityTheory.PfSWUS.DictKAOfParts := by
  intro hF hW hI hM D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a k hk
  obtain ⟨N, φs, hsum, hmono⟩ := hF D n V ψ χ θ μ ω H l s ν Φ hS hR k hk
  refine ⟨N, φs, fun j => npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) - n) *
    IfrB V ν (fun x => φs j (HMul.hMul x a.1)) β, ?_, ?_, ?_⟩
  · obtain ⟨t, ht⟩ := hW D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a k N φs hmono
    exact ⟨t, fun z hz => by rw [hsum]; exact ht z hz⟩
  · rw [hsum, hI D n V ψ χ θ μ ω H l s ν Φ hS hR β hβ a N φs hmono, Finset.mul_sum]
  · exact fun j => hM D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a k hk (φs j) (hmono j)

end GlobalTheory.CompanionTheory.SWDict

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DictionaryMaximalCompactPartsStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dictionary_maximal_compact_parts : PositivityTheory.PfSWUS.DictKAOfParts := by
  first | exact @GlobalTheory.CompanionTheory.SWDict.dictKA_of_parts | exact GlobalTheory.CompanionTheory.SWDict.dictKA_of_parts | (intros; apply GlobalTheory.CompanionTheory.SWDict.dictKA_of_parts <;> assumption)
end
end
end
