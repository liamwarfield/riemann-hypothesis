module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableOfTsumEnormLtTop
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityCuspidalProduct
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureExtensionByOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CanonicalProductEquivMultiplicityOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReverseOrderedProductPermEquiv
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvarianceOfConstantFourierCoefficient

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftInvSubtypeSum
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitGram

variable {D : D7}

abbrev sg (D : D7) : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E)

theorem gramQ_eq (V : HSp D) {r : ℕ} (x : Matrix (Fin V.rank) (Fin r) D.host.E) :
    gramQ V x = Formalism.UG.cT (sg D) x * (HSpace.gram V * x) := rfl

theorem gramQ_mul (V : HSp D) {r : ℕ} {δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E}
    (hδ : Formalism.UG.cT (sg D) δ * HSpace.gram V * δ = HSpace.gram V)
    (x : Matrix (Fin V.rank) (Fin r) D.host.E) : gramQ V (δ * x) = gramQ V x := by
  rw [gramQ_eq, gramQ_eq, Formalism.UG.cT_mul]
  calc Formalism.UG.cT (sg D) x * Formalism.UG.cT (sg D) δ * (HSpace.gram V * (δ * x))
      = Formalism.UG.cT (sg D) x * ((Formalism.UG.cT (sg D) δ * HSpace.gram V * δ) * x) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hδ]

theorem gramQ_herm (V : HSp D) {r : ℕ} (x : Matrix (Fin V.rank) (Fin r) D.host.E) :
    ((gramQ V x).map (D.sp.cm.sig : D.host.E → D.host.E)).transpose = gramQ V x := by
  have hJ : Formalism.UG.cT (sg D) (HSpace.gram V) = HSpace.gram V := Matrix.ext fun i j => (GlobalTheory.Doubling.isHermND_gram V).1 i j
  have hx : Formalism.UG.cT (sg D) (Formalism.UG.cT (sg D) x) = x := Matrix.ext fun i j => star_star (x i j)
  change Formalism.UG.cT (sg D) (gramQ V x) = gramQ V x
  rw [gramQ_eq, Formalism.UG.cT_mul, Formalism.UG.cT_mul, hx, hJ, Matrix.mul_assoc]

theorem leftInv_subtypeSum {M : Type*} [AddCommMonoid M] [TopologicalSpace M] (V : HSp D) {n : ℕ}
    (f : Mx D V.rank n → M) (p : Matrix (Fin V.rank) (Fin n) D.host.E → Prop)
    (hp : ∀ δ : GL (Fin V.rank) D.host.E, Formalism.UG.cT (sg D) δ.1 * HSpace.gram V * δ.1 = HSpace.gram V →
      ∀ ξ, p ξ → p (δ.1 * ξ)) :
    LeftInv (GQ V) fun h => ∑' ξ : {ξ : Matrix (Fin V.rank) (Fin n) D.host.E // p ξ},
      f (GlobalTheory.SiegelFormula.invPt V h ξ.1) := by
  intro γ hγ h
  obtain ⟨δ, hU, hδ⟩ : ∃ δ : GL (Fin V.rank) D.host.E, _ ∧ Formalism.UG.bc (incA D) δ = Formalism.L2.Theta.matHom V γ⁻¹ := inv_mem hγ
  have hU' : Formalism.UG.cT (sg D) δ.1 * HSpace.gram V * δ.1 = HSpace.gram V := hU
  have hUi : Formalism.UG.cT (sg D) (δ⁻¹).1 * HSpace.gram V * (δ⁻¹).1 = HSpace.gram V :=
    (Formalism.UG.UJ (sg D) (HSpace.gram V)).inv_mem hU
  let e : {ξ : Matrix (Fin V.rank) (Fin n) D.host.E // p ξ} ≃ {ξ : Matrix (Fin V.rank) (Fin n) D.host.E // p ξ} :=
    ⟨fun ξ => ⟨δ.1 * ξ.1, hp δ hU' _ ξ.2⟩, fun ξ => ⟨(δ⁻¹).1 * ξ.1, hp δ⁻¹ hUi _ ξ.2⟩,
      fun ξ => Subtype.ext (by simp), fun ξ => Subtype.ext (by simp)⟩
  have h1 : Formalism.L2.Theta.mt V γ⁻¹ = δ.1.map (incA D) := (congrArg Units.val hδ).symm
  have h2 : Formalism.L2.Theta.mt V (γ * h)⁻¹ = Formalism.L2.Theta.mt V h⁻¹ * Formalism.L2.Theta.mt V γ⁻¹ := by rw [mul_inv_rev]; rfl
  refine (tsum_congr fun ξ => ?_).trans (e.tsum_eq fun ξ => f (GlobalTheory.SiegelFormula.invPt V h ξ.1))
  simp only [GlobalTheory.SiegelFormula.invPt, e, Equiv.coe_fn_mk, h2, h1, Matrix.mul_assoc, Matrix.map_mul]

def fibreEquiv (V : HSp D) (r : ℕ) :
    (Σ β : HermE D r, {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1}) ≃
      {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r} where
  toFun p := ⟨p.2.1, p.2.2.1⟩
  invFun x := ⟨⟨gramQ V x.1, gramQ_herm V x.1⟩, ⟨x.1, x.2, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨b, hb⟩, x, hx, hg⟩
    change gramQ V x = b at hg
    subst hg
    rfl
  right_inv _ := rfl

theorem hasSum_IfrB : ∀ (D : Formalism.BasicNotions.D7) (r : ℕ) (V : Formalism.BasicNotions.TH.HSp D) (θ : InfFam D), IsInfFam θ →
    ∀ (ν : Measure (GA D V)), ν.IsHaarMeasure → ∀ φ : Mx D V.rank r → ℂ, φ ∈ schwartzA θ V.rank r →
    GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤ →
    HasSum (fun β : PositivityTheory.GramSchwartzFunctions.HermE D r => PositivityTheory.GramSchwartzFunctions.BC.IfrB V ν φ β) (PositivityTheory.GramSchwartzFunctions.Ifr V ν φ) := by
  intro D r V θ hθ ν hν φ hφ habs
  have : BorelSpace (GA D V) := ⟨rfl⟩
  haveI := hν
  haveI := GlobalTheory.ThetaTransformMeas.countable_field D.host.E
  haveI : Countable (Matrix (Fin V.rank) (Fin r) D.host.E) :=
    inferInstanceAs (Countable (Fin V.rank → Fin r → D.host.E))
  haveI : Countable (Matrix (Fin r) (Fin r) D.host.E) :=
    inferInstanceAs (Countable (Fin r → Fin r → D.host.E))
  haveI : Countable (HermE D r) :=
    inferInstanceAs (Countable {b : Matrix (Fin r) (Fin r) D.host.E // _})
  have hcont : Continuous φ :=
    (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ φ hφ).1
  have hrank : ∀ (δ : GL (Fin V.rank) D.host.E) (ξ : Matrix (Fin V.rank) (Fin r) D.host.E),
      (δ.1 * ξ).rank = ξ.rank := fun δ ξ =>
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 δ.isUnit)
  have hA := leftInv_subtypeSum V (fun y => ‖φ y‖ₑ)
    (fun x : Matrix (Fin V.rank) (Fin r) D.host.E => x.rank = r)
    (fun δ _ ξ h => (hrank δ ξ).trans h)
  have hfin : ∫⁻ q, descend (GQ V) (fun g => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r},
      ‖φ (GlobalTheory.SiegelFormula.invPt V g x.1)‖ₑ) q ∂autMeasure V ν < ⊤ := by
    refine (lintegral_mono fun q => ?_).trans_lt habs
    exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
      (fun ξ => ‖φ (GlobalTheory.SiegelFormula.invPt V q.out ξ)‖ₑ)
  have key := GlobalTheory.CompanionTheory.ThetaOrbit.hasSum_average_descend (Γ := GQ V) (μ := ν) (fibreEquiv V r)
    (fun h x => φ (GlobalTheory.SiegelFormula.invPt V h x.1))
    (fun x => (hcont.comp (GlobalTheory.AbsThetaSemi.continuous_invPt V x.1)).measurable)
    hA
    (fun β => leftInv_subtypeSum V φ
      (fun x : Matrix (Fin V.rank) (Fin r) D.host.E => x.rank = r ∧ gramQ V x = β.1)
      (fun δ hδ ξ h => ⟨(hrank δ ξ).trans h.1, (gramQ_mul V hδ ξ).trans h.2⟩))
    hfin
  exact key

end GlobalTheory.CompanionTheory.SplitGram

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSumInvariantWeylInvolution
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSumInvariantWeylInvolution
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThetaPoisson

section Gen

variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [T2Space A]
  [LocallyCompactSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
  (Γ : AddSubgroup A) [DiscreteTopology Γ] (K : Set A) (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K)
  (B : A → A → ℂ) (hc : ∀ y, Continuous fun x => B x y) (hsy : ∀ x y, B x y = B y x)
  (hadd : ∀ x x' y, B (x + x') y = B x y * B x' y) (hn : ∀ x y, ‖B x y‖ = 1)
  (hker : ∀ x, (∀ γ ∈ Γ, B γ x = 1) ↔ x ∈ Γ) (hinj : ∀ γ ∈ Γ, (∀ x, B γ x = 1) → γ = 0)
  (μ : Measure A) (𝓕 : Set A) [hμ : μ.IsAddHaarMeasure] (hF : IsAddFundamentalDomain Γ 𝓕 μ) (h1 : μ 𝓕 = 1)

include hK hcov hc hsy hadd hn hker hinj hμ hF h1

theorem poisson_translates {f : A → ℂ} (hf : Continuous f)
    (hb : ∀ Q : Set A, IsCompact Q → ∃ b : Γ → ℝ, Summable b ∧ ∀ x ∈ Q, ∀ ξ : Γ, ‖f (ξ + x)‖ ≤ b ξ)
    (hsum : Summable fun γ : Γ => ‖∫ x, f x * B x γ ∂μ‖) :
    ∑' ξ : Γ, f ξ = ∑' γ : Γ, ∫ x, f x * B x γ ∂μ := by
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hc' : ∀ y, Continuous (B y) := fun y => (hc y).congr fun x => hsy x y
  have hadd' : ∀ y x x', B y (x + x') = B y x * B y x' := fun y x x' => by
    rw [hsy y, hadd, hsy x, hsy x']
  have hU : GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiAbs.UnifSummable Γ.subtype f := fun Q hQ => by
    obtain ⟨b, hb1, hb2⟩ := hb Q hQ
    refine ⟨b, hb1, fun c x hx => ?_⟩
    have h := hb2 x hx c
    rwa [add_comm] at h
  have hfi : Integrable f μ := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiAbs.integrable_of_unif hf hU μ hK fun x => by
    obtain ⟨γ, hγ, h⟩ := hcov x
    refine ⟨⟨-γ, Γ.neg_mem hγ⟩, ?_⟩
    simpa [sub_neg_eq_add, add_comm] using h
  have hcont : Continuous fun x => ∑' ξ : Γ, f (ξ + x) := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    obtain ⟨Q, hQ, hxQ⟩ := exists_compact_mem_nhds x
    obtain ⟨b, hb1, hb2⟩ := hb Q hQ
    have h : ContinuousOn (fun x => ∑' ξ : Γ, f (ξ + x)) Q :=
      continuousOn_tsum (fun ξ => (hf.comp (continuous_const.add continuous_id)).continuousOn) hb1
        (fun ξ x hx => hb2 x hx ξ)
    exact h.continuousAt hxQ
  have hcoef : ∀ γ : Γ, ∫ x in 𝓕, B γ x * (∑' ξ : Γ, f (ξ + x)) ∂μ = ∫ x, f x * B x γ ∂μ := by
    intro γ
    have hi : Integrable (fun x => f x * B x γ) μ :=
      hfi.mul_bdd (c := 1) (hc γ).aestronglyMeasurable (Filter.Eventually.of_forall fun y => (hn y γ).le)
    rw [(GlobalTheory.CovolumeOneSelfDual.unfold Γ μ 𝓕 hF _ hi).2]
    congr 1
    funext x
    rw [← tsum_mul_left]
    refine tsum_congr fun ξ => ?_
    rw [hadd, (hker γ).2 γ.2 ξ ξ.2, one_mul, mul_comm, hsy]
  have key := GlobalTheory.CompactQuotientFourier.inversion_at_zero A Γ K hK hcov Γ (fun γ x => B γ x)
    (fun γ => hc' γ) (fun γ x y => hadd' γ x y) (fun a b x => hadd a b x) (fun a x => hn a x)
    (fun x => by rw [← hker x]; exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩)
    (fun a h => Subtype.ext (hinj a a.2 h)) μ 𝓕 hμ hF h1 (fun x => ∑' ξ : Γ, f (ξ + x))
    hcont
    (fun γ hγ x => by
      rw [← (Equiv.addRight (⟨γ, hγ⟩ : Γ)).tsum_eq fun ξ : Γ => f (ξ + x)]
      refine tsum_congr fun ξ => ?_
      simp [add_assoc])
    (by simp only [hcoef]; exact hsum)
  simp only [hcoef, add_zero] at key
  exact key

end Gen

section Adelic

variable {D : D7} {m n : ℕ}

def ratEquiv (D : D7) (m n : ℕ) : Matrix (Fin m) (Fin n) D.host.E ≃ ratMx D m n :=
  Equiv.ofBijective (fun ξ => ⟨rat ξ, ⟨ξ, rfl⟩⟩)
    ⟨fun _ _ h => rat_injective (congrArg Subtype.val h), fun ⟨_, ξ, h⟩ => ⟨ξ, Subtype.ext h⟩⟩

theorem tsum_ratMx (f : Mx D m n → ℂ) :
    ∑' γ : ratMx D m n, f γ = ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, f (ξ.map (incA D)) :=
  ((ratEquiv D m n).tsum_eq fun γ : ratMx D m n => f γ).symm

theorem pairing_symm {T : Matrix (Fin m) (Fin m) D.host.E} (hT : IsHermND D.sp.cm.sig T)
    (ψ : AddChar (AF D.host.F) ℂ) (x y : Mx D m n) :
    GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ x y = GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ y x := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA
  rw [← GlobalTheory.SiegelWeilLitCompare.gramQ_adj hT x y, ← GlobalTheory.DualPairCheck.trace_cA (Matrix.trace (GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.gramQ T x y))]
  congr 2
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, map_sum]
  rfl

theorem translates_bound {θ : InfFam D} (hθ : IsInfFam θ) (φ : schwartzA θ m n) (Q : Set (Mx D m n)) (hQ : IsCompact Q) :
    ∃ b : ratMx D m n → ℝ, Summable b ∧ ∀ x ∈ Q, ∀ ξ : ratMx D m n, ‖φ.1 (ξ + x)‖ ≤ b ξ := by
  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_summable_bound_schwartz_majorant_rational_translates D θ hθ m n
  obtain ⟨-, K, hK, hC⟩ := GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ m n φ.1
    (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ m n φ.1 φ.2)
  obtain ⟨C, hC⟩ := hC N
  obtain ⟨b, hb, hb'⟩ := hN K Q hK hQ
  refine ⟨fun γ => |C| * b ((ratEquiv D m n).symm γ), ((ratEquiv D m n).symm.summable_iff.2 hb).mul_left |C|, ?_⟩
  intro x hx γ
  obtain ⟨ξ, rfl⟩ := (ratEquiv D m n).surjective γ
  have h1 := hb' x hx ξ
  have h2 := hC (x + rat ξ)
  have e : ((ratEquiv D m n ξ : Mx D m n) + x) = x + rat ξ := add_comm _ _
  rw [e]
  beta_reduce
  rw [Equiv.symm_apply_apply]
  exact h2.trans (mul_le_mul (le_abs_self C) h1 (GlobalTheory.Unf.maj_nonneg _ _ _ _) (abs_nonneg C))

end Adelic

theorem theta_weyl : ∀ (D : D7) (n : ℕ) (V : HSp D) ψ χ θ μ ω, HidaSetting D n V ψ χ θ μ ω →
    ∀ g : G D n, mat g = blk4 0 1 (-1) 0 →
    ∀ Φ : schwartzA θ V.rank n,
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
        ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  intro D n V ψ χ θ μ ω hS g hg Φ
  obtain ⟨-, -, hψ, -, -, hθ, ⟨𝓕, hμ⟩, hω⟩ := hS
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_Mx D V.rank n
  haveI : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  have hT := isHermND_gram V
  obtain ⟨h1, h2⟩ := GlobalTheory.T.rationalAdelicMatrices_self_annihilator D V.rank n V.gram hT ψ hψ
  have hs := pairing_symm (n := n) hT ψ
  have hval : ∀ x, (ω g Φ).1 x = ∫ y, Φ.1 y * GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing V.gram ψ y x ∂μ := fun x => by
    rw [hω.weyl g hg Φ x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [hs y x]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing, GlobalTheory.SiegelWeilLitCompare.gramQ_eq]
    rfl
  haveI := hμ.1
  have key := poisson_translates (ratMx D V.rank n) K hK hKc (GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing (n := n) V.gram ψ)
    (fun y => ?_) hs (fun x x' y => ?_) (fun x y => hψ.2.1 _) h1 h2 μ 𝓕 hμ.2.1 hμ.2.2 (f := Φ.1) ?_
    (translates_bound hθ Φ) ?_
  · simp only [← hval] at key
    rw [tsum_ratMx, tsum_ratMx (fun x => (ω g Φ).1 x)] at key
    exact key.symm
  · simp only [hs _ y]
    haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
    haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    have ht : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA (D := D)) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
    exact hψ.1.comp (ht.comp (continuous_const.matrix_mul continuous_id).matrix_trace)
  · simp only [hs _ y]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.gramQ GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.mmul
    rw [Matrix.mul_add, Matrix.trace_add, map_add (f := _), AddChar.map_add_eq_mul]
  · exact (GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ _ n Φ.1
      (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ _ n Φ.1 Φ.2)).1
  · simp only [← hval]
    exact (ratEquiv D V.rank n).summable_iff.1 (GlobalTheory.SiegelWeilLitCompare.summable_rat hθ (ω g Φ))

end GlobalTheory.CompanionTheory.ThetaPoisson
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSumInvariantWeylInvolutionStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_sum_invariant_weyl_involution : ∀ (D : D7) (n : ℕ) (V : HSp D) ψ χ θ μ ω, HidaSetting D n V ψ χ θ μ ω →
  ∀ g : G D n, mat g = blk4 0 1 (-1) 0 →
  ∀ Φ : schwartzA θ V.rank n,
    ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaPoisson.theta_weyl | exact GlobalTheory.CompanionTheory.ThetaPoisson.theta_weyl | (intros; apply GlobalTheory.CompanionTheory.ThetaPoisson.theta_weyl <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KvFintype
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp

abbrev Ov (D : D7) (v : Pl D) : Type := v.adicCompletionIntegers D.host.F

abbrev Lv (D : D7) (v : Pl D) : Type := Fv D.host.F v

abbrev kv (D : D7) (v : Pl D) : Type := IsLocalRing.ResidueField (Ov D v)

instance kvFintype (D : D7) (v : Pl D) : Fintype (kv D v) :=
  @Fintype.ofFinite _ (Formalism.UG.P.glint_finite_residueField v)

def blkGL {R : Type} [CommRing R] (n : ℕ) : GL (Fin (n + n)) R →* GL (Ix n) R :=
  Units.map (Matrix.reindexAlgEquiv R R (finSumFinEquiv (m := n) (n := n)).symm).toAlgHom.toMonoidHom

def thU (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    GLoc D.sp.cm.sig (Jst D n) v →* GL (Ix n) (Fv D.host.F v) :=
  (blkGL n).comp (splitHom D.sp.cm.sig (Jst D n) τ)

def tauC {D : D7} {n : ℕ} {v : Pl D} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (x : Mx D n n) :
    Matrix (Fin n) (Fin n) (Fv D.host.F v) := fun i j => splitProj τ (cv D v (x i j))

def hU (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (g : GL (Ix n) (Fv D.host.F v)) : ℝ≥0 :=
  GlobalTheory.LocIntw.hgtUp _ D.sp.cm.sig (Jst D n) (absEv D.host.F D.host.E v) (GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v)
    (Function.invFun (thU D n v τ) g)

def nvL (D : D7) (v : Pl D) : (Fv D.host.F v)ˣ →* ℝ≥0 :=
  (nnnormHom : Fv D.host.F v →*₀ ℝ≥0).toMonoidHom.comp (Units.coeHom _)

end GlobalTheory.CompanionTheory.Jp

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalPairSubGeneric
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc GlobalTheory.Published GlobalTheory.LocGL.SupportUnique GlobalTheory.SplitRead GlobalTheory.DiagCell

namespace GlobalTheory.CompanionTheory.CuspPairSub

set_option synthInstance.maxHeartbeats 400000

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_eq_singleton_of_sum' {ι A : Type*} [Fintype ι] [DecidableEq ι] {a : A} {t : ι → Multiset A}
    (h : ({a} : Multiset A) = ∑ j, t j) : ∃ j₀, t j₀ = {a} ∧ ∀ j, j ≠ j₀ → t j = 0 := by
  have hc : ∑ j, Multiset.card (t j) = 1 := by
    have := congrArg Multiset.card h
    rw [Multiset.card_sum] at this
    simpa using this.symm
  obtain ⟨j₀, -, h1⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hc.symm ▸ one_ne_zero)
  have hz : ∀ j, j ≠ j₀ → t j = 0 := fun j hj => by
    have h2 := Finset.add_le_sum (s := Finset.univ) (f := fun j => Multiset.card (t j)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j₀) (Finset.mem_univ j) (Ne.symm hj)
    simp only [hc] at h2
    exact Multiset.card_eq_zero.1 (by omega)
  refine ⟨j₀, ?_, hz⟩
  rw [h, Finset.sum_eq_single j₀ (fun j _ hj => hz j hj) (by simp)]

theorem eq_of_hasSupport_singleton {y z : IrrGL (k := k)} (h : HasSupport y.rep {z}) : y = z := by
  obtain ⟨r, u, hu, hi, hc, e, hsub⟩ := h
  obtain rfl : r = 1 := by simpa using congrArg Multiset.card hu
  obtain rfl : u = fun _ => z := funext fun i => by
    rw [Subsingleton.elim i 0]
    simpa using hu
  obtain ⟨d, c⟩ := y
  obtain rfl : z.1 = d := by simpa using Fintype.card_congr e
  have hd : ∑ _ : Fin 1, z.1 = z.1 := by simp
  obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ e (stdBlocks (fun _ : Fin 1 => z.1) hd) _).1
    (piTensor fun _ => z.rep)
  obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_one z hd
  let χ := φ.trans ψ.symm
  obtain ⟨θ⟩ := nonempty_equiv_of_isSubquotient hi z.2.rep.irr
    (hsub.trans (.of_injective χ.toIntertwiningMap χ.toLinearEquiv.injective))
  exact ((IrrGL.of_rep z).symm.trans ((IrrGL.of_eq_of.2 ⟨θ⟩).trans (IrrGL.of_rep ⟨_, c⟩))).symm

theorem exists_equiv_of_cell {l : ℕ} (x y : Fin l → IrrGL (k := k)) (hxc : ∀ a, (x a).IsCusp)
    (hyp : ∀ a, 0 < (y a).1) (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1))
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (y j).1)
    (h0 : jhMult (piTensor fun j => (y j).rep) (cellFunctor f g (piTensor fun i => (x i).rep)) ≠ 0) :
    ∃ e : Fin l ≃ Fin l, ∀ a, y a = x (e a) := by
  have hG := GlobalTheory.CompanionTheory.GeoLink.geometricLemma
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  have hτ : (piTensor fun j => (y j).rep).IsIrreducible := GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun j => (y j).2.rep
  have hτs : IsSmooth (piTensor fun j => (y j).rep) := isSmooth_piTensor fun j => (y j).2.rep.smooth
  obtain ⟨s, hrow, hcol⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_of_cell (hG k).2 f g (fun i => (x i).2.rep.smooth)
    (fun i => (x i).2.rep.hasFiniteLength) hτ hτs h0
  have hR : ∀ i, ∃ t : Fin l → Multiset (IrrGL (k := k)), (∀ j, HasSupport (s i j).ρ (t j)) ∧ {x i} = ∑ j, t j :=
    fun i => GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_sum_of_jac hG hBZ (hasSupport_self (hxc i)) (f i)
      (GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun j => s i j) (hrow i)
      (fun j => s i j) (fun j => GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle _ (fun j => (s i j).irr) j)
  choose t ht hAt using hR
  have hC : ∀ j, HasSupport (y j).rep (∑ i, t i j) := by
    intro j
    have hd : ∑ i, b.1 i j = (y j).1 := by simpa using Fintype.card_congr (g j)
    have hy := GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle (fun j => (y j).rep) (fun j => (y j).2.rep.irr) j
    have h1 := isSubquotient_factor (fun j => multiProd (g j) fun i => (s i j).ρ) j (y j).2.rep.irr
      (hy.trans (isSubquotient_comp hcol _))
    obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ (g j) (stdBlocks (fun i => b.1 i j) hd) _).1
      (piTensor fun i => (s i j).ρ)
    let ψ := φ.trans (prodIrrEquiv hd (fun i => (s i j).ρ) (fun i => (s i j).smooth) fun i => (s i j).irr)
    exact GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr
      (y := fun i => IrrGL.of (s i j).ρ (s i j).smooth (s i j).irr)
      (fun i => (ht i j).of_equiv (IrrGL.equivOf _ _ _)) (y j).2.rep.irr
      (h1.trans (.of_injective ψ.toIntertwiningMap ψ.toLinearEquiv.injective))
  choose r hr1 hr0 using fun i => exists_eq_singleton_of_sum' (hAt i)
  have hsurj : Function.Surjective r := by
    intro j
    by_contra hj
    push_neg at hj
    have hz : ∑ i, t i j = 0 := Finset.sum_eq_zero fun i _ => hr0 i j (Ne.symm (hj i))
    have h1 := (hC j).sum_fst
    rw [hz] at h1
    have := hyp j
    simp at h1
    omega
  have hbij : Function.Bijective r := ⟨Finite.injective_iff_surjective.2 hsurj, hsurj⟩
  let E := Equiv.ofBijective r hbij
  refine ⟨E.symm, fun j => ?_⟩
  have hrE : r (E.symm j) = j := E.apply_symm_apply j
  have hs1 : ∑ i, t i j = {x (E.symm j)} := by
    rw [Finset.sum_eq_single (E.symm j)]
    · rw [← hr1 (E.symm j), hrE]
    · intro i _ hi
      refine hr0 i j fun e => hi ?_
      exact hbij.1 (e.symm.trans hrE.symm)
    · simp
  have h2 := hC j
  rw [hs1] at h2
  exact eq_of_hasSupport_singleton h2

theorem exists_equiv_of_jm_ne_zero {l N : ℕ} (x y : Fin l → IrrGL (k := k)) (hx : ∑ a, (x a).1 = N)
    (hy : ∑ a, (y a).1 = N) (hxc : ∀ a, (x a).IsCusp) (hyp : ∀ a, 0 < (y a).1)
    (h : jm y hy (prodIrr x hx) ≠ 0) : ∃ e : Fin l ≃ Fin l, ∀ a, y a = x (e a) := by
  classical
  haveI : Fintype (SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)) := Fintype.ofFinite _
  have hτ : (piTensor fun j => (y j).rep).IsIrreducible :=
    GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k _ _ fun j => (y j).2.rep
  let f : ∀ (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)) i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1 :=
    fun b => b.nonempty_rows.some
  let g : ∀ (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)) j, (Σ i, Fin (b.1 i j)) ≃ Fin (y j).1 :=
    fun b => b.nonempty_cols.some
  have h1 := (GlobalTheory.CompanionTheory.GeoLink.geometricLemma k).1.jhMult_eq (stdBlocks (fun a => (x a).1) hx)
    (stdBlocks (fun a => (y a).1) hy) (isSmooth_piTensor fun i => (x i).2.rep.smooth) f g hτ
  have h2 : jm y hy (prodIrr x hx) = jhMult (piTensor fun j => (y j).rep)
      (GlobalTheory.SmGL.jac (stdBlocks (fun a => (y a).1) hy) (parInd (stdBlocks (fun a => (x a).1) hx)
        (piTensor fun i => (x i).rep))) := rfl
  rw [h2, h1] at h
  obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact exists_equiv_of_cell x y hxc hyp b (f b) (g b) hb

theorem jm_le_one (hA : IrreducibleAdmissibleGL) {l N : ℕ} (x y : Fin l → IrrGL (k := k)) (hx : ∑ a, (x a).1 = N)
    (hy : ∑ a, (y a).1 = N) (hxc : ∀ a, (x a).IsCusp) (hyc : ∀ a, (y a).IsCusp)
    (hinj : Function.Injective x) : jm y hy (prodIrr x hx) ≤ 1 := by
  rw [GlobalTheory.T.jacquet_multiplicity_cuspidal_product hA x y hx hy hxc hyc]
  have : Set.ncard {e : Fin l ≃ Fin l | ∀ a, y a = x (e a)} ≤ 1 := by
    refine (Set.ncard_le_one_iff (Set.toFinite _)).2 fun {e e'} he he' => Equiv.ext fun a => hinj ?_
    exact (he a).symm.trans (he' a)
  exact_mod_cast this

section Sat

variable {N : ℕ} {V W Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup Y]
  [Module ℂ Y]

theorem false_of_sub_quot {h : ℕ} (t : Fin h → IrrGL (k := k)) (ht : ∑ a, (t a).1 = N) (hA : IrreducibleAdmissibleGL)
    {π : Representation ℂ (GL (Fin N) k) V} (hπ : IsSmooth π) {ω : Representation ℂ (GL (Fin N) k) W}
    (f : ω.IntertwiningMap π) (hf : Function.Injective f) {τ : Representation ℂ (GL (Fin N) k) Y}
    (q : (GlobalTheory.CompanionTheory.BZSeg.TwoSeg.quotRep π ω f).IntertwiningMap τ) (hq : Function.Surjective q)
    (hle : jm t ht π ≤ 1) (h1 : 1 ≤ jm t ht ω) (h2 : 1 ≤ jm t ht τ) : False := by
  let Q := GlobalTheory.CompanionTheory.BZSeg.TwoSeg.quotRep π ω f
  let p : π.IntertwiningMap Q := ⟨(LinearMap.range f.toLinearMap).mkQ, fun g => by ext v; rfl⟩
  have hp : Function.Surjective p := Submodule.mkQ_surjective _
  have hex : Function.Exact f p := fun v => by
    show (LinearMap.range f.toLinearMap).mkQ v = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Iff.rfl
  have hadd : jm t ht π = jm t ht ω + jm t ht Q :=
    GlobalTheory.CompanionTheory.SocleJm.jhMult_jac_exact _ (GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA t) f p hπ hf hp hex
  have hQs : IsSmooth Q := (IsSubquotient.of_surjective p hp).isSmooth hπ
  have h3 : jm t ht τ ≤ jm t ht Q :=
    GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient t ht τ Q hQs (.of_surjective q hq)
  have h4 : (1 : ℕ∞) + 1 ≤ 1 := calc
    (1 : ℕ∞) + 1 ≤ jm t ht ω + jm t ht Q := add_le_add h1 (h2.trans h3)
    _ = jm t ht π := hadd.symm
    _ ≤ 1 := hle
  exact absurd h4 (by norm_num)

theorem surjective_of_jm (hA : IrreducibleAdmissibleGL) {x y : IrrGL (k := k)} (hx : x.IsCusp) (hy : y.IsCusp) (hne : x ≠ y)
    (hd : ∑ a, (![x, y] a).1 = N) (hd' : ∑ a, (![y, x] a).1 = N) {ω : Representation ℂ (GL (Fin N) k) W}
    (f : ω.IntertwiningMap (prodIrr ![x, y] hd)) (hf : Function.Injective f)
    (h1 : 1 ≤ jm ![x, y] hd ω) (h2 : 1 ≤ jm ![y, x] hd' ω) : Function.Surjective f := by
  by_contra hns
  have hs := isSmooth_prodIrr ![x, y] hd
  have hxc : ∀ a, (![x, y] a).IsCusp := Fin.forall_fin_two.2 ⟨hx, hy⟩
  have hyc : ∀ a, (![y, x] a).IsCusp := Fin.forall_fin_two.2 ⟨hy, hx⟩
  have hinj : Function.Injective ![x, y] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have hfl : HasFiniteLength (prodIrr ![x, y] hd) :=
    GlobalTheory.ProdFiniteLength.multiProd_hasFiniteLength GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k 2 N
      (fun a => (![x, y] a).1) (fun a => GlobalTheory.SplitRead.Irr.ofIrrRep (![x, y] a).2.rep) _
  let Q := GlobalTheory.CompanionTheory.BZSeg.TwoSeg.quotRep (prodIrr ![x, y] hd) ω f
  let p : (prodIrr ![x, y] hd).IntertwiningMap Q := ⟨(LinearMap.range f.toLinearMap).mkQ, fun g => by ext v; rfl⟩
  have hp : Function.Surjective p := Submodule.mkQ_surjective _
  have hQs : IsSmooth Q := (IsSubquotient.of_surjective p hp).isSmooth hs
  have hQn : Nontrivial (_ ⧸ LinearMap.range f.toLinearMap) :=
    Submodule.Quotient.nontrivial_iff.2 fun h => hns (LinearMap.range_eq_top.1 h)
  obtain ⟨Y', _, _, τ, hτs, hτi, q, hq⟩ := IrrQuot.exists_irreducible_smooth_quotient Q hQs
    (GlobalTheory.JacquetBlocks.hasFiniteLength_of_surjective p hp hfl) hQn
  have hτsub : IsSubquotient τ (prodIrr ![x, y] hd) := (IsSubquotient.of_surjective q hq).trans (.of_surjective p hp)
  have hsum : x.1 + y.1 = N := by simpa [Fin.sum_univ_two] using hd
  have hN : 0 < N := by have := hx.1; omega
  obtain ⟨u, hu, hu0, g, hg⟩ := GlobalTheory.CompanionTheory.JacquetLeft.exists_embedding hA τ hτs hτi hN
  haveI hYn : Nontrivial Y' := GlobalTheory.JacFactor.nontrivial_of_isIrreducible hτi
  have hg0 : ∃ v, g v ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : Y')
    exact ⟨v, fun h => hv (hg (h.trans (map_zero g).symm))⟩
  have hj := GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA u hu τ hτs g hg0
  have hj' := GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient u hu τ _ hs hτsub
  by_cases hz : (u 1).1 = 0
  · obtain ⟨z, hz1, ⟨E⟩⟩ := GlobalTheory.CompanionTheory.FineProd.ProdSingle.prodIrr_single u hu 0 (fun i hi => by
      obtain rfl : i = 1 := by omega
      exact hz)
    have hsq : IsSubquotient τ z.rep.ρ :=
      .of_injective (E.toIntertwiningMap.comp g) (E.toLinearEquiv.injective.comp hg)
    obtain ⟨θ⟩ := nonempty_equiv_of_isSubquotient hτi z.rep.irr hsq
    have hc : IrrGL.IsCusp (⟨N, z⟩ : IrrGL (k := k)) := hz1 ▸ hu0
    have h0 := GlobalTheory.CompanionTheory.CuspNotInd.jhMult_eq_zero_of_isCusp hA ⟨N, z⟩ ![x, y] hd hc le_rfl
      (Fin.forall_fin_two.2 ⟨hx.1, hy.1⟩)
    exact jhMult_ne_zero_iff.2 ((IsSubquotient.of_injective θ.toIntertwiningMap θ.toLinearEquiv.injective).trans hτsub) h0
  · have hpos : ∀ a, 0 < (u a).1 := by
      refine Fin.forall_fin_two.2 ⟨hu0.1, Nat.pos_of_ne_zero hz⟩
    obtain ⟨e, he⟩ := exists_equiv_of_jm_ne_zero ![x, y] u hd hu hxc hpos
      (ENat.one_le_iff_ne_zero.1 (hj.trans hj'))
    have hcases : u = ![x, y] ∨ u = ![y, x] := by
      have hee : e 0 ≠ e 1 := fun h => by simpa using e.injective h
      have key : ∀ a b : Fin 2, a ≠ b → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by decide
      rcases key _ _ hee with ⟨a, b⟩ | ⟨a, b⟩
      · exact Or.inl (funext (Fin.forall_fin_two.2 ⟨(he 0).trans (by simp [a]), (he 1).trans (by simp [b])⟩))
      · exact Or.inr (funext (Fin.forall_fin_two.2 ⟨(he 0).trans (by simp [a]), (he 1).trans (by simp [b])⟩))
    rcases hcases with rfl | rfl
    · exact false_of_sub_quot ![x, y] hd hA hs f hf q hq (jm_le_one hA _ _ hd hd hxc hxc hinj) h1 hj
    · exact false_of_sub_quot ![y, x] hd' hA hs f hf q hq (jm_le_one hA _ _ hd hd' hxc hyc hinj) h2 hj

end Sat

theorem nu_one_ne {x : IrrGL (k := k)} (hx : 0 < x.1) : x.nu 1 ≠ x := fun h => by
  have h1 : x.nu ((1 : ℕ) : ℂ) = x.nu ((0 : ℕ) : ℂ) := by simpa using h
  exact one_ne_zero (IrrGL.nu_natCast_inj hx |>.1 h1)

end GlobalTheory.CompanionTheory.CuspPairSub
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReverseOrderedProductHasSocle
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReverseOrderedProductHasSocle
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.SocleRev

theorem exists_isSocle_prodIrr_of_isRevOrdered : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LSegJacquet k → LUnlinkedIrr k →
    LUnlinkedComm k → ∀ {h N : ℕ} (Γ : Fin h → Segment k) (y : Fin h → IrrGL (k := k)) (hd : ∑ a, (y a).1 = N),
    IsRevOrdered Γ → (∀ i, IsLSeg (Γ i) (y i).rep) → ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr y hd) := by
  intro k _ _ _ _ hA hJ hI hC h N Γ y hd hR hL
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_canonical_segment_order Γ
  have hR' : IsRevOrdered (Γ ∘ σ) := GlobalTheory.T.canonical_segments_reverse_ordered _ hσ
  have hd' : ∑ a, (y (σ a)).1 = N := by
    rw [← hd]; exact Equiv.sum_comp σ (fun a => (y a).1)
  obtain ⟨e₁⟩ := GlobalTheory.T.reverse_ordered_product_perm_equiv hA hC Γ σ y hd hd' hR hR' hL
  have hL' : ∀ i, IsLSeg ((Γ ∘ σ) i) ((y ∘ σ) i).rep := fun i => hL (σ i)
  obtain ⟨g, z, hz, ⟨e₂⟩, hjm⟩ := GlobalTheory.T.canonical_product_equiv_multiplicity_one hA hJ hI (Γ ∘ σ) (y ∘ σ) hd' hσ hL'
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.socle_of_multiplicity_one hA z hz hjm
  exact ⟨τ, hτ.of_equiv (Representation.Equiv.refl _) (e₁.trans e₂).symm⟩

end GlobalTheory.CompanionTheory.SocleRev
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReverseOrderedProductHasSocleStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reverse_ordered_product_has_socle : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LSegJacquet k → LUnlinkedIrr k → LUnlinkedComm k → ∀ {h N : ℕ} (Γ : Fin h → Segment k) (y : Fin h → IrrGL (k := k)) (hd : ∑ a, (y a).1 = N), IsRevOrdered Γ → (∀ i, IsLSeg (Γ i) (y i).rep) → ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr y hd) := by
  first | exact @GlobalTheory.CompanionTheory.SocleRev.exists_isSocle_prodIrr_of_isRevOrdered | exact GlobalTheory.CompanionTheory.SocleRev.exists_isSocle_prodIrr_of_isRevOrdered | (intros; apply GlobalTheory.CompanionTheory.SocleRev.exists_isSocle_prodIrr_of_isRevOrdered <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactMaximalPairPlace
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.FA
open scoped Classical

attribute [local instance] borelG borelF borelH

namespace GlobalTheory.CompanionTheory.FmPowP

section Generic

variable {H : Type} [Group H]

theorem hint_ind_left (K U : Subgroup H) (hUK : U ≤ K) (hi : U.relIndex K ≠ 0) (f : H → ℂ)
    (hl : ∀ u ∈ U, ∀ g, f (u * g) = f g) (m : H) :
    hint K (fun z => (U : Set H).indicator (fun _ => ((U.relIndex K : ℕ) : ℂ)) z * f (z⁻¹ * m)) = f m := by
  have hC : ((U.relIndex K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hi
  rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H K U _ hUK (fun k hk x => ?_) hi]
  · rw [finsum_eq_single _ ((1 : H) : H ⧸ U)]
    · have hmem : (((1 : H) : H ⧸ U).out : H) ∈ U := by
        have := QuotientGroup.out_eq' ((1 : H) : H ⧸ U)
        simpa using (QuotientGroup.eq.1 this)
      rw [Set.indicator_of_mem (by exact hmem), hl _ (inv_mem hmem)]
      field_simp
    · intro q hq
      have hnot : (q.out : H) ∉ U := fun h => hq (by
        rw [← QuotientGroup.out_eq' q]
        exact QuotientGroup.eq.2 (by simpa using inv_mem h))
      rw [Set.indicator_of_notMem (by exact hnot), zero_mul]
  · have h1 : (x * k ∈ (U : Set H)) ↔ x ∈ (U : Set H) := Subgroup.mul_mem_cancel_right U hk
    have h2 : (x * k)⁻¹ * m = k⁻¹ * (x⁻¹ * m) := by group
    rw [h2, hl _ (inv_mem hk)]
    by_cases hx : x ∈ (U : Set H)
    · rw [Set.indicator_of_mem (h1.2 hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem (fun h => hx (h1.1 h)), Set.indicator_of_notMem hx]

theorem hint_ind_right (K U : Subgroup H) (hUK : U ≤ K) (hi : U.relIndex K ≠ 0) (f : H → ℂ)
    (hr : ∀ u ∈ U, ∀ g, f (g * u) = f g) (m : H) :
    hint K (fun z => f z * (U : Set H).indicator (fun _ => ((U.relIndex K : ℕ) : ℂ)) (z⁻¹ * m)) = f m := by
  have hC : ((U.relIndex K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hi
  rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H K U _ hUK (fun k hk x => ?_) hi]
  · rw [finsum_eq_single _ ((m : H) : H ⧸ U)]
    · obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U m
      have hmem : ((((m : H) : H ⧸ U).out : H))⁻¹ * m ∈ U := by
        rw [hu]; simp
      rw [Set.indicator_of_mem (by exact hmem), hu, hr _ u.2]
      field_simp
    · intro q hq
      have hnot : ((q.out : H))⁻¹ * m ∉ U := fun h => hq (by
        rw [← QuotientGroup.out_eq' q]
        exact QuotientGroup.eq.2 h)
      rw [Set.indicator_of_notMem (by exact hnot), mul_zero]
  · have h2 : (x * k)⁻¹ * m = k⁻¹ * (x⁻¹ * m) := by group
    have h1 : (k⁻¹ * (x⁻¹ * m) ∈ (U : Set H)) ↔ x⁻¹ * m ∈ (U : Set H) :=
      Subgroup.mul_mem_cancel_left U (inv_mem hk)
    rw [hr _ hk, h2]
    by_cases hx : x⁻¹ * m ∈ (U : Set H)
    · rw [Set.indicator_of_mem (h1.2 hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem (fun h => hx (h1.1 h)), Set.indicator_of_notMem hx]

theorem relIndex_ne_of_open [TopologicalSpace H] [IsTopologicalGroup H] {K U : Subgroup H}
    (hU : IsOpen (U : Set H)) (hK : IsCompact (K : Set H)) : U.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have ho : IsOpen ((U.subgroupOf K : Subgroup K) : Set K) := hU.preimage continuous_subtype_val
  haveI : Finite (K ⧸ U.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.index_ne_zero_of_finite

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem isCompact_maximal_pair_place (w : Pl E) : IsCompact ((K2 a b w : Subgroup _) : Set (GLw a w × GLw b w)) := by
  have h1 := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2
  have h2 := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2
  simpa [Subgroup.coe_prod] using h1.prod h2

theorem mconv_idem_left {w : Pl E} {U : Subgroup (GLw a w × GLw b w)} (hU : IsOpen (U : Set (GLw a w × GLw b w)))
    (hUK : U ≤ K2 a b w) (f : LF a b w) (hl : ∀ u ∈ U, ∀ g, f (u * g) = f g) :
    PositivityTheory.Rg.BcN.F2.mconv (idem U) f = f := by
  funext m
  exact hint_ind_left _ U hUK (relIndex_ne_of_open hU (isCompact_maximal_pair_place w)) f hl m

theorem mconv_idem_right {w : Pl E} {U : Subgroup (GLw a w × GLw b w)} (hU : IsOpen (U : Set (GLw a w × GLw b w)))
    (hUK : U ≤ K2 a b w) (f : LF a b w) (hr : ∀ u ∈ U, ∀ g, f (g * u) = f g) :
    PositivityTheory.Rg.BcN.F2.mconv f (idem U) = f := by
  funext m
  exact hint_ind_right _ U hUK (relIndex_ne_of_open hU (isCompact_maximal_pair_place w)) f hr m

theorem mconv_zero_left {w : Pl E} (f : LF a b w) : PositivityTheory.Rg.BcN.F2.mconv (0 : LF a b w) f = 0 := by
  funext m
  simpa [PositivityTheory.Rg.BcN.F2.mconv] using GlobalTheory.CompanionTheory.FamClP.hint_zero (K2 a b w)

theorem mconv_zero_right {w : Pl E} (f : LF a b w) : PositivityTheory.Rg.BcN.F2.mconv f (0 : LF a b w) = 0 := by
  funext m
  simpa [PositivityTheory.Rg.BcN.F2.mconv] using GlobalTheory.CompanionTheory.FamClP.hint_zero (K2 a b w)

theorem idem_left {w : Pl E} (U : Subgroup (GLw a w × GLw b w)) (u) (hu : u ∈ U) (g) : idem U (u * g) = idem U g := by
  have h1 : (u * g ∈ (U : Set (GLw a w × GLw b w))) ↔ g ∈ (U : Set (GLw a w × GLw b w)) :=
    Subgroup.mul_mem_cancel_left U hu
  unfold idem
  by_cases hx : g ∈ (U : Set (GLw a w × GLw b w))
  · rw [Set.indicator_of_mem (h1.2 hx), Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem (fun h => hx (h1.1 h)), Set.indicator_of_notMem hx]

section Sel

variable {κ : Pl E → Type} [∀ w, Fintype (κ w)]

end Sel

section Alg

variable {κ : Pl E → Type} [∀ w, Fintype (κ w)]

theorem mconv_idem_idem {w : Pl E} {U : Subgroup (GLw a w × GLw b w)} (hU : IsOpen (U : Set (GLw a w × GLw b w)))
    (hUK : U ≤ K2 a b w) : PositivityTheory.Rg.BcN.F2.mconv (idem U) (idem U) = idem U :=
  mconv_idem_left hU hUK _ (idem_left U)

end Alg

section Lev

end Lev

section Act

end Act

section Main

variable {κ : Pl E → Type} [∀ w, Fintype (κ w)] {S : Set (Pl E)} {P : Finset (Pl E)} {B : Block E}
  {e : B.κ ≃ ∀ w : P, κ w} {U₁ U₂ : ∀ w : Pl E, Subgroup (GLw B.a w × GLw B.b w)} {L : LM κ B.a B.b}

variable (hAlg : FmAlg) (hAt : FmAtP) (hCM : Tail.ConvMul) (hAct : ActAlg) (hId : ActIdem) (hS : IsSection S)
  (hP : (↑P : Set (Pl E)) ⊆ S) (hU₁ : IsLev U₁) (hU₂ : IsLev U₂) (hok : L.Ok P) (hs : ∀ w, L.s w = idem (U₁ w))
  (ht : ∀ w, L.t w = idem (U₂ w))
  (hinv : ∀ w ∈ P, ∀ x y, ∀ u ∈ U₁ w, ∀ g, L.m w x y (u * g) = L.m w x y g ∧ L.m w x y (g * u) = L.m w x y g)









end Main

end GlobalTheory.CompanionTheory.FmPowP

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsBisExtra
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical

namespace GlobalTheory.CompanionTheory.FinActS

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def sf {S : Set (Pl E)} (φ₁ φ₂ : ∀ w : Pl E, LF a b w) : ∀ i : Slot S, LF a b i.pl
  | .inl w => φ₁ w.1
  | .inr w => φ₂ w.1

end GlobalTheory.CompanionTheory.FinActS

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsInjectiveOfSocle
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsInjectiveOfSocle
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.Multisegment

theorem inShW_of_wd_cosocle {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hSeg : LSegJacquet k)
    {𝔫 : Multiset (Segment k)} {N h h' : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} (Δ : Fin h → Segment k) (Γ : Fin h' → Segment k)
    (v : Fin h' → IrrGL (k := k)) (hd : ∑ a, (v a).1 = N) (hΓ : IsOrderedForm Γ 𝔫)
    (hv : ∀ i, IsLSeg (Γ i) (v i).rep) (hc : IsCosocle π (prodIrr v hd)) (hw : Wd π (wtW Δ)) :
    InShW 𝔫 (wtW Δ) := by
  have h1 : Wd (prodIrr v hd) (wtW Δ) :=
    GlobalTheory.T.word_occurs_of_subquotient (prodIrr v hd) π (isSmooth_prodIrr v hd) hc.isSubquotient _ hw
  have h2 := GlobalTheory.T.segment_product_word_in_shuffle hA hSeg v hd Γ hv (wtW Δ) (GlobalTheory.T.ordered_word_letters_cuspidal Δ) h1
  rwa [hΓ.1] at h2

theorem lInjective {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hSoc : LSocleGL k) (hSeg : LSegJacquet k) : LInjective k := by
  intro 𝔪 𝔫 x h𝔪 h𝔫
  obtain ⟨h, u, hd, ⟨Δ, hΔ, hu⟩, hc⟩ := id h𝔪
  obtain ⟨h', v, hd', ⟨Γ, hΓ, hv⟩, hc'⟩ := id h𝔫
  have wΔ : Wd x.rep (wtW Δ) := GlobalTheory.T.langlands_rep_ordered_word_occurs hA hSoc hSeg 𝔪 x.rep h𝔪 h Δ hΔ
  have wΓ : Wd x.rep (wtW Γ) := GlobalTheory.T.langlands_rep_ordered_word_occurs hA hSoc hSeg 𝔫 x.rep h𝔫 h' Γ hΓ
  exact GlobalTheory.T.ordered_forms_mutual_shuffle_eq hA 𝔪 𝔫 h h' Δ Γ hΔ hΓ
    (inShW_of_wd_cosocle hA hSeg Δ Γ v hd' hΓ hv hc' wΔ)
    (inShW_of_wd_cosocle hA hSeg Γ Δ u hd hΔ hu hc wΓ)

end GlobalTheory.CompanionTheory.Multisegment
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsInjectiveOfSocleStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlands_injective_of_socle : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), LSocleGL k → LSegJacquet k → LInjective k := by
  first | exact @GlobalTheory.CompanionTheory.Multisegment.lInjective | exact GlobalTheory.CompanionTheory.Multisegment.lInjective | (intros; apply GlobalTheory.CompanionTheory.Multisegment.lInjective <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatIntegrableAdelic
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatIntegrableAdelic
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

theorem sb_integrable_selfDual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx → ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, IsSchwartzBruhat Φ → Integrable Φ dx := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn ψ hψ dx hdx Φ hΦ
  exact (GlobalTheory.CompanionTheory.SiegelND.CoefSum.continuous_integrable_tuple σ hCM M n dx hdx.1 Φ hΦ).2

end GlobalTheory.CompanionTheory.SiegelND.Coef
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatIntegrableAdelicStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_integrable_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx → ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, IsSchwartzBruhat Φ → Integrable Φ dx := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.sb_integrable_selfDual | exact GlobalTheory.CompanionTheory.SiegelND.Coef.sb_integrable_selfDual | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.sb_integrable_selfDual <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClosedHermSMx
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.RswTop

theorem topC : PositivityTheory.Rg.Rsw.Cell.TopC := by
  intro D p e
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.CompanionTheory.MuC.hermS_facts D p e
  exact ⟨inferInstance, inferInstance, inferInstance, h2, h1, h3, h4⟩

end GlobalTheory.CompanionTheory.RswTop
end
end
