module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TemperedProductOfSquareIntegrable
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.ExistsDen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaThetaFunctionsOrientedPair
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitarisableSegmentTwistPrecedesAddOneLe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeExistsPosUnique

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneCharpolyTwistSpecial
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneCharpolyTwistSpecial
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WeilDeligne.SpCharpoly

theorem charpoly_blockDiag {m o R : Type*} [Fintype m] [DecidableEq m] [Fintype o]
    [DecidableEq o] [CommRing R] (B : o → Matrix m m R) :
    (Matrix.blockDiagonal B).charpoly = ∏ k, (B k).charpoly := by
  have e : Matrix.charmatrix (Matrix.blockDiagonal B) =
      Matrix.blockDiagonal (fun k => Matrix.charmatrix (B k)) := by
    ext ⟨i, k⟩ ⟨j, k'⟩
    simp only [Matrix.charmatrix_apply, Matrix.blockDiagonal_apply, Matrix.diagonal_apply,
      Prod.mk.injEq]
    split_ifs <;> simp_all
  rw [Matrix.charpoly, e, Matrix.det_blockDiagonal]
  rfl

theorem charpoly_map_diagEnd {n m : ℕ} (f : Module.End ℂ (Fin n → ℂ)) (c : Fin m → ℂ) :
    LinearMap.charpoly (TensorProduct.map f (diagEnd c)) = ∏ i, LinearMap.charpoly (c i • f) := by
  classical
  set b := Pi.basisFun ℂ (Fin n)
  have e : LinearMap.toMatrix (Pi.basisFun ℂ (Fin m)) (Pi.basisFun ℂ (Fin m)) (diagEnd c) =
      Matrix.diagonal c := by
    ext i j
    simp [Matrix.diagonal_apply, Pi.single_apply]
  rw [← LinearMap.charpoly_toMatrix _ (b.tensorProduct (Pi.basisFun ℂ (Fin m))),
    TensorProduct.toMatrix_map, e]
  have e2 : Matrix.kroneckerMap (· * ·) (LinearMap.toMatrix b b f) (Matrix.diagonal c) =
      Matrix.blockDiagonal fun i => LinearMap.toMatrix b b (c i • f) := by
    ext ⟨i, k⟩ ⟨j, k'⟩
    simp only [Matrix.kroneckerMap_apply, Matrix.blockDiagonal_apply, Matrix.diagonal_apply,
      map_smul, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp [mul_comm]
  rw [e2, charpoly_blockDiag]
  exact Finset.prod_congr rfl fun i _ => LinearMap.charpoly_toMatrix _ _

end GlobalTheory.WeilDeligne.SpCharpoly

namespace GlobalTheory.WeilDeligne

theorem charPol_lpTw_lpChar_lpSp : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), (x.lpTw 0).lpChar (WD.lpSp (h := h) 1) = x ∧ ∀ (l : ℕ) (σ : Weil h), ((x.lpTw (((l : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) l)).charPol σ = ((Multiset.range l).map fun j : ℕ => (x.lpTw j).charPol σ).prod := by
  intro E Ω _ _ _ _ _ A w h x
  refine ⟨?_, fun l σ => ?_⟩
  · rw [WD.lpTw_zero]
    induction x using WD.ind with
    | hP n a =>
      rw [WD.lpSp, WD.lpChar_mk]
      refine WD.sound (WDRep.Iso.symm ⟨(TensorProduct.rid ℂ (Fin n → ℂ)).symm ≪≫ₗ
        TensorProduct.congr (LinearEquiv.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ).symm,
        fun σ v => ?_, fun v => ?_⟩)
      · have : (WDRep.sp (h := h) 1).ρ σ = 1 := by
          refine LinearMap.ext fun v => funext fun i => ?_
          simp [WDRep.spEig]
        rw [WDRep.tensor_ρ, this]
        simp
      · have : (WDRep.sp (h := h) 1).N = 0 := by
          refine LinearMap.ext fun v => funext fun i => ?_
          simp [shiftEnd_apply]
        rw [WDRep.tensor_N, this]
        simp
  · induction x using WD.ind with
    | hP n a =>
      have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot
      rw [WD.lpSp, WD.lpTw_mk, WD.lpChar_mk, WD.charPol_mk, WDRep.tensor_ρ, WDRep.sp_ρ,
        SpCharpoly.charpoly_map_diagEnd]
      change _ = ∏ j ∈ Finset.range l, ((WD.mk a).lpTw (j : ℕ)).charPol σ
      rw [← Fin.prod_univ_eq_prod_range (fun j : ℕ => ((WD.mk a).lpTw (j : ℕ)).charPol σ)]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [WD.lpTw_mk, WD.charPol_mk, WDRep.tw_ρ, WDRep.tw_ρ, smul_smul, ← mul_zpow, WDRep.spEig,
        coe_qPow, ← Complex.cpow_add _ _ hq, ← Complex.ofReal_add, sub_add_cancel]

end GlobalTheory.WeilDeligne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneCharpolyTwistSpecialStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDeligne_charpoly_twist_special : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), (x.lpTw 0).lpChar (WD.lpSp (h := h) 1) = x ∧ ∀ (l : ℕ) (σ : Weil h), ((x.lpTw (((l : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) l)).charPol σ = ((Multiset.range l).map fun j : ℕ => (x.lpTw j).charPol σ).prod := by
  exact @_root_.GlobalTheory.WeilDeligne.charPol_lpTw_lpChar_lpSp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationLtOneIffNorm
noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.BridgeInertia

variable {l : ℕ} [Fact l.Prime]

theorem valuation_lt_one_iff_norm {Ω : Type} [Field Ω] {A : ValuationSubring Ω} {j : Ω →+* Loc.Om l}
    (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) (x : Ω) : A.valuation x < 1 ↔ ‖j x‖ < 1 := by
  rw [valuation_lt_one_iff', hj, hj, map_inv₀, norm_inv]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h0 : 0 < ‖j x‖ := norm_pos_iff.mpr ((_root_.map_ne_zero _).mpr hx)
    simp only [hx, false_or, not_le, one_lt_inv₀ h0]
    exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

theorem residue_trivial_of_image {Ω : Type} [Field Ω] [IsAlgClosed Ω] (j : Ω →+* Loc.Om l) (σ : GQ l)
    (h : ∀ y : Ω, ‖j y‖ ≤ 1 → ‖σ (j y) - j y‖ < 1) (x : Loc.Om l) (hx : ‖x‖ ≤ 1) : ‖σ x - x‖ < 1 := by
  obtain ⟨y, hy⟩ := (GlobalTheory.PlaceBridge.denseRange_embedding j).exists_dist_lt x one_pos
  rw [dist_eq_norm] at hy
  have hn : ∀ z, ‖σ z‖ = ‖z‖ := fun z => (spectralNorm_eq_of_equiv σ z).symm
  have hadd : ∀ a b : Loc.Om l, ‖a + b‖ ≤ max ‖a‖ ‖b‖ := IsUltrametricDist.norm_add_le_max
  have hjy : ‖j y‖ ≤ 1 := by
    have e : j y = x + -(x - j y) := by ring
    rw [e]
    exact (hadd _ _).trans (max_le hx (by rw [norm_neg]; exact hy.le))
  have e : σ x - x = σ (x - j y) + ((σ (j y) - j y) + -(x - j y)) := by
    rw [map_sub]; ring
  rw [e]
  refine (hadd _ _).trans_lt (max_lt (by rw [hn]; exact hy) ((hadd _ _).trans_lt (max_lt (h y hjy) ?_)))
  rw [norm_neg]; exact hy

theorem mem_Ine_iff {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosed Ω] {A : ValuationSubring Ω}
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : ∀ x, x ∈ A ↔ ‖Bw.j x‖ ≤ 1) (σ : ↥(GK Bw.Kw)) :
    ((Bw.e.symm σ : ↥(Dec (F := E) A)) : Ω ≃ₐ[E] Ω) ∈ Ine (F := E) A ↔
      ∀ x : Loc.Om l, ‖x‖ ≤ 1 → ‖(σ : GQ l) x - x‖ < 1 := by
  have hc : ∀ y, (σ : GQ l) (Bw.j y) = Bw.j (((Bw.e.symm σ : ↥(Dec (F := E) A)) : Ω ≃ₐ[E] Ω) y) := fun y => by
    rw [← Bw.e_comm, MulEquiv.apply_symm_apply]
  constructor
  · intro h
    refine residue_trivial_of_image Bw.j _ fun y hy => ?_
    rw [hc, ← map_sub, ← valuation_lt_one_iff_norm hj]
    exact h.2 y ((A.valuation_le_one_iff y).2 ((hj y).2 hy))
  · intro h
    refine ⟨(Bw.e.symm σ).2, fun y hy => ?_⟩
    rw [valuation_lt_one_iff_norm hj, map_sub, ← hc]
    exact h _ ((hj y).1 ((A.valuation_le_one_iff y).1 hy))

theorem inertEq : ∀ D : D7, InertEq D := by
  intro D i w hw
  have : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  have key : ∀ σ : Br.G D.nbr i w hw, σ ∈ Br.inert D.nbr i w hw ↔
      ∀ x : Loc.Om (D.nd.l i), ‖x‖ ≤ 1 → ‖(σ : GQ (D.nd.l i)) x - x‖ < 1 := fun σ =>
    mem_Ine_iff (D.nbr i w hw) (D.nbr_ind i w hw) σ
  refine le_antisymm (fun σ hσ => Subgroup.subset_closure ?_) ?_
  · exact (key σ).1 hσ
  · exact (Subgroup.closure_le _).2 fun σ hσ => (key σ).2 hσ

end GlobalTheory.BridgeInertia

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSqIntCoeffOfIsSquareIntegrable
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL MeasureTheory

namespace GlobalTheory.LocGL.SqIntBridge

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} {π : Representation ℂ (GL (Fin N) k) V}

theorem exists_central_scalar (hs : IsSmooth π) (hi : π.IsIrreducible) (hu : IsUnitarisable π) {z : GL (Fin N) k}
    (hz : z ∈ Subgroup.center (GL (Fin N) k)) : ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, π z v = c • v := by
  obtain ⟨c, hc⟩ := schur_GL hs hi ⟨π z, fun g => by
    rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz g]⟩
  have hc' : ∀ v, π z v = c • v := hc
  refine ⟨c, ?_, hc'⟩
  obtain ⟨B, -, hp, hB⟩ := hu
  have := Model.nontrivial_of_isIrreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have h0 : B v v ≠ 0 := fun e => by simpa [e] using hp v hv
  have h1 := congrArg norm (hB z v v)
  rw [hc'] at h1
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, norm_mul, RingHom.id_apply, RCLike.norm_conj] at h1
  have h2 : 0 < ‖B v v‖ := norm_pos_iff.2 h0
  have h3 : ‖c‖ * ‖c‖ = 1 := mul_right_cancel₀ h2.ne' (by rw [mul_assoc, h1, one_mul])
  nlinarith [norm_nonneg c]

theorem norm_coeff_out (hs : IsSmooth π) (hi : π.IsIrreducible) (hu : IsUnitarisable π) (v : V) (l : Module.Dual ℂ V)
    (g : GL (Fin N) k) : ‖l (π (QuotientGroup.mk g : AdGL k N).out v)‖ = ‖l (π g v)‖ := by
  obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center (GL (Fin N) k)) g
  obtain ⟨c, h1, hc⟩ := exists_central_scalar hs hi hu z.2
  rw [hz, map_mul, Module.End.mul_apply, hc, map_smul, map_smul, norm_smul, h1, one_mul]


omit [ValuativeRel k] in
theorem isLocallyConstant_orbit [IsTopologicalRing k] (hs : IsSmooth π) (v : V) :
    IsLocallyConstant fun g : GL (Fin N) k => π g v := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_
  refine Filter.mem_of_superset (((hs v).preimage (continuous_const_mul g⁻¹)).mem_nhds (by simp)) fun x hx => ?_
  have hx' : π (g⁻¹ * x) v = v := hx
  show π x v = π g v
  conv_rhs => rw [← hx', ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

theorem isSqIntCoeff_of_isSquareIntegrable {δ : IrrGL (k := k)} (h : UnitaryDual.IsSquareIntegrable δ) :
    IsSqIntCoeff δ.rep := by
  obtain ⟨-, hu, ν, hν, H⟩ := h
  intro m hm μ hμ v l hl
  obtain rfl : m = _root_.borel _ := hm.measurable_eq
  letI : MeasurableSpace (AdGL k δ.1) := _root_.borel _
  have := secondCountableTopology_GL k (Fin δ.1)
  have hs := δ.2.rep.smooth
  have hF := norm_coeff_out hs δ.2.rep.irr hu v l
  have hl' : l ∈ smoothPart δ.rep.dual := hl.preimage continuous_inv
  have hf : AEStronglyMeasurable (fun q : AdGL k δ.1 => ‖l (δ.rep q.out v)‖) μ := by
    refine Continuous.aestronglyMeasurable ((QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ?_)
    rw [show (fun q : AdGL k δ.1 => ‖l (δ.rep q.out v)‖) ∘ QuotientGroup.mk = fun g => ‖l (δ.rep g v)‖ from funext hF]
    exact ((isLocallyConstant_orbit hs v).comp fun w => ‖l w‖).continuous
  refine ⟨fun q => ‖l (δ.rep q.out v)‖, hF, ?_⟩
  rw [memLp_iff, show ENNReal.ofReal 2 = 2 by simp, eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hf,
    Measure.isMulLeftInvariant_eq_smul μ ν, lintegral_smul_measure]
  have h1 := H v l hl'
  simp only [enorm_norm, ENNReal.toReal_ofNat, ENNReal.rpow_two]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top h1

end GlobalTheory.LocGL.SqIntBridge

namespace GlobalTheory.Published

theorem squareIntegrableSegment_of_ess (h : EssSquareIntegrableSegments) : SquareIntegrableSegment := by
  intro k _ _ _ _ _ δ hδ
  refine (h k δ hδ.1).1 ⟨1, isSmoothChar_one, ?_⟩
  rw [IrrGL.tw_one]
  exact SqIntBridge.isSqIntCoeff_of_isSquareIntegrable hδ

end GlobalTheory.Published

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionGroupEquivLocalGaloisGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalInertiaIffMemPlaceInertia
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalInertiaIffMemPlaceInertia
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.DecInertia

theorem valuation_lt_one_iff_norm {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] {A : ValuationSubring Ω}
    {j : Ω →+* PadicAlgCl p} (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) (x : Ω) :
    A.valuation x < 1 ↔ ‖j x‖ < 1 := by
  rw [valuation_lt_one_iff', hj, hj, map_inv₀, norm_inv]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h0 : 0 < ‖j x‖ := norm_pos_iff.mpr ((_root_.map_ne_zero _).mpr hx)
    simp only [hx, false_or, not_le, one_lt_inv₀ h0]
    exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

theorem inertiaK_iff_mem_Ine (p : ℕ) [Fact p.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (A : ValuationSubring Ω) (j : Ω →+* PadicAlgCl p) (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (i : ↥(A.decompositionSubgroup F) ≃* (PadicAlgCl p ≃ₐ[↥K] PadicAlgCl p))
    (hi : ∀ (g : ↥(A.decompositionSubgroup F)) (x : Ω), i g (j x) = j ((g : Ω ≃ₐ[F] Ω) x))
    (g : ↥(A.decompositionSubgroup F)) :
    i g ∈ Formalism.GaloisCohomology.inertiaK p K ↔ (g : Ω ≃ₐ[F] Ω) ∈ Ine (F := F) A := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have hn : ∀ (σ : PadicAlgCl p ≃ₐ[↥K] PadicAlgCl p) (z : PadicAlgCl p), ‖σ z‖ = ‖z‖ := fun σ z =>
    GlobalTheory.PlaceBridge.norm_algEquiv (σ.restrictScalars ℚ_[p]) z
  have hadd : ∀ a b : PadicAlgCl p, ‖a + b‖ ≤ max ‖a‖ ‖b‖ := IsUltrametricDist.norm_add_le_max
  constructor
  · intro h
    let H : Subgroup (PadicAlgCl p ≃ₐ[↥K] PadicAlgCl p) :=
      ((Ine (F := F) A).subgroupOf (A.decompositionSubgroup F)).map i.toMonoidHom
    have hsub : Formalism.GaloisCohomology.inertiaSet p K ⊆ H := by
      intro σ hσ
      refine ⟨i.symm σ, ?_, by simp⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      refine ⟨(i.symm σ).2, fun x hx => ?_⟩
      rw [valuation_lt_one_iff_norm hj, map_sub, ← hi, MulEquiv.apply_symm_apply]
      exact hσ (j x) ((hj x).1 ((A.valuation_le_one_iff x).1 hx))
    have hle : Formalism.GaloisCohomology.inertiaK p K ≤ H := (Subgroup.closure_le _).2 hsub
    obtain ⟨g', hg', e⟩ := hle h
    have : g' = g := i.injective e
    subst this
    exact Subgroup.mem_subgroupOf.1 hg'
  · intro h
    apply Subgroup.subset_closure
    intro x hx
    obtain ⟨y, hy⟩ := (GlobalTheory.PlaceBridge.denseRange_embedding j).exists_dist_lt x one_pos
    rw [dist_eq_norm] at hy
    have hjy : ‖j y‖ ≤ 1 := by
      have e : j y = x + -(x - j y) := by ring
      rw [e]
      exact (hadd _ _).trans (max_le hx (by rw [norm_neg]; exact hy.le))
    have hgy : ‖(i g) (j y) - j y‖ < 1 := by
      rw [hi, ← map_sub, ← valuation_lt_one_iff_norm hj]
      exact h.2 y ((A.valuation_le_one_iff y).2 ((hj y).2 hjy))
    have e : (i g) x - x = (i g) (x - j y) + (((i g) (j y) - j y) + -(x - j y)) := by
      rw [map_sub]; ring
    rw [e]
    refine (hadd _ _).trans_lt (max_lt (by rw [hn]; exact hy) ((hadd _ _).trans_lt (max_lt hgy ?_)))
    rw [norm_neg]; exact hy

end GlobalTheory.DecInertia
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalInertiaIffMemPlaceInertiaStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localInertia_iff_mem_placeInertia : ∀ (p : ℕ) [Fact p.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (A : ValuationSubring Ω) (j : Ω →+* PadicAlgCl p), (∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) →
    ∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p))
      (i : ↥(A.decompositionSubgroup F) ≃* (PadicAlgCl p ≃ₐ[↥K] PadicAlgCl p)),
      (∀ (g : ↥(A.decompositionSubgroup F)) (x : Ω), i g (j x) = j ((g : Ω ≃ₐ[F] Ω) x)) →
      ∀ g : ↥(A.decompositionSubgroup F), i g ∈ Formalism.GaloisCohomology.inertiaK p K ↔ (g : Ω ≃ₐ[F] Ω) ∈ Ine (F := F) A := by
  first | exact @GlobalTheory.DecInertia.inertiaK_iff_mem_Ine | exact GlobalTheory.DecInertia.inertiaK_iff_mem_Ine | (intros; apply GlobalTheory.DecInertia.inertiaK_iff_mem_Ine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDecompositionGroupEquivPadicGalois
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDecompositionGroupEquivPadicGalois
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.DecGalois

theorem exists_continuousMulEquiv : ∀ (p : ℕ) [Fact p.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (A : ValuationSubring Ω) (j : Ω →+* PadicAlgCl p), (∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) →
    ∃ i : ↥(A.decompositionSubgroup F) ≃ₜ*
      (PadicAlgCl p ≃ₐ[↥(IntermediateField.adjoin ℚ_[p] (Set.range fun x : F => j (algebraMap F Ω x)))] PadicAlgCl p),
      ∀ (g : ↥(A.decompositionSubgroup F)) (x : Ω), i g (j x) = j ((g : Ω ≃ₐ[F] Ω) x) := by
  intro p _ F Ω _ _ _ _ _ A j hj
  let K : Formalism.BasicNotions.Loc.FinExt p :=
    ⟨IntermediateField.adjoin ℚ_[p] (Set.range fun x : F => j (algebraMap F Ω x)),
      GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap F Ω))⟩
  have hK := K.2
  obtain ⟨e, he, he', hec⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := F) hj K rfl
  obtain ⟨hf, hf'⟩ := GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[p] (PadicAlgCl p) K.1
  let e2 : ↥(A.decompositionSubgroup F) ≃* (PadicAlgCl p ≃ₐ[↥K.1] PadicAlgCl p) :=
    e.trans (IntermediateField.fixingSubgroupEquiv K.1)
  refine ⟨{ e2 with continuous_toFun := hf.comp he, continuous_invFun := he'.comp hf' }, fun g x => ?_⟩
  exact hec g x

end GlobalTheory.DecGalois
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDecompositionGroupEquivPadicGaloisStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_decompositionGroup_equiv_padicGalois : ∀ (p : ℕ) [Fact p.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (A : ValuationSubring Ω) (j : Ω →+* PadicAlgCl p), (∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) →
    ∃ i : ↥(A.decompositionSubgroup F) ≃ₜ*
      (PadicAlgCl p ≃ₐ[↥(IntermediateField.adjoin ℚ_[p] (Set.range fun x : F => j (algebraMap F Ω x)))] PadicAlgCl p),
      ∀ (g : ↥(A.decompositionSubgroup F)) (x : Ω), i g (j x) = j ((g : Ω ≃ₐ[F] Ω) x) := by
  first | exact @GlobalTheory.DecGalois.exists_continuousMulEquiv | exact GlobalTheory.DecGalois.exists_continuousMulEquiv | (intros; apply GlobalTheory.DecGalois.exists_continuousMulEquiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionGroupEquivLocalGaloisGroup
noncomputable section

namespace GlobalTheory.DecLocal

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

theorem exists_place_below : ∀ {p : ℕ} [Fact p.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω), A.valuation (p : Ω) < 1 →
    ∃ w : HeightOneSpectrum (𝓞 F), w ∈ Formalism.BasicNotions.placesOver F p ∧ IsPlaceOver A w := by
  intro p _ F Ω _ _ _ _ A hp
  have hint : ∀ x : 𝓞 F, algebraMap F Ω (x : F) ∈ A := fun x =>
    ReciprocityTheory.Gal.mem_of_isIntegral_int A ((NumberField.RingOfIntegers.isIntegral_coe x).algebraMap)
  let f : 𝓞 F →+* A := RingHom.codRestrict ((algebraMap F Ω).comp (algebraMap (𝓞 F) F)) A hint
  let I : Ideal (𝓞 F) := Ideal.comap f (IsLocalRing.maximalIdeal A)
  have hI : ∀ x : 𝓞 F, x ∈ I ↔ A.valuation (algebraMap F Ω (x : F)) < 1 := fun x => by
    change f x ∈ IsLocalRing.maximalIdeal A ↔ _
    exact ValuationSubring.valuation_lt_one_iff A (f x)
  have hpI : ((p : 𝓞 F)) ∈ I := by
    rw [hI]; simpa using hp
  have hp0 : ((p : 𝓞 F)) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  let w : HeightOneSpectrum (𝓞 F) :=
    { asIdeal := I, isPrime := Ideal.comap_isPrime f _,
      ne_bot := fun h => hp0 (by rw [← Ideal.mem_bot, ← h]; exact hpI) }
  exact ⟨w, hpI, fun x => (hI x).symm⟩

theorem exists_root_of_unity : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (j : Ω →+* PadicAlgCl p)
    (n : ℕ) (z : PadicAlgCl p), z ^ (p ^ n) = 1 → ∃ y : Ω, y ^ (p ^ n) = 1 ∧ j y = z := by
  intro p _ Ω _ _ j n z hz
  have hf : ((X ^ (p ^ n) - 1 : Polynomial Ω).map j) = X ^ (p ^ n) - 1 := by simp
  have hne : (X ^ (p ^ n) - 1 : Polynomial (PadicAlgCl p)) ≠ 0 := by
    simpa using X_pow_sub_C_ne_zero (pow_pos (Fact.out : p.Prime).pos n) (1 : PadicAlgCl p)
  have hz' : z ∈ ((X ^ (p ^ n) - 1 : Polynomial Ω).map j).roots := by
    rw [hf, mem_roots hne]; simp [hz]
  rw [Splits.roots_map (IsAlgClosed.splits _), Multiset.mem_map] at hz'
  obtain ⟨y, hy, rfl⟩ := hz'
  refine ⟨y, ?_, rfl⟩
  have := isRoot_of_mem_roots hy
  simpa [sub_eq_zero] using this

theorem norm_lt_one_iff {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (j : Ω →+* PadicAlgCl p)
    (hA : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) (y : Ω) : ‖j y‖ < 1 ↔ A.valuation y < 1 := by
  rw [valuation_lt_one_iff', hA, hA]
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have h0 : 0 < ‖j y‖ := norm_pos_iff.2 ((map_ne_zero j).2 hy)
    rw [map_inv₀, norm_inv]
    simp only [hy, false_or]
    constructor
    · intro h
      exact ⟨h.le, not_le.2 ((one_lt_inv₀ h0).2 h)⟩
    · rintro ⟨h1, h2⟩
      refine lt_of_le_of_ne h1 fun h => h2 ?_
      rw [h, inv_one]

theorem finrank_closure_eq_locDeg : ∀ (p : ℕ) [Fact p.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (j : Ω →+* PadicAlgCl p), (∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) →
    ∀ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v →
      Module.finrank ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] (Set.range fun x : F => j (algebraMap F Ω x))) =
        locDeg v := by
  intro p _ F Ω _ _ _ _ A j hA v hv
  let φ : F →+* PadicAlgCl p := j.comp (algebraMap F Ω)
  obtain ⟨v', -, hφ⟩ := PI.CompDegEF.placeProp p F φ
  have hvp : v ∈ Formalism.BasicNotions.placesOver F p := by
    show ((p : 𝓞 F)) ∈ v.asIdeal
    rw [← hv, ← norm_lt_one_iff A j hA]
    simpa using GlobalTheory.PlaceBridge.norm_l_lt_one (l := p)
  exact PI.CompDegEF.locDegOf_of PI.CompDegEF.ballCard PI.CompDegEF.denseSurj PI.CompDegEF.kerProp
    PI.CompDegEF.normCard p F φ ⟨_, GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range φ⟩
    (fun x => IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩)
    (GlobalTheory.PlaceBridge.adjoin_range_subset_closure φ) v hvp
    (fun x => ⟨(hφ x).1, (norm_lt_one_iff A j hA _).trans (hv x)⟩)

theorem decEquiv : ReciprocityTheory.ChartRestriction.T2.DecEquiv := by
  intro p _ F Ω _ _ _ _ _ A hp
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  obtain ⟨w, hw, hAw⟩ := exists_place_below (F := F) A hp
  obtain ⟨j, hj⟩ := GlobalTheory.PlaceBridge.exists_embedding F Ω w A hw hAw
  obtain ⟨i, hi⟩ := GlobalTheory.T.exists_decompositionGroup_equiv_padicGalois p F Ω A j hj
  refine ⟨_, GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap F Ω)), i, ?_,
    fun g => GlobalTheory.T.localInertia_iff_mem_placeInertia p F Ω A j hj _ i.toMulEquiv hi g,
    fun v hv => finrank_closure_eq_locDeg p F Ω A j hj v hv⟩
  intro O _ ε hε g n ζ hζ
  obtain ⟨y, hy, rfl⟩ := exists_root_of_unity p Ω j n ζ hζ
  obtain ⟨a, ha, ha'⟩ := hε (i.symm g) n y hy
  refine ⟨a, ?_, ha'⟩
  have e := hi (i.symm g) y
  rw [ContinuousMulEquiv.apply_symm_apply] at e
  rw [e, ha, map_pow]

end GlobalTheory.DecLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionGroupEquivLocalGaloisGroupStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decomposition_group_equiv_local_galois_group : ReciprocityTheory.ChartRestriction.T2.DecEquiv := by
  first | exact @GlobalTheory.DecLocal.decEquiv | exact GlobalTheory.DecLocal.decEquiv | (intros; apply GlobalTheory.DecLocal.decEquiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionEqZeroOfMeanSquareZero
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

open scoped ContDiff

namespace GlobalTheory.ThetaSchurBdd

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem psi_ne_zero (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : ψ a ≠ 0 := fun h => by
  have := hψ.1.2.1 a
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem isTheta_star_mul_mul (hψ : IsStdChar D ψ (-1)) {g h f : WO S T → ℂ} (hg : IsThetaFunO ψ S T g)
    (hh : IsThetaFunO ψ S T h) (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (fun x => star (g x) * h x * f x) := {
  quasi γ w := by
    rw [hg.quasi, hh.quasi, hf.quasi, star_mul']
    linear_combination (star (g w) * h w * f w * ψ (-(symplOH S T (ratW T S γ) w))) *
      GlobalTheory.ThetaSchur.mul_star_psi hψ (-(symplOH S T (ratW T S γ) w))
  level := by
    obtain ⟨U1, o1, h1⟩ := hg.level
    obtain ⟨U2, o2, h2⟩ := hh.level
    obtain ⟨U3, o3, h3⟩ := hf.level
    refine ⟨U1 ⊓ U2 ⊓ U3, (o1.inter o2).inter o3, fun u hu hfin => ?_⟩
    funext x
    have e1 := congrFun (h1 u hu.1.1 hfin) x
    have e2 := congrFun (h2 u hu.1.2 hfin) x
    have e3 := congrFun (h3 u hu.2 hfin) x
    simp only [heisO] at e1 e2 e3 ⊢
    have hs := GlobalTheory.ThetaSchur.mul_star_psi hψ (symplOH S T x u)
    rw [← e1, ← e2, ← e3, star_mul']
    linear_combination (-(ψ (symplOH S T x u) * (star (g (x + u)) * h (x + u) * f (x + u)))) * hs
  cont := (hg.cont.star.mul hh.cont).mul hf.cont
  smooth k L hL hL0 w := by
    have hs : ContDiff ℝ ∞ (fun t => star (g (w + L t))) :=
      Complex.conjCLE.contDiff.comp (hg.smooth k L hL hL0 w)
    exact ContDiff.mul (ContDiff.mul hs (hh.smooth k L hL hL0 w)) (hf.smooth k L hL hL0 w) }

theorem exists_bound (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have hp : ∀ γ ∈ ratL T S, ∀ w, ‖f (γ + w)‖ = ‖f w‖ := by
    rintro _ ⟨γ, rfl⟩ w
    exact (congrArg norm (hf.quasi γ w)).trans (by rw [norm_mul, hψ.1.2.1, one_mul])
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.cont.continuousOn
  refine ⟨C, fun w => ?_⟩
  obtain ⟨γ, hγ, h⟩ := hKc w
  rw [← hp γ hγ w]
  exact hC _ h

theorem integrable_sq (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (h1 : μ 𝓕 = 1)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : Integrable (fun w => ‖f w‖ ^ 2) (μ.restrict 𝓕) := by
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  obtain ⟨C, hC⟩ := exists_bound hψ hf
  refine Integrable.of_bound (hf.cont.norm.pow 2).aestronglyMeasurable (C ^ 2)
    (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hC w) 2

theorem thetaFunction_eq_zero_of_meanSquare_zero (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hcv : IsCovolOne (ratL T S) μ 𝓕) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (h0 : nrm2 μ 𝓕 f = 0) :
    f = 0 := by
  obtain ⟨hμ, h𝓕, h1⟩ := hcv
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hae : ∀ᵐ w ∂(μ.restrict 𝓕), ‖f w‖ ^ 2 = 0 :=
    (integral_eq_zero_iff_of_nonneg (fun w => by positivity) (integrable_sq hψ h1 hf)).1 h0
  have ho : IsOpen {x | f x ≠ 0} := isOpen_ne_fun hf.cont continuous_const
  have hper : ∀ γ ∈ ratL T S, ∀ x, (f (γ + x) ≠ 0 ↔ f x ≠ 0) := by
    rintro _ ⟨γ, rfl⟩ x
    show f (ratW T S γ + x) ≠ 0 ↔ _
    rw [hf.quasi, ne_eq, mul_eq_zero, not_or]
    exact ⟨fun h => h.2, fun h => ⟨psi_ne_zero hψ _, h⟩⟩
  have h2 : μ {x | f x ≠ 0} = 0 := by
    refine h𝓕.measure_zero_of_invariant _ (fun g => ?_) ?_
    · ext x
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      show f (((-g : ratL T S) : WO S T) + x) ≠ 0 ↔ f x ≠ 0
      exact hper _ (-g).2 x
    · rw [← Measure.restrict_apply ho.measurableSet]
      rw [ae_iff] at hae
      simpa using hae
  funext x
  by_contra hx
  exact (ho.measure_pos μ ⟨x, hx⟩).ne' h2

end GlobalTheory.ThetaSchurBdd

namespace GlobalTheory.ThetaSchurBdd

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem trig_approx (hψ : IsStdChar D ψ (-1)) {q : WO S T → ℂ} (hq : Continuous q)
    (hqp : ∀ γ ∈ ratL T S, ∀ x, q (γ + x) = q x) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (s : Finset (ratL T S)) (c : ratL T S → ℂ), ∀ x, ‖q x - ∑ a ∈ s, c a * ψ (symplO S T x a)‖ ≤ δ := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨l1, l2, -, l4, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  exact GlobalTheory.trigPoly_dense_periodic (WO S T) (ratL T S) K hK hKc (ratL T S)
    (fun γ x => ψ (symplO S T x γ))
    (fun γ => by
      have : Continuous fun x : WO S T => symplOH S T x (γ : WO S T) :=
        GlobalTheory.WeilVacMove.continuous_symplOH S T continuous_id' continuous_const
      simp only [← l4]
      exact hψ.1.1.comp (this.add this))
    (fun γ x y => by
      simp only [← l4, l1, AddChar.map_add_eq_mul]
      ring)
    (fun γ γ' x => by
      simp only [← l4, AddSubgroup.coe_add, l2, AddChar.map_add_eq_mul]
      ring)
    (fun x => by
      simp only [← l4, AddSubgroup.coe_zero, GlobalTheory.WeilVacMove.symplOH_zero_right, add_zero, AddChar.map_zero_eq_one])
    (fun γ x => hψ.1.2.1 _)
    (fun x => by
      rw [← GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S T x]
      exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩)
    q hq hqp δ hδ

theorem trig_mul_eq (s : Finset (ratL T S)) (c : ratL T S → ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    (fun x => (∑ a ∈ s, c a * ψ (symplO S T x a)) * f x) = ∑ a ∈ s, c a • heisO ψ S T a f := by
  funext x
  rw [Finset.sum_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.ThetaSchur.heisO_rat hf a.2, mul_assoc]

end GlobalTheory.ThetaSchurBdd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCdvrExtensionQkPointsRational
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCdvrExtensionQkPointsRational
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)

namespace GlobalTheory.QkRationalExt

open GlobalTheory.ArcPull GlobalTheory.TorusExt GlobalTheory.QkNumberField

theorem exists_ringHom_extend {K L F : Type} [Field K] [Field L] [Field F] [Algebra K L] [Algebra.IsAlgebraic K L]
    [IsAlgClosed F] (M : IntermediateField K L) (f : M →+* F) : ∃ σ : L →+* F, σ.comp M.val.toRingHom = f := by
  letI : Algebra M F := f.toAlgebra
  have : Algebra.IsAlgebraic M L := Algebra.IsAlgebraic.tower_top (K := K) M
  have : Module.IsTorsionFree M F := DivisionSemiring.to_moduleIsTorsionFree
  have : Module.IsTorsionFree M L := DivisionSemiring.to_moduleIsTorsionFree
  let σ : L →ₐ[M] F := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨σ.toRingHom, RingHom.ext fun x => σ.commutes x⟩

section Ext

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

theorem qkExt_g (hB : D.TauBimult) {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Field F']
    [Algebra (FractionRing R) F'] (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F') {k : ℕ} (z : QkPt D F k) :
    (qkExt hB f hf z).g = gtExt D f hf z.g := by
  unfold qkExt qkMk
  rfl

theorem qkExt_y (hB : D.TauBimult) {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Field F']
    [Algebra (FractionRing R) F'] (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F') {k : ℕ} (z : QkPt D F k) :
    (qkExt hB f hf z).y = z.y := ((qkExt_iff hB f hf z _).2 rfl).1

theorem qkExt_qkExt (hB : D.TauBimult) {F F' F'' : Type} [Field F] [Algebra (FractionRing R) F] [Field F']
    [Algebra (FractionRing R) F'] [Field F''] [Algebra (FractionRing R) F''] (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F') (f' : F' →+* F'')
    (hf' : f'.comp (algebraMap (FractionRing R) F') = algebraMap (FractionRing R) F'') (f'' : F →+* F'')
    (hf'' : f''.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F'') (e : f'.comp f = f'')
    {k : ℕ} (z : QkPt D F k) : qkExt hB f' hf' (qkExt hB f hf z) = qkExt hB f'' hf'' z := by
  refine qk_ext ?_ ?_
  · rw [qkExt_y, qkExt_y, qkExt_y]
  · rw [qkExt_g, qkExt_g, qkExt_g]
    exact gtExt_gtExt f hf f' hf' f'' hf'' e z.g

theorem qkExt_pullQk (hD : IsPullDeg φ D D') (hG : GlobalFnsSt) (hB : D.TauBimult) (hB' : D'.TauBimult)
    {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] [Field F']
    [Algebra (FractionRing R) F'] [Algebra (FractionRing R') F'] (hF : Compat φ F) (hF' : Compat φ F') (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')
    (hf' : f.comp (algebraMap (FractionRing R') F) = algebraMap (FractionRing R') F') {k : ℕ} (z : QkPt D F k) :
    QkExt f (pullQk hD hG hF hB hB' z) (pullQk hD hG hF' hB hB' (qkExt hB f hf z)) := by
  have h₁ : QkExt f z (qkExt hB f hf z) := (qkExt_iff hB f hf _ _).2 rfl
  have h₂ : QkExt f (pullQk hD hG hF hB hB' z) (qkExt hB' f hf' (pullQk hD hG hF hB hB' z)) :=
    (qkExt_iff hB' f hf' _ _).2 rfl
  have h₃ : IsPullGtF φ hD F z.g (pullQk hD hG hF hB hB' z).g := ((eq_pullQk_iff hD hG hF hB hB' z _).1 rfl).2
  have h₄ := isPullGtF_ext hD hF' f hf' h₃ h₁ h₂
  have h₅ : (qkExt hB' f hf' (pullQk hD hG hF hB hB' z)).y = hD.xe.symm (qkExt hB f hf z).y := by
    rw [h₂.1, h₁.1, pullQk_y]
  rw [← (eq_pullQk_iff hD hG hF' hB hB' _ _).2 ⟨h₅, h₄⟩]
  exact h₂

end Ext

theorem exists_rational_of_finite (hL : Laws) {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    {φ : R →+* R'} (hφ : Function.Injective φ) {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D')
    (hB : D.TauBimult) (hB' : D'.TauBimult) {L : Type} [Field L] [Algebra (FractionRing R) L]
    [Algebra.IsAlgebraic (FractionRing R) L] [IsAlgClosed L] [CharZero L]
    (M : IntermediateField (FractionRing R) L) (j : M →+* FractionRing R')
    (hj : ∀ r : R, j (algebraMap (FractionRing R) M (algebraMap R _ r)) = algebraMap R' _ (φ r))
    {k : ℕ} (hk : k ≠ 0)
    (H : ∀ q : QkPt D L k, ∃ z : QkPt D M k, qkExt hB M.val.toRingHom (val_comp M) z = q)
    {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing R') F] (q : QkPt D' F k) :
    ∃ p : QkPt D' (FractionRing R') k, QkExt (algebraMap (FractionRing R') F) p q := by
  have hG := hL.globalFns
  letI : Algebra (FractionRing R) (FractionRing R') := (fracMap hφ).toAlgebra
  letI : Algebra (FractionRing R) F := ((algebraMap (FractionRing R') F).comp (fracMap hφ)).toAlgebra
  have hK : Compat φ (FractionRing R') := fracMap_algebraMap hφ
  have hF : Compat φ F := fun r => congrArg (algebraMap (FractionRing R') F) (fracMap_algebraMap hφ r)
  obtain ⟨q₀, rfl⟩ := pullQk_surjective hD hG hF hB hB' q
  have hjf : j.comp (algebraMap (FractionRing R) M) = algebraMap (FractionRing R) (FractionRing R') :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r =>
      (hj r).trans (fracMap_algebraMap hφ r).symm)
  obtain ⟨σ, e⟩ := exists_ringHom_extend M ((algebraMap (FractionRing R') F).comp j)
  have hh : (algebraMap (FractionRing R') F).comp (algebraMap (FractionRing R) (FractionRing R')) =
      algebraMap (FractionRing R) F := rfl
  have hc : ((algebraMap (FractionRing R') F).comp j).comp
      (algebraMap (FractionRing R) M) = algebraMap (FractionRing R) F := by
    rw [RingHom.comp_assoc, hjf, hh]
  have hσ : σ.comp (algebraMap (FractionRing R) L) = algebraMap (FractionRing R) F := by
    rw [← val_comp M, ← RingHom.comp_assoc, e, hc]
  obtain ⟨x, rfl⟩ := GlobalTheory.ArcExt.exists_qkExt σ hσ hB hL (Nat.cast_ne_zero.2 hk) q₀
  obtain ⟨z, rfl⟩ := H x
  refine ⟨pullQk hD hG hK hB hB' (qkExt hB j hjf z), ?_⟩
  rw [qkExt_qkExt hB _ (val_comp M) σ hσ _ hc e z, ← qkExt_qkExt hB j hjf _ hh _ hc rfl z]
  exact qkExt_pullQk hD hG hB hB' hK hF _ hh (RingHom.comp_id _) _

theorem exists_cdvr_ext_rational : ∀ (T : Formalism.L2.Pj.CDVR) (D : DegPre T.V), D.TauBimult → ∀ N : ℕ, 0 < N → ∀ ϖ : T.V, Irreducible ϖ → ∃ (T' : Formalism.L2.Pj.CDVR) (g : T.V →+* T'.V) (ϖ' : T'.V) (e : ℕ), Function.Injective g ∧ g.Finite ∧ Irreducible ϖ' ∧ N ∣ e ∧ Associated (g ϖ) (ϖ' ^ e) ∧ ∀ (D' : DegPre T'.V) (_ : IsPullDeg g D D'), D'.TauBimult → ∀ k : ℕ, k ∣ N → ∀ q : QkPt D' (AlgebraicClosure (FractionRing T'.V)) k, ∃ p : QkPt D' (FractionRing T'.V) k, QkExt (algebraMap (FractionRing T'.V) (AlgebraicClosure (FractionRing T'.V))) p q := by
  intro T D hB N hN ϖ hϖ
  have hL : Laws := GlobalTheory.allSixLaws.1
  have : CharZero (FractionRing T.V) := charZero_of_injective_algebraMap (IsFractionRing.injective T.V _)
  obtain ⟨M, hM, H⟩ := exists_finite_qk (D := D) (L := AlgebraicClosure (FractionRing T.V)) hL hB
    (Nat.cast_ne_zero.2 hN.ne')
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))
    (algebraMap T.V _ ϖ)) hN
  have h₁ : FiniteDimensional (FractionRing T.V) (IntermediateField.adjoin (FractionRing T.V) {π}) :=
    IntermediateField.finiteDimensional_adjoin fun y _ => Algebra.IsIntegral.isIntegral y
  let M₂ := M ⊔ IntermediateField.adjoin (FractionRing T.V) {π}
  have h₂ : FiniteDimensional (FractionRing T.V) M₂ := inferInstance
  let π₂ : M₂ := ⟨π, (le_sup_right : _ ≤ M₂) (IntermediateField.mem_adjoin_simple_self _ π)⟩
  have hπ₂ : π₂ ^ N = algebraMap (FractionRing T.V) M₂ (algebraMap T.V _ ϖ) := Subtype.ext hπ
  obtain ⟨W, _, _, _, _, _, _, _, hc, hfin, hinj, -, hint, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension T.V (FractionRing T.V) M₂
  have : CharZero W := charZero_of_injective_algebraMap hinj
  obtain ⟨w, hw⟩ := hint π₂ ⟨Polynomial.X ^ N - Polynomial.C ϖ, Polynomial.monic_X_pow_sub_C _ hN.ne', by
    simp [hπ₂]⟩
  have hwN : w ^ N = algebraMap T.V W ϖ := IsFractionRing.injective W M₂ (by
    rw [map_pow, hw, hπ₂]; exact (RingHom.congr_fun hc ϖ).symm)
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hwN
    exact hϖ.ne_zero (hinj (hwN.symm.trans (map_zero _).symm))
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hw0 hϖ'
  let ε := FractionRing.algEquiv W M₂
  let j : M →+* FractionRing W := ε.symm.toRingEquiv.toRingHom.comp
    (IntermediateField.inclusion (le_sup_left : M ≤ M₂)).toRingHom
  have hj : ∀ r : T.V, j (algebraMap (FractionRing T.V) M (algebraMap T.V _ r)) =
      algebraMap W _ (algebraMap T.V W r) := fun r => ε.injective (by
    refine (ε.apply_symm_apply _).trans (Eq.trans ?_ (ε.commutes _).symm)
    exact (RingHom.congr_fun hc r).symm)
  refine ⟨Formalism.L2.Pj.CDVR.mk W, algebraMap T.V W, ϖ', m * N, hinj, RingHom.finite_algebraMap.2 hfin, hϖ',
    Dvd.intro_left m rfl, ?_, ?_⟩
  · rw [← hwN, pow_mul]
    exact hm.pow_pow
  · intro D' hD hB' k hk q
    have hk0 : k ≠ 0 := by rintro rfl; exact hN.ne' (Nat.eq_zero_of_zero_dvd hk)
    exact exists_rational_of_finite hL hinj hD hB hB' M j hj hk0 (H k hk) q

end GlobalTheory.QkRationalExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCdvrExtensionQkPointsRationalStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cdvr_extension_qkPoints_rational : ∀ (T : Formalism.L2.Pj.CDVR) (D : DegPre T.V), D.TauBimult → ∀ N : ℕ, 0 < N → ∀ ϖ : T.V, Irreducible ϖ → ∃ (T' : Formalism.L2.Pj.CDVR) (g : T.V →+* T'.V) (ϖ' : T'.V) (e : ℕ), Function.Injective g ∧ g.Finite ∧ Irreducible ϖ' ∧ N ∣ e ∧ Associated (g ϖ) (ϖ' ^ e) ∧ ∀ (D' : DegPre T'.V) (_ : IsPullDeg g D D'), D'.TauBimult → ∀ k : ℕ, k ∣ N → ∀ q : QkPt D' (AlgebraicClosure (FractionRing T'.V)) k, ∃ p : QkPt D' (FractionRing T'.V) k, QkExt (algebraMap (FractionRing T'.V) (AlgebraicClosure (FractionRing T'.V))) p q := by
  first | exact @GlobalTheory.QkRationalExt.exists_cdvr_ext_rational | exact GlobalTheory.QkRationalExt.exists_cdvr_ext_rational | (intros; apply GlobalTheory.QkRationalExt.exists_cdvr_ext_rational <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsClassificationSupercuspidalSupportMultiStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlandsClassification_supercuspidalSupport_multisegment : ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (𝔪 : Multiset (Segment k)) (x : IrrGL (k := k)), IsL 𝔪 x.rep → HasSupport x.rep (msupp 𝔪) := by
  first | exact @GlobalTheory.LocGL.hasSupport_msupp_of_isL | exact GlobalTheory.LocGL.hasSupport_msupp_of_isL | (intros; apply GlobalTheory.LocGL.hasSupport_msupp_of_isL <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharZeroAdicCompletion
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.LocDict

namespace GlobalTheory.LTRecip

instance charZero_adicCompletion (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective

instance isSepClosure_kbar (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    IsSepClosure (w.adicCompletion E) (Kbar w) := inferInstance

end GlobalTheory.LTRecip

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimeSplitCm
open NumberField IsDedekindDomain Matrix Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.UG Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.BCWords GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitRealPrime

theorem exists_prime_isSplitAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ p : ℕ, p.Prime ∧ ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → IsSplitAt w := by
  intro E _ _ _
  obtain ⟨p, hp, -, hs⟩ := GlobalTheory.LargeSplitPrime.exists_splitsCompl E 0
  refine ⟨p, hp, fun w hw => ?_⟩
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hv : (p : 𝓞 (maximalRealSubfield E)) ∈ (w.under (𝓞 (maximalRealSubfield E))).asIdeal := by
    show algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w.asIdeal
    rwa [map_natCast]
  obtain ⟨a, b, hab, ha, hb⟩ :=
    GlobalTheory.SplitPlace.isSplit_of_norm h2 hp (fun u hu => hs u.asIdeal u.isMaximal hu) _ hv
  by_cases h : a = w
  · exact ⟨b, fun e => hab (h.trans e.symm), HeightOneSpectrum.ext hb⟩
  · exact ⟨a, h, HeightOneSpectrum.ext ha⟩

end GlobalTheory.SplitRealPrime
end
