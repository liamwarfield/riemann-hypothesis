module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCentralizerComm
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleFrobeniusTwistOrderFixedPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitConjOfMinpolyEq
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.AdelicScalarSectionLift
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsToFinitelyGeneratedSubring

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleTrivialOverRealsOfGramCongruent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleTrivialOverRealsOfGramCongruent
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKMid

theorem trivR_of_gram_psi_inv_congr : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ),
    (∀ v : InfinitePlace G.F, ∃ W : GL (Fin G.n) ℂ, G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C) =
      (W : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * G.gram v * (W : Matrix (Fin G.n) (Fin G.n) ℂ)) →
    ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1 := by
  intro p _ G β hW
  choose W hW using hW
  obtain ⟨hinj, hsurj⟩ := GlobalTheory.T.bijective_realTensor_to_prod_matrixAlgebras_infPlaces p G
  obtain ⟨z, hz⟩ := hsurj (fun v => (W v : Matrix (Fin G.n) (Fin G.n) ℂ))
  obtain ⟨z', hz'⟩ := hsurj (fun v => (((W v)⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ))
  have hz1 : ∀ v, G.psiR v z = (W v : Matrix (Fin G.n) (Fin G.n) ℂ) := fun v => congrFun hz v
  have hz2 : ∀ v, G.psiR v z' = (((W v)⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) :=
    fun v => congrFun hz' v
  have e1 : z * z' = 1 := hinj (funext fun v => show G.psiR v (z * z') = G.psiR v 1 by
    rw [map_mul, map_one, hz1, hz2, Units.mul_inv])
  have e2 : z' * z = 1 := hinj (funext fun v => show G.psiR v (z' * z) = G.psiR v 1 by
    rw [map_mul, map_one, hz1, hz2, Units.inv_mul])
  refine ⟨⟨z, z', e1, e2⟩, ?_⟩
  unfold Triv
  rw [Units.val_one, map_one]
  apply hinj
  funext v
  show G.psiR v (z * inC G ℝ (β : G.C) * (starT G.star ℝ z).unop) = G.psiR v 1
  have hb : G.psiR v (inC G ℝ (β : G.C)) = G.psi v (β : G.C) := by
    change G.psiR v ((1 : ℝ) ⊗ₜ (β : G.C)) = _
    rw [psiR_tmul, one_smul]
  rw [map_mul, map_mul, psiR_starT, hb, hz1, map_one]
  set Wm : Matrix (Fin G.n) (Fin G.n) ℂ := (W v : Matrix (Fin G.n) (Fin G.n) ℂ)
  have hg : IsUnit (G.gram v).det := isUnit_iff_ne_zero.2 (G.gram_det v)
  have hM : (G.gram v)⁻¹ * Wmᴴ * G.gram v * Wm = G.psi v ((β⁻¹ : G.Cˣ) : G.C) := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Wmᴴ, ← hW v, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hg, Matrix.one_mul]
  have hBA : ((G.gram v)⁻¹ * Wmᴴ * G.gram v) * (Wm * G.psi v (β : G.C)) = 1 := by
    rw [← Matrix.mul_assoc, hM, ← map_mul, Units.inv_mul, map_one]
  have hAB := mul_eq_one_comm.1 hBA
  simpa [Matrix.mul_assoc] using hAB

end GlobalTheory.LKMid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleTrivialOverRealsOfGramCongruentStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianTriple_trivial_over_reals_of_gram_congruent : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), (∀ v : InfinitePlace G.F, ∃ W : GL (Fin G.n) ℂ, G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C) = (W : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * G.gram v * (W : Matrix (Fin G.n) (Fin G.n) ℂ)) → ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1 := by
  first | (exact @GlobalTheory.LKMid.trivR_of_gram_psi_inv_congr) | (exact GlobalTheory.LKMid.trivR_of_gram_psi_inv_congr) | (intros; apply GlobalTheory.LKMid.trivR_of_gram_psi_inv_congr  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitsLocallyCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitsLocallyCompact
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.OrbFinAf

theorem locCpt_Qv {p : ℕ} [Fact p.Prime] (v : AwayP p) : LocallyCompactSpace (Qv v) := by
  have ho : IsOpen (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ)) :=
    (Valued.isClopen_integer (v.1.adicCompletion ℚ)).isOpen
  exact (GlobalTheory.LKTrip.LevelExists.isCompact_intCompl v.1).locallyCompactSpace_of_mem_nhds_of_addGroup
    (ho.mem_nhds (zero_mem _))

theorem secCount_Qv {p : ℕ} [Fact p.Prime] (v : AwayP p) : SecondCountableTopology (Qv v) := by
  haveI := locCpt_Qv v
  letI : NontriviallyNormedField (Qv v) := Valued.toNontriviallyNormedField _ _
  haveI : ProperSpace (Qv v) := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  exact secondCountable_of_proper

theorem units_topA (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    [LocallyCompactSpace K] [SecondCountableTopology K]
    (A : Type) [Ring A] [Algebra K A] [Module.Finite K A] [TopologicalSpace A] [IsModuleTopology K A] :
    T2Space Aˣ ∧ LocallyCompactSpace Aˣ ∧ SigmaCompactSpace Aˣ := by
  let b := Module.finBasis K A
  let e : A ≃ₗ[K] (Fin (Module.finrank K A) → K) := b.equivFun
  haveI : ContinuousAdd A := IsModuleTopology.toContinuousAdd K A
  have hc1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hc2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : A ≃ₜ (Fin (Module.finrank K A) → K) := ⟨e.toEquiv, hc1, hc2⟩
  haveI : T2Space A := h.isEmbedding.t2Space
  haveI : LocallyCompactSpace A := h.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology A := h.isEmbedding.secondCountableTopology
  haveI : IsTopologicalRing A := IsModuleTopology.isTopologicalRing K A
  haveI : LocallyCompactSpace Aᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology Aᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : LocallyCompactSpace Aˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology Aˣ := Units.isClosedEmbedding_embedProduct.isEmbedding.secondCountableTopology
  haveI : T2Space Aˣ := Units.isEmbedding_embedProduct.t2Space
  exact ⟨inferInstance, inferInstance, sigmaCompactSpace_of_locallyCompact_secondCountable⟩

theorem topA : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C); T2Space (Qv v ⊗[ℚ] G.C)ˣ ∧ LocallyCompactSpace (Qv v ⊗[ℚ] G.C)ˣ ∧ SigmaCompactSpace (Qv v ⊗[ℚ] G.C)ˣ := by
  intro p _ G v
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI := locCpt_Qv v
  haveI := secCount_Qv v
  exact units_topA (Qv v) (Qv v ⊗[ℚ] G.C)

end GlobalTheory.OrbFinAf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitsLocallyCompactStatement
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_units_locally_compact : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C); T2Space (Qv v ⊗[ℚ] G.C)ˣ ∧ LocallyCompactSpace (Qv v ⊗[ℚ] G.C)ˣ ∧ SigmaCompactSpace (Qv v ⊗[ℚ] G.C)ˣ := by
  first | (exact @GlobalTheory.OrbFinAf.topA) | (exact GlobalTheory.OrbFinAf.topA) | (intros; apply GlobalTheory.OrbFinAf.topA  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneHermitianIdealCoprime
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors Matrix TensorProduct

namespace GlobalTheory.AdaptedPlaneIdeal

end GlobalTheory.AdaptedPlaneIdeal

namespace GlobalTheory.AdaptedPlaneIdeal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_ne_zero_of_hasSig {n r s : ℕ} {J : Matrix (Fin n) (Fin n) E} (φ : E →+* ℂ)
    (h : HasSig (J.map φ) r s) : J.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  intro h0
  have hM : (J.map φ).det = 0 := by
    have := RingHom.map_det φ J
    rw [h0, map_zero] at this
    exact this.symm
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hM
  have hD : IsUnit (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fromBlocks_zero₂₁]; simp [Matrix.det_neg]
  have h1 := Matrix.rank_of_isUnit _ hD
  rw [← hA] at h1
  have h2 : (Aᵀ * J.map φ * A.map star).rank ≤ (J.map φ).rank :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  have h3 := LinearMap.finrank_range_add_finrank_ker (J.map φ).mulVecLin
  have h4 : 0 < Module.finrank ℂ (LinearMap.ker (J.map φ).mulVecLin) :=
    Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, hv⟩, fun e => hv0 (congrArg Subtype.val e)⟩
  rw [Module.finrank_fin_fun] at h3
  have h5 : (J.map φ).rank = Module.finrank ℂ (LinearMap.range (J.map φ).mulVecLin) := rfl
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h1
  omega

section Split

variable {v : HeightOneSpectrum (𝓞 F)} {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)}

end Split

end GlobalTheory.AdaptedPlaneIdeal

namespace GlobalTheory.AdaptedPlaneIdeal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Split

variable {v : HeightOneSpectrum (𝓞 F)} {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)}

end Split

end GlobalTheory.AdaptedPlaneIdeal

namespace GlobalTheory.AdaptedPlaneIdeal

end GlobalTheory.AdaptedPlaneIdeal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointIntertwines
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SecLift

section Lin

variable {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]


end Lin

section Model

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

end Model

section Act

open Formalism.IndefR.Lev

theorem actL_apply {D : D7} {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} {g0 : G0 L.Pg L.r}
    (hk : ∃ κ, IsLevelLift V β L g0 κ) (Φ : GA D V → ℂ) (h : GA D V) :
    Links.actL V β L g0 Φ h = (levChi V β (flagL L) hk.choose)⁻¹ * Φ (h * hk.choose) := by
  show actG0 V β L g0 Φ h = _
  rw [actG0, dite_eq_left hk]

theorem span_of_pres {G Γ W K H : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K]
    [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G}
    {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ ρ J χ) [AddCommGroup H] [Module ℂ H] (e : H →ₗ[ℂ] (G → W))
    (hinj : Function.Injective e) (hr : LinearMap.range e = Bridge.AdForms ι ρ J χ) (j : S.Forms → H)
    (hj : ∀ x, e (j x) = P.extL x) (N : Submodule ℂ H) (hN : ∀ x, j x ∈ N) (y : H) : y ∈ N := by
  have h1 : e y ∈ N.map e := by
    have h2 : e y ∈ Submodule.span ℂ (Set.range P.extL) := by
      rw [GlobalTheory.PresBasic.ext_span]
      exact hr.le (LinearMap.mem_range_self _ y)
    refine Submodule.span_le.2 ?_ h2
    rintro _ ⟨x₀, rfl⟩
    exact ⟨j x₀, hN x₀, hj x₀⟩
  obtain ⟨y', hy', h⟩ := h1
  exact hinj h ▸ hy'

theorem coord_translate {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) {κ : GA D V} (hκ : κ ∈ GfC V) (a : ℂ)
    {f f' : Bridge.Gf V → c.W} (hf : ∀ h, f' h = a • f (h * (finHom V).rangeRestrict κ)) (ℓ : c.W →ₗ[ℂ] ℂ) (h : GA D V) :
    ℓ (c.ext f' h) = a * ℓ (c.ext f (h * κ)) := by
  have h1 : c.ext f' h = c.ρ h⁻¹ (f' ((finHom V).rangeRestrict h)) := rfl
  have h2 : c.ext f (h * κ) = c.ρ (h * κ)⁻¹ (f ((finHom V).rangeRestrict (h * κ))) := rfl
  have h3 : c.ρ (h * κ)⁻¹ = c.ρ h⁻¹ :=
    (congrArg c.ρ (mul_inv_rev h κ)).trans ((c.ρ.map_mul κ⁻¹ h⁻¹).trans
      ((congrArg (· * c.ρ h⁻¹) (hc.1 κ⁻¹ ((GfC V).inv_mem hκ))).trans (one_mul _)))
  have h4 := MonoidHom.map_mul (finHom V).rangeRestrict h κ
  have h5 : f' ((finHom V).rangeRestrict h) = a • f ((finHom V).rangeRestrict (h * κ)) :=
    (hf _).trans (congrArg (fun q => a • f q) h4.symm)
  rw [h1, h2, h3, h5]
  exact (congrArg ℓ ((c.ρ h⁻¹).map_smul a _)).trans (ℓ.map_smul a _)

end Act

end GlobalTheory.SecLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralTensorPointsSharpStableRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralTensorPointsSharpStableRing
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

namespace GlobalTheory.OrbFinAf

theorem ratCast_mem_intV_eventually (p : ℕ) [Fact p.Prime] (q : ℚ) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      algebraMap ℚ (Qv v) q ∈ v.1.adicCompletionIntegers ℚ := by
  have h : ∀ᶠ w in (Filter.cofinite : Filter (HeightOneSpectrum ℤ)),
      algebraMap ℚ (w.adicCompletion ℚ) q ∈ w.adicCompletionIntegers ℚ :=
    (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q).2.mono fun _ hv => hv
  exact (Subtype.val_injective.tendsto_cofinite).eventually h

variable {p : ℕ} [Fact p.Prime]

theorem basV_repr_tmul (G : HTGroup p) (v : AwayP p) (r : Qv v) (c : G.C) (k : Fin (Module.finrank ℚ G.C)) :
    (basV G v).repr (r ⊗ₜ c) k = r * algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr c k) := by
  simp [basV, Algebra.TensorProduct.basis_repr_tmul]

theorem eq_sum_tmul (G : HTGroup p) (v : AwayP p) (y : Qv v ⊗[ℚ] G.C) :
    y = ∑ i, (basV G v).repr y i ⊗ₜ (Module.finBasis ℚ G.C i) := by
  conv_lhs => rw [← (basV G v).sum_repr y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [basV, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem isIntV_of_eq_sum (G : HTGroup p) (v : AwayP p) {ι : Type*} (s : Finset ι) (r : ι → Qv v) (c : ι → G.C)
    (hr : ∀ i ∈ s, r i ∈ v.1.adicCompletionIntegers ℚ)
    (hc : ∀ i ∈ s, ∀ k, algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr (c i) k) ∈ v.1.adicCompletionIntegers ℚ) :
    IsIntV G v (∑ i ∈ s, r i ⊗ₜ c i) := by
  intro k
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  exact sum_mem fun i hi => by rw [basV_repr_tmul]; exact mul_mem (hr i hi) (hc i hi k)

theorem intV_order_eventually : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), IsIntV G v 1 ∧ (∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) ∧ (∀ y : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v (starT G.star (Qv v) y).unop) := by
  intro p _ G
  set b := Module.finBasis ℚ G.C
  have H := ((Filter.eventually_all.2 fun k => ratCast_mem_intV_eventually p (b.repr 1 k)).and
    (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => Filter.eventually_all.2 fun k =>
      ratCast_mem_intV_eventually p (b.repr (b i * b j) k))).and
    (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun k =>
      ratCast_mem_intV_eventually p (b.repr (G.star (b i)).unop k))
  refine H.mono fun v ⟨⟨h1, hm⟩, hs⟩ => ⟨?_, ?_, ?_⟩
  · intro k
    rw [Algebra.TensorProduct.one_def, basV_repr_tmul, one_mul]
    exact h1 k
  · intro y z hy hz
    have e : y * z = ∑ ij : Fin (Module.finrank ℚ G.C) × Fin (Module.finrank ℚ G.C),
        ((basV G v).repr y ij.1 * (basV G v).repr z ij.2) ⊗ₜ (b ij.1 * b ij.2) := by
      conv_lhs => rw [eq_sum_tmul G v y, eq_sum_tmul G v z]
      rw [Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
      simp only [Algebra.TensorProduct.tmul_mul_tmul]
      rfl
    rw [e]
    exact isIntV_of_eq_sum G v _ _ _ (fun ij _ => mul_mem (hy ij.1) (hz ij.2)) (fun ij _ k => hm ij.1 ij.2 k)
  · intro y hy
    have e : (starT G.star (Qv v) y).unop = ∑ i, (basV G v).repr y i ⊗ₜ (G.star (b i)).unop := by
      conv_lhs => rw [eq_sum_tmul G v y]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, ← MulOpposite.opAddEquiv_symm_apply, map_sum]
      exact Finset.sum_congr rfl fun i _ => starT_tmul G.star (Qv v) _ _
    rw [e]
    exact isIntV_of_eq_sum G v _ _ _ (fun i _ => hy i) (fun i _ k => hs i k)

end GlobalTheory.OrbFinAf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralTensorPointsSharpStableRingStatement
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_integral_tensor_points_sharp_stable_ring : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), IsIntV G v 1 ∧ (∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) ∧ (∀ y : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v (starT G.star (Qv v) y).unop) := by
  first | (exact @GlobalTheory.OrbFinAf.intV_order_eventually) | (exact GlobalTheory.OrbFinAf.intV_order_eventually) | (intros; apply GlobalTheory.OrbFinAf.intV_order_eventually  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutantOfMaximalDegreeElement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.CentIrr

noncomputable def rootHom (F C : Type) [Field F] [Ring C] [Algebra F C] (y : C) :
    AdjoinRoot (minpoly F y) →ₐ[F] C :=
  Ideal.Quotient.liftₐ (Ideal.span {minpoly F y}) (Polynomial.aeval y) (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
    rw [map_mul, minpoly.aeval, zero_mul])

theorem rootHom_root (F C : Type) [Field F] [Ring C] [Algebra F C] (y : C) :
    rootHom F C y (AdjoinRoot.root (minpoly F y)) = y := by
  exact Polynomial.aeval_X y

theorem commute_iff_mem_adjoin (F C : Type) [Field F] [Ring C] [Algebra F C] [FiniteDimensional F C]
    [Algebra.IsCentral F C] [IsSimpleRing C] (n : ℕ) (hn : 0 < n) (hC : Module.finrank F C = n ^ 2)
    (y : C) (hirr : Irreducible (minpoly F y)) (hdeg : (minpoly F y).natDegree = n) (z : C) :
    Commute z y ↔ z ∈ Algebra.adjoin F ({y} : Set C) := by
  set B := Algebra.adjoin F ({y} : Set C) with hBdef
  have hcommB : ∀ {u v : C}, u ∈ B → v ∈ B → u * v = v * u := by
    intro u v hu hv
    have := Algebra.adjoin_le_centralizer_centralizer F ({y} : Set C) hu
    rw [Subalgebra.mem_centralizer_iff] at this
    apply (this v _).symm
    refine Algebra.adjoin_le ?_ hv
    rw [Set.singleton_subset_iff, SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
  haveI : Fact (Irreducible (minpoly F y)) := ⟨hirr⟩
  set j : AdjoinRoot (minpoly F y) →ₐ[F] C := rootHom F C y
  have hj : Function.Injective j := j.toRingHom.injective
  have hrange : j.range = B := by
    rw [← Algebra.map_top, ← AdjoinRoot.adjoinRoot_eq_top, AlgHom.map_adjoin, Set.image_singleton]
    rw [rootHom_root]
  have hne : minpoly F y ≠ 0 := hirr.ne_zero
  have hEdim : Module.finrank F (AdjoinRoot (minpoly F y)) = n := by
    rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  let eB : AdjoinRoot (minpoly F y) ≃ₐ[F] B := (AlgEquiv.ofInjective j hj).trans (Subalgebra.equivOfEq _ _ hrange)
  haveI : IsSimpleRing B := IsSimpleRing.of_ringEquiv eB.toRingEquiv inferInstance
  have hBdim : Module.finrank F B = n := by rw [← eB.toLinearEquiv.finrank_eq, hEdim]
  set Z := Subalgebra.centralizer F (B : Set C)
  have hBZ : B ≤ Z := by
    intro a ha
    rw [Subalgebra.mem_centralizer_iff]
    intro b hb
    exact hcommB hb ha
  have h1 := GroundTheory.Brauer.finrank_mul_finrank_centralizer (K := F) (A := C) B
  have hdim : Module.finrank F B = Module.finrank F Z := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < Module.finrank F B by rw [hBdim]; exact hn)
    rw [h1, hC, hBdim, sq]
  have hEq : B = Z := Subalgebra.toSubmodule_injective
    (Submodule.eq_of_le_of_finrank_eq (Subalgebra.toSubmodule.monotone hBZ) hdim)
  constructor
  · intro hz
    have hzZ : z ∈ Z := by
      rw [Subalgebra.mem_centralizer_iff]
      intro b hb
      have := Algebra.adjoin_le_centralizer_centralizer F ({y} : Set C) hb
      rw [Subalgebra.mem_centralizer_iff] at this
      refine (this z ?_).symm
      rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]; exact hz.eq.symm
    rw [hEq]; exact hzZ
  · intro hz
    exact (hcommB hz (Algebra.self_mem_adjoin_singleton F y) : _)

theorem centralizer_unit_eq_field : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (y₀ : G.Cˣ),
    Irreducible (minpoly G.F (y₀ : G.C)) → (minpoly G.F (y₀ : G.C)).natDegree = G.n →
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra G.F E) (j : E →ₐ[G.F] G.C),
      Function.Injective j ∧ ∀ z : G.C, Commute z (y₀ : G.C) ↔ ∃ e, j e = z := by
  intro p _ G y₀ hirr hdeg
  haveI : Fact (Irreducible (minpoly G.F (y₀ : G.C))) := ⟨hirr⟩
  let j : AdjoinRoot (minpoly G.F (y₀ : G.C)) →ₐ[G.F] G.C := rootHom G.F G.C (y₀ : G.C)
  have hne : minpoly G.F (y₀ : G.C) ≠ 0 := hirr.ne_zero
  haveI : FiniteDimensional G.F (AdjoinRoot (minpoly G.F (y₀ : G.C))) :=
    (AdjoinRoot.powerBasis hne).finite
  haveI : FiniteDimensional ℚ (AdjoinRoot (minpoly G.F (y₀ : G.C))) :=
    Module.Finite.trans G.F _
  haveI : CharZero (AdjoinRoot (minpoly G.F (y₀ : G.C))) :=
    charZero_of_injective_algebraMap (algebraMap G.F _).injective
  haveI : NumberField (AdjoinRoot (minpoly G.F (y₀ : G.C))) := ⟨⟩
  have hrange : j.range = Algebra.adjoin G.F ({(y₀ : G.C)} : Set G.C) := by
    rw [← Algebra.map_top, ← AdjoinRoot.adjoinRoot_eq_top, AlgHom.map_adjoin, Set.image_singleton]
    rw [rootHom_root]
  refine ⟨AdjoinRoot (minpoly G.F (y₀ : G.C)), inferInstance, inferInstance, inferInstance, j,
    j.toRingHom.injective, fun z => ?_⟩
  rw [commute_iff_mem_adjoin G.F G.C G.n G.n_pos G.rankC _ hirr hdeg z, ← hrange]
  rfl

end GlobalTheory.CentIrr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactConjCharpolyBoundedDenominatorsAwayP
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyTensorLeftMulConjOneTmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyTensorLeftMulConjOneTmul
open GlobalTheory.LKTrip GlobalTheory.LKMid
open scoped TensorProduct Classical

namespace GlobalTheory

theorem conj_one_tmul_charpoly : ∀ (R : Type) [CommRing R] [Algebra ℚ R] (A : Type) [Ring A] [Algebra ℚ A] [Module.Finite ℚ A] (x : (R ⊗[ℚ] A)ˣ) (y : A), (LevelExists.mulMatAlg R A ((x : R ⊗[ℚ] A) * (1 ⊗ₜ[ℚ] y) * ((x⁻¹ : (R ⊗[ℚ] A)ˣ) : R ⊗[ℚ] A))).charpoly = (LinearMap.mulLeft ℚ y).charpoly.map (algebraMap ℚ R) := by
  intro R _ _ A _ _ _ x y
  set b := Module.finBasis ℚ A
  set u := Units.map (LevelExists.mulMatAlg R A).toMonoidHom x with hu
  have h1 : LevelExists.mulMatAlg R A (x : R ⊗[ℚ] A) = (u : Matrix _ _ R) := rfl
  have h2 : LevelExists.mulMatAlg R A ((x⁻¹ : (R ⊗[ℚ] A)ˣ) : R ⊗[ℚ] A) = ((u⁻¹ : (Matrix _ _ R)ˣ) : Matrix _ _ R) := by
    rw [hu, ← map_inv]; rfl
  have hM : LevelExists.mulMatAlg R A (1 ⊗ₜ[ℚ] y) =
      (LinearMap.toMatrix b b (LinearMap.mulLeft ℚ y)).map (algebraMap ℚ R) := by
    ext i j
    simp [LevelExists.mulMatAlg, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply,
      Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_repr_tmul, b, Algebra.leftMulMatrix_eq_repr_mul]
  rw [map_mul, map_mul, h1, h2, Matrix.coe_units_inv, Matrix.charpoly_units_conj, hM, Matrix.charpoly_map,
    LinearMap.charpoly_toMatrix]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyTensorLeftMulConjOneTmulStatement
open GlobalTheory.LKTrip GlobalTheory.LKMid
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_tensorLeftMul_conj_one_tmul : ∀ (R : Type) [CommRing R] [Algebra ℚ R] (A : Type) [Ring A] [Algebra ℚ A] [Module.Finite ℚ A] (x : (R ⊗[ℚ] A)ˣ) (y : A), (LevelExists.mulMatAlg R A ((x : R ⊗[ℚ] A) * (1 ⊗ₜ[ℚ] y) * ((x⁻¹ : (R ⊗[ℚ] A)ˣ) : R ⊗[ℚ] A))).charpoly = (LinearMap.mulLeft ℚ y).charpoly.map (algebraMap ℚ R) := by
  first | (exact @GlobalTheory.conj_one_tmul_charpoly) | (exact GlobalTheory.conj_one_tmul_charpoly) | (intros; apply GlobalTheory.conj_one_tmul_charpoly <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactConjCharpolyBoundedDenominatorsAwayP
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.AwayPDen

theorem continuous_charpoly_coeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

theorem charpoly_den_bounded : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Ω : Set G.GAf), IsCompact Ω → ∃ D : ℕ, 0 < D ∧ ∀ (g : G.GAf) (y : G.C) (x : (AfP p ⊗[ℚ] G.C)ˣ), g ∈ Ω → (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C) = (x : AfP p ⊗[ℚ] G.C) * inC G (AfP p) y * ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) → ∀ i, ∃ k : ℕ, ∃ a : ℤ, ((D * p ^ k : ℕ) : ℚ) * (LinearMap.mulLeft ℚ y).charpoly.coeff i = a := by
  intro p _ G Ω hΩ
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  set d := Module.finrank ℚ G.C
  let φ : G.GAf → AfP p ⊗[ℚ] G.C := fun g => ((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C)
  have hφ : Continuous φ := Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)
  let F : ℕ → AfP p ⊗[ℚ] G.C → AfP p := fun i a => (LevelExists.mulMatAlg (AfP p) G.C a).charpoly.coeff i
  have hF : ∀ i, Continuous (F i) := fun i =>
    (continuous_charpoly_coeff d i).comp
      (IsModuleTopology.continuous_of_linearMap (LevelExists.mulMatAlg (AfP p) G.C).toLinearMap)
  let S : Set (AfP p) := ⋃ i ∈ Finset.range (d + 1), (F i ∘ φ) '' Ω
  have hS : IsCompact S := (Finset.range (d + 1)).isCompact_biUnion fun i _ => hΩ.image ((hF i).comp hφ)
  obtain ⟨D, hD0, hD⟩ := GlobalTheory.T.exists_common_pos_denominator_of_isCompact_finiteAdeleAway p S hS
  refine ⟨D, hD0, fun g y x hg hx i => ?_⟩
  by_cases hi : i ≤ d
  · have hmem : F i (φ g) ∈ S :=
      Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 (Nat.lt_succ_of_le hi))) ⟨g, hg, rfl⟩
    have hval : F i (φ g) = algebraMap ℚ (AfP p) ((LinearMap.mulLeft ℚ y).charpoly.coeff i) := by
      show (LevelExists.mulMatAlg (AfP p) G.C (φ g)).charpoly.coeff i = _
      rw [show φ g = _ from hx]
      have := GlobalTheory.T.charpoly_tensorLeftMul_conj_one_tmul (AfP p) G.C x y
      simp only [inC] at *
      rw [show ((Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] AfP p ⊗[ℚ] G.C) : G.C →+* AfP p ⊗[ℚ] G.C) y = 1 ⊗ₜ[ℚ] y from rfl]
      rw [this, Polynomial.coeff_map]
    have h2 := hD _ hmem
    rw [hval] at h2
    have h3 : algebraMap ℚ (AfP p) ((D : ℚ) * (LinearMap.mulLeft ℚ y).charpoly.coeff i) ∈ LevelExists.intAfP p := by
      rw [map_mul, map_natCast]; exact h2
    obtain ⟨k, a, ha⟩ := GlobalTheory.T.exists_primePow_mul_eq_int_of_integral_finiteAdeleAway p _ h3
    exact ⟨k, a, by rw [← ha]; push_cast; ring⟩
  · refine ⟨0, 0, ?_⟩
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [LinearMap.charpoly_natDegree]; omega)]
    simp

end GlobalTheory.AwayPDen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactConjCharpolyBoundedDenominatorsAwayPStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_conj_charpoly_bounded_denominators_awayP : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Ω : Set G.GAf), IsCompact Ω → ∃ D : ℕ, 0 < D ∧ ∀ (g : G.GAf) (y : G.C) (x : (AfP p ⊗[ℚ] G.C)ˣ), g ∈ Ω → (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C) = (x : AfP p ⊗[ℚ] G.C) * inC G (AfP p) y * ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) → ∀ i, ∃ k : ℕ, ∃ a : ℤ, ((D * p ^ k : ℕ) : ℚ) * (LinearMap.mulLeft ℚ y).charpoly.coeff i = a := by
  first | (exact @GlobalTheory.AwayPDen.charpoly_den_bounded) | (exact GlobalTheory.AwayPDen.charpoly_den_bounded) | (intros; apply GlobalTheory.AwayPDen.charpoly_den_bounded <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonzeroChartOfEffectiveClass
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonzeroChartOfEffectiveClass
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

noncomputable section

namespace GlobalTheory.EffBound

open GlobalTheory.CechPic

theorem exists_sec_of_eff {X : Scheme.{0}} (N : LB X) (hN : N.IsLB) (h : Eff (cls N hN)) :
    ∃ (σ : LB.Sec N) (j : N.ι), σ.f j ≠ 0 := by
  obtain ⟨N', hN', hc, σ, j, hj⟩ := h
  obtain ⟨w, hw⟩ := (cls_eq_iff hN' hN).1 hc
  let e : LB.Sec N' ≃ₗ[Γ(X, ⊤)] LB.Sec N :=
    (SecOn.topEquiv N').symm ≪≫ₗ SecOn.congr hN' hN w hw ⊤ ≪≫ₗ SecOn.topEquiv N
  have hσ : σ ≠ 0 := fun h0 => hj (by rw [h0]; rfl)
  have he : e σ ≠ 0 := by
    intro h0
    exact hσ (e.injective (h0.trans (map_zero e).symm))
  by_contra hne
  push_neg at hne
  exact he (HighTwist.sec_eq_zero _ (hne (e σ)))

end GlobalTheory.EffBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonzeroChartOfEffectiveClassStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_nonzero_chart_of_effective_class : ∀ {X : Scheme.{0}} (N : LB X) (hN : N.IsLB), GlobalTheory.EffBound.Eff (GlobalTheory.CechPic.cls N hN) → ∃ (σ : LB.Sec N) (j : N.ι), σ.f j ≠ 0 := by
  first | exact @GlobalTheory.EffBound.exists_sec_of_eff | exact GlobalTheory.EffBound.exists_sec_of_eff | (intros; apply GlobalTheory.EffBound.exists_sec_of_eff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeKeepsAndCommutes
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeOffLevel

variable {D : D7}

theorem sep_of_offS {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {Q PP : HeightOneSpectrum (𝓞 D.host.E)}
    (hS : OffS D S Q) (hP : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ S) : PP ≠ Q ∧ ¬ Lev.IsConjPl PP Q := by
  obtain ⟨x, hx, hQ⟩ := hS _ hP
  have hx' : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ PP.asIdeal := hx
  refine ⟨fun h => hQ (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) rfl (h ▸ hx'), fun h => ?_⟩
  obtain ⟨c, hc, e⟩ := h _ hx'
  exact hQ c (e.trans ((D.sp.cm.fixed _).2 ⟨x, rfl⟩)) hc

variable {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem levChi_mul : ∀ k ∈ Lev.levG V β L, ∀ k' ∈ Lev.levG V β L,
    Lev.levChi V β L (k * k') = Lev.levChi V β L k * Lev.levChi V β L k' := by
  intro k hk k' hk'
  unfold Lev.levChi
  rw [MonoidHom.map_mul, ← Units.val_mul]
  exact congrArg Units.val ((levChar D.sp.cm V.gram β L).map_mul ⟨_, hk.2⟩ ⟨_, hk'.2⟩)

variable {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
  {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {Q : HeightOneSpectrum (𝓞 D.host.E)} {d : List ℤ} {Rp : Finset (GA D V)}

theorem hasType_heckeLin (hB : Lev.IsBaseFrame V β Λ N) (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal)
    (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ Q ∧ ¬ Lev.IsConjPl PP Q)
    (h : Hecke₂ V (Lev.levG V β L : Set (GA D V)) (Lev.levChi V β L) S Q d Rp) {Φ : GA D V → ℂ}
    (hΦ : Lev.HasType V β L Φ) : Lev.HasType V β L (heckeLin V Rp Φ) :=
  GlobalTheory.SphericalOps.level_heckeLin levChi_mul
    (fun e f _ hi => ((GlobalTheory.LevSplit.lev_split V β Λ N L hB).2 Q e f hi hN hP).2.2) h hΦ

end GlobalTheory.HeckeOffLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharsOfTameLpDim
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TameInertiaChars

theorem exists_basis_eigen {n : ℕ} {Γ : Type} (f : Γ → Module.End ℂ (Fin n → ℂ))
    (hs : ∀ g, (f g).IsSemisimple) (hc : ∀ g k, Commute (f g) (f k)) :
    ∃ B : Module.Basis (Fin n) ℂ (Fin n → ℂ), ∀ j g, ∃ c : ℂ, f g (B j) = c • B j := by
  have h1 := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
    (fun g k _ => hc g k) fun g => Module.End.iSup_maxGenEigenspace_eq_top _
  simp only [fun g => (hs g).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at h1
  let T : Set (Fin n → ℂ) := {v | ∀ g, ∃ c : ℂ, f g v = c • v}
  have h2 : ⊤ ≤ Submodule.span ℂ T := by
    rw [← h1]
    exact iSup_le fun χ v hv => Submodule.subset_span fun g =>
      ⟨χ g, Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hv g)⟩
  let B := Module.Basis.ofSpan h2
  have h3 := Module.Basis.ofSpan_subset h2
  refine ⟨B.reindex (B.indexEquiv (Pi.basisFun ℂ (Fin n))), fun j => ?_⟩
  rw [Module.Basis.reindex_apply]
  exact h3 ⟨_, rfl⟩

theorem charpoly_of_basis {n : ℕ} (f : Module.End ℂ (Fin n → ℂ)) (B : Module.Basis (Fin n) ℂ (Fin n → ℂ))
    (c : Fin n → ℂ) (hB : ∀ j, f (B j) = c j • B j) : f.charpoly = ∏ j, (X - C (c j)) := by
  rw [← LinearMap.charpoly_toMatrix f B, ← Matrix.charpoly_diagonal]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply, hB, map_smul, B.repr_self, Matrix.diagonal_apply]
  by_cases e : i = j
  · subst e; simp
  · simp [Finsupp.single_apply, Ne.symm e, e]

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

end GlobalTheory.TameInertiaChars

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkNormSqEqSimilitudeFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkNormSqEqSimilitudeFactor
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem Pair.mark_norm_sq : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), P.Mark μ →
    ‖μ‖ ^ 2 = ((P.c : ℚ) : ℝ) := by
  intro p _ G P μ hμ
  obtain ⟨v, _, x, hx, hpos⟩ := hμ
  obtain ⟨_, _, hlaw⟩ := GlobalTheory.T.similitudePair_hermitianForm_invertible_similitude p G P v
  set H := G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) with hH
  set A := G.psi v (P.γ : G.C) with hA
  set q : ℂ := star x ⬝ᵥ (H *ᵥ x) with hq
  have hq0 : q ≠ 0 := by
    intro h0; rw [h0] at hpos; simp at hpos
  have key : star x ⬝ᵥ ((Aᴴ * H * A) *ᵥ x) = (star μ * μ) * q := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, hx, dotProduct_mulVec, ← star_mulVec, hx, mulVec_smul, star_smul,
      smul_dotProduct, dotProduct_smul, hq]
    simp only [smul_eq_mul]; ring
  rw [hlaw, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at key
  have hc : star μ * μ = ((P.c : ℚ) : ℂ) := by
    have := mul_right_cancel₀ hq0 key.symm
    exact this
  have h2 : ((‖μ‖ ^ 2 : ℝ) : ℂ) = ((((P.c : ℚ) : ℝ)) : ℂ) := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    push_cast
    exact hc
  exact_mod_cast h2

end GlobalTheory.LKMid
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkNormSqEqSimilitudeFactorStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mark_norm_sq_eq_similitudeFactor : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), P.Mark μ → ‖μ‖ ^ 2 = ((P.c : ℚ) : ℝ) := by
  first | (exact @GlobalTheory.LKMid.Pair.mark_norm_sq) | (exact GlobalTheory.LKMid.Pair.mark_norm_sq) | (intros; apply GlobalTheory.LKMid.Pair.mark_norm_sq  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotMkEqIffPositiveScalarFormIsomorphic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotMkEqIffPositiveScalarFormIsomorphic
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx.Form

theorem rel_equivalence {p : ℕ} [Fact p.Prime] (G : HTGroup p) : Equivalence (Form.Rel (G := G)) := by
  have sh_mul : ∀ a b : G.C, sh G (a * b) = sh G b * sh G a := by
    intro a b; simp only [sh, map_mul, MulOpposite.unop_mul]
  have sh_one : sh G (1 : G.C) = 1 := by simp only [sh, map_one, MulOpposite.unop_one]
  refine ⟨fun P => ?_, fun {P Q} h => ?_, fun {P Q R} h h' => ?_⟩
  · exact ⟨1, 1, one_pos, by simp [sh_one]⟩
  · obtain ⟨y, s, hs, hβ⟩ := h
    refine ⟨y⁻¹, s⁻¹, inv_pos.mpr hs, ?_⟩
    have e : sh G (y : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
      rw [← sh_mul, Units.inv_mul, sh_one]
    rw [hβ]
    simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, e, mul_one,
      inv_mul_cancel₀ hs.ne', mul_inv_cancel₀ hs.ne', one_smul, Units.inv_mul_cancel_left]
  · obtain ⟨y, s, hs, hβ⟩ := h
    obtain ⟨y', s', hs', hβ'⟩ := h'
    refine ⟨y' * y, s' * s, mul_pos hs' hs, ?_⟩
    rw [hβ', hβ, Units.val_mul, sh_mul]
    simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, mul_comm s]

theorem mk_eq_iff_rel : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Form G),
    Quot.mk Form.Rel P = Quot.mk Form.Rel Q ↔ Form.Rel P Q := by
  intro p _ G P Q
  rw [← (rel_equivalence G).eqvGen_iff]
  exact ⟨Quot.eqvGen_exact, Quot.eqvGen_sound⟩

end GlobalTheory.LKCx.Form
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotMkEqIffPositiveScalarFormIsomorphicStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quot_mk_eq_iff_positiveScalarFormIsomorphic : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Form G), Quot.mk Form.Rel P = Quot.mk Form.Rel Q ↔ Form.Rel P Q := by
  first | (exact @GlobalTheory.LKCx.Form.mk_eq_iff_rel) | (exact GlobalTheory.LKCx.Form.mk_eq_iff_rel) | (intros; apply GlobalTheory.LKCx.Form.mk_eq_iff_rel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMonicBoundedPolynomials
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinOpenSubBaseChange
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory


open Matrix NumberField in
open scoped TensorProduct Classical in
theorem _root_.GlobalTheory.finite_monic_coeff_bdd_mul_isIntegral (K : Type) [Field K] [NumberField K]
    (d D : ℕ) (B : ℝ) (hD : 0 < D) :
    {P : Polynomial K | P.Monic ∧ P.natDegree ≤ d ∧ ∀ k, IsIntegral ℤ ((D : K) * P.coeff k) ∧
      ∀ φ : K →+* ℂ, ‖φ (P.coeff k)‖ ≤ B}.Finite := by
  have hT : {c : K | IsIntegral ℤ ((D : K) * c) ∧ ∀ φ : K →+* ℂ, ‖φ c‖ ≤ B}.Finite := by
    have h := NumberField.Embeddings.finite_of_norm_le K ℂ ((D : ℝ) * B)
    refine (h.image fun x => x / (D : K)).subset ?_
    intro c hc
    refine ⟨(D : K) * c, ⟨hc.1, fun φ => ?_⟩, ?_⟩
    · have := mul_le_mul_of_nonneg_left (hc.2 φ) (Nat.cast_nonneg (α := ℝ) D)
      simpa [norm_mul] using this
    · have hD' : (D : K) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
      field_simp
  have hF : (Set.pi Set.univ fun _ : Fin (d + 1) =>
      {c : K | IsIntegral ℤ ((D : K) * c) ∧ ∀ φ : K →+* ℂ, ‖φ c‖ ≤ B}).Finite :=
    Set.Finite.pi fun _ => hT
  refine Set.Finite.of_finite_image
    (f := fun P : Polynomial K => fun i : Fin (d + 1) => P.coeff i) (hF.subset ?_) ?_
  · rintro _ ⟨P, hP, rfl⟩ i -
    exact ⟨(hP.2.2 i).1, (hP.2.2 i).2⟩
  · intro P hP Q hQ hPQ
    ext n
    by_cases hn : n ≤ d
    · exact congrFun hPQ ⟨n, Nat.lt_succ_of_le hn⟩
    · push_neg at hn
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hP.2.1.trans_lt hn),
        Polynomial.coeff_eq_zero_of_natDegree_lt (hQ.2.1.trans_lt hn)]

end GlobalTheory
end

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_monic_bounded_polynomials : ∀ (K : Type) [Field K] [NumberField K] (d D : ℕ) (B : ℝ), 0 < D → {P : Polynomial K | P.Monic ∧ P.natDegree ≤ d ∧ ∀ k, IsIntegral ℤ ((D : K) * P.coeff k) ∧ ∀ φ : K →+* ℂ, ‖φ (P.coeff k)‖ ≤ B}.Finite := by
  first | (exact @GlobalTheory.finite_monic_coeff_bdd_mul_isIntegral) | (exact GlobalTheory.finite_monic_coeff_bdd_mul_isIntegral) | (intros; apply GlobalTheory.finite_monic_coeff_bdd_mul_isIntegral  <;> assumption)
end
