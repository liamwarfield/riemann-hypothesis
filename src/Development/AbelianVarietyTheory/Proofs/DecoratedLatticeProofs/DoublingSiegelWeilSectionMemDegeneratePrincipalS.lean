module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationTwoVariableModelAndLineExte
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelFormulasWittTarget

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelWeilSectionMemDegeneratePrincipalS
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelWeilSectionMemDegeneratePrincipalS
noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause lagr evZero)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.SwSecMem

variable {D : D7} (A B : HSp D) (omh : WRep (dblSp A) B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B))

def intSub : Submodule ℂ (WO (dblSp A) B → ℂ) where
  carrier := {f | ∀ g : GA D (dblSp A), IntegrableOn (fun w => omh (g, 1) f (lagr A B w)) 𝓕 ν}
  zero_mem' g := by
    simp only [map_zero, Pi.zero_apply]
    exact integrableOn_zero
  add_mem' {f f'} hf hf' g := by
    simp only [map_add (f := _), Pi.add_apply]
    exact Integrable.add (hf g) (hf' g)
  smul_mem' c f hf g := by
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    exact Integrable.const_mul (hf g) c

def swLin : intSub A B omh ν 𝓕 →ₗ[ℂ] (GA D (dblSp A) → ℂ) where
  toFun f := swSec A B omh ν 𝓕 f
  map_add' f f' := by
    funext g
    simp only [swSec, evZero, Submodule.coe_add, map_add (f := _), Pi.add_apply]
    exact integral_add (f.2 g) (f'.2 g)
  map_smul' c f := by
    funext g
    simp only [swSec, evZero, Submodule.coe_smul, map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    exact integral_const_mul c _

theorem swSec_mul (φ : WO (dblSp A) B → ℂ) (g k : GA D (dblSp A)) :
    swSec A B omh ν 𝓕 φ (g * k) = swSec A B omh ν 𝓕 (omh (k, 1) φ) g := by
  have : ((g * k, 1) : GA D (dblSp A) × GA D B) = (g, 1) * (k, 1) := by simp
  simp only [swSec]
  rw [this, map_mul, Module.End.mul_apply]

theorem swSec_mem_degPS : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 → ∀ φ, IsThetaFunO ψ (dblSp A) B φ → ∀ a : GL (Fin A.rank) (AE D), IsKFinVec omh (Khat A a) φ → swSec A B omh ν 𝓕 φ ∈ degPS A a χB⁻¹ (sZero A B) := by
  intro hW D ψ A B χB omh hω ν 𝓕 hν φ hφ a hK
  have hint : ∀ f, IsThetaFunO ψ (dblSp A) B f → f ∈ intSub A B omh ν 𝓕 := fun f hf g =>
    (GlobalTheory.T.siegelWeilSection_integrable_and_continuous D ψ A B χB omh hω ν 𝓕 hν _ (hω.om_pres (g, 1) f hf)).1
  refine (mem_degPS A a).2 ⟨GlobalTheory.T.siegelWeilSection_degeneratePrincipalSeries_law hW D ψ A B χB omh hω ν 𝓕 hν φ hφ,
    (GlobalTheory.T.siegelWeilSection_integrable_and_continuous D ψ A B χB omh hω ν 𝓕 hν φ hφ).2, ?_⟩
  let S := Submodule.span ℂ {f : WO (dblSp A) B → ℂ | ∃ k ∈ Khat A a, f = omh (k, 1) φ}
  haveI : FiniteDimensional ℂ S := hK
  have hS : S ≤ intSub A B omh ν 𝓕 := Submodule.span_le.2 (by
    rintro _ ⟨k, -, rfl⟩
    exact hint _ (hω.om_pres _ _ hφ))
  refine isKFinite_iff.2 ⟨LinearMap.range ((swLin A B omh ν 𝓕).comp (Submodule.inclusion hS)), inferInstance,
    fun k hk => ⟨⟨omh (k, 1) φ, Submodule.subset_span ⟨k, hk, rfl⟩⟩, funext fun g => ?_⟩⟩
  exact (swSec_mul A B omh ν 𝓕 φ g k).symm

end GlobalTheory.SwSecMem

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelWeilSectionMemDegeneratePrincipalSStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doublingSiegelWeilSection_mem_degeneratePrincipalSeries : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 → ∀ φ, IsThetaFunO ψ (dblSp A) B φ → ∀ a : GL (Fin A.rank) (AE D), IsKFinVec omh (Khat A a) φ → swSec A B omh ν 𝓕 φ ∈ degPS A a χB⁻¹ (sZero A B) := by
  exact @GlobalTheory.SwSecMem.swSec_mem_degPS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLocFac
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod GlobalTheory.Mem GlobalTheory.Mem.Col2 Formalism.L2.Col Formalism.L2.Forms
open scoped Classical

noncomputable section
namespace GlobalTheory.LocMod

def IsLocFac (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (PP : Formalism.L2.DIV.Pl D.host.E) (c : WO S T →₀ ℂ)
    (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (p : Place D k)
    (Y Y' : Type) (_ : Fintype Y) (_ : DecidableEq Y) (_ : Fintype Y') (_ : DecidableEq Y') (FS : Frame k S.rank Y')
    (FT : Frame k T.rank Y) (Ξk : Matrix Y Y' k → ℂ),
    DenseRange p.pr ∧ Formalism.L2.NTheta.IsIdemAt p.e PP ∧
    (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ↔ p.up FS FT x ∈ stdHom S T) ∧
    Ξk ∈ SB (Matrix Y Y' k) ∧ p.IsCombAt ψ FS FT c Ξk ∧ ∀ γ, Ξ γ = Ξk (FT.γ * γ.map p.pr * FS.β)

end GlobalTheory.LocMod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianReadingFiniteRationalHeisenbergTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianReadingFiniteRationalHeisenbergTranslate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.HeisRead

variable {D : D7}


open GlobalTheory.FockCompare in
theorem realPt_eq_iota {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) (S T : HSp D) (Z : RW T S) :
    realPt θ (m := T.rank) (n := S.rank) (fun τ => Matrix.of fun i j => Z τ i j) = iotaW σ T S Z := by
  have hex : ∃ w : Mx D T.rank S.rank, w.map (finPart D) = 0 ∧ ∀ τ, compAt θ τ w = Matrix.of fun i j => Z τ i j :=
    ⟨iotaW σ T S Z, hσ.real_iota T S Z, fun τ => congrFun (hσ.pi_iota T S Z) τ⟩
  have hs := Classical.epsilon_spec hex
  exact hσ.real_ext hs.1 (hσ.real_iota T S Z) (funext fun τ => (hs.2 τ).trans (congrFun (hσ.pi_iota T S Z) τ).symm)

theorem embH_toHom_apply (S T : HSp D) (δ : ℂ) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (τ : D.what₂.Tau)
    (i : Fin T.rank) (j : Fin S.rank) :
    embH (tauE D) δ (toHom S T rfl rfl γ) τ i j = δ * tauE D τ (γ i j) := by
  simp [embH, toHom, Matrix.toLin'_apply]

end GlobalTheory.AdForm.HeisRead

namespace GlobalTheory.AdForm.HeisRead

theorem term_eq (k sc : ℝ) (δ w g : ℂ) (hδ : δ ≠ 0) (hsc : sc * ‖δ‖ ^ 2 = 2 * k) :
    2 * (Complex.I * (k : ℂ) * ((starRingEnd ℂ) g * -(δ⁻¹ * w))).re = ((sc : ℂ) * (w * (starRingEnd ℂ) (δ * g))).im := by
  have hn : Complex.normSq δ ≠ 0 := Complex.normSq_pos.2 hδ |>.ne'
  have hsc' : sc = 2 * k / Complex.normSq δ := by
    rw [Complex.normSq_eq_norm_sq, eq_div_iff (by rwa [← Complex.normSq_eq_norm_sq]), hsc]
  subst hsc'
  simp only [Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im, Complex.conj_re, Complex.conj_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im]
  rw [Complex.normSq_apply] at hn ⊢
  field_simp
  ring
end GlobalTheory.AdForm.HeisRead

namespace GlobalTheory.AdForm.HeisRead
variable {D : D7}

theorem HV_conj {ι : Type} [Fintype ι] {a b : ℕ} (sc : ℝ) (z w : VV ι a b) :
    HV sc w z = starRingEnd ℂ (HV sc z w) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [HV, LinearMap.mk₂'ₛₗ_apply, map_mul, map_sum, Complex.conj_ofReal, Complex.conj_conj]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _


open GlobalTheory.OrientedHeis in
theorem omO_eq_im (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (δ : ℂ) (sc : ℝ) (hP : StdPair θ S T δ sc ψ)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (z : VCx D.what₂.Tau S.rank T.rank) :
    omO S T (fun τ i j => -(δ⁻¹ * z τ i j)) (fun τ i j => tauE D τ (γ i j)) =
      (HV sc z (embH (tauE D) δ (toHom S T rfl rfl γ))).im := by
  simp only [omO, LinearMap.mk₂_apply, HV, LinearMap.mk₂'ₛₗ_apply, embH_toHom_apply, formAt, hP.gS, hP.gT, inv_one,
    Matrix.one_apply, apply_ite (tauE D _), map_one, map_zero, hP.xi]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hin : ∀ τ (x1 : Fin S.rank), (∑ x2 : Fin S.rank, ∑ x3 : Fin T.rank, if x1 = x2 then (starRingEnd ℂ) ((tauE D τ) (γ x3 x2)) * -(δ⁻¹ * z τ x3 x1) else 0) =
      ∑ x3 : Fin T.rank, (starRingEnd ℂ) ((tauE D τ) (γ x3 x1)) * -(δ⁻¹ * z τ x3 x1) := fun τ x1 => by
    rw [Finset.sum_comm]; simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [hin]
  rw [Finset.mul_sum, Complex.im_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum, Complex.re_sum, Finset.mul_sum, Finset.mul_sum, Complex.im_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Complex.re_sum, Finset.mul_sum, Finset.mul_sum, Complex.im_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact term_eq _ sc δ _ _ hP.ne hP.scale
end GlobalTheory.AdForm.HeisRead
namespace GlobalTheory.AdForm.HeisRead


open GlobalTheory.FockCompare GlobalTheory.OrientedHeis in
theorem xiN_heisO_finOf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ f, IsThetaFunO ψ S T f → ∀ γ v, GlobalTheory.AdTh.IsFinOf S T γ v → xiN θ S T hS hT δ sc (heisO ψ S T v f) = Formalism.L2.Th1.H.opU (HV sc) (embH (tauE D) δ (toHom S T hS hT γ)) (xiN θ S T hS hT δ sc f) := by
  intro D ψ θ S T a b hS hT δ sc hP f hf γ v hv
  subst hS hT
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hP.inf
  funext z
  let G : RW T S := fun τ i j => tauE D τ (γ i j)
  let Z : RW T S := fun τ i j => -(δ⁻¹ * z τ i j)
  have hrat : ratW T S γ = v + iotaW σ T S G := by
    have h1 : ratW T S γ - v = iotaW σ T S G := by
      refine hσ.real_ext (x := ratW T S γ - v) ?_ (hσ.real_iota _ _ _) ?_
      · show (ratW T S γ - v).map (finPart D) = 0
        rw [Matrix.map_sub _ (finPart D).map_sub, hv.2, sub_self]
      · rw [hσ.pi_iota, map_sub]
        funext τ i j
        have h0 : piW θ T S v τ i j = 0 := by
          show θ τ (infPart D (v i j)) = 0
          rw [show infPart D (v i j) = 0 from congrFun (congrFun hv.1 i) j, map_zero]
        show θ τ (infPart D (incA D (γ i j))) - piW θ T S v τ i j = _
        rw [h0, sub_zero, comp_incA hP.inf]
    rw [← h1]; abel
  have hX : ∀ τ i j, embH (tauE D) δ (toHom S T rfl rfl γ) τ i j = δ * tauE D τ (γ i j) :=
    GlobalTheory.AdForm.HeisRead.embH_toHom_apply S T δ γ
  have hp : realPt θ (m := T.rank) (n := S.rank) (fun τ => Matrix.of fun i j => -(δ⁻¹ * z τ (Fin.cast rfl i) (Fin.cast rfl j))) = iotaW σ T S Z := by
    simpa using GlobalTheory.AdForm.HeisRead.realPt_eq_iota hσ S T Z
  have hp' : realPt θ (m := T.rank) (n := S.rank) (fun τ => Matrix.of fun i j => -(δ⁻¹ * (z + embH (tauE D) δ (toHom S T rfl rfl γ)) τ (Fin.cast rfl i) (Fin.cast rfl j))) = iotaW σ T S (Z - G) := by
    rw [← GlobalTheory.AdForm.HeisRead.realPt_eq_iota hσ S T (Z - G)]
    congr 1
    funext τ i j
    simp only [Fin.cast_eq_self, Pi.add_apply, hX, Matrix.of_apply, Pi.sub_apply, Z, G]
    field_simp [hP.ne]
    ring
  unfold xiN Formalism.L2.Th1.H.opU heisO
  beta_reduce
  rw [hp, hp']
  have e0 : symplOH S T (iotaW σ T S Z) v = 0 := GlobalTheory.FinTranslate.symplOH_real_fin hv.1 (hσ.real_iota _ _ _)
  have e1 : iotaW σ T S Z + v = ratW T S γ + iotaW σ T S (Z - G) := by rw [hrat, map_sub]; abel
  have e2 : f (ratW T S γ + iotaW σ T S (Z - G)) = ψ (symplOH S T (iotaW σ T S (Z - G)) (iotaW σ T S G)) * f (iotaW σ T S (Z - G)) := by
    rw [hf.quasi, ← GlobalTheory.FinTranslate.symplOH_skew, hrat, symplOH_add_right,
      GlobalTheory.FinTranslate.symplOH_real_fin hv.1 (hσ.real_iota _ _ _), zero_add]
  have e3 : ψ (symplOH S T (iotaW σ T S (Z - G)) (iotaW σ T S G)) =
      Complex.exp (-(Real.pi * Complex.I) * ((HV sc z (embH (tauE D) δ (toHom S T rfl rfl γ))).im : ℂ)) := by
    rw [psi_symplOH hσ hP.std, hσ.pi_iota, LinearMap.map_sub₂, omO_self hσ, sub_zero]
    exact congrArg (fun t : ℝ => Complex.exp (-(Real.pi * Complex.I) * (t : ℂ)))
      (GlobalTheory.AdForm.HeisRead.omO_eq_im θ ψ S T δ sc hP γ z)
  rw [e0, AddChar.map_zero_eq_one, one_mul, e1, e2, e3]
  set X := embH (tauE D) δ (toHom S T rfl rfl γ)
  have hadd : HV sc (z + X) (z + X) = HV sc z z + HV sc z X + HV sc X z + HV sc X X := by
    simp only [map_add (f := _), LinearMap.add_apply]; ring
  have hc : HV sc X z = starRingEnd ℂ (HV sc z X) := GlobalTheory.AdForm.HeisRead.HV_conj sc z X
  have hcj : starRingEnd ℂ (HV sc z X) = HV sc z X - 2 * Complex.I * ((HV sc z X).im : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  rw [← mul_assoc, ← Complex.exp_add, mul_right_comm, ← Complex.exp_add]
  congr 2
  rw [hadd, hc, hcj]
  ring

end GlobalTheory.AdForm.HeisRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianReadingFiniteRationalHeisenbergTranslateStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussianReading_finiteRationalHeisenbergTranslate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ f, IsThetaFunO ψ S T f → ∀ γ v, GlobalTheory.AdTh.IsFinOf S T γ v → xiN θ S T hS hT δ sc (heisO ψ S T v f) = Formalism.L2.Th1.H.opU (HV sc) (embH (tauE D) δ (toHom S T hS hT γ)) (xiN θ S T hS hT δ sc f) := by
  first | exact @GlobalTheory.AdForm.HeisRead.xiN_heisO_finOf | exact GlobalTheory.AdForm.HeisRead.xiN_heisO_finOf | (intros; apply GlobalTheory.AdForm.HeisRead.xiN_heisO_finOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorOneApply
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LocMod

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
  {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

namespace Place

def intInd (Y Y' : Type) : Matrix Y Y' k → ℂ := Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1

def tensorAt (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Φ : WO S T → ℂ) (Ψ : Matrix Y Y' k → ℂ) : WO S T → ℂ :=
  fun t => Φ (t - p.up FS FT (p.down FS FT t)) * Ψ (p.down FS FT t)

def tensorL (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Φ : WO S T → ℂ) :
    SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ) where
  toFun Ψ := p.tensorAt FS FT Φ Ψ.1
  map_add' Ψ Ψ' := by
    funext t
    simp only [tensorAt, Submodule.coe_add, Pi.add_apply, mul_add]
  map_smul' c Ψ := by
    funext t
    simp only [tensorAt, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem tensorL_apply (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Φ : WO S T → ℂ) (Ψ : SB (Matrix Y Y' k)) :
    p.tensorL FS FT Φ Ψ = p.tensorAt FS FT Φ Ψ.1 := rfl

def tensorOne (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun Φ := p.tensorAt FS FT Φ (intInd Y Y')
  map_add' Φ Φ' := by
    funext t
    simp only [tensorAt, Pi.add_apply, add_mul]
  map_smul' c Φ := by
    funext t
    simp only [tensorAt, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem tensorOne_apply (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Φ : WO S T → ℂ) :
    p.tensorOne FS FT Φ = p.tensorAt FS FT Φ (intInd Y Y') := rfl

end Place
end GlobalTheory.LocMod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKillingImpliesVanishing
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.Aniso

theorem thetaKernel_rationalSource_invariant {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hω : IsWeilDatumO ψ S T χS χT om)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {γ : GA D S} (hγ : γ ∈ GQ S) (c : GA D S) (h : GA D T) :
    thetaKO om (γ * c) h f = thetaKO om c h f := by
  unfold thetaKO
  have e : om (γ * c, h) = om (γ, (1 : GA D T)) * om (c, h) := by
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  rw [e, Module.End.mul_apply]
  exact hω.om_aut γ hγ 1 (GQ T).one_mem _ (hω.om_pres (c, h) f hf)

end GlobalTheory.Core.Rk.Aniso

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelEqTsumSchrodingerFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelEqTsumSchrodingerFunction
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem thetaKO_eq_tsum_sch : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ g h, thetaKO omh g h f = ∑' ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E, sch ψ A B ν 𝓨 (omh (g, 1) f) (mt B h⁻¹ ⬝ (rat ξ : Mx D B.rank A.rank)) := by
  intro D ψ A B χB omh hW ν 𝓨 hν f hf g h
  have hF := hW.om_pres (g, 1) f hf
  have hG := hW.om_pres (1, h) _ hF
  have e : omh (g, h) f = omh (1, h) (omh (g, 1) f) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]
  have hs := (GlobalTheory.HeisMixSource.heis_mixS D ψ hW.std (dblSp A) (zeroSp D) B A.rank (dblDec A) ⟨ν, 𝓨, hν⟩ _ hG).2.2.2.2 0
  rw [map_zero] at hs
  have hl := (GlobalTheory.T.schrodingerFunction_unitary_levi_radical_actions D ψ A B χB omh hW ν 𝓨 hν _ hF).1 h
  unfold thetaKO
  rw [e, ← hs.tsum_eq]
  exact tsum_congr fun ξ => hl (rat ξ)

end GlobalTheory.StdUnn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelEqTsumSchrodingerFunctionStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernel_eq_tsum_schrodingerFunction : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ g h, thetaKO omh g h f = ∑' ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E, sch ψ A B ν 𝓨 (omh (g, 1) f) (mt B h⁻¹ ⬝ (rat ξ : Mx D B.rank A.rank)) := by
  first | exact @GlobalTheory.StdUnn.thetaKO_eq_tsum_sch | exact GlobalTheory.StdUnn.thetaKO_eq_tsum_sch | (intros; apply GlobalTheory.StdUnn.thetaKO_eq_tsum_sch <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsRootOfSUnitRatioUpToRootOfUnityClosureLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsRootOfSUnitRatioUpToRootOfUnityClosureLaws
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

theorem padicValRat_pow_mul_pow_ne_zero_imp {r s : ℚ} (hr : r ≠ 0) (hs : s ≠ 0) (a b : ℕ) (p : ℕ) (hp : p.Prime)
    (h : padicValRat p (r ^ a * s ^ b) ≠ 0) : padicValRat p r ≠ 0 ∨ padicValRat p s ≠ 0 := by
  haveI := Fact.mk hp
  by_contra hc
  push_neg at hc
  apply h
  rw [padicValRat.mul (pow_ne_zero _ hr) (pow_ne_zero _ hs), padicValRat.pow r, padicValRat.pow s, hc.1, hc.2]
  simp

theorem padicValRat_pow_div_pow_ne_zero_imp {r s : ℚ} (hr : r ≠ 0) (hs : s ≠ 0) (a b : ℕ) (p : ℕ) (hp : p.Prime)
    (h : padicValRat p (r ^ a / s ^ b) ≠ 0) : padicValRat p r ≠ 0 ∨ padicValRat p s ≠ 0 := by
  haveI := Fact.mk hp
  by_contra hc
  push_neg at hc
  apply h
  rw [padicValRat.div (pow_ne_zero _ hr) (pow_ne_zero _ hs), padicValRat.pow r, padicValRat.pow s, hc.1, hc.2]
  simp

theorem unitRatio_ne_zero {S : ℕ → Prop} {x y : ℂ} (h : UnitRatio S x y) : x ≠ 0 := by
  obtain ⟨hy, n, hn, r, hr, he, -⟩ := h
  intro hx
  rw [hx, zero_div, zero_pow hn.ne'] at he
  exact hr (by exact_mod_cast he.symm)

theorem unitRatio_refl (S : ℕ → Prop) {y : ℂ} (hy : y ≠ 0) : UnitRatio S y y :=
  ⟨hy, 1, one_pos, 1, one_ne_zero, by simp [div_self hy], fun p _ h => by simp at h⟩

theorem unitRatio_mul {S : ℕ → Prop} {x y x' y' : ℂ} (h : UnitRatio S x y) (h' : UnitRatio S x' y') :
    UnitRatio S (x * x') (y * y') := by
  obtain ⟨hy, n, hn, r, hr, he, hS⟩ := h
  obtain ⟨hy', n', hn', r', hr', he', hS'⟩ := h'
  refine ⟨mul_ne_zero hy hy', n * n', Nat.mul_pos hn hn', r ^ n' * r' ^ n,
    mul_ne_zero (pow_ne_zero _ hr) (pow_ne_zero _ hr'), ?_, ?_⟩
  · have : x * x' / (y * y') = (x / y) * (x' / y') := by field_simp
    rw [this, mul_pow, pow_mul, pow_mul, he, ← pow_mul, mul_comm n n', pow_mul, he']
    push_cast; ring
  · intro p hp hv
    rcases padicValRat_pow_mul_pow_ne_zero_imp hr hr' n' n p hp hv with h1 | h1
    · exact hS p hp h1
    · exact hS' p hp h1

theorem unitRatio_div {S : ℕ → Prop} {x y x' y' : ℂ} (h : UnitRatio S x y) (h' : UnitRatio S x' y') :
    UnitRatio S (x / x') (y / y') := by
  have hx' := unitRatio_ne_zero h'
  obtain ⟨hy, n, hn, r, hr, he, hS⟩ := h
  obtain ⟨hy', n', hn', r', hr', he', hS'⟩ := h'
  refine ⟨div_ne_zero hy hy', n * n', Nat.mul_pos hn hn', r ^ n' / r' ^ n,
    div_ne_zero (pow_ne_zero _ hr) (pow_ne_zero _ hr'), ?_, ?_⟩
  · have : x / x' / (y / y') = (x / y) / (x' / y') := by field_simp
    rw [this, div_pow, pow_mul, pow_mul, he, ← pow_mul, mul_comm n n', pow_mul, he']
    push_cast; ring
  · intro p hp hv
    rcases padicValRat_pow_div_pow_ne_zero_imp hr hr' n' n p hp hv with h1 | h1
    · exact hS p hp h1
    · exact hS' p hp h1

theorem unitRatio_of_pow_eq (S : ℕ → Prop) {x y : ℂ} {n : ℕ} (hy : y ≠ 0) (hn : 0 < n) (h : x ^ n = y ^ n) :
    UnitRatio S x y :=
  ⟨hy, n, hn, 1, one_ne_zero, by rw [div_pow, h, div_self (pow_ne_zero _ hy)]; simp, fun p _ h => by simp at h⟩

theorem unitRatio_prod (S : ℕ → Prop) {I : Type} (s : Finset I) (x y : I → ℂ)
    (h : ∀ i ∈ s, UnitRatio S (x i) (y i)) : UnitRatio S (∏ i ∈ s, x i) (∏ i ∈ s, y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using unitRatio_refl S one_ne_zero
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact unitRatio_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem unitRatio_laws : ∀ S : ℕ → Prop, (∀ y : ℂ, y ≠ 0 → UnitRatio S y y) ∧ (∀ x y x' y' : ℂ, UnitRatio S x y → UnitRatio S x' y' → UnitRatio S (x * x') (y * y') ∧ UnitRatio S (x / x') (y / y') ∧ x ≠ 0) ∧ (∀ (x y : ℂ) (n : ℕ), y ≠ 0 → 0 < n → x ^ n = y ^ n → UnitRatio S x y) ∧ ∀ (I : Type) (s : Finset I) (x y : I → ℂ), (∀ i ∈ s, UnitRatio S (x i) (y i)) → UnitRatio S (∏ i ∈ s, x i) (∏ i ∈ s, y i) :=
  fun S => ⟨fun y hy => unitRatio_refl S hy,
    fun x y x' y' h h' => ⟨unitRatio_mul h h', unitRatio_div h h', unitRatio_ne_zero h⟩,
    fun x y n hy hn h => unitRatio_of_pow_eq S hy hn h,
    fun I s x y h => unitRatio_prod S s x y h⟩

end GlobalTheory.Fam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsRootOfSUnitRatioUpToRootOfUnityClosureLawsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRootOfSUnitRatioUpToRootOfUnity_closure_laws : ∀ S : ℕ → Prop, (∀ y : ℂ, y ≠ 0 → UnitRatio S y y) ∧ (∀ x y x' y' : ℂ, UnitRatio S x y → UnitRatio S x' y' → UnitRatio S (x * x') (y * y') ∧ UnitRatio S (x / x') (y / y') ∧ x ≠ 0) ∧ (∀ (x y : ℂ) (n : ℕ), y ≠ 0 → 0 < n → x ^ n = y ^ n → UnitRatio S x y) ∧ ∀ (I : Type) (s : Finset I) (x y : I → ℂ), (∀ i ∈ s, UnitRatio S (x i) (y i)) → UnitRatio S (∏ i ∈ s, x i) (∏ i ∈ s, y i) := by
  first | exact @GlobalTheory.Fam.unitRatio_laws | exact GlobalTheory.Fam.unitRatio_laws | (intros; apply GlobalTheory.Fam.unitRatio_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlacesIffPlaceSetProd
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlacesIffPlaceSetProd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.KSplit

open GlobalTheory.FinPl.SetCut

variable {D : D7}

theorem idAt_mono {P P' : Pl D → Prop} (h : ∀ w, P w → P' w) {a : AE D} (ha : a ∈ idAt D P) : a ∈ idAt D P' := by
  rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at ha ⊢
  exact ⟨ha.1, fun w hw => ha.2 w fun h' => hw (h w h')⟩

theorem latV_mono (V : HSp D) (L : Lat V) {P P' : Pl D → Prop} (h : ∀ w, P w → P' w) : latV V L P ≤ latV V L P' := by
  apply AddSubgroup.closure_mono
  rintro y ⟨α, hα, h0, r⟩
  exact ⟨α, hα, fun v hv => h0 v fun h' => hv (h v h'), r⟩

theorem mul_mem_idAt {P R : Pl D → Prop} {c : AE D} (hc : ∀ w, ¬ R w → compAt D w c = 0) {a : AE D}
    (ha : a ∈ idAt D P) : c * a ∈ idAt D (fun p => P p ∧ R p) := by
  rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at ha ⊢
  refine ⟨by rw [RingHom.map_mul, ha.1, mul_zero], fun w hw => ?_⟩
  rw [RingHom.map_mul]
  by_cases h : R w
  · rw [ha.2 w fun h' => hw ⟨h', h⟩, mul_zero]
  · rw [hc w h, zero_mul]

theorem smul_mem_latV (V : HSp D) (L : Lat V) {P R : Pl D → Prop} (β : Af D.host.F) (hβ : β ∈ intAf D.host.F)
    (h0 : ∀ v, ¬ R v → evalV D.host.F v β = 0) {y : Fin V.rank → AE D} (hy : y ∈ latV V L P) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β) • y ∈ latV V L (fun p => P p ∧ R p) := by
  have main : latV V L P ≤ (latV V L (fun p => P p ∧ R p)).comap
      (DistribSMul.toAddMonoidHom (Fin V.rank → AE D) (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β))) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hα0, a, ha, x, hx, rfl⟩
    refine AddSubgroup.subset_closure ⟨β * α, fun v => by rw [map_mul]; exact mul_mem (hβ v) (hα v), fun v hv => ?_,
      a, ha, x, hx, ?_⟩
    · rw [map_mul]
      by_cases h : R v
      · rw [hα0 v fun h' => hv ⟨h', h⟩, mul_zero]
      · rw [h0 v h, zero_mul]
    · funext i
      change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * x i)) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      congr 1
      exact Prod.ext (mul_zero _) rfl
  exact main hy

theorem indQ_int (Q : Finset (Pl D)) : indQ D Q ∈ intAf D.host.F := by
  intro v
  rw [evalV_indQ]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem indQc_int (Q : Finset (Pl D)) : 1 - indQ D Q ∈ intAf D.host.F := by
  intro v
  rw [map_sub, map_one]
  exact sub_mem (one_mem _) (indQ_int Q v)

abbrev eQ (Q : Finset (Pl D)) : AE D := algebraMap (AF D.host.F) (AE D) (idemQ D Q)

theorem eQ_off (Q : Finset (Pl D)) (w : Pl D) (hw : ¬ w ∈ Q) : compAt D w (eQ Q) = 0 := by
  rw [(parts_idemQ Q).2 w, if_neg hw]

theorem one_sub_eQ_off (Q : Finset (Pl D)) (w : Pl D) (hw : ¬ w ∉ Q) : compAt D w (1 - eQ Q) = 0 := by
  rw [RingHom.map_sub, RingHom.map_one, (parts_idemQ Q).2 w, if_pos (not_not.1 hw), sub_self]

theorem eQ_mul_of_in {P : Pl D → Prop} (Q : Finset (Pl D)) {a : AE D} (ha : a ∈ idAt D (fun p => P p ∧ p ∈ Q)) :
    eQ Q * a = a :=
  (mem_idAt_Q_iff Q a).1 (idAt_mono (fun _ h => h.2) ha)

theorem eQ_mul_of_out {P : Pl D → Prop} (Q : Finset (Pl D)) {a : AE D} (ha : a ∈ idAt D (fun p => P p ∧ p ∉ Q)) :
    eQ Q * a = 0 := by
  classical
  refine (mem_idOff_iff_mul (· ∈ Q) _ (parts_idemQ Q).1 (fun w => by convert (parts_idemQ Q).2 w) a).1 ?_
  simp only [idOff, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall]
  intro w hw
  exact ((mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere _ _ _).1 ha).2 w fun h => h.2 hw

theorem one_sub_mul_eq {P : Pl D → Prop} (Q : Finset (Pl D)) {a : AE D} (ha : a ∈ idAt D P) :
    (1 - eQ Q) * a = algebraMap (AF D.host.F) (AE D) (idemQc D Q) * a := by
  rw [← sub_eq_zero]
  rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at ha
  apply CMAdele_eq_zero_of_infinite_and_finite_components_zero
  · rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, ha.1, mul_zero, mul_zero, sub_zero]
  · intro w
    rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, (parts_idemQ Q).2 w,
      (parts_idemQc Q).2 w]
    split_ifs
    · rw [sub_self, sub_self]
    · rw [sub_zero, sub_self]

theorem mem_latV_iff_parts (V : HSp D) (L : Lat V) (P : Pl D → Prop) (Q : Finset (Pl D)) {y : Fin V.rank → AE D}
    (hy : ∀ i, y i ∈ idAt D P) :
    y ∈ latV V L P ↔ eQ Q • y ∈ latV V L (fun p => P p ∧ p ∈ Q) ∧
      (1 - eQ Q) • y ∈ latV V L (fun p => P p ∧ p ∉ Q) := by
  constructor
  · intro h
    refine ⟨smul_mem_latV V L (indQ D Q) (indQ_int Q) (fun v hv => by rw [evalV_indQ, if_neg hv]) h, ?_⟩
    have e : (1 - eQ Q) • y = algebraMap (AF D.host.F) (AE D) (idemQc D Q) • y :=
      funext fun i => one_sub_mul_eq Q (hy i)
    rw [e]
    exact smul_mem_latV V L (1 - indQ D Q) (indQc_int Q)
      (fun v hv => by rw [map_sub, map_one, evalV_indQ, if_pos (not_not.1 hv), sub_self]) h
  · rintro ⟨h1, h2⟩
    have e : y = eQ Q • y + (1 - eQ Q) • y := by rw [← add_smul, add_sub_cancel, one_smul]
    rw [e]
    exact add_mem (latV_mono V L (fun _ h => h.1) h1) (latV_mono V L (fun _ h => h.1) h2)

theorem mt_mul (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := rfl

theorem mt_inj (V : HSp D) {a b : GA D V} (h : mt V a = mt V b) : a = b :=
  Subtype.ext (Units.ext h)

theorem mulVec_mem (V : HSp D) {I : Ideal (AE D)} (M : Matrix (Fin V.rank) (Fin V.rank) (AE D))
    {y : Fin V.rank → AE D} (hy : ∀ i, y i ∈ I) (i : Fin V.rank) : (M *ᵥ y) i ∈ I := by
  simp only [Matrix.mulVec, dotProduct]
  exact I.sum_mem fun j _ => I.mul_mem_left _ (hy j)

section Ring

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem cut_sub_one (c : A) (M : Matrix n n A) : c • M + (1 - c) • (1 : Matrix n n A) - 1 = c • (M - 1) := by
  module

theorem cut_mulVec (c : A) (M : Matrix n n A) (y : n → A) (hy : c • y = y) :
    (c • M + (1 - c) • (1 : Matrix n n A)) *ᵥ y = M *ᵥ y := by
  rw [add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, ← mulVec_smul, hy, sub_smul, hy, one_smul, sub_self, add_zero]

theorem cut_mul_cut (c : A) (hc : c * c = c) (M : Matrix n n A) :
    (c • M + (1 - c) • (1 : Matrix n n A)) * ((1 - c) • M + (1 - (1 - c)) • (1 : Matrix n n A)) = M := by
  have h1 : c * (1 - c) = 0 := by linear_combination -hc
  have h2 : (1 - c) * c = 0 := by linear_combination -hc
  have h3 : (1 - c) * (1 - c) = 1 - c := by linear_combination hc
  simp only [sub_sub_cancel, add_mul, mul_add, smul_mul_smul_comm, h1, h2, h3, hc, zero_smul, mul_one, one_mul,
    zero_add, add_zero]
  module

theorem prod_parts (c : A) (a b : Matrix n n A) (ha : c • (a - 1) = a - 1) (hb : c • (b - 1) = 0) (y : n → A) :
    c • ((a * b) *ᵥ y) = a *ᵥ (c • y) ∧ (1 - c) • ((a * b) *ᵥ y) = b *ᵥ ((1 - c) • y) := by
  have h1 : c • b = c • (1 : Matrix n n A) := by rw [← sub_eq_zero, ← smul_sub, hb]
  have h2 : (1 - c) • a = (1 - c) • (1 : Matrix n n A) := by
    rw [← sub_eq_zero, ← smul_sub, sub_smul, ha, one_smul, sub_self]
  constructor
  · rw [← smul_mulVec, ← mul_smul_comm, h1, mul_smul_comm, mul_one, smul_mulVec, mulVec_smul]
  · rw [← smul_mulVec, ← smul_mul_assoc, h2, smul_mul_assoc, one_mul, smul_mulVec, mulVec_smul]

end Ring

theorem inK_cut (V : HSp D) (L : Lat V) {P R : Pl D → Prop} (ε : AF D.host.F) (hε : ε * ε = ε)
    (hoff : ∀ w, ¬ R w → compAt D w (algebraMap (AF D.host.F) (AE D) ε) = 0)
    (hone : ∀ a ∈ idAt D (fun p => P p ∧ R p), algebraMap (AF D.host.F) (AE D) ε * a = a)
    (hlat : ∀ y : Fin V.rank → AE D, (∀ i, y i ∈ idAt D P) → y ∈ latV V L P →
      algebraMap (AF D.host.F) (AE D) ε • y ∈ latV V L (fun p => P p ∧ R p))
    {κ : GA D V} (hκ : InK V L P κ) : InK V L (fun p => P p ∧ R p) (cutG V ε hε κ) := by
  have key : ∀ y : Fin V.rank → AE D, (∀ i, y i ∈ idAt D (fun p => P p ∧ R p)) →
      (y ∈ latV V L (fun p => P p ∧ R p) ↔ y ∈ latV V L P) := by
    intro y hy
    refine ⟨fun h => latV_mono V L (fun _ h => h.1) h, fun h => ?_⟩
    have e : algebraMap (AF D.host.F) (AE D) ε • y = y := funext fun i => hone _ (hy i)
    have := hlat y (fun i => idAt_mono (fun _ h => h.1) (hy i)) h
    rwa [e] at this
  refine ⟨(mem_congGrp_iff V _ _).2 fun i j => ?_, fun y hy => ?_⟩
  · rw [mt_cutG, cut_sub_one]
    exact mul_mem_idAt hoff ((mem_congGrp_iff V _ _).1 hκ.1 i j)
  · have e : algebraMap (AF D.host.F) (AE D) ε • y = y := funext fun i => hone _ (hy i)
    rw [mt_cutG, cut_mulVec _ _ _ e, key y hy, key _ (mulVec_mem V _ hy)]
    exact hκ.2 y fun i => idAt_mono (fun _ h => h.1) (hy i)

theorem inK_iff_prod : ∀ (D : D7) (V : HSp D) (L : Lat V) (P : Pl D → Prop) (Q : Finset (Pl D)) (κ : GA D V),
    InK V L P κ ↔ ∃ a b, InK V L (fun p => P p ∧ p ∈ Q) a ∧ InK V L (fun p => P p ∧ p ∉ Q) b ∧ κ = a * b := by
  intro D V L P Q κ
  have e1 : algebraMap (AF D.host.F) (AE D) (1 - idemQ D Q) = 1 - eQ Q := by rw [map_sub, map_one]
  constructor
  · intro hκ
    refine ⟨cutG V _ (idemQ_mul_self Q) κ, cutG V _ (one_sub_idemQ_mul_self Q) κ,
      inK_cut V L _ _ (eQ_off Q) (fun a ha => eQ_mul_of_in Q ha)
        (fun y hy h => ((mem_latV_iff_parts V L P Q hy).1 h).1) hκ,
      inK_cut V L _ _ (by rw [e1]; exact one_sub_eQ_off Q)
        (fun a ha => by rw [e1, sub_mul, eQ_mul_of_out Q ha, one_mul, sub_zero])
        (fun y hy h => by rw [e1]; exact ((mem_latV_iff_parts V L P Q hy).1 h).2) hκ, mt_inj V ?_⟩
    rw [mt_mul, mt_cutG, mt_cutG, e1]
    exact (cut_mul_cut _ (by rw [← map_mul, idemQ_mul_self]) _).symm
  · rintro ⟨a, b, ha, hb, rfl⟩
    have hA := (mem_congGrp_iff V _ _).1 ha.1
    have hB := (mem_congGrp_iff V _ _).1 hb.1
    refine ⟨mul_mem ((mem_congGrp_iff V _ _).2 fun i j => idAt_mono (fun _ h => h.1) (hA i j))
      ((mem_congGrp_iff V _ _).2 fun i j => idAt_mono (fun _ h => h.1) (hB i j)), fun y hy => ?_⟩
    have hp := prod_parts (eQ Q) (mt V a) (mt V b) (Matrix.ext fun i j => eQ_mul_of_in Q (hA i j))
      (Matrix.ext fun i j => eQ_mul_of_out Q (hB i j)) y
    rw [mem_latV_iff_parts V L P Q hy, mem_latV_iff_parts V L P Q (mulVec_mem V _ hy), mt_mul, hp.1, hp.2]
    exact and_congr (ha.2 _ fun i => mul_mem_idAt (eQ_off Q) (hy i))
      (hb.2 _ fun i => mul_mem_idAt (one_sub_eQ_off Q) (hy i))

end GlobalTheory.FinPl.KSplit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlacesIffPlaceSetProdStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inLatticeStabilizerAtPlaces_iff_placeSet_prod : ∀ (D : D7) (V : HSp D) (L : Lat V) (P : Pl D → Prop) (Q : Finset (Pl D)) (κ : GA D V), InK V L P κ ↔ ∃ a b, InK V L (fun p => P p ∧ p ∈ Q) a ∧ InK V L (fun p => P p ∧ p ∉ Q) b ∧ κ = a * b := by
  first | exact @GlobalTheory.FinPl.KSplit.inK_iff_prod | exact GlobalTheory.FinPl.KSplit.inK_iff_prod | (intros; apply GlobalTheory.FinPl.KSplit.inK_iff_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompIncAAlgebraMap
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
open NumberField IsDedekindDomain
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocMod.SplitCompl

open GlobalTheory.FinPl GlobalTheory.FinPl.SplitPoint GlobalTheory.IdemModTwo GlobalTheory.SplitIdem GlobalTheory.SplitChart GlobalTheory.SplitHecke

variable {D : D7}

theorem incA_algebraMap (t : D.host.F) :
    incA D (algebraMap D.host.F D.host.E t) = algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) t) := by
  rw [← IsScalarTower.algebraMap_apply]
  exact (Algebra.TensorProduct.includeRight (R := D.host.F) (A := AF D.host.F) (B := D.host.E)).commutes t

theorem comp_incA_algebraMap {v : Pl D} {e : AE D} (he : SplitAt D v e) (t : D.host.F) :
    comp he (incA D (algebraMap D.host.F D.host.E t)) = algebraMap D.host.F (Fv D.host.F v) t := by
  rw [incA_algebraMap, comp_algebraMap]
  rfl

def emb {v : Pl D} {e : AE D} (he : SplitAt D v e) : D.host.E →ₐ[D.host.F] Fv D.host.F v :=
  { (comp he).comp (incA D) with commutes' := comp_incA_algebraMap he }

theorem comp_sec {v : Pl D} {e : AE D} (he : SplitAt D v e) (a : Fv D.host.F v) : comp he (sec D v e a) = a := by
  rw [sec_apply, map_mul, comp_fj, comp_self, mul_one, evalV_singleV_same]

theorem sec_comp {v : Pl D} {e : AE D} (he : SplitAt D v e) (x : AE D) : sec D v e (comp he x) = e * x :=
  (sc_spec he x).symm

theorem int_iff_sec {v : Pl D} {e : AE D} (he : SplitAt D v e) (a : Fv D.host.F v) :
    a ∈ 𝒪[Fv D.host.F v] ↔ finPart D (sec D v e a) ∈ intAE D := by
  have h1 := (chart_comp he).2.2.2 (sec D v e a)
  rw [← sec_comp he, comp_sec he] at h1
  rw [h1, isInt_Ov, mem_integer_iff]

def splitPt {v : Pl D} {e : AE D} (h : IsSplitIdem D e) (he : SplitAt D v e)
    (hab : ∃ ε, IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) : SplitPt D (Fv D.host.F v) where
  v := v
  e := e
  split := h
  above := hab
  pr := comp he
  sec := sec D v e
  pr_sec := comp_sec he
  sec_pr := sec_comp he
  cont_pr := continuous_comp he
  cont_sec := continuous_sec
  int_iff := int_iff_sec he

theorem emb_apply {v : Pl D} {e : AE D} (he : SplitAt D v e) (a : D.host.E) : emb he a = comp he (incA D a) := rfl

theorem splitPrime_emb {v : Pl D} {e : AE D} (he : SplitAt D v e) (PP : HeightOneSpectrum (𝓞 D.host.E))
    (h : Formalism.L2.NTheta.IsIdemAt e PP) : GlobalTheory.AdelicU.splitPrime (emb he) = PP := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  by_cases hx : x = 0
  · subst hx; simp only [Submodule.zero_mem]
  rw [GlobalTheory.AdelicU.mem_splitPrime, h.2 x hx, ← sec_comp he, ← emb_apply]
  have h0 : emb he (x : D.host.E) ≠ 0 :=
    (map_ne_zero _).2 (RingOfIntegers.coe_ne_zero_iff.2 hx)
  rw [← int_iff_sec he, mem_integer_iff, HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀, not_le,
    one_lt_inv₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0))]

theorem exists_place : ∀ (D : D7) (PP : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e PP → ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (q : GlobalTheory.FinPl.SplitPt D k), q.e = e ∧ q.v = PP.under (NumberField.RingOfIntegers D.host.F) ∧ (∀ a, (ofSplit q).pr a ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt PP a) ∧ DenseRange (ofSplit q).pr := by
  intro D PP e h
  obtain ⟨-, -, v, ε, hε, hs⟩ := h.1
  have he : SplitAt D v e := splitAt_of h.1 hε hs
  have hP := splitPrime_emb he PP h
  refine ⟨Fv D.host.F v, inferInstance, inferInstance, inferInstance, inferInstance, splitPt h.1 he ⟨ε, hε, hs⟩, rfl, ?_, ?_, ?_⟩
  · show v = _
    rw [← hP, GlobalTheory.AdelicU.splitPrime_under]
  · intro a
    change emb he a ∈ _ ↔ _
    rw [mem_integer_iff, HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.AdelicU.valued_apply_eq_valuation, hP,
      GlobalTheory.Proof.IntegralPowerExpansion.intAt_iff_val]
  · change DenseRange (emb he)
    refine Dense.mono ?_ (HeightOneSpectrum.denseRange_algebraMap D.host.F v)
    rintro _ ⟨t, rfl⟩
    exact ⟨algebraMap D.host.F D.host.E t, (emb he).commutes t⟩
end GlobalTheory.LocMod.SplitCompl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CongAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Transport

def CongAt (B : Base) {a b : ℕ} (P : HeightOneSpectrum (𝓞 B.host.E)) (M₀ : ℕ) (y : TC.GA B a) (y' : TC.GA B b)
    (x x₀ : Formalism.L2.Col.HomE B.fields.E a b) : Prop :=
  ∀ r s, Valued.v (adAt B.host.F P
    ((HMul.hMul (HMul.hMul ((y'⁻¹ : TC.GA B b).1 : Matrix (Fin b) (Fin b) (Formalism.L2.DIV.AfE B.host.F B.host.E))
      ((LinearMap.toMatrix' x).map (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) : Matrix (Fin b) (Fin a) (Formalism.L2.DIV.AfE B.host.F B.host.E)))
      (y.1 : Matrix (Fin a) (Fin a) (Formalism.L2.DIV.AfE B.host.F B.host.E)) -
      ((LinearMap.toMatrix' x₀).map (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) : Matrix (Fin b) (Fin a) (Formalism.L2.DIV.AfE B.host.F B.host.E))) r s)) ≤
    Valued.v ((M₀ : ℕ) : P.adicCompletion B.host.E)

end GlobalTheory.Transport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselAdaptedTranslateLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ColMatch

theorem unitaryAdelicPointFiniteMatrix_inv_eq_of_mul_eq_one {D : D7} (a : GA D (D.sp.X 0)) (M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D))
    (hM : M * GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a = 1) :
    GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ = M := by
  have h1 : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a *
      GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ = 1 := by
    rw [← unitaryAdelicPointFiniteMatrix_base_space_mul, mul_inv_cancel, unitaryAdelicPointFiniteMatrix_base_space_one]
  calc _ = (M * GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a) *
        GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ := by rw [hM, one_mul]
    _ = M := by rw [mul_assoc, h1, mul_one]

end GlobalTheory.ColMatch

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelFormulasWittTargetStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModelFormulas_wittTarget : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedTarget D := by
  first | exact @GlobalTheory.MixTargetProof.mixedTarget | exact GlobalTheory.MixTargetProof.mixedTarget | (intros; apply GlobalTheory.MixTargetProof.mixedTarget <;> assumption)
end
