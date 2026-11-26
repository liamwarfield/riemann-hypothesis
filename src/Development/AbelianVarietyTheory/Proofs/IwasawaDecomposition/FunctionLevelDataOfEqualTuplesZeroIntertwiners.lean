module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolynomialFrameMapsBounded
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTransportGroupsCuspFormsWeilDataIsometryStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneTupleRowsCuspFormsIsometricThetaLifts
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPosIsQuotInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.Mem.QuotHaar

theorem exists_pos_isQuotInt : ∀ (D : D7) (V : HSp D), V.SigOK → ∀ ν : Measure (GA D V), ν.IsHaarMeasure → ∃ r : ℝ, 0 < r ∧
    ∀ 𝓕, IsFundamentalDomain (GQ V) 𝓕 ν → ∀ φ : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) → IntegrableOn φ 𝓕 ν →
      GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V r φ (∫ g in 𝓕, φ g ∂ν) := by
  intro D V hV ν hν
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨μ₀, hμ₀, huniq⟩ := GlobalTheory.Mem.VolMeasure.existsUnique_isVolMeasG D V hV
  haveI := hμ₀.1
  obtain ⟨-, 𝓕₀, h𝓕₀⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ₀ hμ₀.1
  have e : ν = Measure.haarScalarFactor ν μ₀ • μ₀ := Measure.isMulLeftInvariant_eq_smul ν μ₀
  have cpos : 0 < Measure.haarScalarFactor ν μ₀ := Measure.haarScalarFactor_pos_of_isHaarMeasure ν μ₀
  set c := Measure.haarScalarFactor ν μ₀
  refine ⟨c, by exact_mod_cast cpos, ?_⟩
  intro 𝓕 h𝓕 φ hφ hint
  refine ⟨⟨(μ₀, 𝓕₀), hμ₀, h𝓕₀⟩, ?_⟩
  rintro ⟨m, F'⟩ ⟨hm, hF'⟩
  obtain rfl : m = μ₀ := huniq m hm
  have e' : m = c⁻¹ • ν := by rw [e, smul_smul, inv_mul_cancel₀ cpos.ne', one_smul]
  have hac : m ≪ ν := by
    rw [e']
    exact Measure.smul_absolutelyContinuous
  have h𝓕' : IsFundamentalDomain (GQ V) 𝓕 m := h𝓕.mono hac
  have hinv : ∀ (γ : GQ V) (g : GA D V), φ (γ • g) = φ g := fun γ g => hφ γ γ.2 g
  have hint' : IntegrableOn φ 𝓕 m := by
    rw [e', IntegrableOn, Measure.restrict_smul, ENNReal.smul_def]
    exact hint.smul_measure ENNReal.coe_ne_top
  refine ⟨(h𝓕'.integrableOn_iff hF' hinv).1 hint', ?_⟩
  simp only
  rw [← h𝓕'.setIntegral_eq hF' hinv]
  conv_lhs => rw [e]
  rw [Measure.restrict_smul, integral_smul_nnreal_measure]
  simp [NNReal.smul_def, Complex.real_smul]

end GlobalTheory.Mem.QuotHaar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EllTInclTTprod
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.Mem.SchurTensor

theorem ellT_inclT_tprod {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (w : ∀ τ, M.H τ) (v : M.Vec) :
    ellT M w (inclT M (PiTensorProduct.tprod ℂ v)) = ∏ τ, ⟪w τ, (v τ : M.H τ)⟫_ℂ := by
  simp [ellT, inclT]

theorem schur_tensor : ∀ (D : D7) (θ : InfF D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), SchurMult θ M J χ μ 𝓕 → IsInfFam θ → IsQuot V μ 𝓕 → ∀ x ∈ MultT θ M J χ, ∀ y ∈ MultT θ M J χ, ∀ (v : SmT M) (w : M.Vec), IsCuspForm θ V (y (PiTensorProduct.tprod ℂ w)) ∧ IntegrableOn (fun g => star (x v g) * y (PiTensorProduct.tprod ℂ w) g) 𝓕 μ ∧ ∫ g in 𝓕, star (x v g) * y (PiTensorProduct.tprod ℂ w) g ∂μ = ipT M μ 𝓕 y x * star (ellT M (fun τ => (w τ : M.H τ)) (inclT M v)) := by
  intro D θ V S M J χ μ 𝓕 hS hθ hq x hx y hy v w
  have hx' := (mem_multT θ M J χ x).1 hx
  have hy' := (mem_multT θ M J χ y).1 hy
  have hm := (GlobalTheory.MultMem.mem_mult_iff D θ V S M J χ _).1 hy'
  have hI := ipM_spec M μ 𝓕 _ _ (hS hθ hq.1 hq.2 _ hx' _ hy')
  refine ⟨⟨hm.aut w, hm.cusp w⟩, ?_⟩
  induction v using PiTensorProduct.induction_on with
  | smul_tprod c u =>
    obtain ⟨h1, h2⟩ := hI u w
    have e : (fun g => star (x (c • PiTensorProduct.tprod ℂ u) g) * y (PiTensorProduct.tprod ℂ w) g) =
        fun g => star c * (star (x (PiTensorProduct.tprod ℂ u) g) * y (PiTensorProduct.tprod ℂ w) g) := by
      funext g
      rw [map_smul, Pi.smul_apply, smul_eq_mul, star_mul', mul_assoc]
    rw [e]
    refine ⟨h1.const_mul _, ?_⟩
    rw [integral_const_mul, map_smul, map_smul, ellT_inclT_tprod, smul_eq_mul, star_mul', star_prod]
    refine (congrArg (star c * ·) h2).trans ?_
    have e2 : ∏ τ, star ⟪(w τ : M.H τ), (u τ : M.H τ)⟫_ℂ = ∏ τ, ⟪(u τ : M.H τ), (w τ : M.H τ)⟫_ℂ :=
      Finset.prod_congr rfl fun τ _ => inner_conj_symm _ _
    rw [e2, ipT]
    ring
  | add a b ha hb =>
    have e : (fun g => star (x (a + b) g) * y (PiTensorProduct.tprod ℂ w) g) =
        fun g => star (x a g) * y (PiTensorProduct.tprod ℂ w) g + star (x b g) * y (PiTensorProduct.tprod ℂ w) g := by
      funext g
      rw [map_add (f := _), Pi.add_apply, star_add, add_mul]
    rw [e]
    refine ⟨ha.1.add hb.1, ?_⟩
    rw [integral_add ha.1 hb.1, ha.2, hb.2, map_add (f := _), map_add (f := _), star_add, mul_add]

end GlobalTheory.Mem.SchurTensor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KerEqThetaKO
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.Mem.OrientedKer

variable {D : D7}

theorem toTWsmall_zero (S T : HSp D) : toTWsmall S T 0 = 0 := by
  unfold toTWsmall
  rw [Matrix.zero_mul, Matrix.transpose_zero]

theorem ker_eq_thetaKO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (Wf : WeilFun D ψ) (S T : HSp D) (χS χT : IdC D), S.rank < T.rank → admitted T S χT χS → ∀ om, IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∃ Φ : ThS ψ T S, (f ≠ 0 → Φ ≠ 0) ∧ ∀ g h, Wf.ker T S χT χS Φ h g = thetaKO om g h f := by
  intro D ψ hψ Wf S T χS χT hr ha om H f hf
  have ha' : admitted S T χS χT := ⟨ha.1.symm, ha.2.2.1, ha.2.1, ha.2.2.2.2, ha.2.2.2.1⟩
  obtain ⟨omO, H', e⟩ := GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO D ψ hψ S T χS χT _ ha' hr (Wf.core.weil S T χS χT ha')
  obtain ⟨E, -, -, hE, -, -, -, h7, -⟩ := GlobalTheory.OrientedCoord.exists_coord D S T hr.le

  have hf0 : IsThetaFun ψ S T fun y => f (E.symm y) := by
    refine (h7 ψ _).1 ?_
    simp only [AddEquiv.symm_apply_apply]
    exact hf
  let Φ₀ : ThS ψ S T := ⟨fun y => f (E.symm y), mem_ThS.2 hf0⟩
  have hfΦ : f = fun x => Φ₀.1 (toTWsmall S T x) := by
    funext x
    simp only [Φ₀, ← hE, AddEquiv.symm_apply_apply]

  have hΦt : IsThetaFun ψ T S fun x => Φ₀.1 x.transpose :=
    (GlobalTheory.Mem.ThetaClosed.thetaFun_closed D ψ hψ S T Φ₀.1).2.2 hr.ne (mem_ThS.1 Φ₀.2)
  let Φ : ThS ψ T S := ⟨fun x => Φ₀.1 x.transpose, mem_ThS.2 hΦt⟩
  refine ⟨Φ, fun h0 hΦ => h0 ?_, fun g h => ?_⟩
  · funext x
    have := congrFun (congrArg Subtype.val hΦ) (E x).transpose
    simp only [Φ, Φ₀, Matrix.transpose_transpose, AddEquiv.symm_apply_apply, Submodule.coe_zero, Pi.zero_apply] at this
    exact this
  · have hs := Wf.om_swap S T χS χT ha' g h Φ₀ Φ (fun x => congrArg Φ₀.1 (Matrix.transpose_transpose x)) 0
    rw [Matrix.transpose_zero] at hs
    have e1 := congrFun (e (g, h) Φ₀) 0
    rw [toTWsmall_zero, ← hfΦ] at e1
    have e2 := GlobalTheory.WeilUniq.weilDatum_unique D ψ hψ S T χS χT omO om H' H (g, h) f hf
    unfold WeilFun.ker thetaKO
    rw [hs, ← e2]
    exact e1.symm

end GlobalTheory.Mem.OrientedKer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneTupleRowsCuspFormsIsometricThetaLifts
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

noncomputable section
namespace GlobalTheory.Mem.OneTuple

variable {D : D7}

def castG {V V' : HSp D} (h : V = V') : GA D V ≃* GA D V' := h ▸ MulEquiv.refl _

@[simp] theorem castG_rfl (V : HSp D) : castG (rfl : V = V) = MulEquiv.refl _ := rfl

def Moves (V V' : HSp D) (κ : GA D V ≃* GA D V') : Prop :=
  Continuous κ ∧ Continuous κ.symm ∧ (∀ g, κ g ∈ GQ V' ↔ g ∈ GQ V) ∧
    (∀ θ : InfF D, IsInfFam θ → ∀ F, IsCuspForm θ V F → IsCuspForm θ V' fun h => F (κ.symm h)) ∧
    ∀ (ψ : AddChar (AF D.host.F) ℂ) (S : HSp D) (χ χ' : IdC D) om, IsWeilDatumO ψ S V χ χ' om →
      ∃ om', IsWeilDatumO ψ S V' χ χ' om' ∧ ∀ f, IsThetaFunO ψ S V f →
        ∃ f', IsThetaFunO ψ S V' f' ∧ (f ≠ 0 → f' ≠ 0) ∧ ∀ g h, thetaKO om' g (κ h) f' = thetaKO om g h f

theorem moves_castG {V V' : HSp D} (h : V = V') : Moves V V' (castG h) := by
  subst h
  refine ⟨continuous_id, continuous_id, fun g => Iff.rfl, fun θ _ F hF => hF, fun ψ S χ χ' om hom => ⟨om, hom, fun f hf => ⟨f, hf, id, fun g h => rfl⟩⟩⟩

theorem isQuotInt_rescale {V : HSp D} {c : ℝ} (hc : c ≠ 0) (κ : ℝ) {φ : GA D V → ℂ} {z : ℂ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V c φ z) : GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V κ φ (((κ / c : ℝ) : ℂ) * z) := by
  refine ⟨h.1, fun m hm => ?_⟩
  obtain ⟨h1, h2⟩ := h.2 m hm
  refine ⟨h1, ?_⟩
  rw [h2, ← mul_assoc, ← Complex.ofReal_mul, div_mul_cancel₀ _ hc]

theorem quot_transport {V V' : HSp D} {κ : GA D V ≃* GA D V'} (hκ : Moves V V' κ) (hV' : V'.SigOK)
    {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} (hq : IsQuot V ν 𝓕) : ∃ r : ℝ, 0 < r ∧
    ∀ φ : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) → IntegrableOn φ 𝓕 ν →
      GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V' r (fun h => φ (κ.symm h)) (∫ g in 𝓕, φ g ∂ν) := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V'
  haveI := hq.1
  let H : GA D V ≃ₜ GA D V' := { toEquiv := κ.toEquiv, continuous_toFun := hκ.1, continuous_invFun := hκ.2.1 }
  let E : GA D V ≃ᵐ GA D V' := H.toMeasurableEquiv
  haveI : (ν.map κ).IsHaarMeasure := MulEquiv.isHaarMeasure_map ν κ hκ.1 hκ.2.1
  obtain ⟨r, hr, hR⟩ := GlobalTheory.Mem.QuotHaar.exists_pos_isQuotInt D V' hV' (ν.map κ) inferInstance
  refine ⟨r, hr, fun φ hφ hint => ?_⟩
  have hmap : ν.map κ = ν.map E := rfl
  have hmem : ∀ g : GA D V', g ∈ GQ V' ↔ κ.symm g ∈ GQ V := fun g => by
    rw [← hκ.2.2.1, MulEquiv.apply_symm_apply]
  let e : GQ V' ≃ GQ V :=
    { toFun := fun g => ⟨κ.symm g, (hmem g).1 g.2⟩
      invFun := fun g => ⟨κ g, (hκ.2.2.1 g).2 g.2⟩
      left_inv := fun g => Subtype.ext (κ.apply_symm_apply _)
      right_inv := fun g => Subtype.ext (κ.symm_apply_apply _) }
  have hF : IsFundamentalDomain (GQ V') (κ '' 𝓕) (ν.map κ) := by
    have := hq.2.image_of_equiv (ν := ν.map κ) E.toEquiv (by rw [hmap]; exact E.quasiMeasurePreserving_symm ν) e
      (fun g x => by
        show κ (κ.symm g * x) = g * κ x
        rw [map_mul, MulEquiv.apply_symm_apply])
    exact this
  have hinv : ∀ γ ∈ GQ V', ∀ g, (fun h => φ (κ.symm h)) (γ * g) = (fun h => φ (κ.symm h)) g := by
    intro γ hγ g
    simp only [map_mul]
    exact hφ _ ((hmem γ).1 hγ) _
  have hpre : E ⁻¹' (κ '' 𝓕) = 𝓕 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_image]
    refine ⟨fun ⟨y, hy, hxy⟩ => ?_, fun hx => ⟨x, hx, rfl⟩⟩
    have : y = x := κ.injective hxy
    exact this ▸ hy
  have hcomp : (fun h => φ (κ.symm h)) ∘ E = φ := funext fun x => by
    show φ (κ.symm (κ x)) = φ x
    rw [MulEquiv.symm_apply_apply]
  have hint' : IntegrableOn (fun h => φ (κ.symm h)) (κ '' 𝓕) (ν.map κ) := by
    rw [hmap, E.measurableEmbedding.integrableOn_map_iff, hcomp, hpre]
    exact hint
  have := hR _ hF _ hinv hint'
  convert this using 2
  rw [hmap, E.measurableEmbedding.setIntegral_map, hpre]
  exact (congrArg (fun f => ∫ g in 𝓕, f g ∂ν) hcomp).symm
end GlobalTheory.Mem.OneTuple
end

noncomputable section
namespace GlobalTheory.Mem.OneTuple
variable {D : D7}

theorem multT_left {θ : InfF D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {X : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hX : X ∈ MultT θ M J χ) (v : SmT M) :
    ∀ γ ∈ GQ V, ∀ g, X v (γ * g) = X v g := by
  have hm := (GlobalTheory.MultMem.mem_mult_iff D θ V S M J χ _).1 ((mem_multT θ M J χ X).1 hX)
  intro γ hγ g
  induction v using PiTensorProduct.induction_on with
  | smul_tprod c u =>
    have h1 := (hm.aut u).left γ hγ g
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    congr 1
  | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb]

theorem level (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfF D} (hθ : IsInfFam θ) {V V' : HSp D} {κ : GA D V ≃* GA D V'}
    (hκ : Moves V V' κ) (hV' : V'.SigOK) {S : D.what₂.Tau → SPar} (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ)
    {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} (hq : IsQuot V ν 𝓕) : ∃ r : ℝ, 0 < r ∧
    ∀ X ∈ MultT θ M J χ, ∀ Y ∈ MultT θ M J χ, ∀ (v : SmT M) (w : M.Vec),
      GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V' r (fun h => star (X v (κ.symm h)) * Y (PiTensorProduct.tprod ℂ w) (κ.symm h))
        (ipT M ν 𝓕 Y X * star (ellT M (fun τ => (w τ : M.H τ)) (inclT M v))) := by
  obtain ⟨r, hr, hR⟩ := quot_transport hκ hV' hq
  refine ⟨r, hr, fun X hX Y hY v w => ?_⟩
  obtain ⟨-, h1, h2⟩ := GlobalTheory.Mem.SchurTensor.schur_tensor D θ V S M J χ ν 𝓕 (GlobalTheory.MultFinite.schurMult hP ν 𝓕) hθ hq X hX Y hY v w
  rw [← h2]
  refine hR (fun g => star (X v g) * Y (PiTensorProduct.tprod ℂ w) g) (fun γ hγ g => ?_) h1
  simp only [multT_left hX v γ hγ g, multT_left hY _ γ hγ g]

end GlobalTheory.Mem.OneTuple
end

noncomputable section
namespace GlobalTheory.Mem.OneTuple
variable {D : D7}

theorem isQuotInt_const_mul {V : HSp D} {c : ℝ} {φ : GA D V → ℂ} {z : ℂ} (a : ℂ)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V c φ z) : GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V c (fun g => a * φ g) (a * z) := by
  refine ⟨h.1, fun m hm => ?_⟩
  obtain ⟨h1, h2⟩ := h.2 m hm
  refine ⟨h1.const_mul a, ?_⟩
  rw [h2, integral_const_mul]
  ring

theorem isQuotInt_congr {V : HSp D} {c : ℝ} {φ ψ : GA D V → ℂ} {z w : ℂ} (hf : φ = ψ) (hz : z = w)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V c φ z) : GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V c ψ w := hf ▸ hz ▸ h

theorem ellT_unit {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (d : M.Vec) (hd : ∀ τ, ‖(d τ : M.H τ)‖ = 1) :
    ellT M (fun τ => (d τ : M.H τ)) (inclT M (PiTensorProduct.tprod ℂ d)) = 1 := by
  rw [GlobalTheory.Mem.SchurTensor.ellT_inclT_tprod]
  refine Finset.prod_eq_one fun τ _ => ?_
  rw [inner_self_eq_norm_sq_to_K, hd τ]
  simp

theorem levelRow (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfF D} (hθ : IsInfFam θ) {V V' : HSp D} {κ : GA D V ≃* GA D V'}
    (hκ : Moves V V' κ) (hV' : V'.SigOK) {S : D.what₂.Tau → SPar} (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ)
    {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} (hq : IsQuot V ν 𝓕) {N : Type} [NormedAddCommGroup N] [InnerProductSpace ℂ N]
    (e : N →ₗ[ℂ] MultT θ M J χ) {c : ℝ} (hc : 0 < c) (hip : ∀ x y, ⟪x, y⟫_ℂ = (c : ℂ) * ipT M ν 𝓕 (e y).1 (e x).1)
    (d : M.Vec) (hd : ∀ τ, ‖(d τ : M.H τ)‖ = 1) {kq : ℝ} (hkq : 0 < kq) :
    ∃ s r : ℝ, 0 < s ∧ 0 < r ∧ s ^ 2 * (kq / r) = c ∧ ∃ row : N →ₗ[ℂ] CuspS θ V',
      (∀ x h, (row x).1 h = (s : ℂ) * (e x).1 (PiTensorProduct.tprod ℂ d) (κ.symm h)) ∧
      (∀ x y, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V' kq (fun h => star ((row x).1 h) * (row y).1 h) ⟪x, y⟫_ℂ) ∧
      ∀ X ∈ MultT θ M J χ, ∀ (v : SmT M) (x : N),
        GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V' r (fun h => star (X v (κ.symm h)) * (e x).1 (PiTensorProduct.tprod ℂ d) (κ.symm h))
          (ipT M ν 𝓕 (e x).1 X * star (ellT M (fun τ => (d τ : M.H τ)) (inclT M v))) := by
  obtain ⟨r, hr, hR⟩ := level hP hθ hκ hV' M J χ hq
  have hcf : ∀ x, IsCuspForm θ V' fun h => (e x).1 (PiTensorProduct.tprod ℂ d) (κ.symm h) := fun x =>
    hκ.2.2.2.1 θ hθ _ (GlobalTheory.Mem.SchurTensor.schur_tensor D θ V S M J χ ν 𝓕 (GlobalTheory.MultFinite.schurMult hP ν 𝓕) hθ hq _ (e x).2 _ (e x).2
      (PiTensorProduct.tprod ℂ d) d).1
  set s := Real.sqrt (c * r / kq) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 * (kq / r) = c := by
    rw [hs, Real.sq_sqrt (by positivity)]
    field_simp
  let row : N →ₗ[ℂ] CuspS θ V' :=
    { toFun := fun x => ⟨fun h => (s : ℂ) * (e x).1 (PiTensorProduct.tprod ℂ d) (κ.symm h),
        Submodule.smul_mem _ (s : ℂ) (Submodule.subset_span (hcf x))⟩
      map_add' := fun x y => by
        apply Subtype.ext
        funext h
        simp [mul_add]
      map_smul' := fun a x => by
        apply Subtype.ext
        funext h
        simp only [map_smul, Submodule.coe_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  refine ⟨s, r, hs0, hr, hs2, row, fun x h => rfl, fun x y => ?_, fun X hX v x => hR X hX _ (e x).2 v d⟩
  have h1 := isQuotInt_const_mul ((s : ℂ) ^ 2) (isQuotInt_rescale hr.ne' kq (hR _ (e x).2 _ (e y).2 (PiTensorProduct.tprod ℂ d) d))
  refine isQuotInt_congr (funext fun h => ?_) ?_ h1
  · simp only [row, LinearMap.coe_mk, AddHom.coe_mk, star_mul', Complex.star_def, Complex.conj_ofReal]
    ring
  · rw [ellT_unit M d hd, star_one, mul_one, hip, ← hs2]
    push_cast
    ring

end GlobalTheory.Mem.OneTuple
end

noncomputable section
namespace GlobalTheory.Mem.OneTuple
variable {D : D7}

theorem ipT_swap (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfF D} (hθ : IsInfFam θ) {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} (hq : IsQuot V μ 𝓕)
    (d : M.Vec) (hd : ∀ τ, ‖(d τ : M.H τ)‖ = 1) {X Y : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hX : X ∈ MultT θ M J χ)
    (hY : Y ∈ MultT θ M J χ) : ipT M μ 𝓕 X Y = star (ipT M μ 𝓕 Y X) := by
  haveI := hq.1
  have hS : SchurMult θ M J χ μ 𝓕 := GlobalTheory.MultFinite.schurMult hP μ 𝓕
  obtain ⟨c, hc⟩ := hS hθ hq.1 hq.2 _ ((mem_multT θ M J χ X).1 hX) _ ((mem_multT θ M J χ Y).1 hY)
  have h1 := ipM_spec M μ 𝓕 _ _ ⟨c, hc⟩
  have hsw : IsMultIP M μ 𝓕 (PiTensorProduct.lift.symm Y) (PiTensorProduct.lift.symm X) (star c) := by
    intro v v'
    obtain ⟨i1, i2⟩ := hc v' v
    have e : (fun g => star ((PiTensorProduct.lift.symm Y) v g) * (PiTensorProduct.lift.symm X) v' g) =
        fun g => star (star ((PiTensorProduct.lift.symm X) v' g) * (PiTensorProduct.lift.symm Y) v g) := by
      funext g; rw [star_mul', star_star, mul_comm]
    have hI : IntegrableOn (fun g => star ((PiTensorProduct.lift.symm Y) v g) * (PiTensorProduct.lift.symm X) v' g) 𝓕 μ := by
      rw [e]
      exact (Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ).integrable_comp i1
    have hE : ∫ g in 𝓕, star ((PiTensorProduct.lift.symm Y) v g) * (PiTensorProduct.lift.symm X) v' g ∂μ =
        star c * ∏ τ, ⟪(v τ : M.H τ), (v' τ : M.H τ)⟫_ℂ := by
      rw [e]
      have := integral_conj (μ := μ.restrict 𝓕) (f := fun g => star ((PiTensorProduct.lift.symm X) v' g) * (PiTensorProduct.lift.symm Y) v g)
      simp only [Complex.star_def] at this i2 ⊢
      rw [this, i2, map_mul, map_prod]
      congr 1
      exact Finset.prod_congr rfl fun τ _ => inner_conj_symm _ _
    exact ⟨hI, hE⟩
  have hu := hasPeterssonInner_unique M μ 𝓕 _ _ d (by
    rw [Finset.prod_eq_one fun τ _ => by rw [inner_self_eq_norm_sq_to_K, hd τ]; simp]; exact one_ne_zero)
    (ipM_spec M μ 𝓕 _ _ ⟨_, hsw⟩) hsw
  unfold ipT
  rw [hu]
  have hv := hasPeterssonInner_unique M μ 𝓕 _ _ d (by
    rw [Finset.prod_eq_one fun τ _ => by rw [inner_self_eq_norm_sq_to_K, hd τ]; simp]; exact one_ne_zero) h1 hc
  rw [hv]

end GlobalTheory.Mem.OneTuple
end

noncomputable section
namespace GlobalTheory.Mem.OneTuple
variable {D : D7}

theorem ker_smul {ψ : AddChar (AF D.host.F) ℂ} (Wf : WeilFun D ψ) (V W : HSp D) (χ χ' : IdC D) (a : ℂ) (Φ : ThS ψ V W)
    (g : GA D V) (h : GA D W) : Wf.ker V W χ χ' (a • Φ) g h = a * Wf.ker V W χ χ' Φ g h := by
  unfold WeilFun.ker
  rw [map_smul]
  rfl

theorem thetaKO_left {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : IdC D} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hom : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∀ γ ∈ GQ T, ∀ g h, thetaKO om g (γ * h) f = thetaKO om g h f := by
  intro γ hγ g h
  unfold thetaKO
  have e : ((g, γ * h) : GA D S × GA D T) = (1, γ) * (g, h) := by simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hom.om_aut 1 (one_mem _) γ hγ _ (hom.om_pres _ f hf)

theorem step (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfF D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ}
    (Wf : WeilFun D ψ) {V V' W W' : HSp D} (hV : V = V') {κ : GA D W ≃* GA D W'} (hκ : Moves W W' κ) (hW' : W'.SigOK)
    (hrk : V'.rank < W'.rank) {χS χT : IdC D} (hS : IsHC D χS) (hT : IsHC D χT)
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hom : IsWeilDatumO ψ V W χS χT om)
    {SV SW : D.what₂.Tau → SPar} (MV : DSModel V SV) (MW : DSModel W SW) (JV : Set (GA D V)) (χV : GA D V → ℂ)
    (JW : Set (GA D W)) (χW : GA D W → ℂ) (CCs : Submodule ℂ (SmT MW →ₗ[ℂ] (GA D W → ℂ)))
    (hCC : CCs ≤ MultT θ MW JW χW) {νW : Measure (GA D W)} {𝓕W : Set (GA D W)} (hqW : IsQuot W νW 𝓕W)
    {νV : Measure (GA D V)} {𝓕V : Set (GA D V)} (hqV : IsQuot V νV 𝓕V)
    {pt : PolF D W.rank V.rank → (WO V W → ℂ)} (hpt : ∀ P, IsThetaFunO ψ V W (pt P))
    {It : PolF D W.rank V.rank →ₗ[ℂ] SmT MW →ₗ[ℂ] SmT MV} {io : CCs →ₗ[ℂ] MultT θ MV JV χV}
    (hio : Lift.IsIo νW 𝓕W (thetaKO om) pt It CCs (MultT θ MV JV χV) io)
    (φ : PolF D W.rank V.rank) (hφ : pt φ ≠ 0) (d : MV.Vec) (hd : ∀ τ, ‖(d τ : MV.H τ)‖ = 1) (d' : MW.Vec)
    (h1 : ellT MV (fun τ => (d τ : MV.H τ)) (inclT MV (It φ (PiTensorProduct.tprod ℂ d'))) = 1)
    {NV NW : Type} [NormedAddCommGroup NV] [InnerProductSpace ℂ NV] [NormedAddCommGroup NW] [InnerProductSpace ℂ NW]
    (ioN : NW →ₗ[ℂ] NV) (eV : NV →ₗ[ℂ] MultT θ MV JV χV) (eW : NW →ₗ[ℂ] CCs) {cV : ℝ} (hcV : 0 < cV)
    (hioN : ∀ x y, ⟪x, ioN y⟫_ℂ = (cV : ℂ) * ipT MV νV 𝓕V (io (eW y)).1 (eV x).1)
    (rowV : NV →ₗ[ℂ] CuspS θ V') (rowW : NW →ₗ[ℂ] CuspS θ W') {sV rV sW kV kW : ℝ} (hsV : 0 < sV) (hrV : 0 < rV)
    (hsW : 0 < sW) (hkV : 0 < kV) (hkW : 0 < kW)
    (hrowV : ∀ x g, (rowV x).1 g = (sV : ℂ) * (eV x).1 (PiTensorProduct.tprod ℂ d) ((castG hV).symm g))
    (hpairV : ∀ X ∈ MultT θ MV JV χV, ∀ (v : SmT MV) (x : NV),
      GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V' rV
        (fun g => star (X v ((castG hV).symm g)) * (eV x).1 (PiTensorProduct.tprod ℂ d) ((castG hV).symm g))
        (ipT MV νV 𝓕V (eV x).1 X * star (ellT MV (fun τ => (d τ : MV.H τ)) (inclT MV v))))
    (hrowW : ∀ y h, (rowW y).1 h = (sW : ℂ) * ((eW y).1 : SmT MW →ₗ[ℂ] (GA D W → ℂ)) (PiTensorProduct.tprod ℂ d') (κ.symm h)) :
    ∃ Φ : ThS ψ W' V', Φ ≠ 0 ∧ ∀ y : NW, ∃ L : GA D V' → ℂ,
      (∀ g, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt W' kW (fun h => Wf.ker W' V' χT χS Φ h g * (rowW y).1 h) (L g)) ∧
      ∀ x : NV, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V' kV (fun g => star (L g) * (rowV x).1 g) (inner ℂ (ioN y) x) := by
  subst hV
  obtain ⟨rW, hrW, hRW⟩ := quot_transport hκ hW' hqW
  obtain ⟨om', hom', hmv⟩ := hκ.2.2.2.2 ψ V χS χT om hom
  obtain ⟨f', hf', hf'0, hf'eq⟩ := hmv (pt φ) (hpt φ)
  obtain ⟨Φ0, hΦ0, hker⟩ := GlobalTheory.Mem.OrientedKer.ker_eq_thetaKO D ψ hom'.std Wf V W' χS χT hrk ⟨hrk.ne', hT, hS, hom'.resT, hom'.resS⟩ om' hom' f' hf'
  set a : ℝ := cV * rV * rW / (kV * kW * sV * sW) with ha
  have ha0 : 0 < a := by positivity
  refine ⟨(a : ℂ) • Φ0, smul_ne_zero (by exact_mod_cast ha0.ne') (hΦ0 (hf'0 hφ)), fun y => ?_⟩
  have hFm : ((eW y : CCs) : SmT MW →ₗ[ℂ] (GA D W → ℂ)) ∈ MultT θ MW JW χW := hCC (eW y).2
  refine ⟨fun g => (((kW / rW) * a * sW : ℝ) : ℂ) * ((io (eW y)).1 : SmT MV →ₗ[ℂ] (GA D V → ℂ)) (It φ (PiTensorProduct.tprod ℂ d')) g,
    fun g => ?_, fun x => ?_⟩
  · have hinv : ∀ γ ∈ GQ W, ∀ h, (fun h => thetaKO om g h (pt φ) * ((eW y : CCs) : SmT MW →ₗ[ℂ] (GA D W → ℂ)) (PiTensorProduct.tprod ℂ d') h) (γ * h) =
        (fun h => thetaKO om g h (pt φ) * ((eW y : CCs) : SmT MW →ₗ[ℂ] (GA D W → ℂ)) (PiTensorProduct.tprod ℂ d') h) h := by
      intro γ hγ h
      simp only [thetaKO_left hom (hpt φ) γ hγ g h, multT_left hFm _ γ hγ h]
    have hq := hRW _ hinv (hio.integ (eW y) φ (PiTensorProduct.tprod ℂ d') g)
    have hval := hio.eq (eW y) φ (PiTensorProduct.tprod ℂ d') g
    unfold Lift.liftInt at hval
    rw [hval] at hq
    have h2 := isQuotInt_const_mul ((a * sW : ℝ) : ℂ) (isQuotInt_rescale hrW.ne' kW hq)
    refine isQuotInt_congr (funext fun h => ?_) ?_ h2
    · rw [ker_smul, hker, hrowW, ← hf'eq g (κ.symm h), MulEquiv.apply_symm_apply]
      push_cast
      ring
    · push_cast
      ring
  · have hX := (io (eW y)).2
    have h3 := isQuotInt_const_mul ((((kW / rW) * a * sW : ℝ) : ℂ) * sV)
      (isQuotInt_rescale hrV.ne' kV (hpairV _ hX (It φ (PiTensorProduct.tprod ℂ d')) x))
    refine isQuotInt_congr (funext fun g => ?_) ?_ h3
    · rw [hrowV]
      simp only [castG_rfl, MulEquiv.refl_symm, MulEquiv.refl_apply, star_mul', Complex.star_def, Complex.conj_ofReal]
      ring
    · rw [h1, star_one, mul_one, ← inner_conj_symm, hioN,
        ipT_swap hP hθ MV JV χV hqV d hd (eV x).2 hX]
      have hnum : (kW / rW) * a * sW * sV * (kV / rV) = cV := by
        rw [ha]; field_simp
      rw [map_mul, Complex.conj_ofReal, ← Complex.star_def, ← hnum]
      push_cast
      ring

end GlobalTheory.Mem.OneTuple
end

noncomputable section
namespace GlobalTheory.Mem.OneTuple
variable {D : D7}

theorem tau_nonempty (D : D7) : Nonempty D.what₂.Tau :=
  Fintype.card_pos_iff.1 (by
    rw [D.what₂.card_Tau]
    show 0 < 2 * D.R.n
    unfold Formalism.BasicNotions.Ranks.n
    have := D.R.ord_pos
    omega)

theorem pt_ne_zero {V W : HSp D} {S S' : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {M' : DSModel W S'}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {pt : PolF D W.rank V.rank → (WO V W → ℂ)}
    {It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M} (hI : IsItW θ M M' ω pt It) (hpt0 : pt 0 = 0)
    {φ : PolF D W.rank V.rank} {v : SmT M'} (hv : inclT M (It φ v) ≠ 0) : pt φ ≠ 0 := by
  intro h0
  obtain ⟨τ⟩ := tau_nonempty D
  have h1 : (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
    simp [Formalism.QuantumDeterminants.UH]
  have h := hI.eqK τ 1 h1 φ 0 (by rw [hpt0, h0, map_zero]) v
  rw [map_zero, LinearMap.zero_apply, map_zero] at h
  have hrep : M.rep τ 1 = 1 := by
    unfold DSModel.rep
    rw [mul_one, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ))]
    exact (M.ds τ).2.2.1.1.1
  have hid : actT M τ 1 = LinearMap.id := by
    classical
    unfold actT
    rw [hrep]
    have : Function.update (fun ρ => (LinearMap.id : M.H ρ →ₗ[ℂ] M.H ρ)) τ ((1 : M.H τ →L[ℂ] M.H τ) : M.H τ →ₗ[ℂ] M.H τ) =
        fun ρ => LinearMap.id := by
      funext ρ
      by_cases hρ : ρ = τ
      · subst hρ; simp; rfl
      · simp [Function.update_of_ne hρ]
    rw [this, PiTensorProduct.map_id]
  rw [hid, LinearMap.id_apply] at h
  exact hv h.symm

theorem isHC_inv {χ : IdC D} (h : IsHC D χ) : IsHC D χ⁻¹ := by
  refine ⟨⟨h.1.1.inv, fun x => by rw [MonoidHom.inv_apply, h.1.2 x, inv_one]⟩, fun τ => ?_⟩
  obtain ⟨a, ha⟩ := h.2 τ
  exact ⟨-a, GlobalTheory.Mem.HeckeExp.hasInfExp_inv ha⟩

theorem isHC_mu {T : Type} (L : Formalism.IndefR.Links.LevCh D T) {μ0 : T} (hL : L.Is μ0) (t : T) (i : Fin D.R.m) :
    IsHC D (L.mu t ((i : ℕ) + 1)) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have h1 : IsHC D (L.mu0 ((i : ℕ) + 1)) := ⟨(hL.mu0 i).1, fun τ =>
    ⟨_, GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hL.mu0 i) (GlobalTheory.Chain.StepVac.hasInfQ_tau (L.C.isMu0 i).inf) τ⟩⟩
  have h2 : IsHC D (L.xi t) := ⟨(hL.xi t).1, fun τ => ⟨_, GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hL.xi t) hn ho τ⟩⟩
  exact h1.mul h2

theorem isHC_eta {T : Type} (L : Formalism.IndefR.Links.LevCh D T) {μ0 : T} (hL : L.Is μ0) : IsHC D L.eta :=
  ⟨hL.eta.1, fun τ => ⟨_, GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta
    (GlobalTheory.Chain.StepVac.hasInfQ_tau (a := fun _ => 1 / 2) ⟨_, fun _ => by norm_num, L.C.isEta.inf⟩) τ⟩⟩

theorem chrStep_eq {C : Type} [CommGroup C] (μ : ℕ → C) (η : C) (j : ℕ) :
    Lift.chrStep μ η (j + 1) = (if Even j then μ (j + 1) * η⁻¹ else μ (j + 1),
      if Even (j + 1) then μ (j + 1) * η⁻¹ else μ (j + 1)) := by
  unfold Lift.chrStep
  rcases Nat.even_or_odd j with h | h
  · have h1 : Odd (j + 1) := h.add_one
    have h2 : ¬ Even (j + 1) := Nat.not_even_iff_odd.2 h1
    simp [h, h1, h2]
  · have h1 : ¬ Odd (j + 1) := Nat.not_odd_iff_even.2 h.add_one
    have h2 : Even (j + 1) := h.add_one
    have h3 : ¬ Even j := Nat.not_even_iff_odd.2 h
    simp [h1, h2, h3]

theorem isHC_step {T : Type} (L : Formalism.IndefR.Links.LevCh D T) {μ0 : T} (hL : L.Is μ0) (t : T) (j : ℕ) (hj : j < D.R.m) :
    IsHC D (if Even j then L.mu t (j + 1) * L.eta⁻¹ else L.mu t (j + 1)) ∧
      IsHC D (if Even (j + 1) then L.mu t (j + 1) * L.eta⁻¹ else L.mu t (j + 1)) := by
  have h1 := isHC_mu L hL t ⟨j, hj⟩
  have h2 := h1.mul (isHC_inv (isHC_eta L hL))
  constructor <;> split_ifs <;> assumption

end GlobalTheory.Mem.OneTuple
end

noncomputable section
namespace GlobalTheory.Mem.OneTuple
variable {D : D7}

theorem famCast_heq (Sp : ℕ → Type) [∀ j, NormedAddCommGroup (Sp j)] [∀ j, InnerProductSpace ℂ (Sp j)] {i j : ℕ}
    (h : i = j) (x : Sp i) : HEq x (famCast Sp h x) := by
  subst h
  rfl

theorem yc_eq (D : D7) {j : ℕ} (hj : j < D.R.m) : Yc D j = D.sp.Y j := by
  unfold Yc
  rw [min_eq_left hj.le]

theorem rank_lt (D : D7) {j : ℕ} (hj : j < D.R.m) : (D.sp.Y j).rank < (D.sp.Y (j + 1)).rank := by
  rw [D.sp.Y_rank j hj.le, D.sp.Y_rank (j + 1) hj]
  unfold Formalism.BasicNotions.Ranks.rankY
  have := D.R.t_odd.pos
  nlinarith

end GlobalTheory.Mem.OneTuple
end

noncomputable section
namespace GlobalTheory.Mem.OneTuple

set_option maxHeartbeats 1000000 in
theorem topRow (hP : GlobalTheory.Published.CuspRapidDecay) {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (hM : R.IsModels) (t : T) (μ : D.what₂.Tup)
    (eX : D.what₂.Mult μ D.R.m →ₗ[ℂ] LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) (J : Set (GA D D.sp.X'))
    (χ : GA D D.sp.X' → ℂ) (hJ : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) ≤ MultT R.θ R.MX J χ) {cX : ℝ}
    (hcX : 0 < cX) (H3 : ∀ x y, ⟪x, y⟫_ℂ = (cX : ℂ) * ipT R.MX (R.νX t) (R.fdX t) (eX y).1 (eX x).1) (dX : R.MX.Vec)
    (hdX : ∀ τ, ‖(dX τ : R.MX.H τ)‖ = 1) {k : ℝ} (hk : 0 < k) (j : ℕ) (hj : j = D.R.m) :
    ∃ κT : GA D D.sp.X' ≃* GA D (D.sp.Y j), Moves D.sp.X' (D.sp.Y j) κT ∧
      ∃ s : ℝ, 0 < s ∧ ∃ row : D.what₂.Mult μ j →ₗ[ℂ] CuspS R.θ (D.sp.Y j),
      (∀ x h, (row x).1 h = (s : ℂ) * (eX (famCast (D.what₂.Mult μ) hj x)).1 (PiTensorProduct.tprod ℂ dX) (κT.symm h)) ∧
      (∀ x y, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) k (fun h => star ((row x).1 h) * (row y).1 h) ⟪x, y⟫_ℂ) := by
  subst hj
  have hiso0 := GlobalTheory.T.exists_transport_groups_cuspForms_weilData_isometry D D.sp.X' (D.sp.Y D.R.m) D.sp.eYm
  have hiso1 := D.sp.eYm_isom
  have hiso2 := hiso0 hiso1
  obtain ⟨κT, hκT⟩ := hiso2
  have hκM : Moves D.sp.X' (D.sp.Y D.R.m) κT := hκT
  let eT : D.what₂.Mult μ D.R.m →ₗ[ℂ] MultT R.θ R.MX J χ := (Submodule.inclusion hJ) ∘ₗ eX
  have hT : ∀ x y, ⟪x, y⟫_ℂ = (cX : ℂ) * ipT R.MX (R.νX t) (R.fdX t) (eT y).1 (eT x).1 := H3
  have hqX : IsQuot D.sp.X' (R.νX t) (R.fdX t) := ⟨(hM.νX t).1.1, (hM.νX t).2⟩
  have hθ : IsInfFam R.θ := hM.inf
  have hsig := D.sp.Y_sig D.R.m
  have L0 := levelRow (N := D.what₂.Mult μ D.R.m) hP hθ hκM hsig R.MX J χ hqX eT hcX hT dX hdX hk
  obtain ⟨s, r, hs, hr, -, row, hrow, hiso, -⟩ := L0
  exact ⟨κT, hκM, s, hs, row, hrow, hiso⟩

end GlobalTheory.Mem.OneTuple
end


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Mem.OneTuple.rows_theta : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsChain → ∀ (t : T) (μ : D.what₂.Tup), (∃ (e : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] R.CC t j) (eX : D.what₂.Mult μ D.R.m →ₗ[ℂ] LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) (ν : ∀ j, Measure (GA D (Yc D j))) (𝓕 : ∀ j, Set (GA D (Yc D j))) (c : ℕ → ℝ) (cX : ℝ), (∀ j, j < D.R.m → IsQuot (Yc D j) (ν j) (𝓕 j) ∧ 0 < c j ∧ ∀ x y, ⟪x, y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (e j y).1 (e j x).1) ∧ (∃ J χ, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) ≤ MultT R.θ R.MX J χ) ∧ 0 < cX ∧ (∀ x y, ⟪x, y⟫_ℂ = (cX : ℂ) * ipT R.MX (R.νX t) (R.fdX t) (eX y).1 (eX x).1) ∧ (∀ j, j + 1 < D.R.m → ∀ x y, ⟪x, D.what₂.io μ j y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (R.ioY t j (e (j + 1) y)).1 (e j x).1) ∧ ∀ x (y : D.what₂.Mult μ (D.R.m - 1 + 1)) (y' : D.what₂.Mult μ D.R.m), HEq y y' → ⟪x, D.what₂.io μ (D.R.m - 1) y⟫_ℂ = (c (D.R.m - 1) : ℂ) * ipT (R.MY (D.R.m - 1)) (ν (D.R.m - 1)) (𝓕 (D.R.m - 1)) (R.ioX t (eX y')).1 (e (D.R.m - 1) x).1) → ∀ (Wf : WeilFun D R.ψ) (κ : ℕ → ℝ), (∀ j, 0 < κ j) → ∃ (row : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] CuspS R.θ (D.sp.Y j)) (Phi : ∀ j, ThS R.ψ (D.sp.Y (j + 1)) (D.sp.Y j)), (∀ j, j < D.R.m → Phi j ≠ 0) ∧ (∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (κ j) (fun h => star ((row j x).1 h) * (row j y).1 h) (inner ℂ x y)) ∧ ∀ j, j < D.R.m → ∀ y : D.what₂.Mult μ (j + 1), ∃ L : GA D (D.sp.Y j) → ℂ, (∀ g, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y (j + 1)) (κ (j + 1)) (fun h => Wf.ker _ _ (if Even (j + 1) then R.toLevCh.mu t (j + 1) * R.eta⁻¹ else R.toLevCh.mu t (j + 1)) (if Even j then R.toLevCh.mu t (j + 1) * R.eta⁻¹ else R.toLevCh.mu t (j + 1)) (Phi j) h g * (row (j + 1) y).1 h) (L g)) ∧ ∀ x : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (κ j) (fun g => star (L g) * (row j x).1 g) (inner ℂ (D.what₂.io μ j y) x) := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R hL hM hC t μ hyp Wf κ hκ
  obtain ⟨e, eX, ν, 𝓕, c, cX, H1, ⟨J, χ, hJ⟩, hcX, H3, H4, H5⟩ := hyp
  have hθ : IsInfFam R.θ := hM.inf
  have hm2 := D.R.two_le_m
  have hsigY := D.sp.Y_sig
  obtain ⟨d, dX, φ, φX, hd, hdX, hφ, hφX⟩ :=
    GlobalTheory.T.exists_polynomial_frame_maps_bounded D G Pl0 T A Ks R (fun k hk => (hC.ItY t k hk).ne) (hC.ItX t).ne

  have hlow : ∀ j (hj : j < D.R.m), ∃ s r : ℝ, 0 < s ∧ 0 < r ∧ s ^ 2 * (κ j / r) = c j ∧
      ∃ row : D.what₂.Mult μ j →ₗ[ℂ] CuspS R.θ (D.sp.Y j),
      (∀ x h, (row x).1 h = (s : ℂ) * (e j x).1 (PiTensorProduct.tprod ℂ (d j))
        ((GlobalTheory.Mem.OneTuple.castG (GlobalTheory.Mem.OneTuple.yc_eq D hj)).symm h)) ∧
      (∀ x y, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (κ j) (fun h => star ((row x).1 h) * (row y).1 h) ⟪x, y⟫_ℂ) ∧
      ∀ X ∈ R.CC t j, ∀ (v : SmT (R.MY j)) (x : D.what₂.Mult μ j),
        GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) r
          (fun h => star (X v ((GlobalTheory.Mem.OneTuple.castG (GlobalTheory.Mem.OneTuple.yc_eq D hj)).symm h)) *
            (e j x).1 (PiTensorProduct.tprod ℂ (d j)) ((GlobalTheory.Mem.OneTuple.castG (GlobalTheory.Mem.OneTuple.yc_eq D hj)).symm h))
          (ipT (R.MY j) (ν j) (𝓕 j) (e j x).1 X * star (ellT (R.MY j) (fun τ => (d j τ : (R.MY j).H τ)) (inclT (R.MY j) v))) :=
    fun j hj => GlobalTheory.Mem.OneTuple.levelRow hP hθ (GlobalTheory.Mem.OneTuple.moves_castG (GlobalTheory.Mem.OneTuple.yc_eq D hj))
      (hsigY j) (R.MY j) _ _ (H1 j hj).1 (e j) (H1 j hj).2.1 (H1 j hj).2.2 (d j) (hd j hj) (hκ j)

  have htop := GlobalTheory.Mem.OneTuple.topRow hP R hM t μ eX J χ hJ hcX H3 dX hdX (hκ D.R.m)
  choose sL rL hsL hrL hsrL rowL hrowL hisoL hpairL using hlow
  have htop' : ∀ j (hj : j = D.R.m), ∃ κT : GA D D.sp.X' ≃* GA D (D.sp.Y j), GlobalTheory.Mem.OneTuple.Moves D.sp.X' (D.sp.Y j) κT ∧
      ∃ s : ℝ, 0 < s ∧ ∃ row : D.what₂.Mult μ j →ₗ[ℂ] CuspS R.θ (D.sp.Y j),
      (∀ x h, (row x).1 h = (s : ℂ) * (eX (famCast (D.what₂.Mult μ) hj x)).1 (PiTensorProduct.tprod ℂ dX) (κT.symm h)) ∧
      (∀ x y, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (κ j) (fun h => star ((row x).1 h) * (row y).1 h) ⟪x, y⟫_ℂ) := by
    intro j hj
    have := htop j hj
    subst hj
    exact this
  choose κT hκT sT hsT rowT hrowT hisoT using htop'
  let row : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] CuspS R.θ (D.sp.Y j) := fun j =>
    if hj : j < D.R.m then rowL j hj else if hj' : j = D.R.m then rowT j hj' else 0
  have row_low : ∀ j (hj : j < D.R.m), row j = rowL j hj := fun j hj => dif_pos hj
  have row_top : ∀ j (hj : j = D.R.m), row j = rowT j hj := fun j hj => by
    simp only [row, dif_neg (show ¬ j < D.R.m by omega), dif_pos hj]

  have hstep : ∀ j, j < D.R.m → ∃ Φ : ThS R.ψ (D.sp.Y (j + 1)) (D.sp.Y j), Φ ≠ 0 ∧
      ∀ y : D.what₂.Mult μ (j + 1), ∃ L : GA D (D.sp.Y j) → ℂ,
        (∀ g, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y (j + 1)) (κ (j + 1))
          (fun h => Wf.ker _ _ (if Even (j + 1) then R.toLevCh.mu t (j + 1) * R.eta⁻¹ else R.toLevCh.mu t (j + 1))
            (if Even j then R.toLevCh.mu t (j + 1) * R.eta⁻¹ else R.toLevCh.mu t (j + 1)) Φ h g * (row (j + 1) y).1 h) (L g)) ∧
        ∀ x : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (κ j) (fun g => star (L g) * (row j x).1 g)
          (inner ℂ (D.what₂.io μ j y) x) := by
    intro j hj
    obtain ⟨hS, hT⟩ := GlobalTheory.Mem.OneTuple.isHC_step R.toLevCh hL t j hj
    rw [row_low j hj]
    by_cases hA : j + 1 < D.R.m
    · rw [row_low (j + 1) hA]
      have hom := hC.ωY t j hA
      rw [GlobalTheory.Mem.OneTuple.chrStep_eq] at hom
      have hne : R.ptY t j (φ j) ≠ 0 := GlobalTheory.Mem.OneTuple.pt_ne_zero (hC.ItY t j hA)
        (by unfold RealDat.ptY; exact map_zero _) (v := PiTensorProduct.tprod ℂ (d (j + 1))) (fun h0 => by
          have := hφ j hA
          rw [h0, map_zero] at this
          exact zero_ne_one this)
      exact GlobalTheory.Mem.OneTuple.step hP hθ Wf (GlobalTheory.Mem.OneTuple.yc_eq D hj)
        (GlobalTheory.Mem.OneTuple.moves_castG (GlobalTheory.Mem.OneTuple.yc_eq D hA)) (hsigY _) (GlobalTheory.Mem.OneTuple.rank_lt D hj) hS hT hom
        (R.MY j) (R.MY (j + 1)) _ _ _ _ (R.CC t (j + 1)) le_rfl
        (GlobalTheory.Mem.Th.haar_chain hM.νY hM.νY' t (j + 1) hA) (H1 j hj).1 (hC.ptY t j hA)
        (hC.ioY t j (by omega)) (φ j) hne (d j) (hd j hj) (d (j + 1)) (hφ j hA)
        (D.what₂.io μ j) (e j) (e (j + 1)) (H1 j hj).2.1 (H4 j hA) (rowL j hj) (rowL (j + 1) hA)
        (hsL j hj) (hrL j hj) (hsL (j + 1) hA) (hκ j) (hκ (j + 1)) (hrowL j hj) (hpairL j hj) (hrowL (j + 1) hA)
    · obtain rfl : j = D.R.m - 1 := by omega
      rw [row_top (D.R.m - 1 + 1) (GlobalTheory.Mem.Th.pred_m_add_one D)]
      have hom := hC.ωX t
      have e1 : Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m = Lift.chrStep (R.toLevCh.mu t) R.eta (D.R.m - 1 + 1) := by
        rw [GlobalTheory.Mem.Th.pred_m_add_one]
      rw [e1, GlobalTheory.Mem.OneTuple.chrStep_eq] at hom
      have hne : R.ptX t φX ≠ 0 := GlobalTheory.Mem.OneTuple.pt_ne_zero (hC.ItX t)
        (by unfold RealDat.ptX; exact map_zero _) (v := PiTensorProduct.tprod ℂ dX) (fun h0 => by
          rw [h0, map_zero] at hφX
          exact zero_ne_one hφX)
      let eW : D.what₂.Mult μ (D.R.m - 1 + 1) →ₗ[ℂ] LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) :=
        eX ∘ₗ (famCast (D.what₂.Mult μ) (GlobalTheory.Mem.Th.pred_m_add_one D)).toLinearEquiv.toLinearMap
      exact GlobalTheory.Mem.OneTuple.step hP hθ Wf (GlobalTheory.Mem.OneTuple.yc_eq D hj)
        (hκT _ (GlobalTheory.Mem.Th.pred_m_add_one D)) (hsigY _) (GlobalTheory.Mem.OneTuple.rank_lt D hj) hS hT hom
        (R.MY (D.R.m - 1)) R.MX _ _ J χ _ hJ ⟨(hM.νX t).1.1, (hM.νX t).2⟩ (H1 _ hj).1 (hC.ptX t)
        (hC.ioX t) φX hne (d (D.R.m - 1)) (hd _ hj) dX hφX
        (D.what₂.io μ (D.R.m - 1)) (e (D.R.m - 1)) eW (H1 _ hj).2.1
        (fun x y => H5 x y _ (GlobalTheory.Mem.OneTuple.famCast_heq _ _ y)) (rowL _ hj) (rowT _ (GlobalTheory.Mem.Th.pred_m_add_one D))
        (hsL _ hj) (hrL _ hj) (hsT _ _) (hκ _) (hκ _) (hrowL _ hj) (hpairL _ hj) (hrowT _ _)
  choose PhiC hPhiC hL2 using hstep
  let Phi : ∀ j, ThS R.ψ (D.sp.Y (j + 1)) (D.sp.Y j) := fun j => if hj : j < D.R.m then PhiC j hj else 0
  refine ⟨row, Phi, fun j hj => ?_, fun j hj x y => ?_, fun j hj y => ?_⟩
  · simp only [Phi, dif_pos hj]
    exact hPhiC j hj
  · rcases hj.lt_or_eq with hj | hj
    · rw [row_low j hj]
      exact hisoL j hj x y
    · rw [row_top j hj]
      exact hisoT j hj x y
  · simp only [Phi, dif_pos hj]
    exact hL2 j hj y
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneTupleRowsCuspFormsIsometricThetaLiftsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneTuple_rows_cuspForms_isometric_thetaLifts : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsChain → ∀ (t : T) (μ : D.what₂.Tup), (∃ (e : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] R.CC t j) (eX : D.what₂.Mult μ D.R.m →ₗ[ℂ] LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) (ν : ∀ j, Measure (GA D (Yc D j))) (𝓕 : ∀ j, Set (GA D (Yc D j))) (c : ℕ → ℝ) (cX : ℝ), (∀ j, j < D.R.m → IsQuot (Yc D j) (ν j) (𝓕 j) ∧ 0 < c j ∧ ∀ x y, ⟪x, y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (e j y).1 (e j x).1) ∧ (∃ J χ, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) ≤ MultT R.θ R.MX J χ) ∧ 0 < cX ∧ (∀ x y, ⟪x, y⟫_ℂ = (cX : ℂ) * ipT R.MX (R.νX t) (R.fdX t) (eX y).1 (eX x).1) ∧ (∀ j, j + 1 < D.R.m → ∀ x y, ⟪x, D.what₂.io μ j y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (R.ioY t j (e (j + 1) y)).1 (e j x).1) ∧ ∀ x (y : D.what₂.Mult μ (D.R.m - 1 + 1)) (y' : D.what₂.Mult μ D.R.m), HEq y y' → ⟪x, D.what₂.io μ (D.R.m - 1) y⟫_ℂ = (c (D.R.m - 1) : ℂ) * ipT (R.MY (D.R.m - 1)) (ν (D.R.m - 1)) (𝓕 (D.R.m - 1)) (R.ioX t (eX y')).1 (e (D.R.m - 1) x).1) → ∀ (Wf : WeilFun D R.ψ) (κ : ℕ → ℝ), (∀ j, 0 < κ j) → ∃ (row : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] CuspS R.θ (D.sp.Y j)) (Phi : ∀ j, ThS R.ψ (D.sp.Y (j + 1)) (D.sp.Y j)), (∀ j, j < D.R.m → Phi j ≠ 0) ∧ (∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (κ j) (fun h => star ((row j x).1 h) * (row j y).1 h) (inner ℂ x y)) ∧ ∀ j, j < D.R.m → ∀ y : D.what₂.Mult μ (j + 1), ∃ L : GA D (D.sp.Y j) → ℂ, (∀ g, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y (j + 1)) (κ (j + 1)) (fun h => Wf.ker _ _ (if Even (j + 1) then R.toLevCh.mu t (j + 1) * R.eta⁻¹ else R.toLevCh.mu t (j + 1)) (if Even j then R.toLevCh.mu t (j + 1) * R.eta⁻¹ else R.toLevCh.mu t (j + 1)) (Phi j) h g * (row (j + 1) y).1 h) (L g)) ∧ ∀ x : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (κ j) (fun g => star (L g) * (row j x).1 g) (inner ℂ (D.what₂.io μ j y) x) := by
  first | exact @GlobalTheory.Mem.OneTuple.rows_theta | exact GlobalTheory.Mem.OneTuple.rows_theta | (intros; apply GlobalTheory.Mem.OneTuple.rows_theta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunctionLevelDataOfEqualTuplesZeroIntertwiners
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.Mem.RowsTies

theorem isQuotInt_zero {D : D7} (V : HSp D) (hV : V.SigOK) (c : ℝ) {φ : GA D V → ℂ} (h : ∀ g, φ g = 0) :
    GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V c φ 0 := by
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨μ, hμ, -⟩ := GlobalTheory.Mem.VolMeasure.existsUnique_isVolMeasG D V hV
  obtain ⟨-, 𝓕, h𝓕⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ hμ.1
  have e : φ = fun _ => 0 := funext h
  subst e
  exact ⟨⟨(μ, 𝓕), ⟨hμ, h𝓕⟩⟩, fun m _ => ⟨integrableOn_zero, by simp⟩⟩

theorem rows_of_ties : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsChain → ∀ (xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E) (U : Set D.what₂.Tup) (tupT : D.what₂.Tup → T), (∀ μ, ∃ n : ℕ, 0 < n ∧ (xi μ).OrderDvd n) → (∀ μ, (xi μ).TrivOn D.host.F) → (∀ μ ∈ U, R.xiH (tupT μ) = xi μ ∧ (∃ (e : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] R.CC (tupT μ) j) (eX : D.what₂.Mult μ D.R.m →ₗ[ℂ] LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e)) (ν : ∀ j, Measure (GA D (Yc D j))) (𝓕 : ∀ j, Set (GA D (Yc D j))) (c : ℕ → ℝ) (cX : ℝ), (∀ j, j < D.R.m → IsQuot (Yc D j) (ν j) (𝓕 j) ∧ 0 < c j ∧ ∀ x y, ⟪x, y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (e j y).1 (e j x).1) ∧ (∃ J χ, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e) ≤ MultT R.θ R.MX J χ) ∧ 0 < cX ∧ (∀ x y, ⟪x, y⟫_ℂ = (cX : ℂ) * ipT R.MX (R.νX (tupT μ)) (R.fdX (tupT μ)) (eX y).1 (eX x).1) ∧ (∀ j, j + 1 < D.R.m → ∀ x y, ⟪x, D.what₂.io μ j y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (R.ioY (tupT μ) j (e (j + 1) y)).1 (e j x).1) ∧ ∀ x (y : D.what₂.Mult μ (D.R.m - 1 + 1)) (y' : D.what₂.Mult μ D.R.m), HEq y y' → ⟪x, D.what₂.io μ (D.R.m - 1) y⟫_ℂ = (c (D.R.m - 1) : ℂ) * ipT (R.MY (D.R.m - 1)) (ν (D.R.m - 1)) (𝓕 (D.R.m - 1)) (R.ioX (tupT μ) (eX y')).1 (e (D.R.m - 1) x).1)) → (∀ μ, μ ∉ U → ∀ j, j < D.R.m → D.what₂.io μ j = 0) → (∀ θ : InfF D, IsInfFam θ → ∀ ψ, IsStdChar D ψ (-1) → ∀ Wf : WeilFun D ψ, ∃ Rc : RecFun D θ ψ, Rc.ChrIs R.C xi ∧ Rc.IoTie Wf ∧ ∀ μ ∈ U, ∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (Rc.mY μ j * Rc.petC (D.sp.Y j)) (fun h => star ((Rc.row μ j x).1 h) * (Rc.row μ j y).1 h) (inner ℂ x y)) := by
  intro hD D G _ _ Pl0 T A Ks _ _ _ R hL hM hC xi U tupT hf ht hU hoff θ hθ ψ hψ Wf
  obtain rfl : θ = R.θ := (GlobalTheory.Mem.InfFamUnique.existsUnique_infFam D).unique hθ hM.inf
  obtain rfl : ψ = R.ψ := (GlobalTheory.StdAdelicChar.existsUnique_isStdChar D (-1) (Or.inr rfl)).unique hψ (hC.ωX A.μ0).std
  obtain ⟨Rc, hR⟩ := RecFun.exists_chrIs R.C xi hf ht R.θ R.ψ
  have hu := (GlobalTheory.ChrEqUnique.chrEq_unique D).2.1
  have he : Rc.eta = R.eta := hu _ _ _ hR.eta hL.eta
  have key : ∀ μ, ∃ (row : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] CuspS R.θ (D.sp.Y j)) (Phi : ∀ j, ThS R.ψ (D.sp.Y (j + 1)) (D.sp.Y j)),
      (∀ j, j < D.R.m → Phi j ≠ 0) ∧
      (μ ∈ U → ∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j,
        GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (Rc.mY μ j * Rc.petC (D.sp.Y j))
          (fun h => star ((row j x).1 h) * (row j y).1 h) (inner ℂ x y)) ∧
      ∀ j, j < D.R.m → ∀ y : D.what₂.Mult μ (j + 1), ∃ L : GA D (D.sp.Y j) → ℂ,
        (∀ g, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y (j + 1)) (Rc.mY μ (j + 1) * Rc.petC (D.sp.Y (j + 1)))
          (fun h => Wf.ker _ _ (Rc.carY μ (j + 1) (j + 1)) (Rc.carY μ (j + 1) j) (Phi j) h g *
            (row (j + 1) y).1 h) (L g)) ∧
        ∀ x : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (Rc.mY μ j * Rc.petC (D.sp.Y j))
          (fun g => star (L g) * (row j x).1 g) (inner ℂ (D.what₂.io μ j y) x) := fun μ => by
    by_cases hμ : μ ∈ U
    · obtain ⟨hx, hT⟩ := hU μ hμ
      have hc : ∀ j, j < D.R.m → Rc.chr μ (j + 1) = R.toLevCh.mu (tupT μ) (j + 1) := fun j hj =>
        hu _ _ _ (hR.chr μ ⟨j, hj⟩) (hx ▸ GlobalTheory.Mem.TupChar.chrEq_mul (hL.mu0 ⟨j, hj⟩) (hL.xi (tupT μ)))
      obtain ⟨row, Phi, h1, h2, h3⟩ := GlobalTheory.T.oneTuple_rows_cuspForms_isometric_thetaLifts hD D G Pl0 T A Ks R hL hM hC (tupT μ) μ hT Wf
        (fun j => Rc.mY μ j * Rc.petC (D.sp.Y j)) fun j =>
          mul_pos (Rc.mY_pos _ _) (mul_pos (Rc.petF_pos _) (Finset.prod_pos fun _ _ => Rc.meas.petR_pos _ _))
      refine ⟨row, Phi, h1, fun _ => h2, fun j hj y => ?_⟩
      unfold RecFun.carY
      rw [hc j hj, he]
      exact h3 j hj y
    · refine ⟨0, Rc.Phi μ, Rc.Phi_ne hψ μ, fun h => absurd h hμ, fun j hj y => ⟨0, fun g => ?_, fun x => ?_⟩⟩
      · exact isQuotInt_zero _ (D.sp.Y_sig _) _ fun h => by simp
      · rw [hoff μ hμ j hj]
        simpa using isQuotInt_zero _ (D.sp.Y_sig _) _ fun h => by simp
  choose row Phi h1 h2 h3 using key
  exact ⟨{ Rc with row := row, Phi := Phi, Phi_ne := fun _ => h1 }, ⟨hR.chr, hR.eta⟩, h3, h2⟩

end GlobalTheory.Mem.RowsTies
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunctionLevelDataOfEqualTuplesZeroIntertwinersStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functionLevelData_of_equal_tuples_zero_intertwiners : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsChain → ∀ (xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E) (U : Set D.what₂.Tup) (tupT : D.what₂.Tup → T), (∀ μ, ∃ n : ℕ, 0 < n ∧ (xi μ).OrderDvd n) → (∀ μ, (xi μ).TrivOn D.host.F) → (∀ μ ∈ U, R.xiH (tupT μ) = xi μ ∧ (∃ (e : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] R.CC (tupT μ) j) (eX : D.what₂.Mult μ D.R.m →ₗ[ℂ] LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e)) (ν : ∀ j, Measure (GA D (Yc D j))) (𝓕 : ∀ j, Set (GA D (Yc D j))) (c : ℕ → ℝ) (cX : ℝ), (∀ j, j < D.R.m → IsQuot (Yc D j) (ν j) (𝓕 j) ∧ 0 < c j ∧ ∀ x y, ⟪x, y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (e j y).1 (e j x).1) ∧ (∃ J χ, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e) ≤ MultT R.θ R.MX J χ) ∧ 0 < cX ∧ (∀ x y, ⟪x, y⟫_ℂ = (cX : ℂ) * ipT R.MX (R.νX (tupT μ)) (R.fdX (tupT μ)) (eX y).1 (eX x).1) ∧ (∀ j, j + 1 < D.R.m → ∀ x y, ⟪x, D.what₂.io μ j y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (R.ioY (tupT μ) j (e (j + 1) y)).1 (e j x).1) ∧ ∀ x (y : D.what₂.Mult μ (D.R.m - 1 + 1)) (y' : D.what₂.Mult μ D.R.m), HEq y y' → ⟪x, D.what₂.io μ (D.R.m - 1) y⟫_ℂ = (c (D.R.m - 1) : ℂ) * ipT (R.MY (D.R.m - 1)) (ν (D.R.m - 1)) (𝓕 (D.R.m - 1)) (R.ioX (tupT μ) (eX y')).1 (e (D.R.m - 1) x).1)) → (∀ μ, μ ∉ U → ∀ j, j < D.R.m → D.what₂.io μ j = 0) → (∀ θ : InfF D, IsInfFam θ → ∀ ψ, IsStdChar D ψ (-1) → ∀ Wf : WeilFun D ψ, ∃ Rc : RecFun D θ ψ, Rc.ChrIs R.C xi ∧ Rc.IoTie Wf ∧ ∀ μ ∈ U, ∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (Rc.mY μ j * Rc.petC (D.sp.Y j)) (fun h => star ((Rc.row μ j x).1 h) * (Rc.row μ j y).1 h) (inner ℂ x y)) := by
  first | exact @GlobalTheory.Mem.RowsTies.rows_of_ties | exact GlobalTheory.Mem.RowsTies.rows_of_ties | (intros; apply GlobalTheory.Mem.RowsTies.rows_of_ties <;> assumption)
end
