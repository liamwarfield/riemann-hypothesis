module

public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.K2Hermitian
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DenseSplitFrobInvAway
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IteratedFDerivConstSmulOfNe
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleKernelEqSmulPullbackClassKernel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TaylorDirLinear
open Filter Topology

namespace GlobalTheory.PSerLin

theorem map_subst_linear {σ κ R S : Type*} [Finite σ] [Fintype κ] [CommRing R] [CommRing S]
    (h : R →+* S) (c : σ → κ → R) (F : MvPowerSeries σ R) :
    MvPowerSeries.map h (MvPowerSeries.subst
      (fun k => ∑ x, MvPowerSeries.C (c k x) * (MvPowerSeries.X x : MvPowerSeries κ R)) F) =
    MvPowerSeries.subst
      (fun k => ∑ x, MvPowerSeries.C (h (c k x)) * (MvPowerSeries.X x : MvPowerSeries κ S))
      (MvPowerSeries.map h F) := by
  rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp)]
  simp

open Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField


open Classical in
theorem taylorDir_linear (D : D7) {N N' : ℕ} (G : VC D N N' → ℂ)
    (c : D.what₂.Tau × Fin N' × Fin N → D.what₂.Tau × Fin N' × Fin N → ℂ)
    (hG : Differentiable ℂ G) :
    taylorDir (Formalism.MainNotions.TaylorLogMetric.coordV D) (fun z : VC D N N' => G (fun τ i j =>
      ∑ x : D.what₂.Tau × Fin N' × Fin N, c (τ, i, j) x * z x.1 x.2.1 x.2.2)) =
    MvPowerSeries.subst (fun k => ∑ x, MvPowerSeries.C (c k x) *
      (MvPowerSeries.X x : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ))
      (taylorDir (Formalism.MainNotions.TaylorLogMetric.coordV D) G) := by
  let L : (D.what₂.Tau × Fin N' × Fin N → ℂ) →L[ℂ] VC D N N' :=
    ContinuousLinearMap.pi fun τ => ContinuousLinearMap.pi fun a => ContinuousLinearMap.pi fun b =>
      ContinuousLinearMap.proj (τ, a, b)
  have hL : ∀ z τ a b, L z τ a b = z (τ, a, b) := fun _ _ _ _ => rfl
  have hc : Formalism.MainNotions.TaylorLogMetric.coordV D = fun k => L (Pi.single k 1) := by
    funext ⟨k1, k2, k3⟩ τ a b
    simp [hL, Formalism.MainNotions.TaylorLogMetric.coordV, Pi.single_apply]
  have han : AnalyticAt ℂ G 0 :=
    SCV.analyticAt_iff_eventually_differentiableAt.2 (Eventually.of_forall hG)
  have han' : AnalyticAt ℂ (fun z => G (L z)) 0 :=
    han.comp_of_eq (L.analyticAt 0) (map_zero L)
  let ev : (D.what₂.Tau × Fin N' × Fin N) → (VC D N N' →L[ℂ] ℂ) := fun x =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) x.2.2).comp
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N' => Fin N → ℂ) x.2.1).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : D.what₂.Tau => Fin N' → Fin N → ℂ) x.1))
  let ℓ : (D.what₂.Tau × Fin N' × Fin N) → (VC D N N' →L[ℂ] ℂ) := fun k => ∑ x, c k x • ev x
  have hℓ : ∀ k z, ℓ k z = ∑ x, c k x * z x.1 x.2.1 x.2.2 := fun k z => by
    simp [ℓ, ev]
  have h := taylorDir_comp (Formalism.MainNotions.TaylorLogMetric.coordV D) (φ := fun z k => ℓ k z)
    (analyticAt_pi_iff.2 fun k => (ℓ k).analyticAt 0) (funext fun k => map_zero (ℓ k)) han'
  rw [taylor_comp_clm L han, ← hc] at h
  convert h using 2
  · funext z
    refine congrArg G ?_
    funext τ i j
    exact (hℓ (τ, i, j) z).symm
  · funext k
    rw [show (fun z => ℓ k z) = ⇑(ℓ k) from rfl, taylorDir_clm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [MvPowerSeries.smul_eq_C_mul, hℓ, hc]
    simp [hL, Pi.single_apply]

end GlobalTheory.PSerLin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelScalarOfSourceTargetPartsProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTuplePairScalarEqCharacterProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PullbackContractionScalarsIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PullbackContractionScalarsIdentity
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem pullback_contraction_scalars : ∀ (m m' g g' k k' x x' A A' Δ Δ' : ℂ) (n n' c c' : ℤ), m ≠ 0 → m' ≠ 0 → g ≠ 0 → g' ≠ 0 → k ≠ 0 → k' ≠ 0 → x ≠ 0 → x' ≠ 0 → A ≠ 0 → A' ≠ 0 → Δ ≠ 0 → Δ' ≠ 0 → (g' * m' * k') * (g * m * k)⁻¹ * (Δ⁻¹ * A) ^ (-c) * (Δ'⁻¹ * A') ^ c' * ((Δ⁻¹ * A) ^ n' * (Δ'⁻¹ * A') ^ (-n))⁻¹ * (k * x' / (k' * x)) = (m⁻¹ * A ^ (-n')) * (m' * A' ^ n) * (x⁻¹ * g⁻¹ * Δ ^ (n' + c) * A ^ (-c)) * (x' * g' * Δ' ^ (-(n + c')) * A' ^ c') := by
  intro m m' g g' k k' x x' A A' Δ Δ' n n' c c' hm hm' hg hg' hk hk' hx hx' hA hA' hΔ hΔ'
  simp only [mul_zpow, inv_zpow', zpow_neg, zpow_add₀ hΔ, zpow_add₀ hΔ', zpow_add₀ hA, zpow_add₀ hA', neg_add, mul_inv, inv_inv, div_eq_mul_inv]
  field_simp

end GlobalTheory.TwV.DelB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PullbackContractionScalarsIdentityStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_contraction_scalars_identity : ∀ (m m' g g' k k' x x' A A' Δ Δ' : ℂ) (n n' c c' : ℤ), m ≠ 0 → m' ≠ 0 → g ≠ 0 → g' ≠ 0 → k ≠ 0 → k' ≠ 0 → x ≠ 0 → x' ≠ 0 → A ≠ 0 → A' ≠ 0 → Δ ≠ 0 → Δ' ≠ 0 → (g' * m' * k') * (g * m * k)⁻¹ * (Δ⁻¹ * A) ^ (-c) * (Δ'⁻¹ * A') ^ c' * ((Δ⁻¹ * A) ^ n' * (Δ'⁻¹ * A') ^ (-n))⁻¹ * (k * x' / (k' * x)) = (m⁻¹ * A ^ (-n')) * (m' * A' ^ n) * (x⁻¹ * g⁻¹ * Δ ^ (n' + c) * A ^ (-c)) * (x' * g' * Δ' ^ (-(n + c')) * A' ^ c') := by
  first | exact @GlobalTheory.TwV.DelB.pullback_contraction_scalars | exact GlobalTheory.TwV.DelB.pullback_contraction_scalars | (intros; apply GlobalTheory.TwV.DelB.pullback_contraction_scalars <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacterDetIdealKernelLatticeLatticeTuple
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeterminantIdealCharacterClassLatticeEq
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeterminantIdealCharacterClassLatticeEq
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem chi_detId_lat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => (∀ (N : ℕ) (M M' : SDLat D.host.E N), ∀ g ∈ Formalism.L2.Herm.UstdAf D.sp.cm N, Formalism.L2.Herm.Carries g M.1 M'.1 → ∀ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Formalism.L2.Herm.IsDetOf D.sp.cm y g → D.relDet N M M' = QuotientGroup.mk (dtU y)) → (∀ i hi β, latCo D.sp (gramN D i hi) (A.crd i hi) a 1 ((St i hi).K β).lev.Lb = StandardLatticesGL3.stdL D (D.R.N i)) → ∀ i (hi : i ≤ D.R.m) c, t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (t.seam.lat ((t.rd u μ).N i c))) = ((D.chiD ((t.O u μ).dt i c) : ℂˣ) : ℂ)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ _ _ _ i hi c
  rw [← t.O_lat, t.χ_rec, ← Formalism.L2.Ker.initial_lattice_eq_standard (t.O u μ) i, ← t.idl_ok.2.2.2.2 _ ((t.O u μ).L0 i) ((t.O u μ).lat i c),
    ← (t.O u μ).dt_lat, TaylorLogMetric.chiRec_idl D t.idl t.idl_ok.1]
  rfl

end GlobalTheory.TwV
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeterminantIdealCharacterClassLatticeEqStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinantIdealCharacter_classLattice_eq : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => (∀ (N : ℕ) (M M' : SDLat D.host.E N), ∀ g ∈ Formalism.L2.Herm.UstdAf D.sp.cm N, Formalism.L2.Herm.Carries g M.1 M'.1 → ∀ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Formalism.L2.Herm.IsDetOf D.sp.cm y g → D.relDet N M M' = QuotientGroup.mk (dtU y)) → (∀ i hi β, latCo D.sp (gramN D i hi) (A.crd i hi) a 1 ((St i hi).K β).lev.Lb = StandardLatticesGL3.stdL D (D.R.N i)) → ∀ i (hi : i ≤ D.R.m) c, t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (t.seam.lat ((t.rd u μ).N i c))) = ((D.chiD ((t.O u μ).dt i c) : ℂˣ) : ℂ)) := by
  first | exact @GlobalTheory.TwV.chi_detId_lat | exact GlobalTheory.TwV.chi_detId_lat | (intros; apply GlobalTheory.TwV.chi_detId_lat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacterDetIdealKernelLatticeLatticeTuple
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem detId_stdL_heq (D : D7) {n n' : ℕ} (h : n = n') {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin n' → D.host.E)} (hL : HEq L L') :
    TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) L = TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n') L' := by
  subst h
  cases hL
  rfl

theorem chi_detId_kerN : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ (d : Dec J std) j (hj : j ≤ D.R.m) (La : (sysS H X std).Lt j), ((sysS H X std).Pj j).IsLatTup La.2 → t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN j La)) = (∏ τ, TaylorLogMetric.embT D τ (gMat J j hj (d.gam j hj La)).det)⁻¹ * ((D.chiD ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) ∧ (∏ τ, TaylorLogMetric.embT D τ (gMat J j hj (d.gam j hj La)).det) ≠ 0) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD d j hj La hLa
  obtain ⟨⟨hr, -⟩, -, hK, -⟩ := hD j hj La hLa
  have hlat := GlobalTheory.T.kernelLattice_translate_eq_image_classLattice J.A J.dtU J.a J.pins J.tie j hj (clsAt X H j La.1 La.2) (J.pt std j hj La)
    (d.gam j hj La) (d.mem j hj La) (d.kap j hj La) (d.eq j hj La hLa)
  have hU : gMat J j hj (d.gam j hj La) * star (gMat J j hj (d.gam j hj La)) = 1 :=
    GlobalTheory.T.rationalIsometry_orthonormal_matrix_unitary J.A J.dtU J.a J.pins J.tie j hj (d.gam j hj La) (d.mem j hj La)
  have hcl := GlobalTheory.T.determinantIdealCharacter_classLattice_eq J.A J.dtU J.a J.pins J.tie J.rel J.base j hj (clsAt X H j La.1 La.2)
  have hmv := GlobalTheory.T.char_determinantIdeal_unitary_smul_selfDual D t.χ t.χ_ok ((t.O u μ).lat j (clsAt X H j La.1 La.2)) (gMat J j hj (d.gam j hj La)) hU
  rw [t.O_lat] at hmv
  have h1 := detId_stdL_heq D hr hK
  refine ⟨?_, ?_⟩
  · rw [h1]
    have : latK D.sp (gramN D j hj) J.a (J.pt std j hj La).1 ((J.St j hj).K (J.chart std j hj La)).lev.Lb =
        SDLat.smulLat (gMat J j hj (d.gam j hj La)) (t.seam.lat ((t.rd u μ).N j (clsAt X H j La.1 La.2))) := hlat
    rw [this, hmv, hcl]
  · have hdet : (gMat J j hj (d.gam j hj La)).det ≠ 0 := by
      intro h0
      have := congrArg Matrix.det hU
      rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
      exact zero_ne_one this
    exact Finset.prod_ne_zero_iff.mpr fun τ _ => (map_ne_zero (TaylorLogMetric.embT D τ)).mpr hdet

end GlobalTheory.TwV.DelB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacterDetIdealKernelLatticeLatticeTupleStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_detIdeal_kernelLattice_latticeTuple : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ (d : Dec J std) j (hj : j ≤ D.R.m) (La : (sysS H X std).Lt j), ((sysS H X std).Pj j).IsLatTup La.2 → t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN j La)) = (∏ τ, TaylorLogMetric.embT D τ (gMat J j hj (d.gam j hj La)).det)⁻¹ * ((D.chiD ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) ∧ (∏ τ, TaylorLogMetric.embT D τ (gMat J j hj (d.gam j hj La)).det) ≠ 0) := by
  first | exact @GlobalTheory.TwV.DelB.chi_detId_kerN | exact GlobalTheory.TwV.DelB.chi_detId_kerN | (intros; apply GlobalTheory.TwV.DelB.chi_detId_kerN <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTuplePairScalarEqCharacterProduct
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB


set_option maxHeartbeats 1000000 in
theorem scalAt_all : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ (d : Dec J std), ∀ j < D.R.m, d.ScalAt S j) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD d j hj La La' hLa hLa'
  obtain ⟨hmm, ht, hN, -⟩ := GlobalTheory.T.siteSystem_ranks_eq_datum_ranks S
  have hj0 : j ≤ D.R.m := hj.le
  have hj1 : j + 1 ≤ D.R.m := hj
  have hdt0 := (hD j hj0 La hLa).2.2.2
  have hdt1 := (hD (j+1) hj1 La' hLa').2.2.2
  have e0 := d.eq j hj0 La hLa
  have e1 := d.eq (j+1) hj1 La' hLa'
  have M0 := GlobalTheory.T.adelicCharacters_at_det_rational_isometry_rep_level J.A J.dtU J.a J.pins J.tie S.Xi S.muT S.law j hj j hj0 (clsAt X H j La.1 La.2) (J.pt std j hj0 La) (d.gam j hj0 La) (d.mem j hj0 La) (d.kap j hj0 La) e0
  have M1 := GlobalTheory.T.adelicCharacters_at_det_rational_isometry_rep_level J.A J.dtU J.a J.pins J.tie S.Xi S.muT S.law j hj (j+1) hj1 (clsAt X H (j+1) La'.1 La'.2) (J.pt std (j+1) hj1 La') (d.gam (j+1) hj1 La') (d.mem (j+1) hj1 La') (d.kap (j+1) hj1 La') e1
  have C0 := GlobalTheory.T.character_detIdeal_kernelLattice_latticeTuple S hD d j hj0 La hLa
  have C1 := GlobalTheory.T.character_detIdeal_kernelLattice_latticeTuple S hD d (j+1) hj1 La' hLa'
  have eN0 : (((sysS H X std).Pj j).m + 1) / 2 = D.R.N j / 2 := by rw [hN]
  have eN1 : (((sysS H X std).Pj (j + 1)).m + 1) / 2 = D.R.N (j + 1) / 2 := by rw [hN]
  have R0 : ((GL3Theta.rhoOf D (t.O u μ).mt j ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) =
      (((t.O u μ).mt (j + 1) ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ)⁻¹ *
        ((D.chiD ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) ^ (-(((D.R.N (j + 1) / 2 : ℕ) : ℤ))) := by
    simp [GL3Theta.rhoOf]
  have R1 : ((GL3Theta.rhoOf' D (t.O u μ).mt j ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) La'.1 La'.2)) : ℂˣ) : ℂ) =
      (((t.O u μ).mt (j + 1) ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) La'.1 La'.2)) : ℂˣ) : ℂ) *
        ((D.chiD ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) La'.1 La'.2)) : ℂˣ) : ℂ) ^ ((((D.R.N j / 2 : ℕ) : ℤ))) := by
    simp [GL3Theta.rhoOf']
  simp only [Dec.sC, Dec.sP, Dec.uS, Dec.uT, scal0, Base.chiFac, dif_pos hj1, dif_pos hj0]
  rw [R0, R1, hdt0, hdt1, M0.1, M1.1, C0.1, C1.1, eN0, eN1, ht]
  exact GlobalTheory.T.pullback_contraction_scalars_identity _ _ _ _ _ _ _ _ _ _ _ _ _ _ (cTw D j) (cTw D (j + 1)) (Units.ne_zero _) (Units.ne_zero _) M0.2.1 M1.2.1 M0.2.2 M1.2.2
    (Units.ne_zero _) (Units.ne_zero _) (Units.ne_zero _) (Units.ne_zero _) C0.2 C1.2

end GlobalTheory.TwV.DelB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTuplePairScalarEqCharacterProductStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeTuplePairScalar_eq_characterProduct : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ (d : Dec J std), ∀ j < D.R.m, d.ScalAt S j) := by
  first | exact @GlobalTheory.TwV.DelB.scalAt_all | exact GlobalTheory.TwV.DelB.scalAt_all | (intros; apply GlobalTheory.TwV.DelB.scalAt_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrameFactorsCancelPPowerOfPairSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrameFactorsCancelPPowerOfPairSeries
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem eFac_mul_pPow : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) (g : GL3Theta.G1 p) (hLT : LTIso g) (T : Type) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T) (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)), E.iK ((pendT X E hfin hst hLT pos F).eS j La * ((pendT X E hfin hst hLT pos F).eT j La')⁻¹) * pPow X j La La' = 1 := by
  intro p _ X _ E hfin hst g hLT T pos F j La La'
  have hp : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  show E.iK (Pend.eS _ j La * (Pend.eT _ j La')⁻¹) * pPow X j La La' = 1
  simp only [Pend.eS, Pend.eT]
  rw [pPow_eq_prod]
  rw [map_mul, map_inv₀, map_prod, map_prod]
  simp only [map_zpow₀, map_natCast]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one (fun v _ => ?_)
  rw [← zpow_neg, ← zpow_add₀ hp, ← zpow_add₀ hp]
  show (p : ℂ_[p]) ^ _ = 1
  ring_nf
  simp

end GlobalTheory.TwV.DelB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrameFactorsCancelPPowerOfPairSeriesStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameFactors_cancel_p_power_of_pair_series : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) (g : GL3Theta.G1 p) (hLT : LTIso g) (T : Type) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T) (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)), E.iK ((pendT X E hfin hst hLT pos F).eS j La * ((pendT X E hfin hst hLT pos F).eT j La')⁻¹) * pPow X j La La' = 1 := by
  first | exact @GlobalTheory.TwV.DelB.eFac_mul_pPow | exact GlobalTheory.TwV.DelB.eFac_mul_pPow | (intros; apply GlobalTheory.TwV.DelB.eFac_mul_pPow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelScalarOfSourceTargetPartsProduct
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem tieChiH_of_parts : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ (d : Dec J std) (ι : ℂ →+* ℂ_[D.what₂.places.resChar w]), ∀ j < D.R.m, ∀ (cB : ∀ j, (sysS H X std).Lt j → ℂ_[D.what₂.places.resChar w]) (sc : ∀ j, (sysS H X std).Lv.comp (j + 1) → ((sysS H X std).Pj (j + 1)).Tup → ℂ_[D.what₂.places.resChar w]) (cK : ℂ_[D.what₂.places.resChar w]), (∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → cK * cB j La * ι (d.uS S j La) * ι (d.uT S j La') = sc j La'.1 La'.2) → TieChiH S.Y t u μ (clsAt X H) (fun j => clsAt X H (j + 1)) ι sc (d.sH S ι) cB j cK) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD d ι j hj cB sc cK hsc La hLa c' L' hL'
  have hLat := S.Y.Rep_lat j La hLa
  have hsC := GlobalTheory.T.latticeTuplePairScalar_eq_characterProduct S hD d j hj La (c', L') hLat hL'
  have he := GlobalTheory.T.frameFactors_cancel_p_power_of_pair_series _ (sysS H X std) S.E S.hfin S.hst S.g S.hLT D.what₂.Tau (hT.gat_pos u w hg)
    (FrecG S.E.toCEmb (hT.gat_pos u w hg) (J.fd std) t.B t.χ S.lam (ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT (ltC S.g S.hLT)) j La (c', L')
  have h2 := hsc La (c', L') hLat hL'
  show cK * S.E.iK (S.Y.eS j La * (S.Y.eT j (c', L'))⁻¹) * cB j La * (pPow (sysS H X std) j La (c', L') * ι (d.sC S j La (c', L'))) = _
  rw [hsC]
  have hι : ∀ x y : ℂ, ι (x * y) = ι x * ι y := map_mul ι
  simp only [hι]
  linear_combination (cK * cB j La * ι (d.uS S j La) * ι (d.uT S j (c', L')) *
      ι ((GL3Theta.rhoOf D (t.O u μ).mt j ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) *
      ι ((GL3Theta.rhoOf' D (t.O u μ).mt j ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) c' L')) : ℂˣ) : ℂ)) * he +
    ι ((GL3Theta.rhoOf D (t.O u μ).mt j ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) *
      ι ((GL3Theta.rhoOf' D (t.O u μ).mt j ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) c' L')) : ℂˣ) : ℂ) * h2

end GlobalTheory.TwV.DelB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelScalarOfSourceTargetPartsProductStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelScalar_of_sourceTarget_parts_product : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ (d : Dec J std) (ι : ℂ →+* ℂ_[D.what₂.places.resChar w]), ∀ j < D.R.m, ∀ (cB : ∀ j, (sysS H X std).Lt j → ℂ_[D.what₂.places.resChar w]) (sc : ∀ j, (sysS H X std).Lv.comp (j + 1) → ((sysS H X std).Pj (j + 1)).Tup → ℂ_[D.what₂.places.resChar w]) (cK : ℂ_[D.what₂.places.resChar w]), (∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → cK * cB j La * ι (d.uS S j La) * ι (d.uT S j La') = sc j La'.1 La'.2) → TieChiH S.Y t u μ (clsAt X H) (fun j => clsAt X H (j + 1)) ι sc (d.sH S ι) cB j cK) := by
  first | exact @GlobalTheory.TwV.DelB.tieChiH_of_parts | exact GlobalTheory.TwV.DelB.tieChiH_of_parts | (intros; apply GlobalTheory.TwV.DelB.tieChiH_of_parts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSeriesSiteEqChangedFrameClassSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSeriesPairOfPullbackKernelFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PullbackThenFrameSubstitutionEqChangedFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PullbackThenFrameSubstitutionEqChangedFrames
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelB

theorem sum_pullMat_subBG_reframe : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (E : CEmb X.G) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ →+* ℂ_[p]), (∀ z : TaylorLogMetric.Qbar, ι z = lam z) → ∀ (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), LamPos X E pos lam ρ → ∀ (e : ∀ j, X.Lt j → Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E) (c : ℂ_[p]) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)), e j La * star (e j La) = 1 → e (j + 1) La' * star (e (j + 1) La') = 1 → (∀ v, IsUnit (fd.frM j La v).det ∧ IsUnit (fd.frM (j + 1) La' v).det) → ∀ x y, ∑ z, ι (pullMat (e j La) (e (j + 1) La') x z) * (c * subBG E pos fd j La La' z y) = c * subBG E pos (reframe fd ρ e) j La La' x y := by
  intro D p _ X E pos fd lam ι hι ρ hL e c j La La' he he' hdet x y
  classical
  have hs : ∀ q : D.host.E, star q = D.host.conj q := Formalism.BasicNotions.bridge_star_holds D.R D.host
  have hcc : ∀ q : D.host.E, D.host.conj (D.host.conj q) = q := fun q => D.host.φ₀.injective (by
    rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply, Complex.conj_conj])
  have hconj : ∀ τ q, TaylorLogMetric.embT D τ (D.host.conj q) = (starRingEnd ℂ) (TaylorLogMetric.embT D τ q) := fun τ q =>
    D.host.conjE_apply (TaylorLogMetric.embT D τ) q
  have hιe : ∀ τ q, ι (TaylorLogMetric.embT D τ q) = twG X E (pos.symm τ).1 (pos.symm τ).2
      (ρ _ (if IsOddPos (pos.symm τ).2 then D.host.conj q else q)) := by
    intro τ q
    have halg : TaylorLogMetric.embT D τ q ∈ TaylorLogMetric.Qbar := mem_algebraicClosure_iff.2
      ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) q).algHom (TaylorLogMetric.embT D τ).toRatAlgHom)
    have h2 := hL (pos.symm τ).1 (pos.symm τ).2 q
    simp only [Sigma.eta, Equiv.apply_symm_apply] at h2
    rw [← h2]; unfold TaylorLogMetric.lamC; rw [dite_eq_left halg]; exact hι ⟨_, halg⟩
  have hinv : ∀ {n : ℕ} (v : X.Pl) (A : Matrix (Fin n) (Fin n) D.host.E) (M : Matrix (Fin n) (Fin n) (X.G.P.Qq v)),
      A * star A = 1 → ((star A).map (ρ v) * M)⁻¹ = M⁻¹ * A.map (ρ v) := by
    intro n v A M h
    rw [Matrix.mul_inv_rev]
    congr 1
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero (ρ v)) (map_one (ρ v))]
  obtain ⟨τ, b0, a0⟩ := x
  obtain ⟨τ', b1, a1⟩ := y
  by_cases hxy : τ = τ'
  · subst hxy
    rw [Fintype.sum_prod_type, Finset.sum_eq_single τ]
    · rw [Fintype.sum_prod_type]
      simp only [subBG, reframe, pullMat, ↓reduceIte]
      rw [hinv _ _ _ he, hinv _ _ _ he']
      by_cases hodd : IsOddPos (pos.symm τ).2
      set_option synthInstance.maxHeartbeats 100000 in
        · simp only [hodd, ↓reduceIte, map_mul, ← hconj, hιe, Matrix.map_apply, Matrix.mul_apply,
          Matrix.star_apply, hs, map_sum, hcc, Finset.mul_sum, Finset.sum_mul]
          first
            | exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
            | (rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
      set_option synthInstance.maxHeartbeats 100000 in
        · simp only [hodd, ↓reduceIte, map_mul, ← hconj, hιe, Matrix.map_apply, Matrix.mul_apply,
          Matrix.star_apply, hs, map_sum, hcc, Finset.mul_sum, Finset.sum_mul]
          first
            | exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
            | (rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
    · intro τ'' _ hne
      apply Finset.sum_eq_zero
      intro z _
      simp [pullMat, Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [show subBG E pos (reframe fd ρ e) j La La' (τ, b0, a0) (τ', b1, a1) = 0 from if_neg hxy, mul_zero]
    apply Finset.sum_eq_zero
    intro z _
    by_cases h1 : τ = z.1
    · have h2 : z.1 ≠ τ' := fun h => hxy (h1.trans h)
      rw [show subBG E pos fd j La La' z (τ', b1, a1) = 0 from if_neg h2, mul_zero, mul_zero]
    · rw [show pullMat (e j La) (e (j + 1) La') (τ, b0, a0) z = 0 from if_neg h1, map_zero, zero_mul]

end GlobalTheory.TwV.DelB
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PullbackThenFrameSubstitutionEqChangedFramesStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_then_frame_substitution_eq_changed_frames : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (E : CEmb X.G) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ →+* ℂ_[p]), (∀ z : TaylorLogMetric.Qbar, ι z = lam z) → ∀ (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), LamPos X E pos lam ρ → ∀ (e : ∀ j, X.Lt j → Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E) (c : ℂ_[p]) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)), e j La * star (e j La) = 1 → e (j + 1) La' * star (e (j + 1) La') = 1 → (∀ v, IsUnit (fd.frM j La v).det ∧ IsUnit (fd.frM (j + 1) La' v).det) → ∀ x y, ∑ z, ι (pullMat (e j La) (e (j + 1) La') x z) * (c * subBG E pos fd j La La' z y) = c * subBG E pos (reframe fd ρ e) j La La' x y := by
  first | exact @GlobalTheory.TwV.DelB.sum_pullMat_subBG_reframe | exact GlobalTheory.TwV.DelB.sum_pullMat_subBG_reframe | (intros; apply GlobalTheory.TwV.DelB.sum_pullMat_subBG_reframe <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DifferentiableOfUnitaryMatrixPullbackDifferentia
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DifferentiableOfUnitaryMatrixPullbackDifferentia
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwU.XbEntire

theorem entire_of_pull : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a b : ℕ} (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E) (Θ K : TaylorLogMetric.VC D a b → ℂ) (s : ℂ), e * star e = 1 → e' * star e' = 1 → s ≠ 0 → Differentiable ℂ K → (∀ z, K z = s * TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) e e' Θ z) → Differentiable ℂ Θ := by
  intro D cc δ a b e e' Θ K s he he' hs hK hKΘ
  have hinv : ∀ z, Θ z = s⁻¹ * K (Formalism.L2.KerInert.PullbackComparison.tPullL cc δ (star e) (star e') z) := by
    intro z
    rw [hKΘ, ← mul_assoc, inv_mul_cancel₀ hs, one_mul, Formalism.L2.KerInert.PullbackComparison.tPullL_apply]
    show Θ z = Θ (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) e e'
      (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) (star e) (star e') z))
    rw [GlobalTheory.TwU.KerMove.tPull_tPull, mul_eq_one_comm.1 he, mul_eq_one_comm.1 he', GlobalTheory.TwU.KerMove.tPull_one]
  have hf : Θ = fun z => s⁻¹ * K (Formalism.L2.KerInert.PullbackComparison.tPullL cc δ (star e) (star e') z) := funext hinv
  rw [hf]
  exact ((hK.comp (Formalism.L2.KerInert.PullbackComparison.tPullL cc δ (star e) (star e')).differentiable).const_mul _)

end GlobalTheory.TwU.XbEntire
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DifferentiableOfUnitaryMatrixPullbackDifferentiaStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiable_of_unitary_matrixPullback_differentiable : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a b : ℕ} (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E) (Θ K : TaylorLogMetric.VC D a b → ℂ) (s : ℂ), e * star e = 1 → e' * star e' = 1 → s ≠ 0 → Differentiable ℂ K → (∀ z, K z = s * TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) e e' Θ z) → Differentiable ℂ Θ := by
  first | exact @GlobalTheory.TwU.XbEntire.entire_of_pull | exact GlobalTheory.TwU.XbEntire.entire_of_pull | (intros; apply GlobalTheory.TwU.XbEntire.entire_of_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicSeriesAlgebraicMultipleViaPlaceExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicSeriesAlgebraicMultipleViaPlaceExtension
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.SerMap

theorem iteratedFDeriv_smul_of_ne {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] (c : ℂ) (hc : c ≠ 0) (f : E → F) (n : ℕ) :
    iteratedFDeriv ℂ n (fun y => c • f y) = c • iteratedFDeriv ℂ n f := by
  let _ : Invertible c := invertibleOfNonzero hc
  induction n with
  | zero =>
    ext x m
    simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left, ih]
    funext x
    simp only [Function.comp_apply]
    rw [fderiv_const_smul_of_invertible c, map_smul]
    rfl

theorem taylor_mul (D : D7) {N N' : ℕ} (c : ℂ) (G : TaylorLogMetric.VC D N N' → ℂ) (α : TaylorLogMetric.Mono D N N') :
    TaylorLogMetric.taylor D (fun z => c * G z) α = c * TaylorLogMetric.taylor D G α := by
  by_cases hc : c = 0
  · subst hc
    simp only [zero_mul]
    unfold TaylorLogMetric.taylor
    simp
  · unfold TaylorLogMetric.taylor
    have h := iteratedFDeriv_smul_of_ne c hc G (Multiset.card α.toMultiset)
    simp only [smul_eq_mul] at h
    rw [h, Pi.smul_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_div_assoc]

theorem padicSeries_const_mul : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ →+* ℂ_[p]),
    (∀ z : TaylorLogMetric.Qbar, ι z = lam z) → ∀ {a b : ℕ} (K G : TaylorLogMetric.VC D a b → ℂ) (s s' : ℂ), s ∈ TaylorLogMetric.Qbar →
    TaylorLogMetric.CoefIn D K TaylorLogMetric.Qbar → (∀ z, K z = s' * G z) →
    serP lam (fun z => s * K z) = ι (s * s') • MvPowerSeries.map ι (tay G) := by
  intro D p _ lam ι hι a b K G s s' hs hK hKG
  ext α
  have hKt : TaylorLogMetric.taylor D K α = s' * TaylorLogMetric.taylor D G α := by
    have : K = fun z => s' * G z := funext hKG
    rw [this, taylor_mul]
  have hmem : s * TaylorLogMetric.taylor D K α ∈ TaylorLogMetric.Qbar := TaylorLogMetric.Qbar.mul_mem hs (hK α)
  show TaylorLogMetric.lamC lam (TaylorLogMetric.taylor D (fun z => s * K z) α) = _
  rw [taylor_mul, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_map]
  unfold TaylorLogMetric.lamC
  rw [dite_eq_left hmem, ← hι ⟨_, hmem⟩]
  show ι (s * TaylorLogMetric.taylor D K α) = _
  rw [hKt, ← mul_assoc, map_mul]
  rfl

end GlobalTheory.TwV.SerMap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicSeriesAlgebraicMultipleViaPlaceExtensionStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicSeries_algebraic_multiple_via_place_extension : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ →+* ℂ_[p]), (∀ z : TaylorLogMetric.Qbar, ι z = lam z) → ∀ {a b : ℕ} (K G : TaylorLogMetric.VC D a b → ℂ) (s s' : ℂ), s ∈ TaylorLogMetric.Qbar → TaylorLogMetric.CoefIn D K TaylorLogMetric.Qbar → (∀ z, K z = s' * G z) → serP lam (fun z => s * K z) = ι (s * s') • MvPowerSeries.map ι (tay G) := by
  first | exact @GlobalTheory.TwV.SerMap.padicSeries_const_mul | exact GlobalTheory.TwV.SerMap.padicSeries_const_mul | (intros; apply GlobalTheory.TwV.SerMap.padicSeries_const_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TaylorSeriesMatrixPullbackEqLinearSubstitution
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TaylorSeriesMatrixPullbackEqLinearSubstitution
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem pull_eq_linear (D : D7) (T : TaylorLogMetric.Tor D) (hT : ∀ τ, T.emb τ = TaylorLogMetric.embT D τ) {a b : ℕ}
    (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E) (Θ : TaylorLogMetric.VC D a b → ℂ) :
    TaylorLogMetric.pull D T e e' Θ = fun z => Θ (fun τ i j =>
      ∑ x : D.what₂.Tau × Fin b × Fin a, pullMat e e' (τ, i, j) x * z x.1 x.2.1 x.2.2) := by
  funext z
  unfold TaylorLogMetric.pull
  congr 1
  funext τ i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.of_apply, hT,
    Fintype.sum_prod_type, pullMat]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [Fintype.sum_eq_single τ (fun x hx => by simp [Ne.symm hx])]
  simp only [if_true]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [← Complex.star_def]
  ring

end GlobalTheory.TwV.DelB

namespace GlobalTheory.TwV.DelB

theorem tay_eq_taylorDir (D : D7) {a b : ℕ} (G : TaylorLogMetric.VC D a b → ℂ) :
    tay G = taylorDir (Formalism.MainNotions.TaylorLogMetric.coordV D) G := by
  ext α
  exact GlobalTheory.ConjSeries.taylor_eq_coeff D G α

theorem tay_pull_linSub : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a b : ℕ} (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E) (Θ : TaylorLogMetric.VC D a b → ℂ), Differentiable ℂ Θ → tay (TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) e e' Θ) = linSub (pullMat e e') (tay Θ) := by
  intro D cc δ a b e e' Θ hΘ
  rw [pull_eq_linear D (TaylorLogMetric.tor0 D cc δ) (fun _ => rfl) e e' Θ, tay_eq_taylorDir, tay_eq_taylorDir, linSub]
  exact GlobalTheory.PSerLin.taylorDir_linear D Θ (pullMat e e') hΘ

end GlobalTheory.TwV.DelB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TaylorSeriesMatrixPullbackEqLinearSubstitutionStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylorSeries_matrixPullback_eq_linear_substitution : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a b : ℕ} (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E) (Θ : TaylorLogMetric.VC D a b → ℂ), Differentiable ℂ Θ → tay (TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) e e' Θ) = linSub (pullMat e e') (tay Θ) := by
  first | exact @GlobalTheory.TwV.DelB.tay_pull_linSub | exact GlobalTheory.TwV.DelB.tay_pull_linSub | (intros; apply GlobalTheory.TwV.DelB.tay_pull_linSub <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSeriesPairOfPullbackKernelFunction
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TwV.DelB

theorem linSub_smul' {σ R : Type} [Fintype σ] [CommRing R] (B : σ → σ → R) (a : R) (f : MvPowerSeries σ R) :
    linSub B (a • f) = a • linSub B f := by
  rw [MvPowerSeries.smul_eq_C_mul, MvPowerSeries.smul_eq_C_mul, GlobalTheory.TwU.LawAll.linSub_C_mul']

theorem map_linSub' {σ R S : Type} [Fintype σ] [CommRing R] [CommRing S] (h : R →+* S) (B : σ → σ → R)
    (f : MvPowerSeries σ R) :
    MvPowerSeries.map h (linSub B f) = linSub (fun x y => h (B x y)) (MvPowerSeries.map h f) := by
  unfold linSub
  exact GlobalTheory.PSerLin.map_subst_linear h B f

theorem frecG_pull : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (E : CEmb X.G) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ →+* ℂ_[p]), (∀ z : TaylorLogMetric.Qbar, ι z = lam z) → ∀ (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), LamPos X E pos lam ρ → ∀ (e : ∀ j, X.Lt j → Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E) (c : ℂ_[p]) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)), e j La * star (e j La) = 1 → e (j + 1) La' * star (e (j + 1) La') = 1 → ∀ {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ) (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ), PairOK X fd B χ SS cl Ξ₀ muT ρ → j < X.mm → (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 → ∀ (s : ℂ) (Θ : TaylorLogMetric.VC D ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ), s ≠ 0 → (∀ z, kerTh B χ SS cl (fd.kerN j La) (fd.kerN (j + 1) La') (xiM X fd Ξ₀ j La La') z = s * TaylorLogMetric.pull D B.tor (e j La) (e (j + 1) La') Θ z) → FrecG E pos fd B χ lam SS cl Ξ₀ muT c j La La' = linSub (fun x y => c * subBG E pos (reframe fd ρ e) j La La' x y) ((pPow X j La La' * ι (scal0 X fd χ muT j La La' * (Base.chiFac χ _ _ (fd.kerN j La) (fd.kerN (j + 1) La'))⁻¹ * s)) • MvPowerSeries.map ι (tay Θ)) := by
  intro D p _ X E pos fd lam ι hι ρ hρ e c j La La' he he' cc δ B χ SS cl Ξ₀ muT hok hj hL hL' s Θ hs hK
  obtain ⟨-, -, hdiff, hcoef, hsc, hcf, hcf0, hfr⟩ := hok j hj La La' hL hL'
  have hΘ : Differentiable ℂ Θ :=
    GlobalTheory.T.differentiable_of_unitary_matrixPullback_differentiable D cc δ (e j La) (e (j + 1) La') Θ _ s he he' hs hdiff hK
  have hsc' : scal0 X fd χ muT j La La' * (Base.chiFac χ _ _ (fd.kerN j La) (fd.kerN (j + 1) La'))⁻¹ ∈ TaylorLogMetric.Qbar :=
    TaylorLogMetric.Qbar.mul_mem hsc (TaylorLogMetric.Qbar.inv_mem hcf)
  have hser := GlobalTheory.T.padicSeries_algebraic_multiple_via_place_extension D p lam ι hι _ _ _ s hsc' hcoef hK
  have htay := GlobalTheory.T.taylorSeries_matrixPullback_eq_linear_substitution D cc δ (e j La) (e (j + 1) La') Θ hΘ
  have hsub := GlobalTheory.T.pullback_then_frame_substitution_eq_changed_frames D p X E pos fd lam ι hι ρ hρ e c j La La' he he' (fun v => ⟨(hfr v).1, (hfr v).2.1⟩)
  rw [frecG_eq, hser]
  change linSub _ (_ • _ • MvPowerSeries.map ι (tay (TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) (e j La) (e (j + 1) La') Θ))) = _
  rw [htay, map_linSub', ← linSub_smul', ← linSub_smul', GlobalTheory.TwU.LawAll.linSub_linSub', smul_smul]
  congr 1
  funext x y
  exact hsub x y

end GlobalTheory.TwV.DelB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSeriesPairOfPullbackKernelFunctionStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeriesPair_of_pullbackKernelFunction : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (E : CEmb X.G) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ →+* ℂ_[p]), (∀ z : TaylorLogMetric.Qbar, ι z = lam z) → ∀ (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), LamPos X E pos lam ρ → ∀ (e : ∀ j, X.Lt j → Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E) (c : ℂ_[p]) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)), e j La * star (e j La) = 1 → e (j + 1) La' * star (e (j + 1) La') = 1 → ∀ {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ) (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ), PairOK X fd B χ SS cl Ξ₀ muT ρ → j < X.mm → (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 → ∀ (s : ℂ) (Θ : TaylorLogMetric.VC D ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ), s ≠ 0 → (∀ z, kerTh B χ SS cl (fd.kerN j La) (fd.kerN (j + 1) La') (xiM X fd Ξ₀ j La La') z = s * TaylorLogMetric.pull D B.tor (e j La) (e (j + 1) La') Θ z) → FrecG E pos fd B χ lam SS cl Ξ₀ muT c j La La' = linSub (fun x y => c * subBG E pos (reframe fd ρ e) j La La' x y) ((pPow X j La La' * ι (scal0 X fd χ muT j La La' * (Base.chiFac χ _ _ (fd.kerN j La) (fd.kerN (j + 1) La'))⁻¹ * s)) • MvPowerSeries.map ι (tay Θ)) := by
  first | exact @GlobalTheory.TwV.DelB.frecG_pull | exact GlobalTheory.TwV.DelB.frecG_pull | (intros; apply GlobalTheory.TwV.DelB.frecG_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PullbackScalarNeZeroLatticeTuplePair
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PullbackScalarNeZeroLatticeTuplePair
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem pullbackScalar_ne_zero : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std), ∀ j < D.R.m, ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → d.sP S j La La' ≠ 0) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S d j hj La La' h1 h2
  have hj' : j + 1 ≤ D.R.m := hj
  have key := fun (i : ℕ) (hi : i ≤ D.R.m) (Lb : (sysS H X std).Lt i) (hLb : ((sysS H X std).Pj i).IsLatTup Lb.2) =>
    GlobalTheory.T.adelicCharacters_at_det_rational_isometry_rep_level J.A J.dtU J.a J.pins J.tie S.Xi S.muT S.law j hj i hi (clsAt X H i Lb.1 Lb.2) (J.pt std i hi Lb)
      (d.gam i hi Lb) (d.mem i hi Lb) (d.kap i hi Lb) (d.eq i hi Lb hLb)
  have n1 := (key j (Nat.le_of_succ_le hj') La h1).2.2
  have n2 := (key (j + 1) hj' La' h2).2.2
  simp only [Dec.sP, dif_pos hj', Dec.chi]
  exact div_ne_zero (mul_ne_zero n1 (Units.ne_zero _)) (mul_ne_zero n2 (Units.ne_zero _))

end GlobalTheory.TwV.DelB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PullbackScalarNeZeroLatticeTuplePairStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_scalar_ne_zero_latticeTuple_pair : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std), ∀ j < D.R.m, ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → d.sP S j La La' ≠ 0) := by
  first | exact @GlobalTheory.TwV.DelB.pullbackScalar_ne_zero | exact GlobalTheory.TwV.DelB.pullbackScalar_ne_zero | (intros; apply GlobalTheory.TwV.DelB.pullbackScalar_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSeriesSiteEqChangedFrameClassSeries
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.DelB.serAt_all : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → ∀ (d : Dec J std), ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ j < D.R.m, d.SerAt S ι j) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict hPair hPos d ι hι j hj La La' hLa hLa'
  have hr := GlobalTheory.T.siteSystem_ranks_eq_datum_ranks S
  have hu := GlobalTheory.T.decomposition_unitary_mul_star_eq_one S d
  have hp := GlobalTheory.T.latticeTupleKernel_eq_smul_pullback_classKernel S hDict d j hj La La' hLa hLa'
  have hs := GlobalTheory.T.pullback_scalar_ne_zero_latticeTuple_pair S d j hj La La' hLa hLa'
  exact GlobalTheory.T.thetaSeriesPair_of_pullbackKernelFunction D _ (sysS H X std) S.E.toCEmb (hT.gat_pos u w hg) (J.fd std) S.lam ι hι (J.rho std) hPos d.eM
    (ltC S.g S.hLT) j La La' (hu j La) (hu (j + 1) La') t.B t.χ (ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT hPair
    (hr.1 ▸ hj) hLa hLa' (d.sP S j La La') (thCl (X := sysS H X std) t u μ (clsAt X H) j La La') hs hp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSeriesSiteEqChangedFrameClassSeriesStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_site_eq_changedFrame_classSeries : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → ∀ (d : Dec J std), ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ j < D.R.m, d.SerAt S ι j) := by
  first | exact @GlobalTheory.TwV.DelB.serAt_all | exact GlobalTheory.TwV.DelB.serAt_all | (intros; apply GlobalTheory.TwV.DelB.serAt_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SeriesCoefficientsAtKernelSiteOfClassSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoeffRenamedThetaClassSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoeffRenamedThetaClassSeries
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelB

theorem taylor_reV {D : D7} {a b N N' : ℕ} (ha : a = N) (hb : b = N') (G : TaylorLogMetric.VC D N N' → ℂ)
    (α : GL3Theta.Idx D N N' →₀ ℕ) :
    TaylorLogMetric.taylor D (reV ha hb G) (α.mapDomain fun k => (k.1, Fin.cast hb.symm k.2.1, Fin.cast ha.symm k.2.2)) =
      TaylorLogMetric.taylor D G α := by
  subst ha hb
  have h1 : reV (D := D) rfl rfl G = G := by funext z; rfl
  have h2 : (fun k : GL3Theta.Idx D a b => (k.1, Fin.cast (rfl : b = b).symm k.2.1, Fin.cast (rfl : a = a).symm k.2.2)) = id := by
    funext k; rfl
  rw [h1, h2, Finsupp.mapDomain_id]

theorem coeff_resV_thCl : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (p : ℕ) [Fact p.Prime] (X : Sys p) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j) {K : Type} [Field K] (ι : ℂ →+* K) (j : ℕ) (hN : RankTie X D j) (La : X.Lt j) (La' : X.Lt (j + 1)) (s : K) (α : GL3Theta.Idx D (D.R.N j) (D.R.N (j + 1)) →₀ ℕ), MvPowerSeries.coeff (α.mapDomain (eIdx X D pos j hN)) (resV (kapOf X pos j) (s • MvPowerSeries.map ι (tay (thCl t u μ cls j La La')))) = s * ι (TaylorLogMetric.taylor D ((t.rd u μ).Th t.seam t.amb j (cls j La.1 La.2) (cls (j + 1) La'.1 La'.2)) α) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ p _ X pos cls K _ ι j hN La La' s α
  have hr : (X.Pj j).m + 1 = D.R.N j ∧ (X.Pj (j + 1)).m + 1 = D.R.N (j + 1) :=
    ⟨(Formalism.L2.G.Pend.rank_eq X j).trans hN.1.symm, (Formalism.L2.G.Pend.rank_eq X (j + 1)).trans hN.2.symm⟩
  have hres : ∀ {ι' κ' : Type} (f : κ' → ι') (Th : MvPowerSeries ι' K) (n : κ' →₀ ℕ),
      MvPowerSeries.coeff n (resV f Th) = MvPowerSeries.coeff (n.mapDomain f) Th := fun _ _ _ => rfl
  have hcomp : (Formalism.L2.G.Pend.kapOf X pos j ∘ eIdx X D pos j hN) =
      fun k => (k.1, Fin.cast hr.2.symm k.2.1, Fin.cast hr.1.symm k.2.2) := by
    funext k
    simp only [Function.comp, Formalism.L2.G.Pend.kapOf, eIdx, Sigma.eta, Equiv.apply_symm_apply]
    ext <;> rfl
  rw [hres, ← Finsupp.mapDomain_comp, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_map, hcomp]
  congr 2
  show TaylorLogMetric.taylor D (thCl t u μ cls j La La') _ = _
  rw [thCl, dite_eq_left hr]
  exact taylor_reV hr.1 hr.2 _ α

end GlobalTheory.TwV.DelB
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoeffRenamedThetaClassSeriesStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_renamed_thetaClass_series : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (p : ℕ) [Fact p.Prime] (X : Sys p) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j) {K : Type} [Field K] (ι : ℂ →+* K) (j : ℕ) (hN : RankTie X D j) (La : X.Lt j) (La' : X.Lt (j + 1)) (s : K) (α : GL3Theta.Idx D (D.R.N j) (D.R.N (j + 1)) →₀ ℕ), MvPowerSeries.coeff (α.mapDomain (eIdx X D pos j hN)) (resV (kapOf X pos j) (s • MvPowerSeries.map ι (tay (thCl t u μ cls j La La')))) = s * ι (TaylorLogMetric.taylor D ((t.rd u μ).Th t.seam t.amb j (cls j La.1 La.2) (cls (j + 1) La'.1 La'.2)) α) := by
  first | exact @GlobalTheory.TwV.DelB.coeff_resV_thCl | exact GlobalTheory.TwV.DelB.coeff_resV_thCl | (intros; apply GlobalTheory.TwV.DelB.coeff_resV_thCl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SeriesCoefficientsAtKernelSiteOfClassSeries
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem tieSerH_series_of_classes : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) (ι : ℂ →+* ℂ_[D.what₂.places.resChar w]) j (hN : RankTie (sysS H X std) D j), TieSerH S.Y t u μ (clsAt X H) (fun j => clsAt X H (j + 1)) ι (fun j La La' => resV (kapOf (sysS H X std) (hT.gat_pos u w hg) j) (d.gS S ι j La La')) (d.sH S ι) j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S d ι j hN La _ c' L' _ α _
  exact GlobalTheory.T.coeff_renamed_thetaClass_series t u μ _ (sysS H X std) (hT.gat_pos u w hg) (clsAt X H) ι j hN La (c', L') (d.sH S ι j La (c', L')) α

end GlobalTheory.TwV.DelB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SeriesCoefficientsAtKernelSiteOfClassSeriesStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seriesCoefficients_at_kernelSite_of_classSeries : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) (ι : ℂ →+* ℂ_[D.what₂.places.resChar w]) j (hN : RankTie (sysS H X std) D j), TieSerH S.Y t u μ (clsAt X H) (fun j => clsAt X H (j + 1)) ι (fun j La La' => resV (kapOf (sysS H X std) (hT.gat_pos u w hg) j) (d.gS S ι j La La')) (d.sH S ι) j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN)) := by
  first | exact @GlobalTheory.TwV.DelB.tieSerH_series_of_classes | exact GlobalTheory.TwV.DelB.tieSerH_series_of_classes | (intros; apply GlobalTheory.TwV.DelB.tieSerH_series_of_classes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContractionIdentityFramesWithOperatorScalar
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContractionIdentityFramesWithOperatorScalar
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.TwV.DelB

theorem delPolAt_of_frames_scal : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (p : ℕ) [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) (g : GL3Theta.G1 p) (hLT : LTIso g) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (c : ℂ_[p]) (F g₀ : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]), letI := wittFractionAlgebraCp p; letI := algKfC E.toCEmb; FrInv fd → KapLawLt X ℂ_[p] (thFOf X pos F) → let Y := pendT X E hfin hst hLT pos F; ∀ (σ : D.what₂.LL →+* X.G.Kf) (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j) (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j) (κ : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → (D.chTw u μ).cls (j + 1)) (ι : ℂ →+* Y.Kc) (Φ₀ : ∀ j, MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc) (τ : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → XspC (X.Pj (j + 1)) Y.Kc →ₗ[Y.Kc] XspC (X.Pj (j + 1)) Y.Kc) (sc : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → Y.Kc) (sH : ∀ j, X.Lt j → X.Lt (j + 1) → Y.Kc) (sO : ∀ j, X.Lt j → Y.Kc) (Gm : ∀ j, X.Lt j → ((ex.tw.fm u μ).lat j).V → (X.Pj j).Xsp) (j : ℕ) (_ : j < X.mm) (cK : Y.Kc) (hN : RankTie X D j), (∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 → F j La La' = linSub (fun x y => c * subBG E.toCEmb pos fd j La La' x y) (g₀ j La La')) → MoveH Y u μ cmp (fun j La => glInv X j (BOf fd j La)) Gm j → TieOpS (Y := Y) t u μ cls Gm sO j (eIdx X D pos j hN) (Φ₀ j) → KernelEntryDegreeCondition (Y := Y) t u μ cls j (eIdx X D pos j hN) → TieSerH Y t u μ cls κ ι (fun j La La' => resV (kapOf X pos j) (g₀ j La La')) sH j (eIdx X D pos j hN) → TieChiH Y t u μ cls κ ι sc sH (fun j La => Formalism.L2.G.Pend.cA X Y.Kc j (BOf fd j La) * sO j La) j cK → DelYEqH Y (fun j La' => VOf Y.Kc fd c j La') τ j → DelPolAt (Y := Y) t u μ cls cmp κ (phiH D Φ₀ τ sc) (srOf Y) j cK := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ p _ X _ E hfin hst g hLT pos fd c F g₀
  intro hFr hK Y σ cls cmp κ ι Φ₀ τ sc sH sO Gm j hj cK hN hF hMv hOp hDeg hSer hChi hYEq
  intro La hLa x Q hQ c' L' hL'
  letI := Formalism.L2.G.Pend.wittFractionAlgebraCp p
  letI := Formalism.L2.G.Pend.algKfC E.toCEmb
  have hTh : Y.ThF j La (c', L') = Formalism.L2.G.Pend.thFOf X pos F j La (c', L') :=
    (GlobalTheory.TwU.pendT_ThF_lt_of_kapLawLt p X E hfin hst g hLT D.what₂.Tau pos F hK).1 j ‹_› La (c', L') (Y.Rep_lat j La hLa) hL'
  have hsr : srOf Y j La (c', L') = (Y.eS j La * (Y.eT j (c', L'))⁻¹ : X.G.Kf) •
      linSub (fun z y => ∑ w, VOf Y.Kc fd c j (c', L') z w * Formalism.L2.G.Pend.LkB X Y.Kc j (BOf fd j La) w y)
        (resV (Formalism.L2.G.Pend.kapOf X pos j) (g₀ j La (c', L'))) := by
    unfold srOf
    rw [hTh]
    congr 1
    show resV (Formalism.L2.G.Pend.kapOf X pos j) (F j La (c', L')) = _
    rw [hF La (c', L') (Y.Rep_lat j La hLa) hL']
    rw [rename_linear _ _ _ _ (kapOf_bij X pos j)]
    congr 1
    funext z y
    exact substitution_split p X D E.toCEmb pos fd _ hFr j La (c', L') z y
  obtain ⟨hMe, hG, hO⟩ := hMv La hLa x
  beta_reduce at hMe
  have hc := chain_core X Y.Kc j (VOf Y.Kc fd c j (c', L'))
    (blockDiag_VOf X Y.Kc j fd _ (c', L')) (glInv X j (BOf fd j La)) (Gm j La x) hG hO (τ j c' L')
    (hYEq c' L' hL' (Gm j La x) hG hO) (resV (Formalism.L2.G.Pend.kapOf X pos j) (g₀ j La (c', L')))
  rw [glAt_glInv] at hc
  have hPD := pairing_dictionary p X Y.Kc j D (D.R.N j) (D.R.N (j + 1)) ι (eIdx X D pos j hN) (eIdx_injective X D pos j hN) (Φ₀ j)
    (polDY D (t.O u μ).dgen (Q (cls j La.1 La.2)) (N' := D.R.N (j + 1)))
    ((t.rd u μ).Th t.seam t.amb j (cls j La.1 La.2) (κ j c' L'))
    (resV (Formalism.L2.G.Pend.kapOf X pos j) (g₀ j La (c', L'))) (sH j La (c', L'))
    (hDeg La hLa x Q hQ) (fun α hα => hSer La hLa c' L' hL' α (hDeg La hLa x Q hQ α hα))
  have hOS := pairD_lin X Y.Kc j (sO j La • LinearMap.id)
    (trDY X Y.Kc j D (eIdx X D pos j hN) (Φ₀ j) (polDY D (t.O u μ).dgen (Q (cls j La.1 La.2)) (N' := D.R.N (j + 1))))
    (Formalism.L2.G.Pend.polDel X Y.Kc j (Gm j La x)) (fun n => hOp La hLa x Q hQ n)
    (resV (Formalism.L2.G.Pend.kapOf X pos j) (g₀ j La (c', L')))
  show sc j c' L' • τ j c' L' (Φ₀ j (_ • pairR D (polDY D (t.O u μ).dgen (Q (cls j La.1 La.2)) (N' := D.R.N (j + 1)))
      ((t.rd u μ).Th t.seam t.amb j (cls j La.1 La.2) (κ j c' L')))) =
    cK • Formalism.L2.G.Pend.pairD X Y.Kc j (Formalism.L2.G.Pend.polDel X Y.Kc j (cmp j x La.1 La.2)) (srOf Y j La (c', L'))
  rw [hsr, Formalism.L2.G.Pend.pairD_smul_right, ← hMe, hc, hOS, hPD, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.map_smulₛₗ, map_smul, map_smul, map_smul,
    ← algebraMap_smul Y.Kc (Y.eS j La * (Y.eT j (c', L'))⁻¹), smul_smul, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  rw [← hChi La hLa c' L' hL']
  ring

end GlobalTheory.TwV.DelB
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContractionIdentityFramesWithOperatorScalarStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contraction_identity_frames_with_operator_scalar : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (p : ℕ) [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) (g : GL3Theta.G1 p) (hLT : LTIso g) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (c : ℂ_[p]) (F g₀ : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]), letI := wittFractionAlgebraCp p; letI := algKfC E.toCEmb; FrInv fd → KapLawLt X ℂ_[p] (thFOf X pos F) → let Y := pendT X E hfin hst hLT pos F; ∀ (σ : D.what₂.LL →+* X.G.Kf) (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j) (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j) (κ : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → (D.chTw u μ).cls (j + 1)) (ι : ℂ →+* Y.Kc) (Φ₀ : ∀ j, MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc) (τ : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → XspC (X.Pj (j + 1)) Y.Kc →ₗ[Y.Kc] XspC (X.Pj (j + 1)) Y.Kc) (sc : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → Y.Kc) (sH : ∀ j, X.Lt j → X.Lt (j + 1) → Y.Kc) (sO : ∀ j, X.Lt j → Y.Kc) (Gm : ∀ j, X.Lt j → ((ex.tw.fm u μ).lat j).V → (X.Pj j).Xsp) (j : ℕ) (_ : j < X.mm) (cK : Y.Kc) (hN : RankTie X D j), (∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 → F j La La' = linSub (fun x y => c * subBG E.toCEmb pos fd j La La' x y) (g₀ j La La')) → MoveH Y u μ cmp (fun j La => glInv X j (BOf fd j La)) Gm j → TieOpS (Y := Y) t u μ cls Gm sO j (eIdx X D pos j hN) (Φ₀ j) → KernelEntryDegreeCondition (Y := Y) t u μ cls j (eIdx X D pos j hN) → TieSerH Y t u μ cls κ ι (fun j La La' => resV (kapOf X pos j) (g₀ j La La')) sH j (eIdx X D pos j hN) → TieChiH Y t u μ cls κ ι sc sH (fun j La => Formalism.L2.G.Pend.cA X Y.Kc j (BOf fd j La) * sO j La) j cK → DelYEqH Y (fun j La' => VOf Y.Kc fd c j La') τ j → DelPolAt (Y := Y) t u μ cls cmp κ (phiH D Φ₀ τ sc) (srOf Y) j cK := by
  first | exact @GlobalTheory.TwV.DelB.delPolAt_of_frames_scal | exact GlobalTheory.TwV.DelB.delPolAt_of_frames_scal | (intros; apply GlobalTheory.TwV.DelB.delPolAt_of_frames_scal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteContractionIdentityOperatorHalf
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem delPolAt_site : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Law → ∀ (d : Dec J std), ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (Φ₀ : ∀ j, MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ →ₛₗ[ι] XspC ((sysS H X std).Pj (j + 1)) ℂ_[D.what₂.places.resChar w]) (τ : ∀ j, (sysS H X std).Lv.comp (j + 1) → ((sysS H X std).Pj (j + 1)).Tup → XspC ((sysS H X std).Pj (j + 1)) ℂ_[D.what₂.places.resChar w] →ₗ[ℂ_[D.what₂.places.resChar w]] XspC ((sysS H X std).Pj (j + 1)) ℂ_[D.what₂.places.resChar w]) (sc : ∀ j, (sysS H X std).Lv.comp (j + 1) → ((sysS H X std).Pj (j + 1)).Tup → ℂ_[D.what₂.places.resChar w]) (sO : ∀ j, (sysS H X std).Lt j → ℂ_[D.what₂.places.resChar w]) (Gm : ∀ j, (sysS H X std).Lt j → ((ex.tw.fm u μ).lat j).V → ((sysS H X std).Pj j).Xsp), ∀ j < D.R.m, ∀ (cK : ℂ_[D.what₂.places.resChar w]) (hN : RankTie (sysS H X std) D j), MoveH S.Y u μ (kaAt X H hT).cmp (fun j La => glInv (sysS H X std) j (BOf d.fd2 j La)) Gm j → TieOpS (Y := S.Y) t u μ (clsAt X H) Gm sO j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN) (ι := ι) (Φ₀ j) → KernelEntryDegreeCondition (Y := S.Y) t u μ (clsAt X H) j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN) → DelYEqH S.Y (fun j La' => VOf ℂ_[D.what₂.places.resChar w] d.fd2 (ltC S.g S.hLT) j La') τ j → (∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → cK * (Formalism.L2.G.Pend.cA (sysS H X std) ℂ_[D.what₂.places.resChar w] j (BOf d.fd2 j La) * sO j La) * ι (d.uS S j La) * ι (d.uT S j La') = sc j La'.1 La'.2) → DelPolAt (Y := S.Y) t u μ (clsAt X H) (kaAt X H hT).cmp (fun j => clsAt X H (j + 1)) (phiH D Φ₀ τ sc) (srOf S.Y) j cK) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict hPair hPos hLaw d ι hι
  intro Φ₀ τ sc sO Gm j hj cK hN hMove hOp hDeg hDel hSc
  letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
  letI := algKfC S.E.toCEmb
  have hR := GlobalTheory.T.siteSystem_ranks_eq_datum_ranks S
  have hFr := (GlobalTheory.T.siteFrames_and_changedFrames_invertible S).2 d
  have hSer := GlobalTheory.T.thetaSeries_site_eq_changedFrame_classSeries S hDict hPair hPos d ι hι j hj
  have hSerH := GlobalTheory.T.seriesCoefficients_at_kernelSite_of_classSeries S d ι j hN
  have hChi := GlobalTheory.T.kernelScalar_of_sourceTarget_parts_product S hDict d ι j hj (fun j La => Formalism.L2.G.Pend.cA (sysS H X std) ℂ_[D.what₂.places.resChar w] j (BOf d.fd2 j La) * sO j La) sc cK hSc
  exact GlobalTheory.T.contraction_identity_frames_with_operator_scalar t u μ _ (sysS H X std) S.E S.hfin S.hst S.g S.hLT (hT.gat_pos u w hg) d.fd2 (ltC S.g S.hLT)
    (fun j La La' => FrecG S.E.toCEmb (hT.gat_pos u w hg) (J.fd std) t.B t.χ S.lam (ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT (ltC S.g S.hLT) j La La')
    (d.gS S ι) hFr hLaw _ (clsAt X H) (kaAt X H hT).cmp (fun j => clsAt X H (j + 1)) ι Φ₀ τ sc (d.sH S ι) sO Gm j (hR.1 ▸ hj) cK hN
    hSer hMove hOp hDeg hSerH hChi hDel

end GlobalTheory.TwV.DelB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteContractionIdentityOperatorHalfStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelSite_contractionIdentity_operatorHalf : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Law → ∀ (d : Dec J std), ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (Φ₀ : ∀ j, MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ →ₛₗ[ι] XspC ((sysS H X std).Pj (j + 1)) ℂ_[D.what₂.places.resChar w]) (τ : ∀ j, (sysS H X std).Lv.comp (j + 1) → ((sysS H X std).Pj (j + 1)).Tup → XspC ((sysS H X std).Pj (j + 1)) ℂ_[D.what₂.places.resChar w] →ₗ[ℂ_[D.what₂.places.resChar w]] XspC ((sysS H X std).Pj (j + 1)) ℂ_[D.what₂.places.resChar w]) (sc : ∀ j, (sysS H X std).Lv.comp (j + 1) → ((sysS H X std).Pj (j + 1)).Tup → ℂ_[D.what₂.places.resChar w]) (sO : ∀ j, (sysS H X std).Lt j → ℂ_[D.what₂.places.resChar w]) (Gm : ∀ j, (sysS H X std).Lt j → ((ex.tw.fm u μ).lat j).V → ((sysS H X std).Pj j).Xsp), ∀ j < D.R.m, ∀ (cK : ℂ_[D.what₂.places.resChar w]) (hN : RankTie (sysS H X std) D j), MoveH S.Y u μ (kaAt X H hT).cmp (fun j La => glInv (sysS H X std) j (BOf d.fd2 j La)) Gm j → TieOpS (Y := S.Y) t u μ (clsAt X H) Gm sO j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN) (ι := ι) (Φ₀ j) → KernelEntryDegreeCondition (Y := S.Y) t u μ (clsAt X H) j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN) → DelYEqH S.Y (fun j La' => VOf ℂ_[D.what₂.places.resChar w] d.fd2 (ltC S.g S.hLT) j La') τ j → (∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → cK * (Formalism.L2.G.Pend.cA (sysS H X std) ℂ_[D.what₂.places.resChar w] j (BOf d.fd2 j La) * sO j La) * ι (d.uS S j La) * ι (d.uT S j La') = sc j La'.1 La'.2) → DelPolAt (Y := S.Y) t u μ (clsAt X H) (kaAt X H hT).cmp (fun j => clsAt X H (j + 1)) (phiH D Φ₀ τ sc) (srOf S.Y) j cK) := by
  first | exact @GlobalTheory.TwV.DelB.delPolAt_site | exact GlobalTheory.TwV.DelB.delPolAt_site | (intros; apply GlobalTheory.TwV.DelB.delPolAt_site <;> assumption)
end
