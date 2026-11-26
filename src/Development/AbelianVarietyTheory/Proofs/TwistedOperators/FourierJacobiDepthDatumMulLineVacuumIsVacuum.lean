module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiStepCoreComponentMemCoreDepthLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiStepCoreComponentMemCoreDepthLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobi_step_core_component_mem_core_depth_lattice : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ u ∈ (pcFB W F σ h h').Γ₀, ((F.oB σ h').resT _ u).1 ∈ latCore G (2 * σ + 2) := by
  first | exact @GlobalTheory.CoreComp.core_mem_latCore | exact GlobalTheory.CoreComp.core_mem_latCore | (intros; apply GlobalTheory.CoreComp.core_mem_latCore <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiDepthLatticeLineComponentsMem
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittCoreEmbeddingMulVecMemLatticeOfSplits
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittCoreEmbeddingMulVecMemLatticeOfSplits
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.WittCoreLat

open GlobalTheory.FinPl.LatMem

variable {D : D7}

theorem rat_mulVec_tmul {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (c : AF D.host.F) (z : Fin n → D.host.E) :
    rat M *ᵥ (fun i => c ⊗ₜ[D.host.F] z i) = fun k => c ⊗ₜ[D.host.F] (M *ᵥ z) k := by
  funext k
  simp only [Matrix.mulVec, dotProduct, rat, Matrix.map_apply]
  rw [TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show ((1 : AF D.host.F) ⊗ₜ[D.host.F] M k j) * (c ⊗ₜ[D.host.F] z j) = c ⊗ₜ[D.host.F] (M k j * z j)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem i₀_mulVec_mem {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀}
    (hL : ∀ z : Fin S.rank → D.host.E, (∀ v : GlobalTheory.FinPl.Pl D, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈ latV S L (· = v)) → z ∈ L)
    (hmono : ∀ v, MonoAt d L L₀ v) : ∀ y ∈ L₀, d.i₀ *ᵥ y ∈ L := by
  intro y hy
  have hX : d.qX * d.i₀ = 0 := rat_injective (D := D) (by rw [rat_mul, rat_zero]; exact d.pX_j0)
  have hY : d.qY * d.i₀ = 0 := rat_injective (D := D) (by rw [rat_mul, rat_zero]; exact d.pY_j0)
  have h0 : d.q0 * d.i₀ = 1 := rat_injective (D := D) (by rw [rat_mul, rat_one]; exact d.p0_j0)
  refine hL _ fun v => ?_
  set c : AF D.host.F := pairA D.host.F 0 (indP D.host.F (· = v))
  refine (hmono v _).2 ⟨fun i => ?_, fun i => ?_, ?_⟩
  · have : d.pX *ᵥ (fun i => c ⊗ₜ[D.host.F] (d.i₀ *ᵥ y) i) = 0 := by
      rw [HypDec.pX, rat_mulVec_tmul, Matrix.mulVec_mulVec, hX, Matrix.zero_mulVec]
      funext k; exact TensorProduct.tmul_zero _ _
    rw [this]
    have h' : GlobalTheory.FinPl.colMul d.jX i ((0 : Fin ρ → AE D) i) = 0 := by
      funext k; simp [GlobalTheory.FinPl.colMul]
    rw [h']; exact zero_mem _
  · have : d.pY *ᵥ (fun i => c ⊗ₜ[D.host.F] (d.i₀ *ᵥ y) i) = 0 := by
      rw [HypDec.pY, rat_mulVec_tmul, Matrix.mulVec_mulVec, hY, Matrix.zero_mulVec]
      funext k; exact TensorProduct.tmul_zero _ _
    rw [this]
    have h' : GlobalTheory.FinPl.colMul d.jY i ((0 : Fin ρ → AE D) i) = 0 := by
      funext k; simp [GlobalTheory.FinPl.colMul]
    rw [h']; exact zero_mem _
  · rw [HypDec.p0, rat_mulVec_tmul, Matrix.mulVec_mulVec, h0, Matrix.one_mulVec]
    exact AddSubgroup.subset_closure ⟨indP D.host.F (· = v), indicatorAdele_mem_integralAdeles' _ _, indicatorAdele_supported _ _, 1, rfl, y, hy,
      by funext k; rw [one_mul]⟩

end GlobalTheory.WittCoreLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittCoreEmbeddingMulVecMemLatticeOfSplitsStatement
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittCoreEmbedding_mulVec_mem_lattice_of_splits : ∀ {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀}, (∀ z : Fin S.rank → D.host.E, (∀ v : GlobalTheory.FinPl.Pl D, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈ latV S L (· = v)) → z ∈ L) → (∀ v, MonoAt d L L₀ v) → ∀ y ∈ L₀, d.i₀ *ᵥ y ∈ L := by
  first | exact @GlobalTheory.WittCoreLat.i₀_mulVec_mem | exact GlobalTheory.WittCoreLat.i₀_mulVec_mem | (intros; apply GlobalTheory.WittCoreLat.i₀_mulVec_mem <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrthogonalSummandProjectionMemLatticeOfSplits
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrthogonalSummandProjectionMemLatticeOfSplits
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin


open GlobalTheory.FinPl.LatMem in
theorem GlobalTheory.FinPl.projB_mem_of_orthAt : ∀ {D : D7} {S A B : HSp D} (o : OrthDec S A B) {L : Lat S} {LA : Lat A} {LB : Lat B}, (∀ z : Fin B.rank → D.host.E, (∀ v : GlobalTheory.FinPl.Pl D, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈ latV B LB (· = v)) → z ∈ LB) → (∀ v, OrthAt o L LA LB v) → ∀ t ∈ L, o.qB *ᵥ t ∈ LB := by
  intro D S A B o L LA LB hLG hO t ht
  apply hLG
  intro v
  have hY : (fun i => pairA D.host.F 0 (indP D.host.F (· = v)) ⊗ₜ[D.host.F] (1 * t i)) ∈ latV S L (· = v) :=
    AddSubgroup.subset_closure ⟨indP D.host.F (· = v), indicatorAdele_mem_integralAdeles' _ _, indicatorAdele_supported _ _, 1, rfl, t, ht, rfl⟩
  have h2 := ((hO v _).1 hY).2
  convert h2 using 1
  funext i
  simp only [Matrix.mulVec, dotProduct]
  rw [TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show _ = (1 : AF D.host.F) ⊗ₜ[D.host.F] (o.qB i j) * _
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrthogonalSummandProjectionMemLatticeOfSplitsStatement
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonalSummandProjection_mem_lattice_of_splits : ∀ {D : D7} {S A B : HSp D} (o : OrthDec S A B) {L : Lat S} {LA : Lat A} {LB : Lat B}, (∀ z : Fin B.rank → D.host.E, (∀ v : GlobalTheory.FinPl.Pl D, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈ latV B LB (· = v)) → z ∈ LB) → (∀ v, OrthAt o L LA LB v) → ∀ t ∈ L, o.qB *ᵥ t ∈ LB := by
  first | exact @GlobalTheory.FinPl.projB_mem_of_orthAt | exact GlobalTheory.FinPl.projB_mem_of_orthAt | (intros; apply GlobalTheory.FinPl.projB_mem_of_orthAt <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiDepthLatticeLineComponentsMem
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.LineFB

theorem latO_negSp_le' {D : D7} (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO (negSp S) T LS LT P ≤ latO S T LS LT P := by
  unfold latO
  rw [AddSubgroup.closure_le]
  rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  rw [← neg_neg (Matrix.of _)]
  refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

theorem line_mem : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m),
    ∀ u ∈ (pcFB W F σ h h').Γ₀, ((F.oB σ h').resT _ u).2 ∈ lineLat F (σ + 1) := by
  intro D hD T L μ0 hL sc G W M hM F hF σ h h' u hu
  obtain ⟨-, hfr, hline⟩ := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hD T L μ0 hL sc G W M hM F hF
  have hx := AddSubgroup.mem_comap.1 hu
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply] at hx
  have hSc : IsSelfDualC (G.V (.core (2 * (σ + 1) + 1))) (G.Λ (.core (2 * (σ + 1) + 1))) :=
    (G.isV (X := .core (2 * (σ + 1) + 1)) (by simp [Node.InRange]; omega) (fun j e => Node.noConfusion e)).sd
  have hSg : IsSelfDualC (G.V (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) :=
    (G.isV (X := .grid (2 * (σ + 1) + 1) 0) (by simp [Node.InRange]; omega) (fun j e => by simp at e)).sd
  have hTg : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) :=
    (G.isV (X := .grid (2 * σ + 2) 0) (by simp [Node.InRange]; omega) (fun j e => by simp at e)).sd
  have hℓ := (hfr σ h').2.2.1
  have hℓ' := hline (σ + 1)
  have h0 := (hfr σ h').1
  have hj : ∀ y ∈ G.Λ (.core (2 * (σ + 1) + 1)), (F.dJ (σ + 1) h).i₀ *ᵥ y ∈ G.Λ (.grid (2 * (σ + 1) + 1) 0) :=
    GlobalTheory.T.wittCoreEmbedding_mulVec_mem_lattice_of_splits _ (GlobalTheory.T.mem_selfDualLattice_of_mem_all_latticeCompletions hSg) fun v => ((hfr (σ + 1) h).2.1 v).2
  have hq : ∀ t ∈ G.Λ (.grid (2 * σ + 2) 0), ((F.oB σ h').qB * (F.dB σ h').q0) *ᵥ t ∈
      idLat (G.pl.stA sc ^ (σ + 1) * (G.pl.stAbar sc ^ (σ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0}) := by
    intro t ht
    rw [← Matrix.mulVec_mulVec]
    exact GlobalTheory.T.orthogonalSummandProjection_mem_lattice_of_splits _ (GlobalTheory.T.mem_selfDualLattice_of_mem_all_latticeCompletions hℓ) (hfr σ h').2.2.2 _
      (GlobalTheory.T.q0_mulVec_mem_of_splits _ (GlobalTheory.T.mem_selfDualLattice_of_mem_all_latticeCompletions h0) (fun v => ((hfr σ h').2.1 v).1) t ht)
  have key : ((F.oB σ h').resT _ u).2 =
      rat ((F.oB σ h').qB * (F.dB σ h').q0) * ((F.dB σ h').j0 * u * (F.dJ (σ + 1) h).p0) * rat (F.dJ (σ + 1) h).i₀ := by
    rw [OrthDec.resT_apply, rat_mul]
    change _ = (F.oB σ h').pB * (F.dB σ h').p0 * ((F.dB σ h').j0 * u * (F.dJ (σ + 1) h).p0) * (F.dJ (σ + 1) h).j0
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (F.dB σ h').p0, HypDec.p0_j0, Matrix.one_mul, HypDec.p0_j0, Matrix.mul_one]
  rw [key]
  have hz := GlobalTheory.T.rationalMatrix_sandwich_mem_completed_homLattice_selfDual hSg hSc hℓ _ _ hj hq _ (latO_negSp_le' _ _ _ _ _ hx.1)
  obtain ⟨e, he, -⟩ := W.cosVec_is
  have hd := GlobalTheory.T.rationalMatrix_sandwich_mem_completed_ideal_latticeHom G.modul _ ((F.oB σ h').qB * (F.dB σ h').q0) hj hq _ (hx.2 e he)
  refine GlobalTheory.T.completedHomLattice_modulus_depth_mem_shift hD μ0 hL G _ _ _ hSc hℓ hℓ' _ hz ⟨e, he, ?_⟩
  rwa [Matrix.mul_smul, Matrix.smul_mul] at hd

end GlobalTheory.LineFB

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiDepthLatticeLineComponentsMemStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobi_depth_lattice_line_components_mem : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ u ∈ (pcFB W F σ h h').Γ₀, ((F.oB σ h').resT _ u).2 ∈ lineLat F (σ + 1) := by
  first | exact @GlobalTheory.LineFB.line_mem | exact GlobalTheory.LineFB.line_mem | (intros; apply GlobalTheory.LineFB.line_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiDepthDatumMulLineVacuumIsVacuum
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.BoxFB

theorem isHalf_mul_left {D : D7} {k m n : ℕ} {e : AE D} (a : Mx D k m) {u : Mx D m n} (hu : IsHalf e u) :
    IsHalf e (a * u) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_left_comm, hu l j]

theorem vacG_boxT {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {T A B S : HSp D} (d : OrthDec T A B)
    {Γ : AddSubgroup (WO S T)} {ΓA : AddSubgroup (WO S A)} {ΓB : AddSubgroup (WO S B)}
    (hA : ∀ u ∈ Γ, (d.resT S u).1 ∈ ΓA) (hB : ∀ u ∈ Γ, (d.resT S u).2 ∈ ΓB)
    {fA : WO S A → ℂ} {fB : WO S B → ℂ} (vA : VacG ψ S A ΓA fA) (vB : VacG ψ S B ΓB fB) :
    VacG ψ S T Γ (d.boxT S fA fB) := by
  refine ⟨d.isThetaFunO_boxT vA.1 vB.1, fun u hu => ?_, fun e he u hu hh => ?_⟩
  · rw [d.heisO_boxT, map_nsmul, Prod.smul_fst, Prod.smul_snd, vA.2.1 _ (hA u hu), vB.2.1 _ (hB u hu)]
  · rw [d.heisO_boxT, vA.2.2 e he _ (hA u hu) (by rw [d.resT_apply]; exact isHalf_mul_left _ hh),
      vB.2.2 e he _ (hB u hu) (by rw [d.resT_apply]; exact isHalf_mul_left _ hh)]

end GlobalTheory.BoxFB

namespace GlobalTheory.BoxFB

theorem core_mem : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ u ∈ (pcFB W F σ h h').Γ₀, ((F.oB σ h').resT _ u).1 ∈ latCore G (2 * σ + 2) := GlobalTheory.T.jacobi_step_core_component_mem_core_depth_lattice

theorem line_mem : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ u ∈ (pcFB W F σ h h').Γ₀, ((F.oB σ h').resT _ u).2 ∈ lineLat F (σ + 1) := GlobalTheory.T.fourierJacobi_depth_lattice_line_components_mem

theorem vacG_boxT_fb : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ Ξ₁ Φ₀, VacG W.ψ _ _ (latCore G (2 * σ + 2)) Ξ₁ → VacG W.ψ _ _ (lineLat F (σ + 1)) Φ₀ → VacG W.ψ _ _ (pcFB W F σ h h').Γ₀ ((F.oB σ h').boxT _ Ξ₁ Φ₀) := by
  intro D hD T L μ0 hL sc G W M hM F hF σ h h' Ξ₁ Φ₀ hΞ hΦ
  exact vacG_boxT (F.oB σ h') (core_mem D hD T L μ0 hL sc G W M hM F hF σ h h')
    (line_mem D hD T L μ0 hL sc G W M hM F hF σ h h') hΞ hΦ

end GlobalTheory.BoxFB

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiDepthDatumMulLineVacuumIsVacuumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobi_depthDatum_mul_lineVacuum_isVacuum : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ Ξ₁ Φ₀, VacG W.ψ _ _ (latCore G (2 * σ + 2)) Ξ₁ → VacG W.ψ _ _ (lineLat F (σ + 1)) Φ₀ → VacG W.ψ _ _ (pcFB W F σ h h').Γ₀ ((F.oB σ h').boxT _ Ξ₁ Φ₀) := by
  first | exact @GlobalTheory.BoxFB.vacG_boxT_fb | exact GlobalTheory.BoxFB.vacG_boxT_fb | (intros; apply GlobalTheory.BoxFB.vacG_boxT_fb <;> assumption)
end
