module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaUnfoldingEquivariantUnitaryGroups
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLinearModelLatticeVacuumBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleMixedModelBaseValueEquivariant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaIntegrandLocallyUniformMajorant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilMixedCoordinatesContinuousBoundedSupNorm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselUnfoldingOrbitMemParabolicMulStabiliser
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixMulVecMemAdeleIdealSupportedOnPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FinPl

theorem matrix_mulVec_mem_adeleIdealSupportedOnPlaces {D : D7} {P : Pl D → Prop} {m n : ℕ} (A : Matrix (Fin m) (Fin n) (AE D))
    (y : Fin n → AE D) (hy : ∀ i, y i ∈ idAt D P) (i : Fin m) : (A *ᵥ y) i ∈ idAt D P := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem matrixColumnScaledByAdele_zero {D : D7} {m n : ℕ} (x : Mx D m n) (i : Fin n) : colMul x i 0 = 0 := by
  funext k; simp [colMul]

theorem carriesLattice_wittEmbedding_iff_core : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : GlobalTheory.FinPl.Lat S) (L₀ : GlobalTheory.FinPl.Lat S₀) (v : GlobalTheory.FinPl.Pl D) (g : GA D S₀), GlobalTheory.FinPl.MonoAt d L L₀ v → (GlobalTheory.FinPl.Moves S (d.emb0 g) L L (· = v) ↔ GlobalTheory.FinPl.Moves S₀ g L₀ L₀ (· = v)) := by
  intro D S S₀ ρ d L L₀ v g hM
  have hpX : ∀ z : Fin S₀.rank → AE D, d.pX *ᵥ (d.j0 *ᵥ z) = 0 := fun z => by
    rw [Matrix.mulVec_mulVec, d.pX_j0, Matrix.zero_mulVec]
  have hpY : ∀ z : Fin S₀.rank → AE D, d.pY *ᵥ (d.j0 *ᵥ z) = 0 := fun z => by
    rw [Matrix.mulVec_mulVec, d.pY_j0, Matrix.zero_mulVec]
  have hp0 : ∀ z : Fin S₀.rank → AE D, d.p0 *ᵥ (d.j0 *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, d.p0_j0, Matrix.one_mulVec]
  have key : ∀ z : Fin S₀.rank → AE D, d.j0 *ᵥ z ∈ latV S L (· = v) ↔ z ∈ latV S₀ L₀ (· = v) := fun z => by
    rw [hM, hpX, hpY, hp0]
    simp only [Pi.zero_apply, matrixColumnScaledByAdele_zero, zero_mem, implies_true, true_and]
  have hj : ∀ z : Fin S₀.rank → AE D, mt S (d.emb0 g) *ᵥ (d.j0 *ᵥ z) = d.j0 *ᵥ (mt S₀ g *ᵥ z) := fun z => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, d.wittDecomp_anisotropicEmbedding_inclAnisotropic]
  constructor
  · intro h z hz
    rw [← key, ← key, ← hj]
    exact h _ (matrix_mulVec_mem_adeleIdealSupportedOnPlaces _ _ hz)
  · intro h y hy
    have eX : d.pX *ᵥ (mt S (d.emb0 g) *ᵥ y) = d.pX *ᵥ y := by rw [Matrix.mulVec_mulVec, d.wittDecomp_projX_anisotropicEmbedding]
    have eY : d.pY *ᵥ (mt S (d.emb0 g) *ᵥ y) = d.pY *ᵥ y := by rw [Matrix.mulVec_mulVec, d.wittDecomp_projY_anisotropicEmbedding]
    have e0 : d.p0 *ᵥ (mt S (d.emb0 g) *ᵥ y) = mt S₀ g *ᵥ (d.p0 *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, d.wittDecomp_projAnisotropic_anisotropicEmbedding]
    rw [hM y, hM (mt S (d.emb0 g) *ᵥ y), eX, eY, e0]
    exact and_congr Iff.rfl (and_congr Iff.rfl (h _ (matrix_mulVec_mem_adeleIdealSupportedOnPlaces _ _ hy)))

end GlobalTheory.FinPl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselUnfoldingOrbitMemParabolicMulStabiliser
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

noncomputable section

set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.FinPl.OrbitCoset

variable {D : D7}

theorem mem_congGrp_iff' (V : HSp D) (I : Ideal (AE D)) (g : GA D V) :
    g ∈ congGrp V I ↔ (mt V g).map (Ideal.Quotient.mk I) = 1 := by
  unfold congGrp
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Units.ext_iff]
  rfl

theorem matrixTransform_wittCoreEmbedding {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (h : GA D S₀) :
    mt S (d.emb0 h) = d.jX ⬝ d.pX + d.j0 ⬝ mt S₀ h ⬝ d.p0 + d.jY ⬝ d.pY := by
  conv_lhs => rw [← Matrix.mul_one (mt S (d.emb0 h)), ← d.sum_eq_one]
  simp only [Matrix.mul_add, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, d.wittDecomp_anisotropicEmbedding_inclY]

theorem wittCoreEmbedding_mem_supportedSubgroup {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (P : Pl D → Prop) {h : GA D S₀}
    (hh : h ∈ grpAt S₀ P) : d.emb0 h ∈ grpAt S P := by
  rw [grpAt, mem_congGrp_iff'] at hh ⊢
  have hadd : ∀ A B : Matrix (Fin S.rank) (Fin S.rank) (AE D), (A + B).map (Ideal.Quotient.mk (idAt D P)) =
      A.map (Ideal.Quotient.mk (idAt D P)) + B.map (Ideal.Quotient.mk (idAt D P)) :=
    fun A B => Matrix.map_add _ (Ideal.Quotient.mk (idAt D P)).map_add A B
  have key : (mt S (d.emb0 h)).map (Ideal.Quotient.mk (idAt D P)) =
      (d.jX ⬝ d.pX + d.j0 ⬝ d.p0 + d.jY ⬝ d.pY).map (Ideal.Quotient.mk (idAt D P)) := by
    rw [matrixTransform_wittCoreEmbedding]; simp only [hadd, Matrix.map_mul, hh, Matrix.mul_one]
  rw [key, d.sum_eq_one]
  exact Matrix.map_one _ (Ideal.Quotient.mk (idAt D P)).map_zero (Ideal.Quotient.mk (idAt D P)).map_one

theorem emb_mem_grpAt' {S A B : HSp D} (o : OrthDec S A B) {P : Pl D → Prop} {a : GA D A} (ha : a ∈ grpAt A P) :
    o.emb (a, 1) ∈ grpAt S P := by
  rw [grpAt, mem_congGrp_iff'] at ha ⊢
  have hadd : ∀ M N : Matrix (Fin S.rank) (Fin S.rank) (AE D), (M + N).map (Ideal.Quotient.mk (idAt D P)) =
      M.map (Ideal.Quotient.mk (idAt D P)) + N.map (Ideal.Quotient.mk (idAt D P)) :=
    fun M N => Matrix.map_add _ (Ideal.Quotient.mk (idAt D P)).map_add M N
  have key : (mt S (o.emb (a, 1))).map (Ideal.Quotient.mk (idAt D P)) =
      (o.jA ⬝ o.pA + o.jB ⬝ o.pB).map (Ideal.Quotient.mk (idAt D P)) := by
    rw [o.mt_emb, mt_one]; simp only [hadd, Matrix.map_mul, ha, Matrix.mul_one]
  rw [key, o.sum_eq_one]
  exact Matrix.map_one _ (Ideal.Quotient.mk (idAt D P)).map_zero (Ideal.Quotient.mk (idAt D P)).map_one

theorem inK_mul' {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a b : GA D S} (ha : InK S L P a) (hb : InK S L P b) :
    InK S L P (a * b) := by
  refine ⟨mul_mem ha.1 hb.1, fun y hy => ?_⟩
  have hy' : ∀ i, (mt S b *ᵥ y) i ∈ idAt D P := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)
  rw [mt_mul, ← Matrix.mulVec_mulVec, ← ha.2 _ hy', hb.2 y hy]

end GlobalTheory.FinPl.OrbitCoset

namespace GlobalTheory.FinPl.OrbitCoset

theorem orbit_coset : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ) (L : Lat B.V) (L₀ : Lat B.V₀) (v : Pl D), MonoAt B.d L L₀ v →
    ∀ n ∈ flagN B.d, n ∈ grpAt B.V (· = v) → ∀ a ∈ grpAt B.A (· = v), ∀ κ₀, InK B.V₀ L₀ (· = v) κ₀ → ∀ κ,
    InK B.V L (· = v) κ → ∃ r ∈ besGrp B.d B.o, r ∈ grpAt B.V (· = v) ∧ ∃ κ', InK B.V L (· = v) κ' ∧
      n * B.d.emb0 (B.o.emb (a, 1) * κ₀) * κ = r * κ' := by
  intro D σ B L L₀ v hM n hn hnv a ha κ₀ hκ₀ κ hκ
  refine ⟨n * embA B.d B.o a, mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨a, rfl⟩),
    mul_mem hnv (wittCoreEmbedding_mem_supportedSubgroup B.d _ (emb_mem_grpAt' B.o ha)), B.d.emb0 κ₀ * κ,
    inK_mul' ⟨wittCoreEmbedding_mem_supportedSubgroup B.d _ hκ₀.1, (carriesLattice_wittEmbedding_iff_core D B.V B.V₀ σ B.d L L₀ v κ₀ hM).2 hκ₀.2⟩ hκ, ?_⟩
  rw [map_mul, embA_apply]
  group

end GlobalTheory.FinPl.OrbitCoset

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselUnfoldingOrbitMemParabolicMulStabiliserStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselUnfolding_orbit_mem_parabolic_mul_stabiliser : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ) (L : Lat B.V) (L₀ : Lat B.V₀) (v : Pl D), MonoAt B.d L L₀ v → ∀ n ∈ flagN B.d, n ∈ grpAt B.V (· = v) → ∀ a ∈ grpAt B.A (· = v), ∀ κ₀, InK B.V₀ L₀ (· = v) κ₀ → ∀ κ, InK B.V L (· = v) κ → ∃ r ∈ besGrp B.d B.o, r ∈ grpAt B.V (· = v) ∧ ∃ κ', InK B.V L (· = v) κ' ∧ n * B.d.emb0 (B.o.emb (a, 1) * κ₀) * κ = r * κ' := by
  first | exact @GlobalTheory.FinPl.OrbitCoset.orbit_coset | exact GlobalTheory.FinPl.OrbitCoset.orbit_coset | (intros; apply GlobalTheory.FinPl.OrbitCoset.orbit_coset <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBilinearEquivariantOrthogonalSummandLift
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBilinearEquivariantOrthogonalSummandLift
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
open GlobalTheory.FinPl GlobalTheory.FinPl.SrcGl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SrcTheta

section Lift

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S A L T : HSp D} (o : OrthDec S A L) {χS χT : (AE D)ˣ →* Circle}
  {om : Om S T}

theorem contAut_ker (hW : IsWeilDatumO ψ S T χS χT om) {φ : GA D A → ℂ} {Ξ : WO S T → ℂ} (hφ : IsContAut A φ)
    (hΞ : IsThetaFunO ψ S T Ξ) (h : GA D T) (u : WO L T) :
    IsContAut A fun a => φ a * om (o.emb (a, 1), h) Ξ ((o.resS T).symm (0, u)) := by
  refine ⟨fun γ hγ a => ?_, hφ.2.mul ((hW.om_cont Ξ hΞ _).comp
    ((o.continuous_emb.comp (continuous_id.prodMk continuous_const)).prodMk continuous_const))⟩
  have e := GlobalTheory.T.weilRepresentation_rational_translate_substitution D ψ _ _ _ _ _ hW Ξ hΞ _ (o.emb_mem_GQ hγ (one_mem _)) 1 (one_mem _) (o.emb (a, 1)) h
    ((o.resS T).symm (0, u))
  rw [← map_mul, Prod.mk_mul_mk, one_mul, one_mul, inv_one, mt_one, Matrix.one_mul] at e
  beta_reduce
  rw [hφ.1 γ hγ, e]
  congr 2
  rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add, Matrix.mul_assoc, OrthDec.pB_emb, mt_one, Matrix.one_mul]

theorem liftA_add_left (hA : CoCpt A) (vA : Vol A) (hW : IsWeilDatumO ψ S T χS χT om) {φ φ' : GA D A → ℂ}
    {Ξ : WO S T → ℂ} (hφ : IsContAut A φ) (hφ' : IsContAut A φ') (hΞ : IsThetaFunO ψ S T Ξ) :
    liftA o om vA (φ + φ') Ξ = liftA o om vA φ Ξ + liftA o om vA φ' Ξ := by
  funext h w
  simp only [liftA, Pi.add_apply, add_mul]
  exact integral_add (Comm.IsContAut.integrableOn hA vA (contAut_ker o hW hφ hΞ h _))
    (Comm.IsContAut.integrableOn hA vA (contAut_ker o hW hφ' hΞ h _))

theorem liftA_add_right (hA : CoCpt A) (vA : Vol A) (hW : IsWeilDatumO ψ S T χS χT om) {φ : GA D A → ℂ}
    {Ξ Ξ' : WO S T → ℂ} (hφ : IsContAut A φ) (hΞ : IsThetaFunO ψ S T Ξ) (hΞ' : IsThetaFunO ψ S T Ξ') :
    liftA o om vA φ (Ξ + Ξ') = liftA o om vA φ Ξ + liftA o om vA φ Ξ' := by
  funext h w
  simp only [liftA, map_add (f := _), Pi.add_apply, mul_add]
  exact integral_add (Comm.IsContAut.integrableOn hA vA (contAut_ker o hW hφ hΞ h _))
    (Comm.IsContAut.integrableOn hA vA (contAut_ker o hW hφ hΞ' h _))

theorem liftA_smul_left (vA : Vol A) (c : ℂ) (φ : GA D A → ℂ) (Ξ : WO S T → ℂ) :
    liftA o om vA (c • φ) Ξ = c • liftA o om vA φ Ξ := by
  funext h w
  simp only [liftA, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul _ _

theorem liftA_smul_right (vA : Vol A) (c : ℂ) (φ : GA D A → ℂ) (Ξ : WO S T → ℂ) :
    liftA o om vA φ (c • Ξ) = c • liftA o om vA φ Ξ := by
  funext h w
  simp only [liftA, map_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
  exact integral_const_mul _ _

theorem liftA_equiv (vA : Vol A) (hW : IsWeilDatumO ψ S T χS χT om) {φ : GA D A → ℂ} {Ξ : WO S T → ℂ}
    (hφ : IsContAut A φ) (hΞ : IsThetaFunO ψ S T Ξ) (a : GA D A) :
    liftA o om vA (fun x => φ (x * a)) (om (o.emb (a, 1), 1) Ξ) = liftA o om vA φ Ξ := by
  funext h w
  simp only [liftA]
  refine Eq.trans ?_ (Comm.integral_right vA (contAut_ker o hW hφ hΞ h w).1 a)
  congr 1
  funext x
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]

end Lift

theorem exists_linear_of_rel {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (P : Submodule ℂ M) (R : M → N → Prop) (hex : ∀ x ∈ P, ∃! y, R x y)
    (hlin : ∀ (c : ℂ) x y x' y', R x y → R x' y' → R (c • x + x') (c • y + y')) :
    ∃ G : M →ₗ[ℂ] N, (∀ x, ∃ x', R x' (G x)) ∧ ∀ x ∈ P, R x (G x) := by
  choose F hF hFu using fun x : P => hex x.1 x.2
  have hc : ∀ (c : ℂ) (x x' : P), F (c • x + x') = c • F x + F x' := fun c x x' =>
    (hFu (c • x + x') _ (hlin c _ _ _ _ (hF x) (hF x'))).symm
  have h0 : F 0 = 0 := by
    have := hc 1 0 0
    simp only [one_smul, add_zero] at this
    exact left_eq_add.1 this
  let F' : P →ₗ[ℂ] N :=
    { toFun := F
      map_add' := fun x y => by simpa using hc 1 x y
      map_smul' := fun c x => by simpa [h0] using hc c x 0 }
  obtain ⟨Q, hQ⟩ := P.exists_isCompl
  refine ⟨F' ∘ₗ P.linearProjOfIsCompl Q hQ, fun x => ⟨_, hF _⟩, fun x hx => ?_⟩
  have e : P.linearProjOfIsCompl Q hQ x = ⟨x, hx⟩ := Submodule.linearProjOfIsCompl_apply_left hQ ⟨x, hx⟩
  rw [LinearMap.comp_apply, e]
  exact hF ⟨x, hx⟩

theorem exists_theta : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → CoCpt A → ∀ (vA : Vol A) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n), IsSumFrame o ζ α α₀ → ∃ lS : kˣ →* ℂˣ, (CharUnramAt D χT p.v → IsUnram lS) ∧ ∀ (LS : Lat S) (LT : Lat T) (f₀ : WO S T → ℂ), IsSelfDualC S LS → IsSelfDualC T LT → Vac ψ S T LS LT (· = p.v) f₀ → ∃ θ : GlobalTheory.FinPl.SrcGl.CA A →ₗ[ℂ] (Matrix n (n' ⊕ Fin 1) k → ℂ) →ₗ[ℂ] (GA D T → WO L T → ℂ), (∀ (v : GlobalTheory.FinPl.SrcGl.CA A) (Φ : Matrix n (n' ⊕ Fin 1) k → ℂ) (f : WO S T → ℂ), Over ψ α₀ β LS LT f₀ Φ f → θ v Φ = liftA o om vA v f) ∧ ∀ (g : GL n' k) (v : GlobalTheory.FinPl.SrcGl.CA A) (Φ : Matrix n (n' ⊕ Fin 1) k → ℂ), Φ ∈ SB (Matrix n (n' ⊕ Fin 1) k) → θ (GlobalTheory.FinPl.SrcGl.caRep α g v) (fun x => Φ (x * (GlobalTheory.FinPl.SrcGl.blk g).val)) = ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ • θ v Φ := by
  intro D k _ _ _ _ p n n' _ _ _ _ ψ S A L T o ζ _ hA vA χS χT om hW α α₀ β hsum
  obtain ⟨lS, lT, hlS, -, hlin⟩ := GlobalTheory.T.splitPlace_linearModel_latticeVacuum_base D k p ψ S T χS χT om hW
  refine ⟨lS, hlS, fun LS LT f₀ hLS hLT hvac => ?_⟩
  obtain ⟨hex, hth, -⟩ := GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n (n' ⊕ Fin 1) ψ hW.std S T α₀ β LS LT hLS hLT f₀ hvac
  obtain ⟨G, hG, hGP⟩ := exists_linear_of_rel (SB (Matrix n (n' ⊕ Fin 1) k)) (Over ψ α₀ β LS LT f₀) hex
    (fun c x y x' y' h h' => (hlin n _ α₀ β LS LT f₀ x y h).2.2 c x' y' h')
  have hGt : ∀ Φ, IsThetaFunO ψ S T (G Φ) := fun Φ => (hG Φ).elim fun x hx => (hth _ _ hx).1
  have hGf : ∀ Φ f, Over ψ α₀ β LS LT f₀ Φ f → G Φ = f := fun Φ f h =>
    (hex Φ h.2.2.2.1).unique (hGP Φ h.2.2.2.1) h
  let θ : CA A →ₗ[ℂ] (Matrix n (n' ⊕ Fin 1) k → ℂ) →ₗ[ℂ] (GA D T → WO L T → ℂ) :=
    LinearMap.mk₂ ℂ (fun v Φ => liftA o om vA v (G Φ))
      (fun v v' Φ => liftA_add_left o hA vA hW v.2 v'.2 (hGt Φ))
      (fun c v Φ => liftA_smul_left o vA c v (G Φ))
      (fun v Φ Φ' => by rw [map_add (f := _)]; exact liftA_add_right o hA vA hW v.2 (hGt Φ) (hGt Φ'))
      (fun c v Φ => by rw [map_smul]; exact liftA_smul_right o vA c v (G Φ))
  have hθ : ∀ (v : CA A) Φ, θ v Φ = liftA o om vA v (G Φ) := fun _ _ => rfl
  refine ⟨θ, fun v Φ f h => by rw [hθ, hGf Φ f h], fun g v Φ hΦ => ?_⟩
  have h1 := (hlin n _ α₀ β LS LT f₀ Φ _ (hGP Φ hΦ)).1 (blk g) 1
  have hdet : Matrix.GeneralLinearGroup.det (blk g) = Matrix.GeneralLinearGroup.det g := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply]
  have hemb : α₀.gl (blk g) = o.emb (α.gl g, 1) := by
    rw [Comm.emb_gl hsum]
    congr 1
  have hfun : (fun x : Matrix n (n' ⊕ Fin 1) k => (lS (Matrix.GeneralLinearGroup.det (blk g)) : ℂ) *
      (lT (Matrix.GeneralLinearGroup.det (1 : GL n k)) : ℂ) * Φ (((1 : GL n k)⁻¹ : GL n k).val * x * (blk g).val)) =
      (lS (Matrix.GeneralLinearGroup.det g) : ℂ) • fun x => Φ (x * (blk g).val) := by
    funext x
    simp only [hdet, map_one, Units.val_one, mul_one, inv_one, Matrix.one_mul, Pi.smul_apply, smul_eq_mul]
  rw [hfun, hemb, map_one] at h1
  have h2 : θ (caRep α g v) ((lS (Matrix.GeneralLinearGroup.det g) : ℂ) • fun x => Φ (x * (blk g).val)) = θ v Φ := by
    rw [hθ, hθ, hGf _ _ h1]
    exact liftA_equiv o vA hW v.2 (hGt Φ) (α.gl g)
  rw [← h2, map_smul, inv_smul_smul₀ (Units.ne_zero _)]

end GlobalTheory.FinPl.SrcTheta

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBilinearEquivariantOrthogonalSummandLiftStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
open GlobalTheory.FinPl GlobalTheory.FinPl.SrcGl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bilinear_equivariant_orthogonalSummandLift : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → CoCpt A → ∀ (vA : Vol A) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n), IsSumFrame o ζ α α₀ → ∃ lS : kˣ →* ℂˣ, (CharUnramAt D χT p.v → IsUnram lS) ∧ ∀ (LS : Lat S) (LT : Lat T) (f₀ : WO S T → ℂ), IsSelfDualC S LS → IsSelfDualC T LT → Vac ψ S T LS LT (· = p.v) f₀ → ∃ θ : GlobalTheory.FinPl.SrcGl.CA A →ₗ[ℂ] (Matrix n (n' ⊕ Fin 1) k → ℂ) →ₗ[ℂ] (GA D T → WO L T → ℂ), (∀ (v : GlobalTheory.FinPl.SrcGl.CA A) (Φ : Matrix n (n' ⊕ Fin 1) k → ℂ) (f : WO S T → ℂ), Over ψ α₀ β LS LT f₀ Φ f → θ v Φ = liftA o om vA v f) ∧ ∀ (g : GL n' k) (v : GlobalTheory.FinPl.SrcGl.CA A) (Φ : Matrix n (n' ⊕ Fin 1) k → ℂ), Φ ∈ SB (Matrix n (n' ⊕ Fin 1) k) → θ (GlobalTheory.FinPl.SrcGl.caRep α g v) (fun x => Φ (x * (GlobalTheory.FinPl.SrcGl.blk g).val)) = ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ • θ v Φ := by
  first | exact @GlobalTheory.FinPl.SrcTheta.exists_theta | exact GlobalTheory.FinPl.SrcTheta.exists_theta | (intros; apply GlobalTheory.FinPl.SrcTheta.exists_theta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergIsotropicFixesVacuum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.FlatFix

variable {D : D7}

theorem two_ne_zero_at (w : Pl D) : (2 : Fv D.host.F w) ≠ 0 := by
  rw [← map_ofNat (algebraMap D.host.F (Fv D.host.F w)) 2]
  exact (map_ne_zero_iff _ (algebraMap D.host.F (Fv D.host.F w)).injective).2 two_ne_zero

theorem two_inv_int (w : Pl D) (hw : (2 : 𝓞 D.host.F) ∉ w.asIdeal) :
    (2⁻¹ : Fv D.host.F w) ∈ w.adicCompletionIntegers D.host.F := by
  have h3 : HeightOneSpectrum.valuation D.host.F w (2 : D.host.F) = 1 := by
    have := HeightOneSpectrum.valuation_of_algebraMap (K := D.host.F) w (2 : 𝓞 D.host.F)
    rw [HeightOneSpectrum.intValuation_eq_one_iff.2 hw] at this
    rw [← this]
    congr 1
  have h2 : ((2 : D.host.F) : Fv D.host.F w) = 2 := by
    rw [← map_ofNat (algebraMap D.host.F (Fv D.host.F w)) 2]; rfl
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, ← h2,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', h3, inv_one]

theorem finite_two (P : Pl D → Prop) : {v : Pl D | P v ∧ (2 : 𝓞 D.host.F) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {(2 : 𝓞 D.host.F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact two_ne_zero
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  exact (Ideal.dvd_span_singleton).2 hv.2


open Classical in
def halfOff (P : Pl D → Prop) : Af D.host.F :=
  RestrictedProduct.mk (fun w => if P w ∧ (2 : 𝓞 D.host.F) ∉ w.asIdeal then (2⁻¹ : Fv D.host.F w) else 0)
    (Filter.Eventually.of_forall fun w => by
      split_ifs with h
      · exact two_inv_int w h.2
      · exact zero_mem _)

open Classical in
theorem evalV_halfOff (P : Pl D → Prop) (w : Pl D) :
    evalV D.host.F w (halfOff P) = if P w ∧ (2 : 𝓞 D.host.F) ∉ w.asIdeal then (2⁻¹ : Fv D.host.F w) else 0 := rfl

theorem halfOff_int (P : Pl D → Prop) : halfOff P ∈ intAf D.host.F := by
  classical
  intro w
  rw [evalV_halfOff]
  split_ifs with h
  · exact two_inv_int w h.2
  · exact zero_mem _

theorem pair_add (a b : Af D.host.F) : pairA D.host.F 0 (a + b) = pairA D.host.F 0 a + pairA D.host.F 0 b :=
  Prod.ext (add_zero (0 : Ainf D.host.F)).symm rfl

theorem sum_pair {ι : Type} (s : Finset ι) (α : ι → Af D.host.F) :
    ∑ i ∈ s, pairA D.host.F 0 (α i) = pairA D.host.F 0 (∑ i ∈ s, α i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Prod.ext rfl rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, pair_add]

theorem indicatorIdempotent_eq_add_sum (P : Pl D → Prop) (Qs : Finset (Pl D)) (hQ : ∀ v, v ∈ Qs ↔ P v ∧ (2 : 𝓞 D.host.F) ∈ v.asIdeal)
    (ε : Pl D → AF D.host.F) (hε : ∀ v ∈ Qs, IsPlaceIdem D v (ε v)) :
    GlobalTheory.SelfDualAt.cP P = pairA D.host.F 0 (halfOff P + halfOff P) + ∑ v ∈ Qs, ε v := by
  classical
  choose! α hα h1 h0 using hε
  rw [Finset.sum_congr rfl hα, sum_pair, ← pair_add]
  unfold GlobalTheory.SelfDualAt.cP
  congr 1
  refine FiniteAdeleRing.ext (R := 𝓞 D.host.F) D.host.F fun w => ?_
  change evalV D.host.F w (GlobalTheory.SelfDualAt.indP P) = evalV D.host.F w (halfOff P + halfOff P + ∑ i ∈ Qs, α i)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_add (f := _), map_sum, GlobalTheory.SelfDualAt.evalV_indP, evalV_halfOff]
  by_cases hw : w ∈ Qs
  · obtain ⟨hP, h2⟩ := (hQ w).1 hw
    rw [Finset.sum_eq_single_of_mem w hw (fun v hv hvw => h0 v hv w (Ne.symm hvw)), h1 w hw, if_pos hP,
      if_neg (fun h => h.2 h2), zero_add, zero_add]
  · rw [Finset.sum_eq_zero (fun v hv => h0 v hv w (fun h => hw (h ▸ hv))), add_zero]
    by_cases hP : P w
    · have h2 : (2 : 𝓞 D.host.F) ∉ w.asIdeal := fun h2 => hw ((hQ w).2 ⟨hP, h2⟩)
      rw [if_pos hP, if_pos ⟨hP, h2⟩, ← two_mul, mul_inv_cancel₀ (two_ne_zero_at w)]
    · rw [if_neg hP, if_neg (fun h => hP h.1), add_zero]

theorem int_alg_pair {β : Af D.host.F} (hβ : β ∈ intAf D.host.F) :
    finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β)) ∈ intAE D := by
  have e : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β) = pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  have e2 : finPart D (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) =
      β ⊗ₜ[D.host.F] ((1 : 𝓞 D.host.E) : D.host.E) := by
    show Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id _ _) (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) = _
    rw [Algebra.TensorProduct.map_tmul]; rfl
  rw [e, e2]
  exact AddSubgroup.subset_closure ⟨β, hβ, 1, rfl⟩

theorem fix_add {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f : WO S T → ℂ} {z : WO S T}
    (hiso : ∀ c c' : AE D, symplOH S T (c • z) (c' • z) = 0) {a b : AE D}
    (ha : heisO ψ S T (a • z) f = f) (hb : heisO ψ S T (b • z) f = f) : heisO ψ S T ((a + b) • z) f = f := by
  have key := GlobalTheory.LatVac.heisO_heisO ψ (a • z) (b • z) f
  rw [hb, ha, hiso a b, ψ.map_zero_eq_one, one_smul, ← add_smul] at key
  exact key.symm

end GlobalTheory.FinPl.FlatFix


open GlobalTheory.FinPl.FlatFix in
theorem GlobalTheory.FinPl.FlatFix.fix_of_isotropic : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (LS : Lat S) (LT : Lat T) (P : Pl D → Prop), IsSelfDualC S LS → IsSelfDualC T LT → (∀ v, P v → Tame D v) → ∀ f : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (LS : Set _) (LT : Set _) P) f → ∀ z ∈ latO S T (LS : Set _) (LT : Set _) P, (∀ c c' : AE D, symplOH S T (c • z) (c' • z) = 0) → heisO ψ S T z f = f := by
  intro D ψ S T LS LT P _ _ hT f hf z hz hiso
  classical
  have hfix_split : ∀ e, IsSplitIdem D e → heisO ψ S T (e • z) f = f := fun e he =>
    hf.2 e he _ (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ P e (GlobalTheory.SplitHomLattice.idem_int he) z hz)
      (fun i j => by rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he.1])
  have hQ := finite_two (D := D) P
  have hmemQ : ∀ v, v ∈ hQ.toFinset ↔ P v ∧ (2 : 𝓞 D.host.F) ∈ v.asIdeal := fun v => hQ.mem_toFinset
  have hch : ∀ v, v ∈ hQ.toFinset → ∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D v ε ∧
      e + cA D e = algebraMap (AF D.host.F) (AE D) ε := by
    intro v hv
    obtain ⟨hPv, h2⟩ := (hmemQ v).1 hv
    rcases (hT v hPv).2 with h | h
    · exact absurd h2 h
    · exact h
  choose! e ε he hε hsum using hch
  have hdec := indicatorIdempotent_eq_add_sum P hQ.toFinset hmemQ ε hε
  have hzc : algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP P) • z = z := by
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact GlobalTheory.SelfDualAt.algebraMap_placeIdempotent_mul P _ (LatMem.latO_mxAt hz i j)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hzc, hdec, map_add (f := _), map_sum]
  refine fix_add hiso ?_ ?_
  · have hm := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ P _ (int_alg_pair (halfOff_int P)) z hz
    have e2 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (halfOff P + halfOff P)) • z =
        2 • (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (halfOff P)) • z) := by
      rw [pair_add, map_add (f := _), add_smul, two_nsmul]
    rw [e2]
    exact hf.1 _ hm
  · refine Finset.sum_induction _ (fun c => heisO ψ S T (c • z) f = f) (fun a b ha hb => fix_add hiso ha hb) ?_ ?_
    · rw [zero_smul]; exact GlobalTheory.LatVac.heisO_zero ψ f
    · intro v hv
      rw [← hsum v hv]
      exact fix_add hiso (hfix_split _ (he v hv)) (hfix_split _ (GlobalTheory.IdemSumVac.isSplitIdem_cA (he v hv)))

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OffIdempotentMemIdealTwoIntegers
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OffIdempotentMemIdealTwoIntegers
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OffIdemTwo
open GlobalTheory.IdemSupport GlobalTheory.OffIdemDen

theorem exists_split {K : Type} [Field K] [NumberField K] (c d : 𝓞 K) (hc0 : c ≠ 0) (hd : d ≠ 0) :
    ∃ x y : 𝓞 K, (x : K) / c * c + (y : K) / d * d = 1 ∧
      (∀ Q : HeightOneSpectrum (𝓞 K), ¬ (c ∈ Q.asIdeal ∧ d ∈ Q.asIdeal) →
        ∃ g t : 𝓞 K, g ≠ 0 ∧ g ∉ Q.asIdeal ∧ (x : K) / c = t * (g : K)⁻¹) ∧
      (∀ Q : HeightOneSpectrum (𝓞 K), ¬ (c ∈ Q.asIdeal ∧ d ∈ Q.asIdeal) →
        ∃ g t : 𝓞 K, g ≠ 0 ∧ g ∉ Q.asIdeal ∧ (y : K) / d = t * (g : K)⁻¹) := by
  obtain ⟨G, hG⟩ : ∃ G : Ideal (𝓞 K), G = Ideal.span {c} ⊔ Ideal.span {d} := ⟨_, rfl⟩
  obtain ⟨I', hI'⟩ : G ∣ Ideal.span {c} := Ideal.dvd_iff_le.2 (hG ▸ le_sup_left)
  obtain ⟨D', hD'⟩ : G ∣ Ideal.span {d} := Ideal.dvd_iff_le.2 (hG ▸ le_sup_right)
  have hG0 : G ≠ 0 := by
    intro h
    have : c ∈ G := hG ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
    rw [h, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    exact hc0 this
  have hcop : I' ⊔ D' = ⊤ := by
    apply mul_left_cancel₀ hG0
    rw [Ideal.mul_sup, ← hI', ← hD', Ideal.mul_top, hG]
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 (hcop.symm ▸ Submodule.mem_top : (1 : 𝓞 K) ∈ I' ⊔ D')
  have coe0 : ∀ w : 𝓞 K, w ≠ 0 → (w : K) ≠ 0 := fun w hw => RingOfIntegers.coe_ne_zero_iff.2 hw
  have hint : ∀ (w z : 𝓞 K), w ≠ 0 → (∀ g ∈ G, g * z ∈ Ideal.span {w}) →
      ∀ Q : HeightOneSpectrum (𝓞 K), ¬ (c ∈ Q.asIdeal ∧ d ∈ Q.asIdeal) →
      ∃ g t : 𝓞 K, g ≠ 0 ∧ g ∉ Q.asIdeal ∧ (z : K) / w = t * (g : K)⁻¹ := by
    intro w z hw hz Q hQ
    have hGQ : ¬ G ≤ Q.asIdeal := fun h => hQ
      ⟨h (hG ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)),
       h (hG ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))⟩
    obtain ⟨g, hg, hgQ⟩ := Set.not_subset.1 hGQ
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (hz g hg)
    have hg0 : g ≠ 0 := fun h => hgQ (h ▸ Q.asIdeal.zero_mem)
    have hgE := coe0 g hg0
    have hwE := coe0 w hw
    have htE : (t : K) * w = g * z := by
      have := congrArg (algebraMap (𝓞 K) K) ht
      rwa [map_mul, map_mul] at this
    refine ⟨g, t, hg0, hgQ, ?_⟩
    field_simp
    linear_combination -htE
  refine ⟨x, y, ?_, hint c x hc0 fun g hg => hI' ▸ Ideal.mul_mem_mul hg hx,
    hint d y hd fun g hg => hD' ▸ Ideal.mul_mem_mul hg hy⟩
  rw [div_mul_cancel₀ _ (coe0 c hc0), div_mul_cancel₀ _ (coe0 d hd)]
  have := congrArg (algebraMap (𝓞 K) K) hxy
  rwa [map_add, map_one] at this

theorem off_comp {D : D7} {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : Comp D Φ) {e : AE D}
    {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e SS) :
    (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS) → Φ (1 - e - cA D e) Q = 0) ∧
    ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Φ (1 - e - cA D e) Q ∈ Q.adicCompletionIntegers D.host.E := by
  obtain ⟨⟨es, hes, rfl⟩, horth⟩ := he
  have hdl : ∀ P ∈ SS, IsDelta Φ P (es P) := fun P hP => delta_of_isIdemAt hΦ (hes P hP)
  have hdc : ∀ P ∈ SS, IsDelta Φ (cP P) (cA D (es P)) := fun P hP => delta_conj hΦ (hdl P hP)
  have hE : ∀ Q, Φ (∑ P ∈ SS, es P) Q = ∑ P ∈ SS, Φ (es P) Q := fun Q => map_sum (evQ Φ Q) _ _
  have hC : ∀ Q, Φ (cA D (∑ P ∈ SS, es P)) Q = ∑ P ∈ SS, Φ (cA D (es P)) Q := fun Q => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]; exact map_sum (evQ Φ Q) _ _
  have hO : ∀ Q, Φ (1 - ∑ P ∈ SS, es P - cA D (∑ P ∈ SS, es P)) Q =
      1 - Φ (∑ P ∈ SS, es P) Q - Φ (cA D (∑ P ∈ SS, es P)) Q := fun Q => by
    change evQ Φ Q _ = _
    rw [map_sub, map_sub, map_one]; rfl
  have hprod : ∀ Q, Φ (∑ P ∈ SS, es P) Q * Φ (cA D (∑ P ∈ SS, es P)) Q = 0 := fun Q => by
    rw [← ev_mul, horth, ev_zero]

  have hzero : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), (Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS) →
      Φ (1 - ∑ P ∈ SS, es P - cA D (∑ P ∈ SS, es P)) Q = 0 := by
    intro Q hQQ
    rw [hO]
    rcases hQQ with hQ | hQ
    · have h1 : Φ (∑ P ∈ SS, es P) Q = 1 := by
        rw [hE, Finset.sum_eq_single Q (fun P hP hne => (hdl P hP).2.2 Q (Ne.symm hne))
          (fun h => absurd hQ h), (hdl Q hQ).2.1]
      have h2 := hprod Q
      rw [h1, one_mul] at h2
      rw [h1, h2, sub_self, sub_zero]
    · rw [conjP_eq_cP] at hQ
      have h1 : Φ (cA D (∑ P ∈ SS, es P)) Q = 1 := by
        rw [hC, Finset.sum_eq_single (cP Q) (fun P hP hne => (hdc P hP).2.2 Q (fun h => hne (by
            rw [h, cP_cP])))
          (fun h => absurd hQ h)]
        have := (hdc (cP Q) hQ).2.1
        rwa [cP_cP] at this
      have h2 := hprod Q
      rw [h1, mul_one] at h2
      rw [h1, h2, sub_zero, sub_self]

  have hoint : ∀ Q : HeightOneSpectrum (𝓞 D.host.E),
      Φ (1 - ∑ P ∈ SS, es P - cA D (∑ P ∈ SS, es P)) Q ∈ Q.adicCompletionIntegers D.host.E := by
    intro Q
    rw [hO, hE, hC]
    exact sub_mem (sub_mem (Q.adicCompletionIntegers D.host.E).one_mem
      (sum_mem fun P hP => delta_mem (hdl P hP) Q)) (sum_mem fun P hP => delta_mem (hdc P hP) Q)
  exact ⟨hzero, hoint⟩

theorem term_int {D : D7} {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : Comp D Φ) (o : AE D)
    (hoint : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Φ o Q ∈ Q.adicCompletionIntegers D.host.E) (u : D.host.E)
    (hu : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Φ o Q = 0 ∨ ∃ g t : 𝓞 D.host.E, g ≠ 0 ∧ g ∉ Q.asIdeal ∧
      u = t * (g : D.host.E)⁻¹) : finPart D (o * incA D u) ∈ intAE D := by
  rw [hΦ.int]
  intro Q
  rw [ev_mul, hΦ.inc]
  rcases hu Q with h0 | ⟨g, t, hg0, hgQ, heq⟩
  · rw [h0, zero_mul]
    exact (Q.adicCompletionIntegers D.host.E).zero_mem
  · refine mul_mem (hoint Q) ?_
    have : algebraMap D.host.E (Q.adicCompletion D.host.E) u ∈ Q.adicCompletionIntegers D.host.E := by
      rw [heq, map_mul]
      exact mul_mem (Q.coe_mem_adicCompletionIntegers t) ((inv_mem_iff Q hg0).2 hgQ)
    exact this

theorem off_two : ∀ (D : D7) (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ c : ℕ, 0 < c → ∀ d : 𝓞 D.host.E, d ≠ 0 → (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (c : 𝓞 D.host.E) ∈ Q.asIdeal → d ∈ Q.asIdeal → Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS) → ∃ a₁ a₂ : AE D, finPart D a₁ ∈ intAE D ∧ finPart D a₂ ∈ intAE D ∧ 1 - e - cA D e = a₁ * incA D (c : D.host.E) + a₂ * incA D (d : D.host.E) := by
  intro D e SS he c hc d hd hcd
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨hzero, hoint⟩ := off_comp hΦ he
  generalize 1 - e - cA D e = o at hzero hoint ⊢
  have hc0 : (c : 𝓞 D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  obtain ⟨x, y, hxy, hx, hy⟩ := exists_split (c : 𝓞 D.host.E) d hc0 hd
  have hcast : ((c : 𝓞 D.host.E) : D.host.E) = (c : D.host.E) := map_natCast _ c
  rw [hcast] at hxy hx
  refine ⟨o * incA D ((x : D.host.E) / c), o * incA D ((y : D.host.E) / d),
    term_int hΦ o hoint _ fun Q => ?_, term_int hΦ o hoint _ fun Q => ?_, ?_⟩
  · by_cases h : (c : 𝓞 D.host.E) ∈ Q.asIdeal ∧ d ∈ Q.asIdeal
    · exact Or.inl (hzero Q (hcd Q h.1 h.2))
    · exact Or.inr (hx Q h)
  · by_cases h : (c : 𝓞 D.host.E) ∈ Q.asIdeal ∧ d ∈ Q.asIdeal
    · exact Or.inl (hzero Q (hcd Q h.1 h.2))
    · exact Or.inr (hy Q h)
  · have h1 := congrArg (incA D) hxy
    rw [map_add (f := _), map_mul, map_mul, map_one] at h1
    rw [mul_assoc, mul_assoc, ← mul_add, h1, mul_one]

end GlobalTheory.OffIdemTwo
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OffIdempotentMemIdealTwoIntegersStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.offIdempotent_mem_ideal_two_integers : ∀ (D : D7) (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ c : ℕ, 0 < c → ∀ d : 𝓞 D.host.E, d ≠ 0 → (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (c : 𝓞 D.host.E) ∈ Q.asIdeal → d ∈ Q.asIdeal → Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS) → ∃ a₁ a₂ : AE D, finPart D a₁ ∈ intAE D ∧ finPart D a₂ ∈ intAE D ∧ 1 - e - cA D e = a₁ * incA D (c : D.host.E) + a₂ * incA D (d : D.host.E) := by
  first | exact @GlobalTheory.OffIdemTwo.off_two | exact GlobalTheory.OffIdemTwo.off_two | (intros; apply GlobalTheory.OffIdemTwo.off_two <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatWeilRepresentationCores
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatWeilRepresentationCores
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.FlatCommBF

variable {D : D7}

theorem sFinite_of_haar {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [LocallyCompactSpace G]
    [SecondCountableTopology G] (ν : Measure G) (h : ν.IsHaarMeasure) : SFinite ν := by
  haveI := h
  infer_instance

theorem continuous_psiUni (ψ : AddChar (AF D.host.F) ℂ) (hψ : Continuous ψ) (ρ : ℕ) :
    Continuous fun u : UX D ρ => psiUni ψ u.1 := by
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  have hv : Continuous fun u : UX D ρ => u.1.1 := Units.continuous_val.comp continuous_subtype_val
  unfold psiUni psiE upSum
  refine hψ.comp (ht.comp ?_)
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  split_ifs
  · exact (continuous_apply j).comp ((continuous_apply i).comp hv)
  · exact continuous_const

theorem jacT_integral (ψ : AddChar (AF D.host.F) ℂ) {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (y : Mx D S.rank ρ) (n : GA D T) {U : Type} [MeasurableSpace U] (m : Measure U) (G : U → WO S T₀ → ℂ)
    (w : WO S T₀) : jacT ψ d S y n (fun w' => ∫ u, G u w' ∂m) w = ∫ u, jacT ψ d S y n (G u) w ∂m := by
  simp only [jacT, heisO, Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul, integral_const_mul]

theorem jacT_smul (ψ : AddChar (AF D.host.F) ℂ) {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (y : Mx D S.rank ρ) (n : GA D T) (c : ℂ) (f : WO S T₀ → ℂ) :
    jacT ψ d S y n (c • f) = c • jacT ψ d S y n f := by
  funext w
  simp only [jacT, heisO, Pi.smul_apply, smul_eq_mul]
  ring


set_option maxHeartbeats 400000 in
theorem flatBF_om : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → ∀ h₀, ∀ n ∈ radX J.d, ∀ h', flatBF s (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) = s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (flatBF s Ψ)) := by
  intro D ψ ρ B J s om' hom' Ψ hΨ h₀ n hn h'
  have hstd : IsStdChar D ψ (-1) := s.weil.std
  obtain ⟨hloc, hsc, -⟩ := GlobalTheory.UnitU.topology D ρ
  haveI := hloc
  haveI := hsc
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI : SFinite s.vU.ν := @sFinite_of_haar (UX D ρ) _ _ _ hloc hsc s.vU.ν s.vU.unit.1
  obtain ⟨hbase, -, hx0, -⟩ := GlobalTheory.Unf.base_point D J.W J.W₀ ρ J.d
  have hlin : LinearIndependent D.host.E J.d.e.transpose := hbase.1
  have hev := GlobalTheory.Unf.evalAt_xZero_yZero D ψ ρ B J s om' hom' Ψ hΨ
  have hom1 : s.om 1 Ψ = Ψ := by rw [map_one]; rfl

  have e3 : ∀ u : UX D ρ, evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1)
      (yZero B.V₀ ρ (vecB B.o B.ζ)) = s.om₀ (1, h') (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ u.1.1)
      (yZero B.V₀ ρ (vecB B.o B.ζ))) := by
    intro u
    have h := hev.1 u 1 1 (one_mem _) h'
    rw [map_one, one_mul, ← Prod.one_eq_mk, map_one, ← Prod.one_eq_mk, map_one] at h
    rw [h]
    simp only [opA, jacT_one]
    rfl
  have e2 : ∀ u : UX D ρ, evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1)
      (yZero B.V₀ ρ (vecB B.o B.ζ)) = opA ψ J.d B.o B.ζ s.om₀ n h' (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ
      (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ))) := by
    intro u
    have h := hev.1 u 1 n hn h'
    rw [map_one, ← Prod.one_eq_mk, map_one, ← Prod.one_eq_mk, map_one] at h
    exact h

  have hmix := GlobalTheory.MixValues.mixed_values D ψ hstd
  have thev : ∀ Φ, IsThetaFunO ψ B.V J.W Φ → ∀ u : UX D ρ, IsThetaFunO ψ B.V₀ J.W₀
      (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Φ (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ))) :=
    fun Φ hΦ u => hmix.2 B.V₀ J.W J.W₀ ρ J.d s.vT.μ s.vT.𝓕 s.vT.covol _
      (hmix.1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Φ hΦ _) _
  have thom : ∀ p, IsThetaFunO ψ B.V J.W (s.om p Ψ) := fun p => s.weil.om_pres p Ψ hΨ
  have hFL := GlobalTheory.Unf.Flat.flatLaw D ψ hstd B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.vU J.d.e hlin
    (yZero B.V₀ ρ (vecB B.o B.ζ))
  have thflat : ∀ p, IsThetaFunO ψ B.V₀ J.W₀ (flatBF s (s.om p Ψ)) := fun p => by
    have h := (hFL _ (thom p)).2
    rw [← hx0] at h
    exact h
  obtain ⟨M, hMi, hM⟩ := GlobalTheory.Unf.flatFun_majorant D ψ B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.χV s.χW s.om s.weil s.vU J.d.e hlin
    Ψ hΨ {1, (1, J.d.emb0 h'), (1, n * J.d.emb0 h'), (embA B.d B.o h₀, n * J.d.emb0 h')} (Set.toFinite _).isCompact
  simp only [← hx0] at hM
  have bound : ∀ p ∈ ({1, (1, J.d.emb0 h'), (1, n * J.d.emb0 h'), (embA B.d B.o h₀, n * J.d.emb0 h')} :
      Set (GA D B.V × GA D J.W)), ∀ (u : UX D ρ) w, ‖star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕
      (s.om p Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w‖ ≤ M u :=
    fun p hp u w => hM p hp _ w u
  have hmc := GlobalTheory.MixCont.mixed_coords_continuous D ψ B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.χV s.χW s.om s.weil Ψ hΨ
  have hxu : Continuous fun u : UX D ρ => xZero J.d ⬝ u.1.1 :=
    continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)
  have cont : ∀ p, Continuous fun q : UX D ρ × WO B.V₀ J.W₀ => star (psiUni ψ q.1.1) *
      evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om p Ψ) (xZero J.d ⬝ q.1.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) q.2 := by
    intro p
    have h1 : Continuous fun q : UX D ρ × WO B.V₀ J.W₀ => ((p, xZero J.d ⬝ q.1.1.1, yZero B.V₀ ρ (vecB B.o B.ζ), q.2) :
        (GA D B.V × GA D J.W) × Mx D J.W.rank ρ × Mx D B.V₀.rank ρ × WO B.V₀ J.W₀) :=
      continuous_const.prodMk ((hxu.comp continuous_fst).prodMk (continuous_const.prodMk continuous_snd))
    have h2 := hmc.2.comp h1
    have h3 : Continuous fun q : UX D ρ × WO B.V₀ J.W₀ => star (psiUni ψ q.1.1) :=
      ((continuous_psiUni ψ hstd.1.1 ρ).comp continuous_fst).star
    exact h3.mul h2
  have hci := GlobalTheory.CommInt.om_integral_comm D ψ B.V₀ J.W₀ s.χV s.χW s.om₀ s.weil₀ (UX D ρ) s.vU.ν

  have hF : ∀ u : UX D ρ, (fun w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) = star (psiUni ψ u.1) • evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) :=
    fun u => rfl
  have hG : ∀ (u : UX D ρ) w, s.om₀ (1, h') (fun w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) w =
      star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w := by
    intro u w
    rw [hF, map_smul, e3]
    rfl
  have step1 : ∀ w, s.om₀ (1, h') (flatBF s Ψ) w = ∫ u, star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν := by
    intro w
    have h := hci (fun u w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) (1, h') M
      (fun u => by rw [hF]; exact GlobalTheory.OrientedHeis.theta_smul _ (thev Ψ hΨ u))
      (by have h := cont 1; rw [hom1] at h; exact h)
      (by simp only [hG]; exact cont _)
      hMi
      (fun u w => ⟨by have h := bound 1 (by simp) u w; rw [hom1] at h; exact h, by rw [hG]; exact bound _ (by simp) u w⟩)
      (by have h := thflat 1; rw [hom1] at h; exact h) w
    exact h.trans (integral_congr_ae (Filter.Eventually.of_forall fun u => hG u w))

  have hF2 : ∀ u : UX D ρ, (fun w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) =
      star (psiUni ψ u.1) • evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) := fun u => rfl
  have hG2 : ∀ (u : UX D ρ) w, s.om₀ (B.o.emb (h₀, 1), 1) (fun w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) w =
      star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w := by
    intro u w
    rw [hF2, map_smul, e2, hev.1 u h₀ n hn h']
    rfl
  have step2 : ∀ w, s.om₀ (B.o.emb (h₀, 1), 1) (fun w => ∫ u, star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν) w =
      ∫ u, star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν := by
    intro w
    have h := hci (fun u w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) (B.o.emb (h₀, 1), 1) M
      (fun u => by rw [hF2]; exact GlobalTheory.OrientedHeis.theta_smul _ (thev _ (thom _) u))
      (cont _)
      (by simp only [hG2]; exact cont _)
      hMi
      (fun u w => ⟨bound _ (by simp) u w, by rw [hG2]; exact bound _ (by simp) u w⟩)
      (thflat _) w
    exact h.trans (integral_congr_ae (Filter.Eventually.of_forall fun u => hG2 u w))

  have hopa : opA ψ J.d B.o B.ζ s.om₀ n h' (flatBF s Ψ) =
      fun w => ∫ u, star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν := by
    funext w
    have h1 : s.om₀ (1, h') (flatBF s Ψ) = fun w => ∫ u, star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν :=
      funext step1
    show jacT ψ J.d B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ)) n (s.om₀ (1, h') (flatBF s Ψ)) w = _
    rw [h1, jacT_integral]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have h2 : (fun w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) =
        star (psiUni ψ u.1) • s.om₀ (1, h') (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ))) := by
      rw [e3]; rfl
    dsimp only
    rw [h2, jacT_smul, e2]
    rfl
  rw [hopa]
  funext w
  exact (step2 w).symm

end GlobalTheory.Unf.FlatCommBF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatWeilRepresentationCoresStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselToJacobiFlat_weilRepresentation_cores : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → ∀ h₀, ∀ n ∈ radX J.d, ∀ h', flatBF s (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) = s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (flatBF s Ψ)) := by
  first | exact @GlobalTheory.Unf.FlatCommBF.flatBF_om | exact GlobalTheory.Unf.FlatCommBF.flatBF_om | (intros; apply GlobalTheory.Unf.FlatCommBF.flatBF_om <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesFinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

theorem finite_levelPlaces_or_tuplePlaces : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → Set.Finite {PP : Pl D.host.E | PP ∈ (pk W).Pg ∨ QAll W PP} := by
  intro D L hT Gi Gl Kc Yd cX ex W h
  haveI : Finite W.P.T := h.fin
  have hU : {PP : Pl D.host.E | PP ∈ (pk W).Pg ∨ QAll W PP} =
      ((pk W).Pg : Set (Pl D.host.E)) ∪ ⋃ t, ((pk W).Q t : Set (Pl D.host.E)) := by
    ext PP
    simp [QAll]
  rw [hU]
  exact (Finset.finite_toSet _).union (Set.finite_iUnion fun t => Finset.finite_toSet _)

end GlobalTheory.Fam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesFiniteStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_places_finite : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → Set.Finite {PP : Pl D.host.E | PP ∈ (pk W).Pg ∨ QAll W PP} := by
  first | exact @GlobalTheory.Fam.finite_levelPlaces_or_tuplePlaces | exact GlobalTheory.Fam.finite_levelPlaces_or_tuplePlaces | (intros; apply GlobalTheory.Fam.finite_levelPlaces_or_tuplePlaces <;> assumption)
end
end
