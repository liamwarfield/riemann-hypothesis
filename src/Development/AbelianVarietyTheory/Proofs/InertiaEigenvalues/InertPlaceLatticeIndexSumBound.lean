module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDeltaPsi
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitMulMemIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOrientedFiniteFixesFockPolynomialVecto
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalDoubleCosetLabelIffDecreasing
public import ReciprocityTheory.ResidueCardinality.ArtinOntoB

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeIndexEqLocalUnitaryIndexAtInert
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndexTransferAlongProjection
namespace GlobalTheory

theorem index_transfer_along_projection {M N : Type} [AddCommGroup M] [AddCommGroup N]
    (L : AddSubgroup M) (T p : M →+ M) (Φ : M →+ N) (h : N →+ N)
    (hpL : ∀ y ∈ L, p y ∈ L) (hTp : ∀ y, T (p y) = p (T y))
    (hT1 : ∀ y, T (y - p y) = y - p y) (hΦ : ∀ y, Φ y = 0 → p y = 0)
    (hΦT : ∀ y, Φ (T y) = h (Φ y)) :
    (L.map T).relIndex L = ((L.map Φ).map h).relIndex (L.map Φ) := by
  have key : ∀ y ∈ L, (y ∈ L.map T ↔ Φ y ∈ (L.map Φ).map h) := by
    intro y hy
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Φ x, ⟨x, hx, rfl⟩, (hΦT x).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, hxy⟩
      have h0 : Φ (T x - y) = 0 := by rw [map_sub, hΦT, hxy, sub_self]
      have hp : p (T x) = p y := by
        have := hΦ _ h0
        rwa [map_sub, sub_eq_zero] at this
      refine ⟨p x + (y - p y), L.add_mem (hpL x hx) (L.sub_mem hy (hpL y hy)), ?_⟩
      show T (p x + (y - p y)) = y
      rw [map_add (f := _), hT1, hTp, hp]
      abel
  let ψ : L →+ L.map Φ :=
    (Φ.comp L.subtype).codRestrict (L.map Φ) (fun x => ⟨x.1, x.2, rfl⟩)
  have hψ : Function.Surjective ψ := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hc : (L.map T).addSubgroupOf L =
      (((L.map Φ).map h).addSubgroupOf (L.map Φ)).comap ψ := by
    ext ⟨y, hy⟩
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
    exact key y hy
  unfold AddSubgroup.relIndex
  rw [hc, AddSubgroup.index_comap_of_surjective _ hψ]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeIndexEqLocalUnitaryIndexAtInert
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.InertLatIndex

open GlobalTheory.InertLoc Formalism.UG

theorem finPart_surjective (D : D7) : Function.Surjective (finPart D) := by
  intro b
  obtain ⟨a, ha⟩ := Algebra.TensorProduct.map_surjective (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
    (fun b => ⟨pairA D.host.F 0 b, rfl⟩) Function.surjective_id b
  exact ⟨a, ha⟩

theorem ker_finPart_le {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {e : AE D} {σ : LP D P →+* LP D P}
    {π : AE D →+* LP D P} (hC : Chart e σ π) : RingHom.ker (finPart D) ≤ RingHom.ker π := by
  intro a ha
  rw [RingHom.mem_ker] at ha ⊢
  refine (hC.2.2.1 a).2 ?_
  refine GlobalTheory.LatVac.tensor_prod_eq_zero (F := D.host.F) (A := _) (B := _) _ ?_ ?_
  · show infPart D (e * a) = 0
    rw [map_mul, hC.1.2.2, zero_mul]
  · show finPart D (e * a) = 0
    rw [map_mul, ha, mul_zero]

theorem mem_span_basisFun {K : Type} [Field K] (O : ValuationSubring K) {n : Type} [Fintype n] [DecidableEq n]
    (z : n → K) : z ∈ Submodule.span O (Set.range (Pi.basisFun K n)) ↔ ∀ i, z i ∈ O := by
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro i
      rw [Pi.basisFun_apply]
      by_cases hij : j = i
      · subst hij; simp
      · simp [Pi.single_apply, Ne.symm hij]
    | zero => intro i; simp
    | add x y _ _ hx hy => intro i; exact add_mem (hx i) (hy i)
    | smul a x _ hx => intro i; exact mul_mem a.2 (hx i)
  · intro hz
    have : z = ∑ i, (⟨z i, hz i⟩ : O) • Pi.basisFun K n i := by
      conv_lhs => rw [← (Pi.basisFun K n).sum_repr z]
      rfl
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem finMat_apply {D : D7} {W : HSp D} (x : GA D W) (i j : Fin W.rank) :
    finMat D.sp.cm.sig W.gram x i j = finPart D (Formalism.L2.Theta.mt W x i j) := rfl

theorem finMat_sub_one_eq {D : D7} {W : HSp D} {e : AE D} (x : GA D W) (hx : SuppF W e x) (i j : Fin W.rank) :
    finMat D.sp.cm.sig W.gram x i j - (1 : Matrix (Fin W.rank) (Fin W.rank)
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) i j =
      finPart D e * (finMat D.sp.cm.sig W.gram x i j - (1 : Matrix (Fin W.rank) (Fin W.rank)
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) i j) := by
  have h1ij : (1 : Matrix (Fin W.rank) (Fin W.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) i j =
      finPart D ((1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) i j) := by
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  rw [h1ij, finMat_apply, ← RingHom.map_sub, ← RingHom.map_mul, ← Matrix.sub_apply, hx i j]

theorem finMat_mulVec_fix {D : D7} {W : HSp D} {e : AE D} (x : GA D W) (hx : SuppF W e x)
    (y : Fin W.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    finMat D.sp.cm.sig W.gram x *ᵥ (y - finPart D e • y) = y - finPart D e • y := by
  funext i
  have key : ∀ j, finMat D.sp.cm.sig W.gram x i j * (y - finPart D e • y) j =
      (1 : Matrix (Fin W.rank) (Fin W.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) i j *
        (y - finPart D e • y) j := by
    intro j
    have := finMat_sub_one_eq x hx i j
    rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (y j) * this
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_congr rfl (fun j _ => key j)]
  simp [Matrix.one_apply]

theorem inv_mulVec_conj {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n] (β g : GL n K) (w : n → K) :
    (β⁻¹).1 *ᵥ ((β.1 * g.1 * (β⁻¹).1) *ᵥ w) = g.1 *ᵥ ((β⁻¹).1 *ᵥ w) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]


set_option maxHeartbeats 1000000 in
theorem latIndex_eq_of_chart {D : D7} {W : HSp D} {P : HeightOneSpectrum (𝓞 D.host.E)} {e : AE D}
    {σ : LP D P →+* LP D P} {π : AE D →+* LP D P} {β : GL (Fin W.rank) (LP D P)}
    (α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (hα : finPart D e = α ⊗ₜ[D.host.F] (1 : D.host.E))
    (hαint : ∀ a ∈ intAf D.host.F, α * a ∈ intAf D.host.F)
    (hC : Chart e σ π) (hF : Frame W e σ π β) (x : GA D W) (hx : SuppF W e x) (g : GL (Fin W.rank) (LP D P))
    (hxg : (Formalism.L2.Theta.mt W x).map π = β.1 * g.1 * (β⁻¹).1) :
    latIndex W x = ((Submodule.span (P.adicCompletionIntegers D.host.E)
        (Set.range (Pi.basisFun (LP D P) (Fin W.rank)))).map
        ((g.1 : Matrix (Fin W.rank) (Fin W.rank) (LP D P)).mulVecLin.restrictScalars
          (P.adicCompletionIntegers D.host.E))).toAddSubgroup.relIndex
      (Submodule.span (P.adicCompletionIntegers D.host.E) (Set.range (Pi.basisFun (LP D P) (Fin W.rank)))).toAddSubgroup := by
  let πf : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E →+* LP D P :=
    (RingHom.liftOfSurjective (finPart D) (finPart_surjective D)) ⟨π, ker_finPart_le hC⟩
  have hπf : ∀ a, πf (finPart D a) = π a := fun a => RingHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hπe : π e = 1 := by
    have h0 : e * (e - 1) = 0 := by rw [mul_sub, hC.1.1, mul_one, sub_self]
    have := (hC.2.2.1 (e - 1)).2 h0
    rwa [RingHom.map_sub, RingHom.map_one, sub_eq_zero] at this
  let T : (Fin W.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+
      (Fin W.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    (finMat D.sp.cm.sig W.gram x).mulVecLin.toAddMonoidHom
  let p : (Fin W.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+
      (Fin W.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := DistribSMul.toAddMonoidHom _ (finPart D e)
  let Φ : (Fin W.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin W.rank → LP D P) :=
    ((β⁻¹).1 : Matrix (Fin W.rank) (Fin W.rank) (LP D P)).mulVecLin.toAddMonoidHom.comp
      (πf.toAddMonoidHom.compLeft (Fin W.rank))
  let h : (Fin W.rank → LP D P) →+ (Fin W.rank → LP D P) :=
    ((g.1 : Matrix (Fin W.rank) (Fin W.rank) (LP D P)).mulVecLin.restrictScalars
      (P.adicCompletionIntegers D.host.E)).toAddMonoidHom
  have hΦ : ∀ y, Φ y = (β⁻¹).1 *ᵥ (fun k => πf (y k)) := fun y => rfl
  have h1 : ∀ y ∈ Formalism.L2.NTheta.LamHat W, p y ∈ Formalism.L2.NTheta.LamHat W := by
    have hle : Formalism.L2.NTheta.LamHat W ≤ (Formalism.L2.NTheta.LamHat W).comap p := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨a, ha, z, hz, rfl⟩
      show p _ ∈ Formalism.L2.NTheta.LamHat W
      apply AddSubgroup.subset_closure
      refine ⟨α * a, hαint a ha, z, hz, ?_⟩
      funext i
      show finPart D e * (a ⊗ₜ[D.host.F] z i) = _
      rw [hα, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact fun y hy => hle hy
  have h2 : ∀ y, T (p y) = p (T y) := fun y => by
    show finMat D.sp.cm.sig W.gram x *ᵥ (finPart D e • y) = finPart D e • (finMat D.sp.cm.sig W.gram x *ᵥ y)
    exact Matrix.mulVec_smul _ _ _
  have h3 : ∀ y, T (y - p y) = y - p y := fun y => finMat_mulVec_fix x hx y
  have h4 : ∀ y, Φ y = 0 → p y = 0 := by
    intro y hy
    have h0 : ∀ k, πf (y k) = 0 := by
      intro k
      have := congrArg (fun w => β.1 *ᵥ w) hy
      simp only [hΦ, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at this
      exact congrFun this k
    funext k
    obtain ⟨a, ha⟩ := finPart_surjective D (y k)
    have hπa : π a = 0 := by rw [← hπf, ha]; exact h0 k
    show finPart D e * y k = 0
    rw [← ha, ← RingHom.map_mul, (hC.2.2.1 a).1 hπa, RingHom.map_zero]
  have h5 : ∀ y, Φ (T y) = h (Φ y) := by
    intro y
    have hmap : (finMat D.sp.cm.sig W.gram x).map πf = β.1 * g.1 * (β⁻¹).1 := by
      rw [← hxg]
      exact Matrix.ext fun i j => hπf _
    have hT : (fun k => πf ((finMat D.sp.cm.sig W.gram x *ᵥ y) k)) =
        (finMat D.sp.cm.sig W.gram x).map πf *ᵥ (fun k => πf (y k)) :=
      funext fun k => RingHom.map_mulVec πf _ y k
    show Φ (finMat D.sp.cm.sig W.gram x *ᵥ y) = g.1 *ᵥ Φ y
    rw [hΦ, hΦ, hT, hmap]
    exact inv_mulVec_conj β g _
  have hmapΦ : (Formalism.L2.NTheta.LamHat W).map Φ =
      (Submodule.span (P.adicCompletionIntegers D.host.E) (Set.range (Pi.basisFun (LP D P) (Fin W.rank)))).toAddSubgroup := by
    ext z
    rw [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup]
    refine Iff.trans ?_ (mem_span_basisFun _ z).symm
    constructor
    · rintro ⟨y, hy, rfl⟩
      choose a ha using fun k => finPart_surjective D (y k)
      have hpy : (fun i => finPart D (e * a i)) ∈ Formalism.L2.NTheta.LamHat W := by
        have := h1 y hy
        convert this using 1
        funext i
        show finPart D (e * a i) = finPart D e * y i
        rw [RingHom.map_mul, ha]
      have hi := (hF.2 a).1 hpy
      have hz : Φ y = (β⁻¹).1 *ᵥ fun k => π (a k) := by
        rw [hΦ]
        congr 1
        funext k
        rw [← ha, hπf]
      rw [hz]
      exact hi
    · intro hz
      choose a ha using fun k => hC.2.1 ((β.1 *ᵥ z) k)
      have hb : (β⁻¹).1 *ᵥ (fun k => π (a k)) = z := by
        have : (fun k => π (a k)) = β.1 *ᵥ z := funext ha
        rw [this, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      refine ⟨fun i => finPart D (e * a i), (hF.2 a).2 ?_, ?_⟩
      · rw [hb]; exact hz
      · rw [hΦ]
        convert hb using 2
        funext k
        rw [hπf, RingHom.map_mul, hπe, one_mul]
  unfold latIndex
  rw [GlobalTheory.index_transfer_along_projection (Formalism.L2.NTheta.LamHat W) T p Φ h h1 h2 h3 h4 h5, hmapΦ,
    Submodule.map_toAddSubgroup]
  rfl

theorem latIndex_chart_eq : ∀ (D : D7) (W : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε → ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (σ : GlobalTheory.InertLoc.LP D P →+* GlobalTheory.InertLoc.LP D P) (π : AE D →+* GlobalTheory.InertLoc.LP D P) (β : GL (Fin W.rank) (GlobalTheory.InertLoc.LP D P)) (ι : Formalism.UG.UJ σ (1 : Matrix (Fin W.rank) (Fin W.rank) (GlobalTheory.InertLoc.LP D P)) →* GA D W), GlobalTheory.InertLoc.Chart (algebraMap (AF D.host.F) (AE D) ε) σ π → GlobalTheory.InertLoc.Frame W (algebraMap (AF D.host.F) (AE D) ε) σ π β → GlobalTheory.InertLoc.GrpChart W (algebraMap (AF D.host.F) (AE D) ε) σ π β ι → ∀ (g : Formalism.UG.UJ σ (1 : Matrix (Fin W.rank) (Fin W.rank) (GlobalTheory.InertLoc.LP D P))), latIndex W (ι g) = ((Submodule.span (P.adicCompletionIntegers D.host.E) (Set.range (Pi.basisFun (GlobalTheory.InertLoc.LP D P) (Fin W.rank)))).map (((g : GL (Fin W.rank) (GlobalTheory.InertLoc.LP D P)) : Matrix (Fin W.rank) (Fin W.rank) (GlobalTheory.InertLoc.LP D P)).mulVecLin.restrictScalars (P.adicCompletionIntegers D.host.E))).toAddSubgroup.relIndex (Submodule.span (P.adicCompletionIntegers D.host.E) (Set.range (Pi.basisFun (GlobalTheory.InertLoc.LP D P) (Fin W.rank)))).toAddSubgroup := by
  intro D W v ε hε P σ π β ι hC hF hG g
  obtain ⟨α, hεα, hα1, hα0⟩ := hε
  have hα : finPart D (algebraMap (AF D.host.F) (AE D) ε) = α ⊗ₜ[D.host.F] (1 : D.host.E) := by
    subst hεα; rfl
  have hαint : ∀ a ∈ intAf D.host.F, α * a ∈ intAf D.host.F := by
    intro a ha w
    rw [map_mul]
    by_cases hw : w = v
    · subst hw; rw [hα1, one_mul]; exact ha w
    · rw [hα0 w hw, zero_mul]; exact zero_mem _
  exact latIndex_eq_of_chart α hα hαint hC hF (ι g) (hG.1 g) g.1 (hG.2.1 g)

end GlobalTheory.InertLatIndex
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeIndexEqLocalUnitaryIndexAtInertStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLatticeIndex_eq_localUnitaryIndex_at_inert : ∀ (D : D7) (W : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε → ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (σ : GlobalTheory.InertLoc.LP D P →+* GlobalTheory.InertLoc.LP D P) (π : AE D →+* GlobalTheory.InertLoc.LP D P) (β : GL (Fin W.rank) (GlobalTheory.InertLoc.LP D P)) (ι : Formalism.UG.UJ σ (1 : Matrix (Fin W.rank) (Fin W.rank) (GlobalTheory.InertLoc.LP D P)) →* GA D W), GlobalTheory.InertLoc.Chart (algebraMap (AF D.host.F) (AE D) ε) σ π → GlobalTheory.InertLoc.Frame W (algebraMap (AF D.host.F) (AE D) ε) σ π β → GlobalTheory.InertLoc.GrpChart W (algebraMap (AF D.host.F) (AE D) ε) σ π β ι → ∀ (g : Formalism.UG.UJ σ (1 : Matrix (Fin W.rank) (Fin W.rank) (GlobalTheory.InertLoc.LP D P))), latIndex W (ι g) = ((Submodule.span (P.adicCompletionIntegers D.host.E) (Set.range (Pi.basisFun (GlobalTheory.InertLoc.LP D P) (Fin W.rank)))).map (((g : GL (Fin W.rank) (GlobalTheory.InertLoc.LP D P)) : Matrix (Fin W.rank) (Fin W.rank) (GlobalTheory.InertLoc.LP D P)).mulVecLin.restrictScalars (P.adicCompletionIntegers D.host.E))).toAddSubgroup.relIndex (Submodule.span (P.adicCompletionIntegers D.host.E) (Set.range (Pi.basisFun (GlobalTheory.InertLoc.LP D P) (Fin W.rank)))).toAddSubgroup := by
  first | exact @GlobalTheory.InertLatIndex.latIndex_chart_eq | exact GlobalTheory.InertLatIndex.latIndex_chart_eq | (intros; apply GlobalTheory.InertLatIndex.latIndex_chart_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualSumLe
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StdPowMemOfLe
open scoped BigOperators

namespace GlobalTheory.HermNbr

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] {r : ℕ}

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
theorem mem_std {x : Fin r → K} :
    x ∈ Submodule.span O (Set.range (Pi.basisFun K (Fin r))) ↔
      ∀ i, x i ∈ (algebraMap O K).range := by
  classical
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      intro i
      rw [Pi.basisFun_apply, Pi.single_apply]
      split_ifs
      · exact ⟨1, map_one _⟩
      · exact ⟨0, map_zero _⟩
    | zero => intro i; exact ⟨0, map_zero _⟩
    | add y z _ _ hy hz => intro i; exact add_mem (hy i) (hz i)
    | smul a y _ hy =>
      intro i
      rw [Pi.smul_apply, Algebra.smul_def]
      exact mul_mem ⟨a, rfl⟩ (hy i)
  · intro hx
    choose a ha using hx
    have : x = ∑ i, a i • Pi.basisFun K (Fin r) i := by
      funext j
      simp [Finset.sum_apply, Pi.basisFun_apply, Pi.single_apply, Algebra.smul_def, ha]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
theorem hf_mulVec (cK : K ≃+* K) (J g : Matrix (Fin r) (Fin r) K)
    (hU : (g.map cK).transpose * J * g = J) (x y : Fin r → K) :
    hf cK J (g.mulVec x) (g.mulVec y) = hf cK J x y := by
  have e1 : (fun i => cK (g.mulVec x i)) = (g.map cK).mulVec (fun i => cK (x i)) := by
    funext i
    exact RingHom.map_mulVec cK.toRingHom g x i
  unfold hf
  rw [e1, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hU]

theorem std_sd (c : O ≃+* O) (cK : K ≃+* K)
    (hcK : ∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) (hc2 : ∀ x, cK (cK x) = x)
    (J : Matrix (Fin r) (Fin r) O) (hJ : IsUnit J.det) :
    IsSD cK (J.map (algebraMap O K)) (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))) := by
  classical
  intro x
  constructor
  · intro hx y hy
    rw [mem_std] at hx hy
    unfold hf
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply]
    refine Subring.sum_mem _ fun i _ => mul_mem (conj_mem_range c cK hcK (hx i)) ?_
    exact Subring.sum_mem _ fun j _ => mul_mem ⟨_, rfl⟩ (hy j)
  · intro h
    rw [mem_std]
    set w : Fin r → K := Matrix.vecMul (fun i => cK (x i)) (J.map (algebraMap O K)) with hw
    have hwR : ∀ j, w j ∈ (algebraMap O K).range := by
      intro j
      have hej : Pi.single j (1 : K) ∈ Submodule.span O (Set.range (Pi.basisFun K (Fin r))) :=
        Submodule.subset_span ⟨j, Pi.basisFun_apply K (Fin r) j⟩
      have := h _ hej
      unfold hf at this
      rwa [Matrix.dotProduct_mulVec, dotProduct_single, mul_one] at this
    have hJJ : J.map (algebraMap O K) * J⁻¹.map (algebraMap O K) = 1 := by
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hJ, Matrix.map_one _ (map_zero _) (map_one _)]
    have hx' : (fun i => cK (x i)) = Matrix.vecMul w (J⁻¹.map (algebraMap O K)) := by
      rw [hw, Matrix.vecMul_vecMul, hJJ, Matrix.vecMul_one]
    intro i
    have hi : cK (x i) ∈ (algebraMap O K).range := by
      rw [show cK (x i) = (fun i => cK (x i)) i from rfl, hx']
      simp only [Matrix.vecMul, dotProduct, Matrix.map_apply]
      exact Subring.sum_mem _ fun j _ => mul_mem (hwR j) ⟨_, rfl⟩
    rw [← hc2 (x i)]
    exact conj_mem_range c cK hcK hi

theorem exists_pow_mul_mem {ϖ : O} (hϖ : Irreducible ϖ) (y : K) :
    ∃ k : ℕ, algebraMap O K (ϖ ^ k) * y ∈ (algebraMap O K).range := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) y
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb0 hϖ
  refine ⟨k, u * a, ?_⟩
  have hb' : algebraMap O K b ≠ 0 := by
    intro h; exact hb0 (IsFractionRing.injective O K (by simpa using h))
  rw [← hu, map_mul, map_mul]
  field_simp

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
theorem std_pow_mem_of_le {ϖ : O} {x : Fin r → K} {k : Fin r → ℕ}
    (hk : ∀ i, algebraMap O K (ϖ ^ k i) * x i ∈ (algebraMap O K).range) :
    (ϖ ^ (∑ i, k i)) • x ∈ Submodule.span O (Set.range (Pi.basisFun K (Fin r))) := by
  rw [mem_std]
  intro i
  have hle : k i ≤ ∑ j, k j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [Pi.smul_apply, Algebra.smul_def, ← Nat.sub_add_cancel hle, pow_add, map_mul, mul_assoc]
  exact mul_mem ⟨_, rfl⟩ (hk i)

theorem idx_std {ϖ : O} (hϖ : Irreducible ϖ) :
    idx ϖ (Submodule.span O (Set.range (Pi.basisFun K (Fin r))) : Submodule O (Fin r → K)) =
      Nat.card (IsLocalRing.ResidueField O) ^ r := by
  classical
  set L0 : Submodule O (Fin r → K) := Submodule.span O (Set.range (Pi.basisFun K (Fin r)))
  have hex : ∀ (x : L0.toAddSubgroup) (i : Fin r), ∃ a : O, algebraMap O K a = (x : Fin r → K) i :=
    fun x i => mem_std.1 x.2 i
  choose a ha using hex
  have hadd : ∀ x y i, a (x + y) i = a x i + a y i := by
    intro x y i
    apply IsFractionRing.injective O K
    rw [map_add (f := _), ha, ha, ha]; rfl
  let ψ : L0.toAddSubgroup →+ (Fin r → IsLocalRing.ResidueField O) :=
    AddMonoidHom.mk' (fun x i => IsLocalRing.residue O (a x i)) (by
      intro x y; funext i; simp [hadd])
  have hker : (L0.map (ϖ • (LinearMap.id : (Fin r → K) →ₗ[O] (Fin r → K)))).toAddSubgroup.addSubgroupOf
      L0.toAddSubgroup = ψ.ker := by
    ext x
    rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker]
    change (x : Fin r → K) ∈ L0.map _ ↔ (fun i => IsLocalRing.residue O (a x i)) = 0
    rw [funext_iff]
    simp only [Pi.zero_apply, IsLocalRing.residue_eq_zero_iff,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, hy, hyx⟩ i
      obtain ⟨b, hb⟩ := mem_std.1 hy i
      refine ⟨b, IsFractionRing.injective O K ?_⟩
      rw [ha, ← hyx, map_mul, hb]
      simp [Algebra.smul_def]
    · intro h
      choose b hb using h
      refine ⟨fun i => algebraMap O K (b i), mem_std.2 fun i => ⟨b i, rfl⟩, ?_⟩
      funext i
      show (ϖ • (fun i => algebraMap O K (b i))) i = (x : Fin r → K) i
      rw [Pi.smul_apply, Algebra.smul_def, ← map_mul, ← hb, ha]
  have hsurj : Function.Surjective ψ := by
    intro z
    choose b hb using fun i => IsLocalRing.residue_surjective (z i)
    have hm : (fun i => algebraMap O K (b i)) ∈ L0.toAddSubgroup := mem_std.2 fun i => ⟨b i, rfl⟩
    refine ⟨⟨_, hm⟩, ?_⟩
    funext i
    change IsLocalRing.residue O (a ⟨_, hm⟩ i) = z i
    have : a ⟨_, hm⟩ i = b i := IsFractionRing.injective O K (by rw [ha])
    rw [this, hb]
  unfold idx
  rw [AddSubgroup.relIndex, hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj,
    Nat.card_congr AddSubgroup.topEquiv.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin r),
    Fintype.card_fin]

end GlobalTheory.HermNbr
end

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory.HermNbr

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] {r : ℕ}

theorem good_map (cK : K ≃+* K) {J : Matrix (Fin r) (Fin r) K} {ϖ : O} {N : ℕ}
    {L : Submodule O (Fin r → K)} (hL : Good cK J ϖ N L) (hϖ : Irreducible ϖ)
    (g : GL (Fin r) K) (hU : ((g : Matrix (Fin r) (Fin r) K).map cK).transpose * J *
      (g : Matrix (Fin r) (Fin r) K) = J) :
    Good cK J ϖ N (L.map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)) := by
  set G := ((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O with hG
  set Gi := (((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O with hGi
  have h1 : ∀ x, G (Gi x) = x := by
    intro x
    change (g : Matrix (Fin r) (Fin r) K).mulVec ((((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)).mulVec x) = x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have h2 : ∀ x, Gi (G x) = x := by
    intro x
    change (((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)).mulVec ((g : Matrix (Fin r) (Fin r) K).mulVec x) = x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have memG : ∀ x, x ∈ L.map G ↔ Gi x ∈ L := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩; rw [h2]; exact hy
    · intro h; exact ⟨Gi x, h, h1 x⟩
  have hfG : ∀ x y, hf cK J (G x) (G y) = hf cK J x y := fun x y => hf_mulVec cK J _ hU x y
  obtain ⟨hSD, habs, hidx⟩ := hL
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rw [memG, hSD (Gi x)]
    constructor
    · intro h y hy
      rw [← h1 x, ← h1 y, hfG]
      exact h _ ((memG y).1 hy)
    · intro h y hy
      have := h (G y) ((memG _).2 (by rw [h2]; exact hy))
      rwa [← h1 x, hfG] at this
  · intro x
    obtain ⟨k, hk⟩ := habs (Gi x)
    refine ⟨k, (memG _).2 ?_⟩
    rw [map_smul]
    exact hk
  · have hinj : Function.Injective G.toAddMonoidHom := fun x y h => by
      have := congrArg Gi h
      simpa [h2] using this
    set f : (Fin r → K) →ₗ[O] (Fin r → K) := ϖ • LinearMap.id with hf'
    have hcomm : (L.map G).map f = (L.map f).map G := by
      rw [← Submodule.map_comp, ← Submodule.map_comp]
      congr 1
      ext x
      simp [hf', hG]
    have e : ∀ P : Submodule O (Fin r → K),
        (P.map G).toAddSubgroup = P.toAddSubgroup.map G.toAddMonoidHom := fun P => by
      ext x; simp [Submodule.mem_map]
    unfold idx at hidx ⊢
    rw [← hf'] at hidx ⊢
    rw [hcomm, e, e, AddSubgroup.relIndex_map_map_of_injective _ _ hinj, hidx]

end GlobalTheory.HermNbr

theorem GlobalTheory.HermNbr.selfDual_sum_le : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (c : O ≃+* O) (cK : K ≃+* K), (∀ x, c (c x) = x) → (∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) → (∃ x, IsUnit (c x - x)) → ∀ (r n : ℕ) (J : Matrix (Fin r) (Fin r) O), IsUnit J.det → J.transpose.map c = J → 2 * r + 5 ≤ n → ∀ C : Finset (GL (Fin r) K), (∀ g ∈ C, ((g : Matrix (Fin r) (Fin r) K).map cK).transpose * J.map (algebraMap O K) * (g : Matrix (Fin r) (Fin r) K) = J.map (algebraMap O K)) → (∀ g ∈ C, (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) ≠ Submodule.span O (Set.range (Pi.basisFun K (Fin r)))) → (∀ g ∈ C, ∀ g' ∈ C, (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) = (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g' : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) → g = g') → ∑ g ∈ C, ((((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)).toAddSubgroup.relIndex (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).toAddSubgroup : ℕ) : ℝ) ^ (-(n : ℝ) / 2) ≤ 8 * (Nat.card (IsLocalRing.ResidueField O) : ℝ) ^ (-(2 : ℝ)) := by
  intro O K _ _ _ _ _ _ _ c cK hc hcK _ r n J hJdet hJh hn C hU hne hinj
  classical
  set J' := J.map (algebraMap O K) with hJ'
  have hc2 : ∀ x : K, cK (cK x) = x := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) x
    rw [map_div₀, map_div₀, hcK, hcK, hcK, hcK, hc, hc]
  have hJ'h : J'.transpose.map cK = J' := by
    ext i j
    simp only [hJ', Matrix.map_apply, Matrix.transpose_apply, hcK]
    have := congrFun (congrFun hJh i) j
    simp only [Matrix.map_apply, Matrix.transpose_apply] at this
    rw [this]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  set Q := Nat.card (IsLocalRing.ResidueField O) with hQdef
  have hQ2 : 2 ≤ Q := Finite.one_lt_card
  set L0 : Submodule O (Fin r → K) := Submodule.span O (Set.range (Pi.basisFun K (Fin r))) with hL0def
  have hL0 : GlobalTheory.HermNbr.Good cK J' ϖ (Q ^ r) L0 := by
    refine ⟨GlobalTheory.HermNbr.std_sd c cK hcK hc2 J hJdet, ?_, GlobalTheory.HermNbr.idx_std hϖ⟩
    intro x
    choose k hk using fun i => GlobalTheory.HermNbr.exists_pow_mul_mem hϖ (x i)
    exact ⟨_, GlobalTheory.HermNbr.std_pow_mem_of_le hk⟩
  set φ : GL (Fin r) K → Submodule O (Fin r → K) := fun g =>
    L0.map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) with hφ
  have hgood : ∀ g ∈ C, GlobalTheory.HermNbr.Good cK J' ϖ (Q ^ r) (φ g) := fun g hg =>
    GlobalTheory.HermNbr.good_map cK hL0 hϖ g (hU g hg)

  have hQr : (2 : ℝ) ≤ Q := by exact_mod_cast hQ2
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hQ1 : (0 : ℝ) < (Q : ℝ) - 1 := by linarith
  set s : ℝ := (n : ℝ) / 2 with hs
  set D : ℝ := (Q : ℝ) ^ r * Q / ((Q : ℝ) - 1) with hD
  set y : ℝ := (Q : ℝ) ^ (-(2 : ℝ)) with hy
  have hs0 : 0 < s := by
    have : (5 : ℝ) ≤ n := by exact_mod_cast (by omega : 5 ≤ n)
    rw [hs]; linarith
  have hD0 : 0 ≤ D := by positivity
  have hy0 : 0 < y := Real.rpow_pos_of_pos hQ0 _
  have hy4 : y ≤ 1 / 4 := by
    rw [hy, Real.rpow_neg hQ0.le]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  have hρ : D * (Q : ℝ) ^ (-s) ≤ 2 * y := by
    have hsr : (r : ℝ) + 5 / 2 ≤ s := by
      have : ((2 * r + 5 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at this
      rw [hs]; linarith
    have h1 : (Q : ℝ) ^ (-s) ≤ (Q : ℝ) ^ (-((r : ℝ) + 5 / 2)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h2 : (Q : ℝ) ^ (-((r : ℝ) + 5 / 2)) = ((Q : ℝ) ^ r)⁻¹ * ((Q : ℝ) ^ (-(2 : ℝ)) * (Q : ℝ) ^ (-(1 / 2 : ℝ))) := by
      rw [← Real.rpow_add hQ0, show -((r : ℝ) + 5 / 2) = -(r : ℝ) + (-(2 : ℝ) + -(1 / 2 : ℝ)) by ring,
        Real.rpow_add hQ0, Real.rpow_neg hQ0.le, Real.rpow_natCast]
    have h3 : (Q : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have h4 : (Q : ℝ) / ((Q : ℝ) - 1) ≤ 2 := by
      rw [div_le_iff₀ hQ1]; linarith
    have hQr0 : (0 : ℝ) < (Q : ℝ) ^ r := by positivity
    calc D * (Q : ℝ) ^ (-s) ≤ D * (Q : ℝ) ^ (-((r : ℝ) + 5 / 2)) := mul_le_mul_of_nonneg_left h1 hD0
      _ = (Q : ℝ) / ((Q : ℝ) - 1) * (y * (Q : ℝ) ^ (-(1 / 2 : ℝ))) := by
          rw [h2, hD, hy]; field_simp
      _ ≤ 2 * (y * 1) := by
          apply mul_le_mul h4 (mul_le_mul_of_nonneg_left h3 hy0.le) (by positivity) (by norm_num)
      _ = 2 * y := by ring
  have hρ1 : D * (Q : ℝ) ^ (-s) < 1 := by linarith

  have key := GlobalTheory.HermNbr.graph_sum {L | GlobalTheory.HermNbr.Good cK J' ϖ (Q ^ r) L}
    (fun L Λ => Λ.toAddSubgroup.relIndex L.toAddSubgroup) (GlobalTheory.HermNbr.Nbrs cK J' ϖ) Q hQ2 s D
    hs0 hD0 hρ1 (fun L _ => AddSubgroup.relIndex_self _)
    (fun L hL Λ hΛ hne hi => by
      obtain ⟨L', h1, h2, h3, h4⟩ :=
        GlobalTheory.HermNbr.step_exists c cK hcK hc2 hJ'h hϖ hL hΛ hne hi
      exact ⟨L', h1, h2, h3, h4⟩)
    (fun L hL t ht => by
      have h := GlobalTheory.HermNbr.card_nbrs c cK hcK hc2 hJ'h hϖ hL (by positivity) t ht
      rw [hD, le_div_iff₀ hQ1]
      have : ((t.card * (Q - 1) : ℕ) : ℝ) ≤ ((Q ^ r * Q : ℕ) : ℝ) := by exact_mod_cast h
      push_cast [Nat.cast_sub (by omega : 1 ≤ Q)] at this
      linarith)
    L0 hL0 (C.image φ)
    (by
      intro Λ hΛ
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hΛ)
      exact hgood g hg)
    (by
      intro h
      obtain ⟨g, hg, hg'⟩ := Finset.mem_image.1 h
      exact hne g hg hg')
  rw [Finset.sum_image (fun g hg g' hg' h => hinj g hg g' hg' h)] at key
  have hsum : ∀ g ∈ C, (((φ g).toAddSubgroup.relIndex L0.toAddSubgroup : ℕ) : ℝ) ^ (-(n : ℝ) / 2) =
      (((φ g).toAddSubgroup.relIndex L0.toAddSubgroup : ℕ) : ℝ) ^ (-s) := by
    intro g _; rw [hs, neg_div]
  rw [← Finset.sum_congr rfl hsum] at key
  refine le_trans key ?_
  set ρ := D * (Q : ℝ) ^ (-s)
  have hρ0 : 0 ≤ ρ := by positivity
  rw [div_le_iff₀ (by linarith)]
  nlinarith
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StdLatticeMapEqIffMemGLintValuationSubring
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StdLatticeMapEqIffMemGLintValuationSubring
open Matrix

namespace GlobalTheory.GLintLattice

variable {K : Type} [Field K] (A : ValuationSubring K) {r : ℕ}

theorem mem_span_basisFun_iff (y : Fin r → K) :
    y ∈ Submodule.span A (Set.range (Pi.basisFun K (Fin r))) ↔ ∀ i, y i ∈ A := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩ i
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  · intro h
    refine ⟨fun i => ⟨y i, h i⟩, ?_⟩
    ext j
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]

theorem mulVec_maps_iff (M : Matrix (Fin r) (Fin r) K) :
    (∀ y : Fin r → K, (∀ i, y i ∈ A) → ∀ i, (M *ᵥ y) i ∈ A) ↔ ∀ i j, M i j ∈ A := by
  constructor
  · intro h i j
    have := h (Pi.single j 1) (fun k => by
      by_cases hk : k = j
      · subst hk; simp
      · simp [Pi.single_apply, hk]) i
    simpa [Matrix.mulVec_single_one] using this
  · intro h y hy i
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mem (fun j _ => mul_mem (h i j) (hy j))

theorem mem_GLint_iff (x : GL (Fin r) K) :
    x ∈ Formalism.UG.GLint (Fin r) A.toSubring ↔
      (∀ i j, (x : Matrix (Fin r) (Fin r) K) i j ∈ A) ∧
        (∀ i j, ((x⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j ∈ A) := by
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · show ((u : Matrix (Fin r) (Fin r) A.toSubring) i j : K) ∈ A
      exact (u : Matrix (Fin r) (Fin r) A.toSubring) i j |>.2
    · rw [← map_inv]
      show (((u⁻¹ : GL (Fin r) A.toSubring) : Matrix (Fin r) (Fin r) A.toSubring) i j : K) ∈ A
      exact ((u⁻¹ : GL (Fin r) A.toSubring) : Matrix (Fin r) (Fin r) A.toSubring) i j |>.2
  · rintro ⟨h1, h2⟩
    let M : Matrix (Fin r) (Fin r) A.toSubring := Matrix.of fun i j => ⟨_, h1 i j⟩
    let M' : Matrix (Fin r) (Fin r) A.toSubring := Matrix.of fun i j => ⟨_, h2 i j⟩
    have hM : M.map A.toSubring.subtype = (x : Matrix (Fin r) (Fin r) K) := by ext; rfl
    have hM' : M'.map A.toSubring.subtype = ((x⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) := by
      ext; rfl
    have inj : Function.Injective fun N : Matrix (Fin r) (Fin r) A.toSubring => N.map A.toSubring.subtype :=
      Matrix.map_injective Subtype.val_injective
    have e1 : M * M' = 1 := inj (by
      simp only
      rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _)]
      exact x.mul_inv)
    have e2 : M' * M = 1 := inj (by
      simp only
      rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _)]
      exact x.inv_mul)
    refine ⟨⟨M, M', e1, e2⟩, ?_⟩
    ext i j
    rfl

theorem stdLattice_map_eq_iff_mem_GLint : ∀ (K : Type) [Field K] (A : ValuationSubring K) (r : ℕ)
    (x : GL (Fin r) K),
    (Submodule.span A (Set.range (Pi.basisFun K (Fin r)))).map
        ((x : Matrix (Fin r) (Fin r) K).mulVecLin.restrictScalars A) =
      Submodule.span A (Set.range (Pi.basisFun K (Fin r))) ↔
    x ∈ Formalism.UG.GLint (Fin r) A.toSubring := by
  intro K _ A r x
  have hf : ∀ z, ((x : Matrix (Fin r) (Fin r) K).mulVecLin.restrictScalars A) z =
      (x : Matrix (Fin r) (Fin r) K) *ᵥ z := fun z => rfl
  have inv_x : ∀ z : Fin r → K, ((x⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *ᵥ
      ((x : Matrix (Fin r) (Fin r) K) *ᵥ z) = z := by
    intro z; rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have x_inv : ∀ z : Fin r → K, (x : Matrix (Fin r) (Fin r) K) *ᵥ
      (((x⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *ᵥ z) = z := by
    intro z; rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  rw [mem_GLint_iff, ← mulVec_maps_iff, ← mulVec_maps_iff]
  constructor
  · intro h
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · have hm : (x : Matrix (Fin r) (Fin r) K) *ᵥ y ∈
          (Submodule.span A (Set.range (Pi.basisFun K (Fin r)))).map
            ((x : Matrix (Fin r) (Fin r) K).mulVecLin.restrictScalars A) :=
        ⟨y, (mem_span_basisFun_iff A y).2 hy, hf y⟩
      rw [h] at hm
      exact (mem_span_basisFun_iff A _).1 hm
    · have hm : y ∈ (Submodule.span A (Set.range (Pi.basisFun K (Fin r)))).map
            ((x : Matrix (Fin r) (Fin r) K).mulVecLin.restrictScalars A) := by
        rw [h]; exact (mem_span_basisFun_iff A y).2 hy
      obtain ⟨z, hz, hzy⟩ := hm
      rw [hf] at hzy
      rw [← hzy, inv_x]
      exact (mem_span_basisFun_iff A z).1 hz
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      rw [hf, mem_span_basisFun_iff]
      exact h1 z ((mem_span_basisFun_iff A z).1 hz)
    · intro y hy
      refine ⟨((x⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *ᵥ y,
        (mem_span_basisFun_iff A _).2 (h2 y ((mem_span_basisFun_iff A y).1 hy)), ?_⟩
      rw [hf, x_inv]

end GlobalTheory.GLintLattice
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StdLatticeMapEqIffMemGLintValuationSubringStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stdLattice_map_eq_iff_mem_GLint_valuationSubring : ∀ (K : Type) [Field K] (A : ValuationSubring K) (r : ℕ) (x : GL (Fin r) K), (Submodule.span A (Set.range (Pi.basisFun K (Fin r)))).map ((x : Matrix (Fin r) (Fin r) K).mulVecLin.restrictScalars A) = Submodule.span A (Set.range (Pi.basisFun K (Fin r))) ↔ x ∈ Formalism.UG.GLint (Fin r) A.toSubring := by
  first | exact @GlobalTheory.GLintLattice.stdLattice_map_eq_iff_mem_GLint | exact GlobalTheory.GLintLattice.stdLattice_map_eq_iff_mem_GLint | (intros; apply GlobalTheory.GLintLattice.stdLattice_map_eq_iff_mem_GLint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertPlaceLatticeIndexSumBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.InertIdx

theorem indexSum_inert : ∀ (D : D7) (W : HSp D) (n : ℕ), 2 * W.rank + 5 ≤ n → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (f : Formalism.L2.Theta.AE D), IsFinIdem D v f → (∃ w : HeightOneSpectrum (𝓞 D.host.E), Formalism.UG.IsInertAt D.host.F D.host.E v w) → ∀ C : Finset (GA D W), (∀ g ∈ C, SuppF W f g ∧ g ∉ KsphC W ∅) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ KsphC W ∅ → g = g') → ∑ g ∈ C, (latIndex W g : ℝ) ^ (-(n : ℝ) / 2) ≤ 8 * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(4 : ℝ)) := by
  classical
  intro D W n hn v f hf ⟨w, hw⟩ C hC hdist
  obtain ⟨ε, hε, rfl⟩ := hf
  have hP := GlobalTheory.HeckeRowsCompare.isPrimeIdem_of_inert (P := w) hw hε
  have hc := GlobalTheory.LabChar.fixed_of_tie hP
  obtain ⟨ϖ, σ, q, π, hU, -, hCh, hV⟩ := GlobalTheory.InertLoc.exists_chart hc hP
  obtain ⟨β, ι, hFr, hGC⟩ := hV W
  obtain ⟨hσσ, hσv, -, -, ⟨x0, hx0, hx0v⟩, -, -⟩ := hU
  let K := GlobalTheory.InertLoc.LP D w
  let O := w.adicCompletionIntegers D.host.E

  have hσO : ∀ x : O, σ (x : K) ∈ O := fun x => by
    show Valued.v (σ (x : K)) ≤ 1
    rw [hσv]; exact x.2
  let cO : O ≃+* O :=
    { toFun := fun x => ⟨σ x, hσO x⟩, invFun := fun x => ⟨σ x, hσO x⟩,
      left_inv := fun x => Subtype.ext (hσσ x), right_inv := fun x => Subtype.ext (hσσ x),
      map_mul' := fun x y => Subtype.ext (map_mul σ _ _), map_add' := fun x y => Subtype.ext (map_add σ _ _) }
  let cK : K ≃+* K :=
    { toFun := σ, invFun := σ, left_inv := hσσ, right_inv := hσσ, map_mul' := map_mul σ, map_add' := map_add σ }

  let H : GA D W → Formalism.UG.UJ σ (1 : Matrix (Fin W.rank) (Fin W.rank) K) := fun g =>
    if hg : SuppF W (algebraMap (AF D.host.F) (AE D) ε) g then (hGC.2.2.1 g hg).choose else 1
  have hH : ∀ g ∈ C, ι (H g) = g := fun g hg => by
    simp only [H, dif_pos (hC g hg).1]
    exact (hGC.2.2.1 g (hC g hg).1).choose_spec
  have hinj : Set.InjOn (fun g => ((H g : GL (Fin W.rank) K))) C := fun g hg g' hg' e => by
    rw [← hH g hg, ← hH g' hg', Subtype.ext e]
  have hsum := Finset.sum_image (f := fun x : GL (Fin W.rank) K =>
      ((((Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).map (((x : Matrix (Fin W.rank) (Fin W.rank) K)).mulVecLin.restrictScalars O)).toAddSubgroup.relIndex
        (Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).toAddSubgroup : ℕ) : ℝ) ^ (-(n : ℝ) / 2)) hinj
  have hterm : ∀ g ∈ C, (latIndex W g : ℝ) ^ (-(n : ℝ) / 2) = ((((Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).map ((((H g : GL (Fin W.rank) K) : Matrix (Fin W.rank) (Fin W.rank) K)).mulVecLin.restrictScalars O)).toAddSubgroup.relIndex
        (Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).toAddSubgroup : ℕ) : ℝ) ^ (-(n : ℝ) / 2) := fun g hg => by
    conv_lhs => rw [← hH g hg]
    rw [GlobalTheory.T.selfDualLatticeIndex_eq_localUnitaryIndex_at_inert D W v ε hε w σ π β ι hCh hFr hGC (H g)]
  rw [Finset.sum_congr rfl hterm, ← hsum]

  have hcard : Nat.card (IsLocalRing.ResidueField O) = Ideal.absNorm v.asIdeal ^ 2 := by
    rw [ReciprocityTheory.Bridge.ResidueFieldCardinality.card_residue, ← GlobalTheory.LFun.InertChart.absNorm_eq
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _) hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hfin : Finite (IsLocalRing.ResidueField O) := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact pow_ne_zero _ (by
      have := Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot
      exact this))
  have hunit : IsUnit (cO ⟨x0, hx0⟩ - ⟨x0, hx0⟩) := by
    have hne : σ x0 - x0 ≠ 0 := fun e => by rw [e, map_zero] at hx0v; exact zero_ne_one hx0v
    refine isUnit_iff_exists_inv.2 ⟨⟨(σ x0 - x0)⁻¹, ?_⟩, Subtype.ext ?_⟩
    · show Valued.v ((σ x0 - x0)⁻¹) ≤ 1
      rw [map_inv₀, hx0v, inv_one]
    · exact mul_inv_cancel₀ hne
  have hunitary : ∀ x ∈ C.image (fun g => ((H g : GL (Fin W.rank) K))),
      ((x : Matrix (Fin W.rank) (Fin W.rank) K).map cK)ᵀ * (1 : Matrix (Fin W.rank) (Fin W.rank) O).map (algebraMap O K) *
        (x : Matrix (Fin W.rank) (Fin W.rank) K) = (1 : Matrix (Fin W.rank) (Fin W.rank) O).map (algebraMap O K) := by
    intro x hx
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hx
    have h1 := (H g).2
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact h1
  have hnontriv : ∀ x ∈ C.image (fun g => ((H g : GL (Fin W.rank) K))),
      (Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).map ((x : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O) ≠
        Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank))) := by
    intro x hx he
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hx
    have h1 := (GlobalTheory.T.stdLattice_map_eq_iff_mem_GLint_valuationSubring K O W.rank _).1 he
    have h2 := (hGC.2.2.2 (H g)).2 h1
    rw [hH g hg] at h2
    exact (hC g hg).2 h2
  have hdist' : ∀ x ∈ C.image (fun g => ((H g : GL (Fin W.rank) K))), ∀ x' ∈ C.image (fun g => ((H g : GL (Fin W.rank) K))),
      (Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).map ((x : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O) =
        (Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).map ((x' : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O) →
      x = x' := by
    intro x hx x' hx' he
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨g', hg', rfl⟩ := Finset.mem_image.1 hx'
    have hm : (Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).map
        (((((H g)⁻¹ * H g' : Formalism.UG.UJ σ (1 : Matrix (Fin W.rank) (Fin W.rank) K)) : GL (Fin W.rank) K) : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O) =
        Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank))) := by
      have hcomp : ∀ (a b : GL (Fin W.rank) K), ((((a * b : GL (Fin W.rank) K)) : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O) =
          ((a : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O).comp ((b : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O) := by
        intro a b
        ext y : 1
        simp [Matrix.mulVec_mulVec]
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hcomp, Submodule.map_comp, ← he, ← Submodule.map_comp, ← hcomp, inv_mul_cancel]
      ext y
      simp
    have h1 := (GlobalTheory.T.stdLattice_map_eq_iff_mem_GLint_valuationSubring K O W.rank _).1 hm
    have h2 := (hGC.2.2.2 _).2 h1
    rw [map_mul, map_inv, hH g hg, hH g' hg'] at h2
    rw [hdist g hg g' hg' h2]
  have key := GlobalTheory.HermNbr.selfDual_sum_le O K cO cK (fun x => Subtype.ext (hσσ x)) (fun x => rfl)
    ⟨⟨x0, hx0⟩, hunit⟩ W.rank n 1 (by simp) (by simp) hn
    (C.image fun g => ((H g : GL (Fin W.rank) K))) hunitary hnontriv hdist'
  refine key.trans (le_of_eq ?_)
  rw [hcard]
  have hv0 : (0 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := Nat.cast_nonneg _
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hv0]
  norm_num

end GlobalTheory.InertIdx

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertPlaceLatticeIndexSumBoundStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_latticeIndex_sum_bound : ∀ (D : D7) (W : HSp D) (n : ℕ), 2 * W.rank + 5 ≤ n → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (f : Formalism.L2.Theta.AE D), IsFinIdem D v f → (∃ w : HeightOneSpectrum (𝓞 D.host.E), Formalism.UG.IsInertAt D.host.F D.host.E v w) → ∀ C : Finset (GA D W), (∀ g ∈ C, SuppF W f g ∧ g ∉ KsphC W ∅) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ KsphC W ∅ → g = g') → ∑ g ∈ C, (latIndex W g : ℝ) ^ (-(n : ℝ) / 2) ≤ 8 * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(4 : ℝ)) := by
  first | exact @GlobalTheory.InertIdx.indexSum_inert | exact GlobalTheory.InertIdx.indexSum_inert | (intros; apply GlobalTheory.InertIdx.indexSum_inert <;> assumption)
end
