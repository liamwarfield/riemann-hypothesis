module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRowSubstitutionPolyDiagonalEqSumComponents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDefiniteUnitaryRationalInfConjLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylTensorReductionWeightProjector
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LiftNabStdMemLatN
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalisedStandardWeylOfLiftMem

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPhiOfFrameInjectiveShift
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPhiOfFrameInjectiveShift
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameRead

theorem lift_nabStd_mem_latN : ∀ (K : Type) [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] (w : HeightOneSpectrum (𝓞 K)) (e0 : K →+* PadicAlgCl l) (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (lam : ι → DomWeight n) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) (F : Frame l ι n) (Φ : VV K lam →ₛₗ[e0] NablaT (PadicAlgCl l) n lamW), AtPlace w e0 → Function.Injective F.emb → (∀ x : K, ‖e0 x‖ ≤ 1 → e0 x ∈ Set.range F.emb) → Shift lam lamW c → IsPhi e0 lam lamW Φ → ∀ v : VV K lam, (v : Pol K ι n) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) → Φ v ∈ F.latN lamW :=
  _root_.UpperTheory.Reformulated.B.Ga11.lift_nabStd_mem_latN

end GlobalTheory.FrameRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPhiOfFrameInjectiveShiftStatement
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPhi_mem_latN_of_frame_injective_shift : ∀ (K : Type) [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] (w : HeightOneSpectrum (𝓞 K)) (e0 : K →+* PadicAlgCl l) (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (lam : ι → DomWeight n) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) (F : Frame l ι n) (Φ : VV K lam →ₛₗ[e0] NablaT (PadicAlgCl l) n lamW), AtPlace w e0 → Function.Injective F.emb → (∀ x : K, ‖e0 x‖ ≤ 1 → e0 x ∈ Set.range F.emb) → Shift lam lamW c → IsPhi e0 lam lamW Φ → ∀ v : VV K lam, (v : Pol K ι n) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) → Φ v ∈ F.latN lamW := by
  first | exact @GlobalTheory.FrameRead.lift_nabStd_mem_latN | exact GlobalTheory.FrameRead.lift_nabStd_mem_latN | (intros; apply GlobalTheory.FrameRead.lift_nabStd_mem_latN <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalBasisIntegralRelativeAdelicPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalBasisIntegralRelativeAdelicPoint
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocBasisInt

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_isIntegral' {K : Type} [NormedField K] [IsUltrametricDist K] {x : K} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  have := (Valuation.integer.integers (NormedField.valuation (K := K))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at this
  exact_mod_cast this

theorem norm_inc_le_one (inc : E →+* PadicAlgCl l) (r : 𝓞 E) : ‖inc (r : E)‖ ≤ 1 :=
  norm_le_one_of_isIntegral' ((RingOfIntegers.isIntegral_coe r).map inc.toIntAlgHom)

theorem norm_natCast_eq_one' {m : ℕ} (hm : ¬ l ∣ m) : ‖(m : PadicAlgCl l)‖ = 1 := by
  have h : (m : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (m : ℚ_[l]) := (map_natCast _ m).symm
  rw [h, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact ((Fact.out : l.Prime).coprime_iff_not_dvd).mpr hm

theorem norm_ev_latHat_le_one (inc : E →+* PadicAlgCl l)
    (ev : FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* PadicAlgCl l) (hev : EvOk inc ev) {M : ℕ}
    (L : Set (Fin M → E)) (hL : ∀ x ∈ L, ∀ i, x i ∈ (algebraMap (𝓞 E) E).range)
    (z : Fin M → FiniteAdeleRing (𝓞 F) F ⊗[F] E) (hz : z ∈ StandardLattice.latHat F E L) (a : Fin M) :
    ‖ev (z a)‖ ≤ 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, x, hx, rfl⟩ := hy
    obtain ⟨r, hr⟩ := hL x hx a
    have e : c ⊗ₜ[F] x a = (c ⊗ₜ[F] (1 : E)) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x a) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    show ‖ev (c ⊗ₜ[F] x a)‖ ≤ 1
    rw [e, map_mul, norm_mul, hev.1, ← hr]
    exact mul_le_one₀ (hev.2.1 c hc) (norm_nonneg _) (norm_inc_le_one inc r)
  | zero => simp
  | add y w _ _ hy hw =>
    show ‖ev (y a + w a)‖ ≤ 1
    rw [map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy hw)
  | neg y _ hy =>
    show ‖ev (-(y a))‖ ≤ 1
    rwa [map_neg, norm_neg]

end General

end GlobalTheory.LocBasisInt

namespace GlobalTheory.LocBasisInt

section Space

variable {D : D7}

theorem selfDualLattice_frame_span_integral_coordinates (V : Formalism.BasicNotions.TH.HSp D) (hL0 : V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame))
    (x : Fin V.rank → D.host.E) (hx : x ∈ StandardLattice.L0c D V) (i : Fin V.rank) :
    x i ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  have hx' : ∑ j, x j • V.frame j ∈ V.L0 := hx
  rw [hL0, Submodule.mem_span_range_iff_exists_fun] at hx'
  obtain ⟨c, hc⟩ := hx'
  have hc' : ∑ j, ((c j : D.host.E)) • V.frame j = ∑ j, x j • V.frame j := by
    rw [← hc]; refine Finset.sum_congr rfl fun j _ => ?_
    exact (algebraMap_smul D.host.E (c j) (V.frame j))
  have h2 := congrArg (fun v => V.frame.repr v i) hc'
  simp only [Module.Basis.repr_sum_self] at h2
  exact ⟨c i, h2⟩

end Space

end GlobalTheory.LocBasisInt

namespace GlobalTheory.LocBasisInt

section Space

variable {D : D7}

theorem norm_ev_hLat_le_one (V : Formalism.BasicNotions.TH.HSp D) (hL0 : V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame))
    {l : ℕ} [Fact l.Prime] (inc : D.host.E →+* PadicAlgCl l)
    (ev : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l) (hev : EvOk inc ev)
    (y : Bridge.Gf V) (x : Fin V.rank → D.host.E) (hx : x ∈ Bridge.hLat V y) (a : Fin V.rank) :
    ‖ev (Matrix.mulVec ((y : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E))⁻¹).val
      (fun i => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] x i) a)‖ ≤ 1 := by
  unfold Bridge.hLat at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    have hx' := hx
    simp only [Set.mem_ofPred, Subgroup.coe_inv] at hx'
    exact norm_ev_latHat_le_one inc ev hev (StandardLattice.L0c D V) (fun x hx i => selfDualLattice_frame_span_integral_coordinates V hL0 x hx i) _ hx' a
  | zero =>
    simp only [Pi.zero_apply, TensorProduct.tmul_zero]
    rw [show (fun _ : Fin V.rank => (0 : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) = 0 from rfl]
    simp
  | add x w _ _ hx hw =>
    have e : (fun i => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (x + w) i) =
        (fun i => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] x i) +
          (fun i => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] w i) := by
      funext i; simp [TensorProduct.tmul_add]
    rw [e, Matrix.mulVec_add, Pi.add_apply, map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hw)
  | smul r x _ hx =>
    have e : (fun i => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (r • x) i) =
        ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (r : D.host.E)) •
          (fun i => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] x i) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      congr 1
    rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, norm_mul, hev.1]
    exact mul_le_one₀ (norm_inc_le_one inc r) (norm_nonneg _) hx

end Space

end GlobalTheory.LocBasisInt

namespace GlobalTheory.LocBasisInt

theorem locBasis_integral : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (l : ℕ) [Fact l.Prime] (inc : D.host.E →+* PadicAlgCl l) (ev : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l), EvOk inc ev → V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame) → ∀ (y : Bridge.Gf V) (B : GL (Fin V.rank) D.host.E), Formalism.L2.Forms.IsLocBasis l (Bridge.hLat V y : Set (Fin V.rank → D.host.E)) B → ∀ a b, ‖((Matrix.GeneralLinearGroup.map ev (y : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)))⁻¹ * Matrix.GeneralLinearGroup.map inc B).val a b‖ ≤ 1 := by
  intro D V l _ inc ev hev hL0 y B hB a b
  obtain ⟨s, hs, hmem⟩ := (hB (fun k => B.val k b)).2 ⟨1, fun h => (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h), fun c => by
    have e : Matrix.mulVec (B⁻¹).val (fun k => B.val k b) c = ((B⁻¹).val * B.val) c b := rfl
    rw [e, Units.inv_mul, Matrix.one_apply]
    split_ifs
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩⟩
  have h := norm_ev_hLat_le_one V hL0 inc ev hev y _ hmem a
  have e : (fun i => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (((s : D.host.E) • fun k => B.val k b) i)) =
      ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (s : D.host.E)) •
        (fun i => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] B.val i b) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, norm_mul, hev.1, map_natCast,
    norm_natCast_eq_one' hs, one_mul] at h
  rw [← map_inv, Units.val_mul, Matrix.mul_apply]
  refine le_of_eq_of_le (congrArg norm ?_) h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mulVec, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, hev.1]
  rfl

end GlobalTheory.LocBasisInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalBasisIntegralRelativeAdelicPointStatement
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localBasis_integral_relative_adelicPoint : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (l : ℕ) [Fact l.Prime] (inc : D.host.E →+* PadicAlgCl l) (ev : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l), EvOk inc ev → V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame) → ∀ (y : Bridge.Gf V) (B : GL (Fin V.rank) D.host.E), Formalism.L2.Forms.IsLocBasis l (Bridge.hLat V y : Set (Fin V.rank → D.host.E)) B → ∀ a b, ‖((Matrix.GeneralLinearGroup.map ev (y : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)))⁻¹ * Matrix.GeneralLinearGroup.map inc B).val a b‖ ≤ 1 := by
  first | exact @GlobalTheory.LocBasisInt.locBasis_integral | exact GlobalTheory.LocBasisInt.locBasis_integral | (intros; apply GlobalTheory.LocBasisInt.locBasis_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnimodularMatricesPreserveFrameLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnimodularMatricesPreserveFrameLattices
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameRead

theorem exists_gl_preimage {O C : Type} [CommRing O] [CommRing C] (φ : O →+* C) (hφ : Function.Injective φ) {n : ℕ}
    (u : GL (Fin n) C) (h : ∀ a b, u.val a b ∈ Set.range φ ∧ (u⁻¹).val a b ∈ Set.range φ) :
    ∃ u0 : GL (Fin n) O, Matrix.GeneralLinearGroup.map φ u0 = u := by
  choose M hM using fun a b => (h a b).1
  choose M' hM' using fun a b => (h a b).2
  have e1 : φ.mapMatrix (Matrix.of M) = u.val := by ext a b; simp [hM]
  have e2 : φ.mapMatrix (Matrix.of M') = (u⁻¹).val := by ext a b; simp [hM']
  have inj : Function.Injective (φ.mapMatrix : Matrix (Fin n) (Fin n) O →+* Matrix (Fin n) (Fin n) C) := fun A B hAB => by
    ext a b; exact hφ (congrFun (congrFun hAB a) b)
  have h1 : Matrix.of M * Matrix.of M' = 1 := inj (by rw [map_mul, map_one, e1, e2, Units.mul_inv])
  have h2 : Matrix.of M' * Matrix.of M = 1 := inj (by rw [map_mul, map_one, e1, e2, Units.inv_mul])
  refine ⟨⟨Matrix.of M, Matrix.of M', h1, h2⟩, Units.ext ?_⟩
  exact e1

theorem det_map_gl {O C : Type} [CommRing O] [CommRing C] (φ : O →+* C) {n : ℕ} (g : GL (Fin n) O) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map φ g) = Units.map φ.toMonoidHom (Matrix.GeneralLinearGroup.det g) := by
  ext
  simp [Matrix.GeneralLinearGroup.map, RingHom.map_det]

theorem lamG_mem_lattices : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) (F : Frame l ι n), Function.Injective F.emb → (∀ τ, Antitone (res n (lamW τ))) → ∀ u : ι → GL (Fin n) (PadicAlgCl l), (∀ τ a b, (u τ).val a b ∈ Set.range F.emb ∧ (u τ)⁻¹.val a b ∈ Set.range F.emb) → ∀ z, (z ∈ F.latN lamW → lamG (PadicAlgCl l) n lamW c u z ∈ F.latN lamW) ∧ (z ∈ F.latD lamW → lamG (PadicAlgCl l) n lamW c u z ∈ F.latD lamW) := by
  intro l _ ι _ _ n lamW c F hinj hlam u hu z
  choose u0 hu0 using fun τ => exists_gl_preimage F.emb hinj (u τ) (hu τ)
  have hu' : u = fun τ => Matrix.GeneralLinearGroup.map F.emb (u0 τ) := funext fun τ => (hu0 τ).symm
  subst hu'
  have hs : ((∏ τ, Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map F.emb (u0 τ)) ^ c τ : (PadicAlgCl l)ˣ) : PadicAlgCl l) =
      F.emb ((∏ τ, Matrix.GeneralLinearGroup.det (u0 τ) ^ c τ : F.Oˣ) : F.O) := by
    simp only [det_map_gl, ← map_zpow, ← map_prod]
    rfl
  have key : ∀ x, lamG (PadicAlgCl l) n lamW c (fun τ => Matrix.GeneralLinearGroup.map F.emb (u0 τ)) (GlobalTheory.LatBC.bc F.emb n lamW x) =
      GlobalTheory.LatBC.bc F.emb n lamW (((∏ τ, Matrix.GeneralLinearGroup.det (u0 τ) ^ c τ : F.Oˣ) : F.O) • grp F.O n lamW u0 x) := by
    intro x
    rw [lamG_apply, hs, ← GlobalTheory.LatBC.bc_grp, LinearMap.map_smulₛₗ]
  constructor
  · intro hz
    obtain ⟨x, rfl⟩ := (GlobalTheory.LatBC.latN_iff F lamW _).1 hz
    exact (GlobalTheory.LatBC.latN_iff F lamW _).2 ⟨_, (key x).symm⟩
  · intro hz
    obtain ⟨x, hx, rfl⟩ := (GlobalTheory.LatBC.latD_iff F lamW hlam _).1 hz
    refine (GlobalTheory.LatBC.latD_iff F lamW hlam _).2 ⟨_, ?_, (key x).symm⟩
    exact Submodule.smul_mem _ _ (Formalism.CohomologicalDescent.RealLocalDeltaNabla.nablaRep_mem_delta F.O ι (fun _ => n) (fun _ => n) (fun _ => le_rfl)
      (fun τ => res n (lamW τ)) u0 x hx)

end GlobalTheory.FrameRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnimodularMatricesPreserveFrameLatticesStatement
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unimodular_matrices_preserve_frame_lattices : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) (F : Frame l ι n), Function.Injective F.emb → (∀ τ, Antitone (res n (lamW τ))) → ∀ u : ι → GL (Fin n) (PadicAlgCl l), (∀ τ a b, (u τ).val a b ∈ Set.range F.emb ∧ (u τ)⁻¹.val a b ∈ Set.range F.emb) → ∀ z, (z ∈ F.latN lamW → lamG (PadicAlgCl l) n lamW c u z ∈ F.latN lamW) ∧ (z ∈ F.latD lamW → lamG (PadicAlgCl l) n lamW c u z ∈ F.latD lamW) := by
  first | exact @GlobalTheory.FrameRead.lamG_mem_lattices | exact GlobalTheory.FrameRead.lamG_mem_lattices | (intros; apply GlobalTheory.FrameRead.lamG_mem_lattices <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntermediateFieldPadicIntegersEqNormLeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntermediateFieldPadicIntegersEqNormLeOne
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameOf

theorem intEmb_range_norm_le_one : ∀ (l : ℕ) [Fact l.Prime] (Lf : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] Lf],
    Function.Injective (intEmb Lf) ∧ ∀ x, x ∈ Set.range (intEmb Lf) ↔ x ∈ Lf ∧ ‖x‖ ≤ 1 := by
  intro l _ Lf _
  refine ⟨fun a b h => Subtype.ext (Subtype.ext h), fun x => ?_⟩
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨(a : Lf).2, ?_⟩
    rw [← Formalism.BasicNotions.Examples₂.LB.isIntegral_iff_norm_le]
    have ha : IsIntegral ℤ_[l] (a : Lf) := a.2
    exact ha.map (Lf.val.restrictScalars ℤ_[l])
  · rintro ⟨hx, hn⟩
    rw [← Formalism.BasicNotions.Examples₂.LB.isIntegral_iff_norm_le] at hn
    have hi : IsIntegral ℤ_[l] (⟨x, hx⟩ : Lf) :=
      (isIntegral_algHom_iff (Lf.val.restrictScalars ℤ_[l]) Subtype.val_injective).1 hn
    exact ⟨⟨⟨x, hx⟩, hi⟩, rfl⟩

end GlobalTheory.FrameOf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntermediateFieldPadicIntegersEqNormLeOneStatement
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intermediateField_padic_integers_eq_norm_le_one : ∀ (l : ℕ) [Fact l.Prime] (Lf : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] Lf], Function.Injective (intEmb Lf) ∧ ∀ x, x ∈ Set.range (intEmb Lf) ↔ x ∈ Lf ∧ ‖x‖ ≤ 1 := by
  first | exact @GlobalTheory.FrameOf.intEmb_range_norm_le_one | exact GlobalTheory.FrameOf.intEmb_range_norm_le_one | (intros; apply GlobalTheory.FrameOf.intEmb_range_norm_le_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalBasisDualBasisEmbeddedLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalBasisDualBasisEmbeddedLattice
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocBasisDual

open Formalism.HermitianLatticesTheory Formalism.UG _root_.Formalism.L2.Forms
open scoped Matrix

theorem natCast_notMem {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {l s : ℕ}
    (hl : l.Prime) (hlw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal) (hs : ¬ l ∣ s) : (s : 𝓞 K) ∉ w.asIdeal := by
  intro h
  have hcop : Nat.Coprime l s := (hl.coprime_iff_not_dvd).2 hs
  obtain ⟨a, b, e⟩ := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (𝓞 K))
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← e]
  refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)
  · simpa using hlw
  · simpa using h

theorem isBasisAt_tauLat {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} {n : ℕ}
    (emb : ι → E →+* K) (τ : ι) (w : HeightOneSpectrum (𝓞 K)) {l : ℕ} (hl : l.Prime)
    (hlw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal) (M : Submodule (𝓞 E) (Fin n → E)) (B : GL (Fin n) E)
    (hB : IsLocBasis l (M : Set (Fin n → E)) B) : IsBasisAt w (tauLat emb τ M) (bc (emb τ) B) := by
  have h1 : ¬ l ∣ 1 := fun h => hl.one_lt.ne' (Nat.dvd_one.1 h)
  unfold IsBasisAt
  apply le_antisymm
  · rw [← localized_localized w (colLat _)]
    refine localization_mono _ ?_
    unfold tauLat
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s', hs', hint⟩ := (hB x).1 ⟨1, h1, by simpa using hx⟩
    refine ⟨(s' : 𝓞 K), natCast_notMem w hl hlw hs', ?_⟩
    rw [lc_mem_colLat]
    intro a
    have e : ((s' : 𝓞 K) • fun b => emb τ (x b)) = fun b => emb τ (((s' : E) • x) b) := by
      funext b
      simp [Algebra.smul_def]
    rw [e, Formalism.L2.Col.vl_bc_inv_mulVec, Matrix.mulVec_smul]
    obtain ⟨r, hr⟩ := hint a
    exact du_map_mem_one (emb τ) (Submodule.mem_one.2 ⟨r, by rw [hr]; rfl⟩)
  · rw [← localized_localized w (tauLat emb τ M)]
    refine localization_mono _ ?_
    unfold colLat
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨s', hs', hmem⟩ := (hB (fun a => (B : Matrix (Fin n) (Fin n) E) a j)).2 ⟨1, h1, fun a => by
      have e : (((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ fun a => (B : Matrix (Fin n) (Fin n) E) a j) a =
          (1 : Matrix (Fin n) (Fin n) E) a j := by
        have h2 : ((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) * (B : Matrix (Fin n) (Fin n) E) = 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        rw [← h2]
        rfl
      rw [e, Matrix.one_apply]
      split_ifs
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp⟩⟩
    refine ⟨(s' : 𝓞 K), natCast_notMem w hl hlw hs', ?_⟩
    refine Submodule.subset_span ⟨_, hmem, ?_⟩
    funext b
    simp [Algebra.smul_def, bc_coe]

end GlobalTheory.LocBasisDual

namespace GlobalTheory.LocBasisDual

theorem basisAt_dualFr_tauLat : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (emb : ι → E →+* K) (τ : ι) (w : HeightOneSpectrum (𝓞 K)) (l : ℕ), l.Prime → ((l : ℕ) : 𝓞 K) ∈ w.asIdeal → ∀ (M : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E M → (∃ B, Formalism.L2.Forms.IsLocBasis l (M : Set (Fin n → E)) B) ∧ Submodule.IsLattice K (dualFr (tauLat emb τ M)) ∧ ∀ B : GL (Fin n) E, Formalism.L2.Forms.IsLocBasis l (M : Set (Fin n → E)) B → IsBasisAt w (dualFr (tauLat emb τ M)) (inside₂ K n (Matrix.GeneralLinearGroup.map (emb τ) B)) := by
  intro E K _ _ _ _ ι _ n emb τ w l hl hlw M hM
  have : Fact l.Prime := ⟨hl⟩
  refine ⟨Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis l E M hM.fg (Submodule.IsFullLattice.span_eq_top (self := hM)),
    (Formalism.L2.DIV.dualFr_tauLat_isLattice emb τ M hM).toIsLattice, fun B hB => ?_⟩
  exact pb_isBasisAt_dualFr w _ (tauLatticeLattice_holds E K ι n emb τ M hM).fg _
    (isBasisAt_tauLat emb τ w hl hlw M B hB)

end GlobalTheory.LocBasisDual
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalBasisDualBasisEmbeddedLatticeStatement
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localBasis_dualBasis_embeddedLattice : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (emb : ι → E →+* K) (τ : ι) (w : HeightOneSpectrum (𝓞 K)) (l : ℕ), l.Prime → ((l : ℕ) : 𝓞 K) ∈ w.asIdeal → ∀ (M : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E M → (∃ B, Formalism.L2.Forms.IsLocBasis l (M : Set (Fin n → E)) B) ∧ Submodule.IsLattice K (dualFr (tauLat emb τ M)) ∧ ∀ B : GL (Fin n) E, Formalism.L2.Forms.IsLocBasis l (M : Set (Fin n → E)) B → IsBasisAt w (dualFr (tauLat emb τ M)) (inside₂ K n (Matrix.GeneralLinearGroup.map (emb τ) B)) := by
  first | exact @GlobalTheory.LocBasisDual.basisAt_dualFr_tauLat | exact GlobalTheory.LocBasisDual.basisAt_dualFr_tauLat | (intros; apply GlobalTheory.LocBasisDual.basisAt_dualFr_tauLat <;> first | assumption | exact Submodule.IsFullLattice.toIsLattice (self := by assumption))
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapEqOneOfIsLocEnv
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EvLocal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem map_eq_zero_of_repr {F A E R ι : Type} [Field F] [CommRing A] [CommRing E] [Algebra F A] [Algebra F E] [CommRing R]
    [Fintype ι] (b : Module.Basis ι F E) (φ : A ⊗[F] E →+* R) (z : A ⊗[F] E)
    (hc : ∀ i, φ (((Algebra.TensorProduct.basis A b).repr z i) ⊗ₜ[F] 1) = 0) : φ z = 0 := by
  have hs : z = ∑ i, ((Algebra.TensorProduct.basis A b).repr z i ⊗ₜ[F] (1 : E)) * ((1 : A) ⊗ₜ[F] b i) := by
    conv_lhs => rw [← (Algebra.TensorProduct.basis A b).sum_repr z]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul', smul_eq_mul,
      one_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hs, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_mul, hc i, zero_mul]

theorem ev_eq_zero {D : D7} {l : ℕ} [Fact l.Prime] {inc : D.host.E →+* PadicAlgCl l}
    {ev : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l} (hev : EvOk inc ev)
    (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)
    (hz : ∀ w : HeightOneSpectrum (𝓞 D.host.F), ((l : ℕ) : 𝓞 D.host.F) ∈ w.asIdeal → GlobalTheory.HeckeRowsCompare.cmp D w z = 0) :
    ev z = 0 := by
  refine map_eq_zero_of_repr (A := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (Module.finBasis D.host.F D.host.E) ev z fun i => ?_
  refine hev.2.2.1 _ fun w hw => ?_
  have e := congrArg (fun z => (Algebra.TensorProduct.basis (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F w)
    (Module.finBasis D.host.F D.host.E)).repr z i) (hz w hw)
  simp only [GlobalTheory.HeckeRowsCompare.cmp, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at e
  rw [GlobalTheory.HeckeRowsCompare.repr_map, map_zero] at e
  exact e

theorem map_eq_one_of_isLocEnv : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i : ok × ℕ) (x : Bridge.Gf V) {l : ℕ} [Fact l.Prime] (inc : D.host.E →+* PadicAlgCl l) (ev : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l), EvOk inc ev → ((l : ℕ) : 𝓞 D.host.E) ∉ (pl i.1.1).asIdeal → isLocEnv V pl ok i x → ((x : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map ev = 1 := by
  intro D V Pl0 pl ok i x l _ inc ev hev hl hx
  have hloc : GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V ((pl i.1).under (𝓞 D.host.F)) x :=
    GlobalTheory.Mem.R3.LiftInertChi.locAt_of_isLocElt V _ x ((GlobalTheory.Hk3Split.isLabElt_of_isTEnv V pl ok i x).2.1 hx)
  ext a b
  have h0 : ev (x.1.1 a b - (1 : Matrix (Fin V.rank) (Fin V.rank) _) a b) = 0 := by
    refine ev_eq_zero hev _ fun w hw => ?_
    have hne : w ≠ (pl i.1).under (𝓞 D.host.F) := by
      rintro rfl
      apply hl
      have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (l : 𝓞 D.host.F) ∈ (pl i.1.1).asIdeal := hw
      rwa [map_natCast] at h2
    have h1 : x.1.1.map (GlobalTheory.HeckeRowsCompare.cmp D w) = 1 := hloc w hne
    have h3 := congrFun (congrFun h1 a) b
    rw [Matrix.map_apply] at h3
    rw [map_sub, h3, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [map_sub, sub_eq_zero] at h0
  rw [Matrix.map_apply]
  refine h0.trans ?_
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.EvLocal

end
end

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial

namespace GlobalTheory.FrameRead

open Formalism.IndefR.Bridge

theorem avatar_comm {C W M I : Type} [Field C] [AddCommGroup W] [Module ℂ W] [AddCommGroup M] [Module C M] (io : C ≃+* ℂ)
    (θ : W →+ M) (hs : ∀ (a : ℂ) w, θ (a • w) = io.symm a • θ w) (A : Module.End ℂ W) (B : Module.End C M) (v : I → W)
    (hv : Submodule.span ℂ (Set.range v) = ⊤) (h : ∀ i, θ (A (v i)) = B (θ (v i))) (x : W) : θ (A x) = B (θ x) := by
  have hx : x ∈ Submodule.span ℂ (Set.range v) := hv ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact h i
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add (f := _), hx, hy]
  | smul a x _ hx => simp only [map_smul, hs, hx]

theorem exists_reading_lat {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] {T : Type} [Fintype T]
    [DecidableEq T] {n : ℕ} {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} (P : ClassPres ι S σ ρ J χ)
    (lab : T → (E →+* K)) (lam : T → DomWeight n) (c0 : VV K lam →ₛₗ[σ] W) (e : S.V ≃ₗ[K] VV K lam) (hce : ∀ x, P.coef x = c0 (e x))
    (Lat : S.Cl → Submodule (𝓞 E) (Fin n → E)) (hlat : ∀ c, Submodule.IsFullLattice E (Lat c))
    (hN : ∀ c, (S.Nab c).map ((e : S.V →ₗ[K] VV K lam).restrictScalars (𝓞 K)) = nabAtr lab lam (Lat c))
    (hD : ∀ c, (S.Del c).map ((e : S.V →ₗ[K] VV K lam).restrictScalars (𝓞 K)) = delAtr lab lam (Lat c))
    (hc1 : LinearIndependent ℂ (fun i => c0 (bVV K lam i))) (hc2 : Submodule.span ℂ (Set.range fun i => c0 (bVV K lam i)) = ⊤)
    {l : ℕ} [Fact l.Prime] (w : HeightOneSpectrum (𝓞 K)) (e0 : K →+* PadicAlgCl l) (io : PadicAlgCl l ≃+* ℂ) (hw : AtPlace w e0)
    (hio : ∀ x, io (e0 x) = σ x) (m : G →* (T → GL (Fin n) (PadicAlgCl l)))
    (hrat : ∀ γ, ∃ γE, (∀ v, c0 (rhoVr lab lam γE v) = ρ γ (c0 v)) ∧
      m (ι γ) = fun τ => Matrix.GeneralLinearGroup.map (e0.comp (lab τ)) γE)
    (hint : ∀ c B, Formalism.L2.Forms.IsLocBasis l (Lat c : Set (Fin n → E)) B → ∀ τ a b,
      ‖((m (P.y c) τ)⁻¹ * Matrix.GeneralLinearGroup.map (e0.comp (lab τ)) B).val a b‖ ≤ 1 ∧
      ‖((Matrix.GeneralLinearGroup.map (e0.comp (lab τ)) B)⁻¹ * m (P.y c) τ).val a b‖ ≤ 1)
    (lamW : T → ℕ → ℕ) (cs : T → ℤ) (hS : Shift lam lamW cs)
    (Lf : IntermediateField ℚ_[l] (PadicAlgCl l)) (hL : ∀ x, e0 x ∈ Lf) (hmL : ∀ g τ a b, (m g τ).val a b ∈ Lf) (F : Frame l T n)
    (hinj : Function.Injective F.emb) (hF : ∀ x, x ∈ Set.range F.emb ↔ x ∈ Lf ∧ ‖x‖ ≤ 1)
    (hk : ∀ (k : J) τ a b, (m k τ).val a b ∈ Set.range F.emb) (hχ : ∀ k : J, io.symm (χ k : ℂ) ∈ Set.range F.emb) :
    ∃ rd : S.Forms →ₛₗ[e0] (G → NablaT (PadicAlgCl l) n lamW),
      (∀ f γ g, rd f (ι γ * g) = rd f g) ∧
      (∀ f (k : J) g, lamG (PadicAlgCl l) n lamW cs (m k) (rd f (g * k)) = io.symm (χ k : ℂ) • rd f g) ∧
      (∀ (n : ℕ) (f : Fin n → S.Forms), LinearIndependent K f → LinearIndependent (PadicAlgCl l) fun a => rd (f a)) ∧
      (∀ (f f' : S.Forms) (A : Finset G), P.ext f' = dcOp A (P.ext f) → (∀ a ∈ A, m a = 1) →
        ∀ g, rd f' g = ∑ s ∈ A, rd f (g * s)) ∧
      (∀ f : S.Forms, (∀ c, (f : S.Cl → S.V) c ∈ S.Nab c) → ∀ g, rd f g ∈ F.latN lamW) ∧
      ∀ f : S.Forms, (∀ g, rd f g ∈ F.latD lamW) → ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ ∀ c, s • (f : S.Cl → S.V) c ∈ S.Del c := by
  obtain ⟨Φ, hΦ, hli⟩ := GlobalTheory.T.exists_dualWeylTensor_lift_coefficientSpace _ _ e0 _ _ lam lamW cs hS
  obtain ⟨θ, hs, hθ, hθi⟩ := exists_avatar io hio (bVV K lam) c0 hc1 hc2 Φ hli
  have heq := GlobalTheory.T.dualWeylTensorLift_equivariant _ _ e0 _ _ lam lamW cs Φ hS hΦ
  let Λ0 := lamG (PadicAlgCl l) n lamW cs
  let Λ : G →* Module.End (PadicAlgCl l) (NablaT (PadicAlgCl l) n lamW) := Λ0.comp m
  have hΛ : ∀ γ x, θ (ρ γ x) = Λ (ι γ) (θ x) := by
    intro γ x
    obtain ⟨γE, hγ, hE⟩ := hrat γ
    refine avatar_comm io θ hs _ _ _ hc2 (fun i => ?_) x
    rw [← hγ, hθ, hθ]
    refine (heq (embGL lab γE) _).trans ?_
    show Λ0 _ _ = Λ0 (m (ι γ)) _
    rw [hE]
    rfl
  obtain ⟨rd, h1, h2, h3, h4, h5⟩ := exists_reading P io hio θ hs hθi Λ hΛ
  have hanti : ∀ τ, Antitone (res n (lamW τ)) := fun τ a b hab => by
    have := (lam τ).anti hab
    have ha := hS τ a
    have hb := hS τ b
    show lamW τ b ≤ lamW τ a
    omega
  have hstab := GlobalTheory.T.unimodular_matrices_preserve_frame_lattices l _ n lamW cs F hinj hanti
  have hlw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal := by
    rw [hw]
    have : e0 (((l : ℕ) : 𝓞 K) : K) = algebraMap ℚ_[l] (PadicAlgCl l) l := by simp
    rw [this, PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  have hmulL : ∀ A B : GL (Fin n) (PadicAlgCl l), (∀ a b, A.val a b ∈ Lf) → (∀ a b, B.val a b ∈ Lf) →
      ∀ a b, (A * B).val a b ∈ Lf := fun A B hA hB a b => by
    rw [Units.val_mul, Matrix.mul_apply]
    exact sum_mem fun x _ => mul_mem (hA _ _) (hB _ _)

  have key : ∀ (c : S.Cl), ∃ (B : T → GL (Fin n) K) (u : T → GL (Fin n) (PadicAlgCl l)),
      (∀ τ, Submodule.IsLattice K (dualFr (tauLat lab τ (Lat c)))) ∧
      (∀ τ, IsBasisAt w (dualFr (tauLat lab τ (Lat c))) (B τ)) ∧
      (∀ τ a b, (u τ).val a b ∈ Set.range F.emb ∧ (u τ)⁻¹.val a b ∈ Set.range F.emb) ∧
      ∀ v, Λ (P.y c)⁻¹ (Φ v) = Λ0 u (Φ (rhoK lam B⁻¹ v)) := by
    intro c
    have hb := fun τ => by
      first
      | exact GlobalTheory.T.localBasis_dualBasis_embeddedLattice _ _ _ _ lab τ w l Fact.out hlw _ (hlat c)
      | exact GlobalTheory.T.localBasis_dualBasis_embeddedLattice _ _ _ _ lab τ w l Fact.out hlw _ (hlat c).toIsLattice
    rcases isEmpty_or_nonempty T with hE | ⟨⟨τ0⟩⟩
    · refine ⟨1, 1, fun τ => hE.elim τ, fun τ => hE.elim τ, fun τ => hE.elim τ, fun v => ?_⟩
      have : m (P.y c)⁻¹ = 1 := Subsingleton.elim _ _
      show Λ0 (m (P.y c)⁻¹) _ = _
      rw [this, inv_one, map_one (rhoK lam)]
      rfl
    obtain ⟨B, hB⟩ := (hb τ0).1
    refine ⟨invTrK (embGL lab B), (m (P.y c))⁻¹ * fun τ => Matrix.GeneralLinearGroup.map (e0.comp (lab τ)) B,
      fun τ => (hb τ).2.1, fun τ => (hb τ).2.2 B hB, fun τ a b => ⟨(hF _).2 ⟨?_, ?_⟩, (hF _).2 ⟨?_, ?_⟩⟩, fun v => ?_⟩
    · refine hmulL _ _ (fun a b => ?_) (fun a b => hL _) a b
      rw [← map_inv]
      exact hmL _ τ a b
    · exact (hint c B hB τ a b).1
    · rw [Pi.mul_apply, mul_inv_rev, Pi.inv_apply, inv_inv, ← map_inv]
      exact hmulL _ _ (fun a b => hL _) (hmL _ τ) a b
    · rw [Pi.mul_apply, mul_inv_rev, Pi.inv_apply, inv_inv]
      exact (hint c B hB τ a b).2
    · rw [← map_inv invTrK, ← map_inv (embGL lab), heq]
      show Λ0 (m (P.y c)⁻¹) _ = (Λ0 _ * Λ0 _) _
      rw [← map_mul Λ0, map_inv m, mul_assoc]
      have : ((fun τ => Matrix.GeneralLinearGroup.map (e0.comp (lab τ)) B) *
          fun τ => Matrix.GeneralLinearGroup.map e0 (embGL lab B⁻¹ τ)) = 1 := by
        funext τ
        show Matrix.GeneralLinearGroup.map (e0.comp (lab τ)) B * Matrix.GeneralLinearGroup.map (e0.comp (lab τ)) B⁻¹ = 1
        rw [← map_mul, mul_inv_cancel, map_one]
      rw [this, mul_one]
  have hrange : ∀ x : K, ‖e0 x‖ ≤ 1 → e0 x ∈ Set.range F.emb := fun x hx => (hF _).2 ⟨hL x, hx⟩
  refine ⟨rd, h1, h2, h3, fun f f' A hA hA1 => h4 f f' A hA fun a ha => ?_, fun f hf g => ?_, fun f hf => ?_⟩
  · show Λ0 (m a) = 1
    rw [hA1 a ha, map_one]
  · have hy : ∀ c, rd f (P.y c) ∈ F.latN lamW := fun c => by
      obtain ⟨B, u, -, hB, hu, hv⟩ := key c
      rw [h5, hce, hθ, hv]
      refine (hstab u hu _).1 (GlobalTheory.T.isPhi_mem_latN_of_frame_injective_shift _ l w e0 _ _ lam lamW _ F Φ hw hinj hrange hS hΦ _ ?_)
      have hm : e ((f : S.Cl → S.V) c) ∈ nabAtr lab lam (Lat c) := hN c ▸ ⟨_, hf c, rfl⟩
      have hm' : ((e ((f : S.Cl → S.V) c) : VV K lam) : Pol K T n) ∈
        transLat lam (nabStd K lam) (fun τ => dualFr (tauLat lab τ (Lat c))) := hm
      simp only [transLat, Submodule.mem_iInf] at hm'
      exact hm' w B hB
    rw [P.dec_spec g, mul_assoc, h1]
    have h6 := congrArg (Λ0 (m (P.decK g)⁻¹)) (h2 f (P.decK g) (P.y (P.decC g)))
    have h7 : ∀ z, Λ0 (m (P.decK g)⁻¹) (Λ (P.decK g) z) = z := fun z => by
      show (Λ _ * Λ _) z = z
      rw [← map_mul, inv_mul_cancel, map_one]
      rfl
    rw [h7] at h6
    rw [h6]
    refine (hstab _ (fun τ a b => ⟨hk (P.decK g)⁻¹ τ a b, ?_⟩) _).1 ?_
    · rw [Subgroup.coe_inv, map_inv, Pi.inv_apply, inv_inv]
      exact hk _ τ a b
    · obtain ⟨r, hr⟩ := hχ (P.decK g)
      obtain ⟨x, hx⟩ := (GlobalTheory.LatBC.latN_iff F lamW _).1 (hy (P.decC g))
      exact (GlobalTheory.LatBC.latN_iff F lamW _).2 ⟨r • x, by rw [map_smulₛₗ, hr, hx]⟩
  · have hy : ∀ c, ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • (f : S.Cl → S.V) c ∈ S.Del c := fun c => by
      obtain ⟨B, u, hlat', hB, hu, hv⟩ := key c
      have h6 := hf (P.y c)
      rw [h5, hce, hθ, hv] at h6
      have h7 := (hstab u⁻¹ (fun τ a b => ⟨(hu τ a b).2, by rw [Pi.inv_apply, inv_inv]; exact (hu τ a b).1⟩) _).2 h6
      have h8 : ∀ z, Λ0 u⁻¹ (Λ0 u z) = z := fun z => by
        show (Λ0 _ * Λ0 _) z = z
        rw [← map_mul, inv_mul_cancel, map_one]
        rfl
      rw [h8] at h7
      have h9 := GlobalTheory.T.mem_localisedStandardWeyl_of_lift_mem _ l w e0 _ _ lam lamW _ F Φ hw (fun x => ((hF _).1 ⟨x, rfl⟩).2) hS hΦ _ h7
      have hlatFull : ∀ τ, Submodule.IsFullLattice K (dualFr (tauLat lab τ (Lat c))) := by
        intro τ
        have hcol : Submodule.span K (colLat (B τ) : Set (Fin n → K)) = ⊤ := by
          rw [colLat, Submodule.span_span_of_tower]
          change Submodule.span K (Set.range ((B τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).col) = ⊤
          rw [← Matrix.range_mulVecLin]
          exact LinearMap.range_eq_top.mpr (Matrix.mulVec_surjective_iff_isUnit.mpr (B τ).isUnit)
        refine { toIsLattice := hlat' τ, span_eq_top := ?_ }
        rw [eq_top_iff, ← hcol, Submodule.span_le]
        intro x hx
        apply Submodule.span_le_restrictScalars (GlobalTheory.LatBasisAt.locRing w) K _
        rw [← GlobalTheory.LatBasisAt.mem_localization_iff_mem_span, hB τ,
          GlobalTheory.LatBasisAt.mem_localization_iff_mem_span]
        exact Submodule.subset_span hx
      have h10 : ((e ((f : S.Cl → S.V) c) : VV K lam) : Pol K T n) ∈
          Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delP lam fun τ => dualFr (tauLat lab τ (Lat c))) := by
        rw [(GlobalTheory.TransLoc.nabDelLoc_free_leVV.1 _ _ _ lam _ hlatFull w B hB).2]
        refine ⟨_, h9, ?_⟩
        show (rhoP lam B * rhoP lam B⁻¹) _ = _
        rw [← map_mul, mul_inv_cancel, map_one]
        rfl
      obtain ⟨s, hs1, hs2⟩ := h10
      refine ⟨s, hs1, ?_⟩
      have h11 : s • e ((f : S.Cl → S.V) c) ∈ delAtr lab lam (Lat c) := hs2
      rw [← hD c] at h11
      obtain ⟨x, hx, hxe⟩ := h11
      have : x = s • (f : S.Cl → S.V) c := e.injective (by
        rw [← algebraMap_smul K s, map_smul, algebraMap_smul]; exact hxe)
      exact this ▸ hx
    classical
    choose s hs1 hs2 using hy
    refine ⟨∏ c, s c, prod_mem (S := w.asIdeal.primeCompl) fun c _ => hs1 c, fun c => ?_⟩
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ c), mul_smul]
    exact Submodule.smul_mem _ _ (hs2 c)

theorem scalar_eq {O C T : Type} [CommRing O] [Field C] [Fintype T] (φ : O →+* C) (a : Oˣ) (d : T → Oˣ) (cs : T → ℤ) (x : C)
    (h : (φ a * ∏ τ, φ (d τ) ^ (-cs τ)) * x = 1) :
    φ ((a⁻¹ * ∏ τ, d τ ^ cs τ : Oˣ) : O) = x ∧ ∏ τ, φ (d τ) ^ cs τ = φ a * x ∧ x ≠ 0 := by
  have hd : ∀ τ, φ (d τ) ≠ 0 := fun τ => ((d τ).isUnit.map φ).ne_zero
  have ha : φ a ≠ 0 := (a.isUnit.map φ).ne_zero
  have hp : (∏ τ, φ (d τ) ^ cs τ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (hd τ)
  simp only [zpow_neg, Finset.prod_inv_distrib] at h
  have h2 : ∏ τ, φ (d τ) ^ cs τ = φ a * x := by
    field_simp at h
    linear_combination -h
  refine ⟨?_, h2, by rintro rfl; simp at h⟩
  have e : φ ((∏ τ, d τ ^ cs τ : Oˣ) : O) = ∏ τ, φ (d τ) ^ cs τ := by
    rw [Units.coe_prod, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have := map_zpow (Units.map (φ : O →* C)) (d τ) (cs τ)
    exact (congrArg Units.val this).trans (Units.val_zpow_eq_zpow_val _ _)
  rw [Units.val_mul, map_mul, e, h2, map_units_inv, inv_mul_cancel_left₀ ha]

theorem smul_cancel {C M : Type} [Field C] [AddCommGroup M] [Module C M] {a x d : C} {u r : M} (hx : x ≠ 0) (hd : d = a * x)
    (h : d • u = x • r) : a • u = r :=
  smul_right_injective M hx (show x • a • u = x • r by rw [← h, hd, smul_smul, mul_comm])

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Core

variable {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {l : ℕ} [Fact l.Prime]

def evG (ev : D.what₂.Tau → (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l)) :
    Gf V →* (D.what₂.Tau → GL (Fin V.rank) (PadicAlgCl l)) :=
  MonoidHom.pi fun τ => (Matrix.GeneralLinearGroup.map (ev τ)).comp (Gf V).subtype

theorem evG_rat {ev : D.what₂.Tau → (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l)}
    {inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl l)} (hev : ∀ τ x, ev τ (1 ⊗ₜ[D.host.F] x) = inc τ x) (γ : Formalism.L2.Theta.GQ V) :
    ∃ γE, IsRatMat V γ γE ∧ evG V ev (ratF V γ) = fun τ => Matrix.GeneralLinearGroup.map (inc τ) γE := by
  obtain ⟨γE, hγ⟩ : ∃ γE, IsRatMat V γ γE := by
    obtain ⟨x, hx⟩ := γ
    obtain ⟨y, -, hy⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hx)
    exact ⟨y, hy.symm⟩
  refine ⟨γE, hγ, funext fun τ => Units.ext (Matrix.ext fun a b => ?_)⟩
  have e : Units.val (Formalism.L2.Theta.finHom V (γ : Formalism.L2.Theta.GA D V)) a b = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] γE.val a b := by
    have hγ' : Formalism.L2.Theta.matHom V (γ : Formalism.L2.Theta.GA D V) = _ := hγ
    rw [Formalism.L2.Theta.finHom, MonoidHom.comp_apply, hγ']
    show (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E))
      ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ⊗ₜ[D.host.F] (γE.val a b)) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  show ev τ (Units.val (Formalism.L2.Theta.finHom V (γ : Formalism.L2.Theta.GA D V)) a b) = inc τ (γE.val a b)
  rw [e]
  exact hev τ _

end Core

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)


set_option maxHeartbeats 4000000 in
theorem reads_rank (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (lamW : D.what₂.Tau → ℕ → ℕ)
    (cs : D.what₂.Tau → ℤ) (hS : Shift (fun τ => lamLdef (D := D) (Vc D j).rank ((j : ℕ) + 1) τ) lamW cs) {N : ℕ}
    (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (io : PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w) ≃+* ℂ)
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)))
    (bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (rk : Fin N ≃o Fin (Vc D j).rank)
    (Lf : IntermediateField ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) [FiniteDimensional ℚ_[Formalism.EigenvalueLevelCeiling.plc w] Lf]
    (kap : levJ p j (p.R.mu w) →* (D.what₂.Tau → GL (Fin N) (intR Lf))) (chi : levJ p j (p.R.mu w) →* (intR Lf)ˣ)
    (hC : ChoiceOk p j w e0 false io ev bs rk (fun τ => -cs τ) kap chi) (hbs : ∀ τ, bs τ = 1) :
    ∃ R : Reads (frameOf p j (p.R.mu w) (Formalism.EigenvalueLevelCeiling.plc w) N Lf kap chi) lamW (blk p j (p.R.mu w)) w,
      R.e0 = e0 ∧ R.ix = Subtype.val := by
  classical
  obtain rfl : N = (Vc D j).rank := by simpa using Fintype.card_congr rk.toEquiv
  obtain rfl : rk = OrderIso.refl _ := Subsingleton.elim _ _
  obtain ⟨hw, hL, hio, hev, hkap, hchi⟩ := hC
  obtain ⟨gramR, c0R, c0L, tie⟩ := p.charW.base.fam.tie
  obtain ⟨e, -, hce, -, hN, hD⟩ := tie.coefL j (p.R.mu w)
  have hM := tie.mapL j
  obtain ⟨hinj, hF⟩ := GlobalTheory.T.intermediateField_padic_integers_eq_norm_le_one _ Lf
  have hev' : ∀ τ, EvOk (e0.comp (labLL D τ)) (ev τ) := hev
  have hk : ∀ (k : levJ p j (p.R.mu w)) τ, Matrix.GeneralLinearGroup.map (intEmb Lf) (kap k τ) = evG (Vc D j) ev k τ := by
    intro k τ
    refine Units.ext ((hkap k τ).trans ?_)
    rw [kapMat, hbs, inv_one, Units.val_one, one_mul, mul_one]
    rfl
  have hdet : ∀ (k : levJ p j (p.R.mu w)) τ, ((Matrix.GeneralLinearGroup.det (evG (Vc D j) ev k τ) : (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))ˣ) :
      PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) = intEmb Lf (kap k τ).val.det := by
    intro k τ
    rw [← hk, RingHom.map_det]
    rfl
  have hχ : ∀ k : levJ p j (p.R.mu w), (intEmb Lf (chi k) * ∏ τ, intEmb Lf (kap k τ).val.det ^ (-cs τ)) *
      io.symm ((levChi p j (p.R.mu w) k : ℂˣ) : ℂ) = 1 := by
    intro k
    apply io.injective
    rw [map_mul, RingEquiv.apply_symm_apply, map_one]
    exact hchi k
  have hsc := fun k : levJ p j (p.R.mu w) =>
    scalar_eq (intEmb Lf) (chi k) (fun τ => Matrix.GeneralLinearGroup.det (kap k τ)) cs _ (hχ k)
  have hLatFull (g : Bridge.Gf (Vc D j)) : Submodule.IsFullLattice D.host.E (hLat (Vc D j) g) := by
    obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D (Vc D j)
    obtain ⟨Λ, hΛ, h1, h2, -⟩ := GlobalTheory.AdLat.exists_lattice_latOf D.host.F D.host.E (Vc D j).rank (GlobalTheory.Member.latC (Vc D j)) g.1 hfg hsp
    rw [SetLike.coe_injective ((GlobalTheory.RepsCompare.coe_hLat (Vc D j) g).trans hΛ.symm)]
    letI : Submodule.IsLattice D.host.E Λ := Submodule.IsLattice.of_fg D.host.E h1
    exact { span_eq_top := h2 }
  obtain ⟨rd, h1, h2, h3, h4, h5, h6⟩ := exists_reading_lat (p.R.B.L j (p.R.mu w)).pres (labLL D) _ (c0L j) e hce
    (fun c => hLat (Vc D j) ((p.R.B.L j (p.R.mu w)).pres.y c)) (fun c => hLatFull _) hN hD hM.2.1 hM.2.2 w e0 io hw hio
    (evG (Vc D j) ev)
    (fun γ => (evG_rat (Vc D j) (fun τ => (hev' τ).1) γ).imp fun γE h => ⟨hM.1 γ γE h.1, h.2⟩)
    (fun c B hB τ a b => ⟨GlobalTheory.T.localBasis_integral_relative_adelicPoint (Vc D j) _ _ _ (hev' τ) (p.stdV j).2 _ B hB a b,
      GlobalTheory.T.adelicPoint_integral_relative_localBasis (Vc D j) _ _ _ (hev' τ) (p.stdV j).2 _ B hB a b⟩)
    lamW cs hS Lf hL
    (fun g τ a b => (IntermediateField.adjoin_le_iff.2 (by rintro _ ⟨x, rfl⟩; exact hL _)) ((hev' τ).2.2.2 _))
    (frameOf p j (p.R.mu w) (Formalism.EigenvalueLevelCeiling.plc w) _ Lf kap chi) hinj hF
    (fun k τ a b => ⟨(kap k τ).val a b, congrArg (fun M : GL _ _ => M.val a b) (hk k τ)⟩)
    (fun k => ⟨(((chi k)⁻¹ * ∏ τ, Matrix.GeneralLinearGroup.det (kap k τ) ^ cs τ : (intR Lf)ˣ) : intR Lf), (hsc k).1⟩)
  refine ⟨⟨e0, Subtype.val, rd, hw, fun x => (hF _).2 ⟨hL _, ?_⟩, fun f => ⟨?_, fun k g => ?_⟩, h3, fun i f g => ?_, h5, h6⟩, rfl, rfl⟩
  · exact (GlobalTheory.T.norm_le_one_iff_integral_at_padicEmbedding_place _ _ w e0 hw _).2 ⟨1, (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top, x, by simp⟩
  · rintro _ ⟨γ, rfl⟩ g
    exact h1 f γ g
  · have h7 := h2 f k g
    rw [lamG_apply] at h7
    have h8 := smul_cancel (hsc k).2.2 (Eq.trans (by simp only [Units.coe_prod, Units.val_zpow_eq_zpow_val, hdet k]; rfl) (hsc k).2.1) h7
    rw [← funext (hk k)] at h8
    exact h8
  · have hr : 1 ≤ i.1.2 ∧ i.1.2 ≤ (Vc D j).rank := ⟨i.2.1, i.2.2.1⟩
    have h7 := h4 f _ _ ((p.R.B.L j (p.R.mu w)).hecke.op_eq i.1 hr f) (fun a ha => funext fun τ => Units.ext
      (GlobalTheory.EvLocal.map_eq_one_of_isLocEnv (Vc D j) p.R.pl _ i.1 a _ _ (hev' τ) i.2.2.2
        ((p.R.B.L j (p.R.mu w)).hecke.hA_loc i.1 hr a ha))) g
    refine h7.trans ?_
    show _ = intEmb Lf 1 • _
    rw [map_one, one_smul]
    rfl

end Point

end GlobalTheory.FrameRead
