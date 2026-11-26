module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFundIpow
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeWithDensityDetNormSq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatDetHMapInjectiveIsometry
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatDetHMapInjectiveIsometry
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.DetMap

section General

variable {R K U V : Type*} [CommRing R] [Field K] [Algebra R K]
  [AddCommGroup U] [Module K U] [Module R U] [IsScalarTower R K U]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem length_quot_map (f : U →ₗ[R] V) (hf : Function.Injective f) (A B : Submodule R U) :
    Module.length R ((A.map f) ⧸ (B.map f).comap (A.map f).subtype) =
      Module.length R (A ⧸ B.comap A.subtype) := by
  let e : A ≃ₗ[R] A.map f := Submodule.equivMapOfInjective f hf A
  have he : (B.comap A.subtype).map (e : A →ₗ[R] A.map f) = (B.map f).comap (A.map f).subtype := by
    ext z
    constructor
    · rintro ⟨⟨a, ha⟩, haB, rfl⟩
      exact ⟨a, haB, rfl⟩
    · intro hz
      obtain ⟨b, hb, hbz⟩ := hz
      obtain ⟨a, ha, haz⟩ := z.2
      obtain rfl : a = b := hf (haz.trans hbz.symm)
      exact ⟨⟨a, ha⟩, hb, Subtype.ext haz⟩
  exact (Submodule.Quotient.equiv _ _ e he).length_eq.symm

theorem localization_map₂ (hRK : Function.Injective (algebraMap R K)) (i : U →ₗ[K] V)
    (hi : Function.Injective i) (p : Ideal R) [p.IsPrime] (A : Submodule R U) :
    Formalism.HermitianLatticesTheory.localization₂ p (A.map (i.restrictScalars R)) = (Formalism.HermitianLatticesTheory.localization₂ p A).map (i.restrictScalars R) := by
  ext x
  constructor
  · rintro ⟨s, hs, a, ha, hax⟩
    have hs0 : algebraMap R K s ≠ 0 := by
      intro h0
      apply hs
      have : s = 0 := hRK (by rw [h0, map_zero])
      rw [this]
      exact p.zero_mem
    refine ⟨(algebraMap R K s)⁻¹ • a, ⟨s, hs, ?_⟩, ?_⟩
    · rw [← algebraMap_smul K s ((algebraMap R K s)⁻¹ • a), smul_smul, mul_inv_cancel₀ hs0, one_smul]
      exact ha
    · rw [LinearMap.restrictScalars_apply] at hax ⊢
      rw [map_smul, hax, ← algebraMap_smul K s x, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  · rintro ⟨y, ⟨s, hs, hsy⟩, rfl⟩
    exact ⟨s, hs, s • y, hsy, LinearMap.map_smul _ s y⟩

theorem locLen_map (hRK : Function.Injective (algebraMap R K)) (i : U →ₗ[K] V)
    (hi : Function.Injective i) (p : Ideal R) [p.IsPrime] (A B : Submodule R U) :
    Formalism.HermitianLatticesTheory.locLen p (A.map (i.restrictScalars R)) (B.map (i.restrictScalars R)) =
      Formalism.HermitianLatticesTheory.locLen p A B := by
  unfold Formalism.HermitianLatticesTheory.locLen
  rw [localization_map₂ hRK i hi p A, localization_map₂ hRK i hi p B,
    length_quot_map (i.restrictScalars R) (by simpa using hi)]

theorem lidx_map (hRK : Function.Injective (algebraMap R K)) (i : U →ₗ[K] V)
    (hi : Function.Injective i) (p : Ideal R) [p.IsPrime] (A B : Submodule R U) :
    Formalism.HermitianLatticesTheory.lidx p (A.map (i.restrictScalars R)) (B.map (i.restrictScalars R)) =
      Formalism.HermitianLatticesTheory.lidx p A B := by
  have hi' : Function.Injective (i.restrictScalars R) := by simpa using hi
  unfold Formalism.HermitianLatticesTheory.lidx
  rw [← Submodule.map_inf _ hi', locLen_map hRK i hi, locLen_map hRK i hi]

end General

section NumberField

variable {K U V : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup U] [Module K U] [Module (𝓞 K) U] [IsScalarTower (𝓞 K) K U]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem genIdxH_map (i : U →ₗ[K] V) (hi : Function.Injective i) (A B : Submodule (𝓞 K) U) :
    genIdxH (A.map (i.restrictScalars (𝓞 K))) (B.map (i.restrictScalars (𝓞 K))) = genIdxH A B := by
  have hRK : Function.Injective (algebraMap (𝓞 K) K) := IsFractionRing.injective (𝓞 K) K
  unfold genIdxH
  refine finprod_congr fun P => ?_
  haveI := P.isPrime
  rw [lidx_map hRK i hi]

theorem mem_dual (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule (𝓞 K) K) := by
  simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]

theorem dualInH_map (hU : U →ₗ⋆[K] U →ₗ[K] K) (hV : V →ₗ⋆[K] V →ₗ[K] K) (i : U →ₗ[K] V)
    (hiso : ∀ x y, hV (i x) (i y) = hU x y) (N : Submodule (𝓞 K) U) :
    dualInH hV (N.map (i.restrictScalars (𝓞 K))) =
      (dualInH hU N).map (i.restrictScalars (𝓞 K)) := by
  have hspan : (Submodule.span K ((N.map (i.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V)) =
      (Submodule.span K (N : Set U)).map i := by
    rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image]
  ext x
  simp only [dualInH, Submodule.mem_inf, Submodule.restrictScalars_mem, hspan, mem_dual,
    Submodule.mem_map, LinearMap.coe_restrictScalars]
  constructor
  · rintro ⟨hx, y, hy, rfl⟩
    refine ⟨y, ⟨fun n hn => ?_, hy⟩, rfl⟩
    rw [← hiso]
    exact hx (i n) ⟨n, hn, rfl⟩
  · rintro ⟨y, ⟨hy, hys⟩, rfl⟩
    refine ⟨?_, y, hys, rfl⟩
    rintro _ ⟨n, hn, rfl⟩
    rw [hiso]
    exact hy n hn

end NumberField

theorem latDetH_map : ∀ (K U V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup U] [Module K U] [Module (𝓞 K) U] [IsScalarTower (𝓞 K) K U] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (hU : U →ₗ⋆[K] U →ₗ[K] K) (hV : V →ₗ⋆[K] V →ₗ[K] K) (i : U →ₗ[K] V), Function.Injective i → (∀ x y, hV (i x) (i y) = hU x y) → ∀ N : Submodule (𝓞 K) U, latDetH hV (N.map (i.restrictScalars (𝓞 K))) = latDetH hU N := by
  intro K U V _ _ _ _ _ _ _ _ _ _ _ hU hV i hi hiso N
  unfold latDetH
  rw [dualInH_map hU hV i hiso, genIdxH_map i hi]

end GlobalTheory.LoopC.DetMap
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatDetHMapInjectiveIsometryStatement
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latDetH_map_injective_isometry : ∀ (K U V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup U] [Module K U] [Module (𝓞 K) U] [IsScalarTower (𝓞 K) K U] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (hU : U →ₗ⋆[K] U →ₗ[K] K) (hV : V →ₗ⋆[K] V →ₗ[K] K) (i : U →ₗ[K] V), Function.Injective i → (∀ x y, hV (i x) (i y) = hU x y) → ∀ N : Submodule (𝓞 K) U, latDetH hV (N.map (i.restrictScalars (𝓞 K))) = latDetH hU N := by
  first | exact @GlobalTheory.LoopC.DetMap.latDetH_map | exact GlobalTheory.LoopC.DetMap.latDetH_map | (intros; apply GlobalTheory.LoopC.DetMap.latDetH_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSplitUnitVectorOrthComplement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

private theorem hform_eq_star_dotProduct (I : AutInst) (x y : Fin I.n → I.E) :
    Formalism.UG.hform (starRingEnd I.E) I.J x y = star x ⬝ᵥ (I.J *ᵥ y) := by
  change (∑ i, ∑ j, star (x i) * I.J i j * y j) = _
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem IsPerp.exists_split {I : AutInst} {D : Sib I} {s : Bool} {x : Fin I.n → I.E}
    {A : Matrix (Fin I.n) (Fin D.n) I.E} {xf : I.Gf} (h : IsPerp D s x A xf) {y : Fin I.n → I.E}
    (hy : y ∈ lamX I (1, xf)) : ∃ a : 𝓞 I.E, ∃ w ∈ D.L, y = a • x + A *ᵥ w := by
  obtain ⟨hn, hβ, hxA, hAJ, hx, hL⟩ := h
  have hJ : I.Jᴴ = I.J := by
    rw [← (show Formalism.UG.cT (starRingEnd I.E) I.J = I.Jᴴ by ext i j; rfl)]
    exact I.J_herm
  have hsq : sgn I.E s * sgn I.E s = 1 := by cases s <;> simp [sgn]
  have hβ0 : star x ⬝ᵥ (I.J *ᵥ x) ≠ 0 := by
    intro h0
    rw [hβ] at h0
    rw [h0, zero_mul] at hsq
    exact zero_ne_one hsq
  obtain ⟨u, A', -, -, -, -, hres, -⟩ :=
    exists_dual_of_anisotropic_orthogonal I.E I.n D.n I.J D.J x A hn hJ D.J_det hβ0 hxA hAJ

  have hdec : y = (u ⬝ᵥ y) • x + A *ᵥ (A' *ᵥ y) := by
    have h1 : (vecMulVec x u + A * A') *ᵥ y = y := by rw [hres, one_mulVec]
    rw [add_mulVec, ← mulVec_mulVec] at h1
    refine h1.symm.trans ?_
    congr 1
    ext i
    simp [mulVec, dotProduct, vecMulVec, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

  have hpair : ∀ (c : I.E) (w : Fin D.n → I.E), y = c • x + A *ᵥ w →
      star x ⬝ᵥ (I.J *ᵥ y) = c * sgn I.E s := by
    intro c w e
    rw [e, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul, hβ, mulVec_mulVec,
      dotProduct_mulVec, hxA, zero_dotProduct, add_zero]
  have hcoef : u ⬝ᵥ y = sgn I.E s * Formalism.UG.hform (starRingEnd I.E) I.J x y := by
    rw [hform_eq_star_dotProduct, hpair _ _ hdec]
    linear_combination (-(u ⬝ᵥ y)) * hsq
  have hint : Formalism.UG.hform (starRingEnd I.E) I.J x y ∈ (algebraMap (𝓞 I.E) I.E).range :=
    (((GlobalTheory.PointLattice.lamX_selfDual I (1, xf)).2.2.2.1 y).mp hy) x hx
  have hsgn : sgn I.E s ∈ (algebraMap (𝓞 I.E) I.E).range := by
    cases s
    · exact ⟨-1, by simp [sgn]⟩
    · exact ⟨1, by simp [sgn]⟩
  obtain ⟨a, ha⟩ := Subring.mul_mem _ hsgn hint
  have hca : (u ⬝ᵥ y) • x = a • x := by rw [hcoef, ← ha, algebraMap_smul]
  refine ⟨a, A' *ᵥ y, (hL _).mpr ?_, ?_⟩
  · have e : A *ᵥ (A' *ᵥ y) = y - a • x := by
      rw [← hca]
      exact eq_sub_of_add_eq' hdec.symm
    rw [e]
    exact Submodule.sub_mem _ hy (Submodule.smul_mem _ a hx)
  · rw [← hca]
    exact hdec

theorem afVec_mulVec_eq_afMat_mulVec (I : AutInst) {m k : ℕ} (A : Matrix (Fin m) (Fin k) I.E) (w : Fin k → I.E) :
    afVec I (A *ᵥ w) = afMat I A *ᵥ afVec I w := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [afVec, afMat, mulVec, dotProduct, map_sum]

private theorem mem_lf_iff_mem_latS (I : AutInst) (v : Fin I.n → I.E ⊗[I.F] Af I.F) :
    v ∈ I.Lf ↔ v ∈ Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L := by
  show v ∈ lamAf (F := I.F) I.L ↔ v ∈ Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L
  unfold lamAf Formalism.UG.latS
  constructor
  · refine fun hv => Submodule.span_mono ?_ hv
    rintro _ ⟨y, rfl⟩
    exact ⟨y, y.2, rfl⟩
  · refine fun hv => Submodule.span_mono ?_ hv
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

theorem adelicLattice_split : ∀ (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf), IsPerp D s x A xf → ∀ z : Fin I.n → I.E ⊗[I.F] Af I.F, I.fmat xf⁻¹ *ᵥ z ∈ I.Lf ↔ ∃ a ∈ IntAf I.F I.E, ∃ w ∈ D.inst.Lf, z = a • afVec I x + afMat I A *ᵥ w := by
  intro I D s x A xf h z
  have hmem : ∀ y : Fin I.n → I.E, y ∈ lamX I (1, xf) → I.fmat xf⁻¹ *ᵥ afVec I y ∈ I.Lf :=
    fun y hy => ((GlobalTheory.PointLattice.lamX_selfDual I (1, xf)).1 y).mp hy
  obtain ⟨-, -, -, -, hx, hL⟩ := id h
  constructor
  · intro hz
    have hspan := Formalism.UG.P.csSpan_back Formalism.UG.P.integral_adele_approximation_holds I.L
      (Module.Finite.iff_fg.mpr I.L_fg) I.L_span (xf : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) z
      ((mem_lf_iff_mem_latS I _).mp hz)
    clear hz
    induction hspan using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨y, hy, rfl⟩ := hv
      have hy' : y ∈ lamX I (1, xf) := by
        rw [GlobalTheory.PointLattice.lamX_eq_globLat]
        exact hy
      obtain ⟨a0, w0, hw0, e⟩ := IsPerp.exists_split h hy'
      refine ⟨Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E a0), Formalism.UG.CS.incl_int a0,
        afVec I w0, Submodule.subset_span ⟨⟨w0, hw0⟩, rfl⟩, ?_⟩
      rw [← afVec_mulVec_eq_afMat_mulVec]
      funext i
      simp [afVec, e, Algebra.smul_def, map_add (f := _), map_mul]
    | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
    | add v1 v2 _ _ h1 h2 =>
      obtain ⟨a1, ha1, w1, hw1, rfl⟩ := h1
      obtain ⟨a2, ha2, w2, hw2, rfl⟩ := h2
      refine ⟨a1 + a2, add_mem ha1 ha2, w1 + w2, add_mem hw1 hw2, ?_⟩
      rw [add_smul, mulVec_add]
      abel
    | smul c v _ h1 =>
      obtain ⟨a, ha, w, hw, rfl⟩ := h1
      refine ⟨(c : I.E ⊗[I.F] Af I.F) * a, mul_mem c.2 ha, (c : I.E ⊗[I.F] Af I.F) • w,
        Submodule.smul_mem _ c hw, ?_⟩
      show (c : I.E ⊗[I.F] Af I.F) • (a • afVec I x + afMat I A *ᵥ w) = _
      rw [smul_add, mul_smul, mulVec_smul]
  · rintro ⟨a, ha, w, hw, rfl⟩
    rw [mulVec_add, mulVec_smul]
    refine add_mem (Submodule.smul_mem I.Lf ⟨a, ha⟩ (hmem x hx)) ?_
    have hw' : w ∈ Submodule.span (IntAf I.F I.E)
        (Set.range fun y : D.L => afVec I (y : Fin D.n → I.E)) := hw
    clear hw
    induction hw' using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨⟨y, hy⟩, rfl⟩ := hv
      show I.fmat xf⁻¹ *ᵥ (afMat I A *ᵥ afVec I y) ∈ I.Lf
      rw [← afVec_mulVec_eq_afMat_mulVec]
      exact hmem _ ((hL y).mp hy)
    | zero => simp
    | add v1 v2 _ _ h1 h2 =>
      rw [mulVec_add, mulVec_add]
      exact add_mem h1 h2
    | smul c v _ h1 =>
      show I.fmat xf⁻¹ *ᵥ (afMat I A *ᵥ ((c : I.E ⊗[I.F] Af I.F) • v)) ∈ I.Lf
      rw [mulVec_smul, mulVec_smul]
      exact Submodule.smul_mem I.Lf c h1

end GlobalTheory.StabUnfold
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsClosedEmbeddingOrthogonalUnitaryRealPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsClosedEmbeddingOrthogonalUnitaryRealPlace
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

theorem star_dot_Jm {n : ℕ} (ε : Fin n → Bool) (x : Fin n → ℂ) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) = (qEps ε x : ℂ) := by
  unfold qEps Formalism.REAL.Jm
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : (starRingEnd ℂ) (x i) * x i = ((‖x i‖ : ℝ) : ℂ) ^ 2 := Complex.conj_mul' (x i)
  split_ifs
  · simp [hi]
  · simp [hi]

theorem realUJ_eq {n : ℕ} (ε : Fin n → Bool) :
    Formalism.UG.UJ (starRingEnd ℂ) (Formalism.REAL.Jm ε) = Formalism.REAL.UJ ε := by
  unfold Formalism.REAL.UJ Formalism.UG.UJ Formalism.REAL.inUJ
  have hc : ∀ M : Matrix (Fin n) (Fin n) ℂ, Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
    intro M
    ext i j
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply, Complex.star_def]
  ext g
  change Formalism.UG.cT (starRingEnd ℂ) (g : Matrix (Fin n) (Fin n) ℂ) * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε ↔
    (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
  rw [hc]

theorem exists_closedEmbedding_unitary_orthogonal (n m : ℕ) (ε : Fin n → Bool) (ε' : Fin m → Bool) (s : Bool)
    (x₀ : Fin n → ℂ) (B : Matrix (Fin n) (Fin m) ℂ) (hn : m + 1 = n) (hq : qEps ε x₀ = sgn ℝ s)
    (hx : star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0) (hB : Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε') :
    ∃ j : Formalism.REAL.UJ ε' →* Formalism.REAL.UJ ε, Topology.IsClosedEmbedding j ∧
      ∀ g, uMat (j g) *ᵥ x₀ = x₀ ∧ uMat (j g) * B = B * uMat g := by
  unfold uMat
  have hJh : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
    unfold Formalism.REAL.Jm
    rw [diagonal_conjTranspose]
    congr 1
    funext a
    by_cases h : ε a <;> simp [h]
  have hdet : (Formalism.REAL.Jm ε').det ≠ 0 := by
    unfold Formalism.REAL.Jm
    rw [det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => by by_cases h : ε' a <;> simp [h]
  have hβ : star x₀ ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x₀) ≠ 0 := by
    rw [star_dot_Jm, hq]
    cases s <;> simp [sgn]
  obtain ⟨u, A', hA'B, hA'x, huB, hux, hres, hBJx⟩ :=
    exists_dual_of_anisotropic_orthogonal ℂ n m (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε') x₀ B hn hJh hdet hβ hx hB
  have hcT : ∀ {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℂ), Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
    intro p q M
    ext i k
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply, Complex.star_def]
  have hstar : (fun i => starRingEnd ℂ (x₀ i)) = star x₀ := by
    funext i
    simp [Complex.star_def]
  obtain ⟨j, hjmat, hjrange⟩ := GlobalTheory.T.exists_unitary_orthogonal_embedding_stabilizer ℂ (starRingEnd ℂ) n m (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε') x₀ u B A'
    (by rw [hstar]; exact isUnit_iff_ne_zero.mpr hβ) (by rw [hstar]; exact hx) (by rw [hcT]; exact hBJx)
    (by rw [hcT]; exact hB) hA'B hA'x huB hux hres
  obtain ⟨jj, hjj, hrange⟩ : ∃ jj : Formalism.REAL.UJ ε' →* Formalism.REAL.UJ ε,
      (∀ g, ((jj g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
        vecMulVec x₀ u + B * ((g : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) * A') ∧
      ∀ h : Formalism.REAL.UJ ε, ((h : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *ᵥ x₀ = x₀ → ∃ g, jj g = h := by
    refine ⟨(MulEquiv.subgroupCongr (realUJ_eq ε)).toMonoidHom.comp
      (j.comp (MulEquiv.subgroupCongr (realUJ_eq ε')).symm.toMonoidHom), fun g => hjmat _, ?_⟩
    intro h hh
    obtain ⟨g', hg'⟩ := hjrange ((MulEquiv.subgroupCongr (realUJ_eq ε)).symm h) hh
    refine ⟨MulEquiv.subgroupCongr (realUJ_eq ε') g', ?_⟩
    apply Subtype.ext
    exact congrArg Subtype.val hg'
  have h0 : vecMulVec x₀ u * B = 0 := by
    ext i k
    have hk := congrFun huB k
    simp only [vecMul, dotProduct, Pi.zero_apply] at hk
    change (∑ j, (x₀ i * u j) * B j k) = 0
    simp only [mul_assoc, ← Finset.mul_sum, hk, mul_zero]
  have hv : vecMulVec x₀ u *ᵥ x₀ = x₀ := by
    ext i
    simp only [mulVec, dotProduct, vecMulVec_apply, mul_assoc, ← Finset.mul_sum]
    rw [show ∑ k, u k * x₀ k = 1 from hux, mul_one]
  have hfix : ∀ g, ((jj g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *ᵥ x₀ = x₀ := by
    intro g
    rw [hjj, add_mulVec, hv, ← mulVec_mulVec, hA'x, mulVec_zero, add_zero]
  have hcomm : ∀ g, ((jj g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * B =
      B * ((g : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) := by
    intro g
    rw [hjj, Matrix.add_mul, h0, zero_add, Matrix.mul_assoc (B * _), hA'B, Matrix.mul_one]
  have hback : ∀ M : Matrix (Fin m) (Fin m) ℂ, A' * (vecMulVec x₀ u + B * M * A') * B = M := by
    intro M
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc A' (vecMulVec x₀ u), h0, Matrix.mul_zero, zero_add,
      Matrix.mul_assoc, Matrix.mul_assoc, hA'B, Matrix.mul_one, ← Matrix.mul_assoc, hA'B, Matrix.one_mul]
  have hval' : Continuous fun g : Formalism.REAL.UJ ε' => ((g : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) :=
    Units.continuous_val.comp continuous_subtype_val
  have hinv' : Continuous fun g : Formalism.REAL.UJ ε' => (((g : GL (Fin m) ℂ)⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  have hjinv : ∀ g, ((((jj g : GL (Fin n) ℂ))⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      vecMulVec x₀ u + B * (((g : GL (Fin m) ℂ)⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) * A' := by
    intro g
    have h1 := hjj g⁻¹
    rw [map_inv] at h1
    exact h1
  have hcont : Continuous jj := by
    refine continuous_induced_rng.2 ?_
    rw [Units.continuous_iff]
    constructor
    · exact Continuous.congr (continuous_const.add ((continuous_const.matrix_mul hval').matrix_mul continuous_const))
        fun g => (hjj g).symm
    · exact Continuous.congr (continuous_const.add ((continuous_const.matrix_mul hinv').matrix_mul continuous_const))
        fun g => (hjinv g).symm
  let ψ : Formalism.REAL.UJ ε → Matrix (Fin m) (Fin m) ℂ × (Matrix (Fin m) (Fin m) ℂ)ᵐᵒᵖ := fun h =>
    (A' * ((h : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * B,
      MulOpposite.op (A' * (((h : GL (Fin n) ℂ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * B))
  have hψc : Continuous ψ := by
    refine Continuous.prodMk ?_ ?_
    · exact (continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)).matrix_mul
        continuous_const
    · exact MulOpposite.continuous_op.comp ((continuous_const.matrix_mul
        (Units.continuous_coe_inv.comp continuous_subtype_val)).matrix_mul continuous_const)
  have hψ : ∀ g, ψ (jj g) = Units.embedProduct _ (g : GL (Fin m) ℂ) := by
    intro g
    refine Prod.ext ?_ ?_
    · show A' * ((jj g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * B = ((g : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ)
      rw [hjj, hback]
    · show MulOpposite.op (A' * ((((jj g : GL (Fin n) ℂ))⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * B) =
        MulOpposite.op ((((g : GL (Fin m) ℂ))⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ)
      rw [hjinv, hback]
  have hind : Topology.IsInducing jj := by
    refine Topology.IsInducing.of_comp hcont hψc ?_
    have he : ψ ∘ jj = fun g : Formalism.REAL.UJ ε' => Units.embedProduct _ (g : GL (Fin m) ℂ) := funext hψ
    rw [he]
    exact Units.isInducing_embedProduct.comp Topology.IsInducing.subtypeVal
  have hinj : Function.Injective jj := by
    intro a b hab
    have hc := congrArg ψ hab
    rw [hψ, hψ] at hc
    exact Subtype.ext (Units.ext (congrArg Prod.fst hc))
  have hrng : Set.range jj = {h : Formalism.REAL.UJ ε | ((h : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *ᵥ x₀ = x₀} := by
    ext h
    constructor
    · rintro ⟨g, rfl⟩
      exact hfix g
    · intro hh
      exact hrange h hh
  have hclosed : IsClosed (Set.range jj) := by
    rw [hrng]
    exact isClosed_eq ((Units.continuous_val.comp continuous_subtype_val).matrix_mulVec continuous_const)
      continuous_const
  exact ⟨jj, ⟨⟨hind, hinj⟩, hclosed⟩, fun g => ⟨hfix g, hcomm g⟩⟩

end GlobalTheory.StabUnfold
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsClosedEmbeddingOrthogonalUnitaryRealPlaceStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedEmbedding_orthogonalUnitary_realPlace : ∀ (n m : ℕ) (ε : Fin n → Bool) (ε' : Fin m → Bool) (s : Bool) (x₀ : Fin n → ℂ) (B : Matrix (Fin n) (Fin m) ℂ), m + 1 = n → qEps ε x₀ = sgn ℝ s → star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0 → Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε' → ∃ j : Formalism.REAL.UJ ε' →* Formalism.REAL.UJ ε, Topology.IsClosedEmbedding j ∧ ∀ g, uMat (j g) *ᵥ x₀ = x₀ ∧ uMat (j g) * B = B * uMat g := by
  first | exact @GlobalTheory.StabUnfold.exists_closedEmbedding_unitary_orthogonal | exact GlobalTheory.StabUnfold.exists_closedEmbedding_unitary_orthogonal | (intros; apply GlobalTheory.StabUnfold.exists_closedEmbedding_unitary_orthogonal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPairMoveByIntegralUnipotent
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPairMoveByIntegralUnipotent
noncomputable section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

namespace GlobalTheory.LoopC.PairMove

open GlobalTheory.LoopC.FrEqv

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
  {Λ : Submodule (𝓞 E) S.V}

theorem aut_mul {n m : S.V ≃ₗ[E] S.V} (hm : IsAutLam S Λ m) (hn : IsAutLam S Λ n) : IsAutLam S Λ (m * n) := by
  refine ⟨Subgroup.mul_mem _ hm.1 hn.1, ?_⟩
  have key : ∀ y, (m * n) y ∈ Λ ↔ y ∈ Λ := fun y => by
    show m (n y) ∈ Λ ↔ y ∈ Λ
    rw [aut_mem_iff hm, aut_mem_iff hn]
  ext x
  rw [mem_gmap, ← key ((m * n).symm x), LinearEquiv.apply_symm_apply]

theorem aut_symm {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) : IsAutLam S Λ n.symm := by
  refine ⟨Subgroup.inv_mem _ hn.1, ?_⟩
  ext x
  rw [mem_gmap, LinearEquiv.symm_symm, aut_mem_iff hn]

theorem mem_iff_of_map {n : S.V ≃ₗ[E] S.V} {U W : Submodule E S.V}
    (h : U.map (n : S.V →ₗ[E] S.V) = W) (x : S.V) : n x ∈ W ↔ x ∈ U := by
  rw [← h, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

theorem map_of_mem_iff {n : S.V ≃ₗ[E] S.V} {U W : Submodule E S.V}
    (h : ∀ x, n x ∈ W ↔ x ∈ U) : U.map (n : S.V →ₗ[E] S.V) = W := by
  ext y
  rw [Submodule.mem_map_equiv, ← h (n.symm y), LinearEquiv.apply_symm_apply]

theorem map_symm {n : S.V ≃ₗ[E] S.V} {U W : Submodule E S.V}
    (h : U.map (n : S.V →ₗ[E] S.V) = W) : W.map (n.symm : S.V →ₗ[E] S.V) = U := by
  ext y
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm]
  exact mem_iff_of_map h y

theorem orth_mem {n : S.V ≃ₗ[E] S.V} (hn : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) {U W : Submodule E S.V}
    (h : U.map (n : S.V →ₗ[E] S.V) = W) {x : S.V} (hx : x ∈ orth S U) : n x ∈ orth S W := by
  have hn' : ∀ a b, S.hT (n a) (n b) = S.hT a b := hn
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  intro w hw
  rw [← h] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  show S.hT (n u) (n x) = 0
  rw [hn']
  exact hx u hu

theorem lrep_mem {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) {F : LFlag S r T} {G : LFlag S r T'}
    (h : (Xsp F).map (n : S.V →ₗ[E] S.V) = Xsp G) {x : S.V} (hx : x ∈ Lrep Λ F) : n x ∈ Lrep Λ G := by
  simp only [Lrep, Submodule.mem_inf, Submodule.restrictScalars_mem] at hx ⊢
  exact ⟨(aut_mem_iff hn x).2 hx.1, orth_mem hn.1 h hx.2⟩

theorem xlam_mem {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) {F : LFlag S r T} {G : LFlag S r T'}
    (h : (Xsp F).map (n : S.V →ₗ[E] S.V) = Xsp G) {x : S.V} (hx : x ∈ XLam Λ F) : n x ∈ XLam Λ G := by
  simp only [XLam, Submodule.mem_inf, Submodule.restrictScalars_mem] at hx ⊢
  exact ⟨(aut_mem_iff hn x).2 hx.1, (mem_iff_of_map h x).2 hx.2⟩

theorem ngx_mem {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) {F G : LFlag S r T} {F' G' : LFlag S r T'}
    (h : (Xsp F).map (n : S.V →ₗ[E] S.V) = Xsp G) (h' : (Xsp F').map (n : S.V →ₗ[E] S.V) = Xsp G') (g : ℕ)
    {x : S.V} (hx : x ∈ NgX Λ g F F') : n x ∈ NgX Λ g G G' := by
  have hΛ : Λ.map ((n : S.V →ₗ[E] S.V).restrictScalars (𝓞 E)) = Λ := hn.2
  have hle : (NgX Λ g F F').map ((n : S.V →ₗ[E] S.V).restrictScalars (𝓞 E)) ≤ NgX Λ g G G' := by
    rw [NgX, NgX, Submodule.map_sup, Submodule.map_sup, Submodule.map_smul'', hΛ]
    refine sup_le_sup (sup_le_sup le_rfl ?_) ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact xlam_mem hn h hy
    · rintro _ ⟨y, hy, rfl⟩
      exact xlam_mem hn h' hy
  exact hle (Submodule.mem_map_of_mem hx)

theorem ngx_iff {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) {F G : LFlag S r T} {F' G' : LFlag S r T'}
    (h : (Xsp F).map (n : S.V →ₗ[E] S.V) = Xsp G) (h' : (Xsp F').map (n : S.V →ₗ[E] S.V) = Xsp G') (g : ℕ)
    (x : S.V) : n x ∈ NgX Λ g G G' ↔ x ∈ NgX Λ g F F' := by
  constructor
  · intro hx
    have := ngx_mem (aut_symm hn) (map_symm h) (map_symm h') g hx
    rwa [LinearEquiv.symm_apply_apply] at this
  · exact ngx_mem hn h h' g

theorem nlam_map {n : S.V ≃ₗ[E] S.V} {F : LFlag S r T} (hn : n ∈ NLam Λ F) :
    (Xsp F).map (n : S.V →ₗ[E] S.V) = Xsp F := by
  have key : ∀ m ∈ NLam Λ F, ∀ x ∈ Xsp F, m x ∈ Xsp F := by
    intro m hm x hx
    rw [← sub_add_cancel (m x) x]
    exact add_mem (hm.2.2 x (X_le_orth hx)) hx
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact key n hn x hx
  · intro x hx
    exact ⟨n.symm x, key _ (symm_mem_NLam hn) x hx, by simp⟩

theorem xflag_top (F : LFlag S r T) : Xflag F r = Xsp F := by
  show Submodule.span E (F.fl.e '' {i | i.1 < r}) = Submodule.span E (Set.range F.fl.e)
  rw [show {i : Fin r | i.1 < r} = Set.univ from Set.eq_univ_of_forall fun i => i.2, Set.image_univ]

theorem finrank_X (F : LFlag S r T) : finrank E (Xsp F) = r := by
  show finrank E (Submodule.span E (Set.range F.fl.e)) = r
  rw [finrank_span_eq_card F.fl.e_indep, Fintype.card_fin]

theorem frame_move {n : S.V ≃ₗ[E] S.V} {F A : LFlag S r T} {ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)}
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1)
    (h3 : frame A = frameAct (fun a => n (frame F a)) ξ) :
    (Xsp F).map (n : S.V →ₗ[E] S.V) = Xsp A ∧ n F.fl.z - A.fl.z ∈ Xsp A := by
  have hFe : ∀ i : Fin r, frame F i.castSucc = F.fl.e i := fun i => by
    show Fin.snoc (α := fun _ => S.V) F.fl.e F.fl.z i.castSucc = F.fl.e i
    simp
  have hAe : ∀ i : Fin r, frame A i.castSucc = A.fl.e i := fun i => by
    show Fin.snoc (α := fun _ => S.V) A.fl.e A.fl.z i.castSucc = A.fl.e i
    simp
  have hFz : frame F (Fin.last r) = F.fl.z := by
    show Fin.snoc (α := fun _ => S.V) F.fl.e F.fl.z (Fin.last r) = F.fl.z
    simp
  have hAz : frame A (Fin.last r) = A.fl.z := by
    show Fin.snoc (α := fun _ => S.V) A.fl.e A.fl.z (Fin.last r) = A.fl.z
    simp
  have hmem : ∀ i : Fin r, n (frame F i.castSucc) ∈ (Xsp F).map (n : S.V →ₗ[E] S.V) := fun i =>
    Submodule.mem_map_of_mem (by rw [hFe]; exact Submodule.subset_span ⟨i, rfl⟩)
  have hX : Xsp A ≤ (Xsp F).map (n : S.V →ₗ[E] S.V) := by
    show Submodule.span E (Set.range A.fl.e) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [← hAe j, h3]
    simp only [frameAct, SetLike.mem_coe]
    refine Submodule.sum_mem _ fun a _ => ?_
    by_cases ha : j.castSucc < a
    · rw [h1 a j.castSucc ha]
      simp
    · have hne : a ≠ Fin.last r := by
        rintro rfl
        exact ha (Fin.castSucc_lt_last j)
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 hne
      exact Submodule.smul_mem _ _ (hmem i)
  have hF : (Xsp F).map (n : S.V →ₗ[E] S.V) = Xsp A := by
    have : FiniteDimensional E (Xsp F) := FiniteDimensional.span_of_finite E (Set.finite_range _)
    symm
    apply Submodule.eq_of_le_of_finrank_eq hX
    rw [LinearEquiv.finrank_map_eq, finrank_X, finrank_X]
  refine ⟨hF, ?_⟩
  rw [← hAz, h3]
  simp only [frameAct]
  rw [Fin.sum_univ_castSucc, h2 (Fin.last r), hFz]
  have hs : ∑ i : Fin r, ((ξ i.castSucc (Fin.last r) : 𝓞 E) : E) • n (frame F i.castSucc) ∈ Xsp A := by
    rw [← hF]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem i)
  have e : ((1 : 𝓞 E) : E) • n F.fl.z = n F.fl.z := by simp
  rw [e, sub_add_eq_sub_sub_swap, sub_self, zero_sub]
  exact neg_mem hs

theorem move {g : ℕ} {F : LFlag S r T} {F' F'' A B : LFlag S r T'} {β n' n'' : S.V ≃ₗ[E] S.V}
    (hp : IsPair Λ F F' F'' β g) (hn' : n' ∈ NLam Λ F) (hn'' : n'' ∈ NLam Λ F)
    (hA : (Xsp F').map (n' : S.V →ₗ[E] S.V) = Xsp A) (zA : n' F'.fl.z - A.fl.z ∈ Xsp A)
    (hB : (Xsp F'').map (n'' : S.V →ₗ[E] S.V) = Xsp B) (zB : n'' F''.fl.z - B.fl.z ∈ Xsp B) :
    IsAutLam S Λ (n'' * β * n'⁻¹) ∧
      (Xsp A).map ((n'' * β * n'⁻¹ : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V) = Xsp B ∧
      (n'' * β * n'⁻¹) A.fl.z - B.fl.z ∈ Xsp B ∧ IotaCompat Λ F A B (n'' * β * n'⁻¹) g := by
  have hn'A : IsAutLam S Λ n' := hn'.1
  have hn''A : IsAutLam S Λ n'' := hn''.1
  obtain ⟨hβ, hβF, hβz, hι⟩ := hp
  have hγ : ∀ x, (n'' * β * n'⁻¹) x = n'' (β (n'.symm x)) := fun x => rfl
  have hβX : (Xsp F').map (β : S.V →ₗ[E] S.V) = Xsp F'' := by
    have := hβF r
    rwa [xflag_top, xflag_top] at this
  have hAB : (Xsp A).map ((n'' * β * n'⁻¹ : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V) = Xsp B := by
    apply map_of_mem_iff
    intro x
    rw [hγ, mem_iff_of_map hB, mem_iff_of_map hβX, mem_iff_of_map (map_symm hA)]
  have hFn' : (Xsp F).map (n' : S.V →ₗ[E] S.V) = Xsp F := nlam_map hn'
  have hFn'' : (Xsp F).map (n'' : S.V →ₗ[E] S.V) = Xsp F := nlam_map hn''
  refine ⟨aut_mul (aut_mul hn''A hβ) (aut_symm hn'A), hAB, ?_, ?_⟩
  · have e : (n'' * β * n'⁻¹) A.fl.z - B.fl.z =
        (n'' F''.fl.z - B.fl.z) - (n'' * β * n'⁻¹) (n' F'.fl.z - A.fl.z) := by
      simp only [hγ, map_sub, LinearEquiv.symm_apply_apply, hβz]
      abel
    rw [e]
    exact sub_mem zB (by rw [← hAB]; exact Submodule.mem_map_of_mem zA)
  · intro x' hx' l hl
    have hy : n'.symm x' ∈ Lrep Λ F' := lrep_mem (aut_symm hn'A) (map_symm hA) hx'
    have hm : n'.symm l ∈ Lrep Λ F := lrep_mem (aut_symm hn'A) (map_symm hFn') hl
    simp only [Lrep, Submodule.mem_inf, Submodule.restrictScalars_mem] at hl
    have h1 : l - x' ∈ NgX Λ g F A ↔ n'.symm l - n'.symm x' ∈ NgX Λ g F F' := by
      rw [← ngx_iff hn'A hFn' hA g, map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    have h3 : n'.symm l - β (n'.symm x') ∈ NgX Λ g F F'' ↔
        n'' (n'.symm l) - (n'' * β * n'⁻¹) x' ∈ NgX Λ g F B := by
      rw [hγ x', ← ngx_iff hn''A hFn'' hB g, map_sub]
    have hd : l - n'' (n'.symm l) ∈ NgX Λ g F B := by
      obtain ⟨hνA, -, hνo⟩ := mul_mem_NLam (symm_mem_NLam hn') hn''
      have e1 : n'' (n'.symm l) - l ∈ XLam Λ F := by
        simp only [XLam, Submodule.mem_inf, Submodule.restrictScalars_mem]
        exact ⟨sub_mem ((aut_mem_iff hνA l).2 hl.1) hl.1, hνo l hl.2⟩
      have e2 : n'' (n'.symm l) - l ∈ NgX Λ g F B := by
        rw [NgX]
        exact Submodule.mem_sup_left (Submodule.mem_sup_right e1)
      rw [← neg_sub]
      exact neg_mem e2
    have h4 : n'' (n'.symm l) - (n'' * β * n'⁻¹) x' ∈ NgX Λ g F B ↔
        l - (n'' * β * n'⁻¹) x' ∈ NgX Λ g F B := by
      rw [show l - (n'' * β * n'⁻¹) x' = (n'' (n'.symm l) - (n'' * β * n'⁻¹) x') + (l - n'' (n'.symm l)) by abel]
      exact (add_mem_cancel_right hd).symm
    exact h1.trans ((hι _ hy _ hm).trans (h3.trans h4))

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pair_move : ∀ (D : D7) (T T' : D.host.E) (Λ : LatV D) (g : ℕ) (F : Fg D T) (F' F'' A B : Fg D T') (β n' n'' : (hS D).V ≃ₗ[D.host.E] (hS D).V), IsPair Λ F F' F'' β g → n' ∈ NLam Λ F → n'' ∈ NLam Λ F → FrameEqv D n' F' A → FrameEqv D n'' F'' B → IsAutLam (hS D) Λ (n'' * β * n'⁻¹) ∧ (Xsp A).map ((n'' * β * n'⁻¹ : (hS D).V ≃ₗ[D.host.E] (hS D).V) : (hS D).V →ₗ[D.host.E] (hS D).V) = Xsp B ∧ (n'' * β * n'⁻¹) A.fl.z - B.fl.z ∈ Xsp B ∧ IotaCompat Λ F A B (n'' * β * n'⁻¹) g := by
  intro D T T' Λ g F F' F'' A B β n' n'' hp hn' hn'' hA hB
  obtain ⟨ξ, h1, h2, h3⟩ := hA
  obtain ⟨η, k1, k2, k3⟩ := hB
  obtain ⟨a1, a2⟩ := frame_move h1 h2 h3
  obtain ⟨b1, b2⟩ := frame_move k1 k2 k3
  exact move hp hn' hn'' a1 a2 b1 b2

end GlobalTheory.LoopC.PairMove

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPairMoveByIntegralUnipotentStatement
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPair_move_by_integralUnipotent : ∀ (D : D7) (T T' : D.host.E) (Λ : LatV D) (g : ℕ) (F : Fg D T) (F' F'' A B : Fg D T') (β n' n'' : (hS D).V ≃ₗ[D.host.E] (hS D).V), IsPair Λ F F' F'' β g → n' ∈ NLam Λ F → n'' ∈ NLam Λ F → FrameEqv D n' F' A → FrameEqv D n'' F'' B → IsAutLam (hS D) Λ (n'' * β * n'⁻¹) ∧ (Xsp A).map ((n'' * β * n'⁻¹ : (hS D).V ≃ₗ[D.host.E] (hS D).V) : (hS D).V →ₗ[D.host.E] (hS D).V) = Xsp B ∧ (n'' * β * n'⁻¹) A.fl.z - B.fl.z ∈ Xsp B ∧ IotaCompat Λ F A B (n'' * β * n'⁻¹) g := by
  first | exact @GlobalTheory.LoopC.PairMove.pair_move | exact GlobalTheory.LoopC.PairMove.pair_move | (intros; apply GlobalTheory.LoopC.PairMove.pair_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelMatrixSkewCoordinatesRationalAut
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelMatrixSkewCoordinatesRationalAut
noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.RefCovSkew

theorem herm_esI {k r : ℕ} (u : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) u (bvec (esI k r a)) = u (eI k r a) := by
  have ha := a.2
  have ht : WeylGroupFacts.tau k r (esI k r a) = eI k r a := by
    have h1 : (esI k r a).val < r ∨ r + k < (esI k r a).val := Or.inr (by simp only [esI]; omega)
    apply Fin.ext; unfold WeylGroupFacts.tau; dsimp only; rw [if_pos h1]; simp only [esI, eI]; omega
  have hs : WeylGroupFacts.sgn k r (esI k r a) = 1 := if_neg (by simp only [esI]; omega)
  unfold herm bvec
  rw [← Pi.single_star, star_one, single_one_dotProduct]
  simp only [mulVec, dotProduct, WeylGroupFacts.hpk_row, ht, hs]
  simp

theorem sum_eI_apply {k r : ℕ} (c : Fin r → ℂ) (a : Fin r) :
    (∑ b, c b • bvec (eI k r b)) (eI k r a) = c a := by
  simp [Finset.sum_apply, Rad.bvec_apply, Rad.eI_inj]

theorem coords_skew : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (r : ℕ) (N : NF H r) (k : ℕ) (σ : K →+* ℂ) (ρ : ℝ) (β : Fin r → ℕ) (Φ : V → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r), 0 < ρ → IsFrameOf N k σ ρ β Φ z z' g → ∀ (s : V ≃ₗ[K] V) (q : (UTin β → ℂ) × PTop k r N.j), (∀ x, crd k r N.j β q *ᵥ Φ x = Φ (s x)) → q.1 = 0 → q.2.1 = 0 → (∀ b : Fin r, N.j ≤ b.val → s (N.ist b) - N.ist b ∈ II N.F N.F') ∧ (∀ p : {p : UT r // N.j ≤ p.1.1.val}, q.2.2.1 p = ((ρ ^ ((r - p.1.1.1.val) + (r - p.1.1.2.val)) : ℝ) : ℂ) * σ (H.B (s (N.ist p.1.1.2)) (N.ist p.1.1.1))) ∧ ∀ a : {a : Fin r // N.j ≤ a.val}, q.2.2.2 a = ρ ^ (2 * (r - a.1.val)) * (σ (H.B (s (N.ist a.1)) (N.ist a.1))).im := by
  intro K V _ _ _ _ _ _ _ _ H r N k σ ρ β Φ z z' g hρ hF s q hq hq1 hq2
  obtain ⟨hr, -, -, -, -, he, hi, -⟩ := hF
  have he1 : ∀ a : Fin r, Φ (N.F.e a.castSucc) = ((ρ ^ (r - a.val) : ℝ) : ℂ) • bvec (eI k r a) := fun a => (he a).1
  have ht : ∀ n : ℕ, ((ρ ^ n : ℝ) : ℂ) ≠ 0 := fun n => by
    exact_mod_cast (pow_pos hρ n).ne'
  set S : Matrix (Fin r) (Fin r) ℂ := skewM (Swap.extS r N.j q.2.2).1 (Swap.extS r N.j q.2.2).2 with hSdef
  have hM : crd k r N.j β q = pEl k r 0 S := by
    rw [RefCovTop.crd_of_zero β q hq1, Swap.pTop_eq, pOf, hq2, map_zero]
  have hS0 : ∀ a b : Fin r, ¬ N.j ≤ a.val → S a b = 0 := fun a b ha => Swap.skew_ext_zero q.2.2 a b ha
  have hcol : ∀ b : Fin r, pEl k r 0 S *ᵥ bvec (esI k r b) = bvec (esI k r b) + ∑ a, S a b • bvec (eI k r a) := by
    intro b
    rw [((Rad.radical k r).1 0 S).2.2.1 b]
    simp [herm]
  have hsb : ∀ b : Fin r, N.j ≤ b.val → Φ (s (N.ist b)) =
      (((ρ ^ (r - b.val))⁻¹ : ℝ) : ℂ) • (bvec (esI k r b) + ∑ a, S a b • bvec (eI k r a)) := by
    intro b hb; rw [← hq, hM, hi b hb, mulVec_smul, hcol]
  have hB : ∀ a b : Fin r, N.j ≤ a.val → N.j ≤ b.val → σ (H.B (s (N.ist b)) (N.ist a)) =
      (((ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) * ((((ρ ^ (r - b.val))⁻¹ : ℝ) : ℂ) * S a b) := by
    intro a b ha hb
    rw [← hr.2.2.1, hsb b hb, hi a ha, RealMat.herm_smul_right, herm_esI, Pi.smul_apply, Pi.add_apply, sum_eI_apply,
      Rad.bvec_apply, if_neg (Rad.eI_ne_esI a b), zero_add, smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
  refine ⟨fun b hb => ?_, fun p => ?_, fun a => ?_⟩
  · have hΦy : Φ (s (N.ist b) - N.ist b) = ∑ a, ((((ρ ^ (r - b.val))⁻¹ : ℝ) : ℂ) * S a b) • bvec (eI k r a) := by
      rw [RealMat.phi_sub hr, hsb b hb, hi b hb, smul_add, add_sub_cancel_left, Finset.smul_sum]
      simp_rw [smul_smul]
    have hproj : NFGeom.proj N (s (N.ist b) - N.ist b) = s (N.ist b) - N.ist b := by
      apply RealMat.phi_inj hr
      rw [NFGeom.proj_apply, RealMat.phi_sum hr, hΦy, Finset.sum_filter]
      refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs with ha
      · rw [hr.2.1, he1, ← hr.2.2.1, hΦy, hi a ha, RealMat.herm_smul_right, herm_esI, sum_eI_apply, smul_smul]
        congr 1
        rw [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_inv, mul_comm, ← mul_assoc,
          mul_inv_cancel₀ (ht _), one_mul]
      · rw [hS0 a b ha, mul_zero, zero_smul]
    rw [← hproj]; exact NFGeom.proj_mem N _
  · obtain ⟨⟨⟨a, b⟩, hab⟩, ha⟩ := p
    have hab' : a < b := hab
    have ha' : N.j ≤ a.val := ha
    have hb : N.j ≤ b.val := le_trans ha' (le_of_lt hab')
    simp only
    rw [hB a b ha' hb]
    have hSab : S a b = q.2.2.1 ⟨⟨(a, b), hab⟩, ha⟩ := by
      simp [hSdef, skewM, hab', Swap.extS, Swap.extZ, ha']
    rw [hSab, pow_add, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_inv]
    have h1 := ht (r - a.val)
    have h2 := ht (r - b.val)
    field_simp
  · obtain ⟨a, ha⟩ := a
    simp only
    rw [hB a a ha ha]
    have hSaa : S a a = ((q.2.2.2 ⟨a, ha⟩ : ℝ) : ℂ) * Complex.I := by
      simp [hSdef, skewM, Swap.extS, Swap.extZ, ha]
    rw [hSaa]
    have e : ((((ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) * ((((ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) * (((q.2.2.2 ⟨a, ha⟩ : ℝ) : ℂ) * Complex.I))) =
        (((ρ ^ (r - a.val))⁻¹ * ((ρ ^ (r - a.val))⁻¹ * q.2.2.2 ⟨a, ha⟩) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [e, Complex.mul_I_im, Complex.ofReal_re, two_mul, pow_add]
    have h1 : ρ ^ (r - a.val) ≠ 0 := (pow_pos hρ _).ne'
    field_simp

end GlobalTheory.DegVol.RefCovSkew
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelMatrixSkewCoordinatesRationalAutStatement
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselModelMatrix_skew_coordinates_rational_aut : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (r : ℕ) (N : NF H r) (k : ℕ) (σ : K →+* ℂ) (ρ : ℝ) (β : Fin r → ℕ) (Φ : V → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r), 0 < ρ → IsFrameOf N k σ ρ β Φ z z' g → ∀ (s : V ≃ₗ[K] V) (q : (UTin β → ℂ) × PTop k r N.j), (∀ x, crd k r N.j β q *ᵥ Φ x = Φ (s x)) → q.1 = 0 → q.2.1 = 0 → (∀ b : Fin r, N.j ≤ b.val → s (N.ist b) - N.ist b ∈ II N.F N.F') ∧ (∀ p : {p : UT r // N.j ≤ p.1.1.val}, q.2.2.1 p = ((ρ ^ ((r - p.1.1.1.val) + (r - p.1.1.2.val)) : ℝ) : ℂ) * σ (H.B (s (N.ist p.1.1.2)) (N.ist p.1.1.1))) ∧ ∀ a : {a : Fin r // N.j ≤ a.val}, q.2.2.2 a = ρ ^ (2 * (r - a.1.val)) * (σ (H.B (s (N.ist a.1)) (N.ist a.1))).im := by
  first | exact @GlobalTheory.DegVol.RefCovSkew.coords_skew | exact GlobalTheory.DegVol.RefCovSkew.coords_skew | (intros; apply GlobalTheory.DegVol.RefCovSkew.coords_skew <;> assumption)
end
end
