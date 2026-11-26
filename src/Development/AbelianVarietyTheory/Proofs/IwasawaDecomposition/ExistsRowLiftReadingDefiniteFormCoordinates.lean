module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelChainOverTopSpaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLiftSpacesOverDefiniteForms

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteRepresentativesRowFiniteTypes
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteRepresentativesRowFiniteTypes
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

noncomputable section

namespace GlobalTheory.RowTypeReps


set_option maxHeartbeats 2000000 in
theorem reps_exist : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat), ∃ (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F.lv2 rep := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hI hP _ y
  have hB := hP.char.base
  have h0 := hB.models.ν0
  have hD : ∀ b, principalLevelFrame.IsotDecomp R.θ y.PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)))
      (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) R.e0 R.ν0 R.fd0 := by
    intro b
    obtain ⟨h1, h2⟩ := GlobalTheory.FinTypesRows.isotL_span_orth D (Yc D 0) _ R.θ (R.MY 0) y.PY y.hF (R.βY 0)
      (R.dat0 (R.toRealDat.levR F.lv2 b)) R.e0 _ _ hI (D.sp.Y_sig _) hB.models.inf y.stdPsi.1 h0.1.1 h0.2
      (GlobalTheory.Mem.R3.IsotIndep.gaL_finSum _ _ _ _ _)
    exact ⟨h1.symm, h2⟩

  have hp : ∀ b, PeterssonHilbertSpace.IsHermPos (Mult.goodPart R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)))
      (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) R.e0) (Mult.ipM (R.MY 0) R.ν0 R.fd0) := by
    intro b
    have h1 := hermPos_mono (GlobalTheory.HilbertLevels.herm_lev hI hB.models.inf (D.sp.Y_sig _) (R.MY 0) (R.βY 0)
      (R.dat0 (R.toRealDat.levR F.lv2 b)) h0.1.1 h0.2) (Submodule.map_mono (Mult.goodPart_le R.θ (R.MY 0) _ _ R.e0))
    have h2 := h1.map_equiv (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).symm
    convert h2 using 1
    · ext x
      rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
    · funext x x'
      simp only [ipMT, LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply]
  haveI := principalLevelFrame.finite_FTR R.θ y.PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)))
    (fun b => levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) (fun _ => R.e0) (fun _ => R.ν0) (fun _ => R.fd0) hD hp
  refine ⟨principalLevelFrame.FTR R.θ y.PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)))
    (fun b => levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) (fun _ => R.e0), principalLevelFrame.rowRepR R.θ,
    ⟨inferInstance, fun π => principalLevelFrame.rowRepR_occ R.θ π, fun π π' h => principalLevelFrame.rowRepR_inj R.θ π π' h, ?_⟩⟩
  intro ρ hρ
  exact ⟨Quotient.mk _ ⟨ρ, hρ⟩, Formalism.L2.Col.finTypRep_mk_iso ⟨ρ, hρ⟩⟩

end GlobalTheory.RowTypeReps
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteRepresentativesRowFiniteTypesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_representatives_rowFiniteTypes : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat), ∃ (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F.lv2 rep := by
  first | exact @GlobalTheory.RowTypeReps.reps_exist | exact GlobalTheory.RowTypeReps.reps_exist | (intros; apply GlobalTheory.RowTypeReps.reps_exist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexificationOfDefiniteGroupForms
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFormsTieOLatTie
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Indef
open scoped ComplexOrder

open scoped Matrix MatrixOrder

namespace GlobalTheory.Mem.CoordForms

theorem exists_sqrt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) :
    ∃ S T : Matrix (Fin n) (Fin n) ℂ, Sᴴ * S = A ∧ S * T = 1 ∧ T * S = 1 := by
  obtain ⟨S, hS⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.posSemidef.nonneg
  rw [Matrix.star_eq_conjTranspose] at hS
  have hdet : IsUnit S.det := by
    have h := hA.det_pos.ne'
    rw [hS, Matrix.det_mul] at h
    exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul h)
  exact ⟨S, S⁻¹, hS.symm, Matrix.mul_nonsing_inv S hdet, Matrix.nonsing_inv_mul S hdet⟩

variable {K : Type} [Field K] {n : ℕ}

noncomputable def emb (σ : K →+* ℂ) (S : Matrix (Fin n) (Fin n) ℂ) : (Fin n → K) →ₛₗ[σ] EuclideanSpace ℂ (Fin n) where
  toFun x := Matrix.toEuclideanLin S (WithLp.toLp 2 fun i => σ (x i))
  map_add' x y := by
    rw [← map_add (f := _)]
    congr 1
    ext i
    simp
  map_smul' a x := by
    rw [← map_smul]
    congr 1
    ext i
    simp

theorem emb_ofLp (σ : K →+* ℂ) (S : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → K) :
    (emb σ S x).ofLp = S *ᵥ fun i => σ (x i) := rfl

noncomputable def act (σ : K →+* ℂ) (S T : Matrix (Fin n) (Fin n) ℂ) (h1 : S * T = 1) (h2 : T * S = 1) :
    Matrix (Fin n) (Fin n) K →+* Module.End ℂ (EuclideanSpace ℂ (Fin n)) where
  toFun E := Matrix.toEuclideanLin (S * E.map σ * T)
  map_one' := by
    ext1 v
    apply WithLp.ofLp_injective
    change (S * (1 : Matrix (Fin n) (Fin n) K).map σ * T) *ᵥ v.ofLp = v.ofLp
    rw [Matrix.map_one _ (map_zero σ) (map_one σ), mul_one, h1, Matrix.one_mulVec]
  map_mul' E F := by
    ext1 v
    apply WithLp.ofLp_injective
    change (S * (E * F).map σ * T) *ᵥ v.ofLp = (S * E.map σ * T) *ᵥ ((S * F.map σ * T) *ᵥ v.ofLp)
    rw [Matrix.mulVec_mulVec, Matrix.map_mul]
    congr 1
    calc S * (E.map σ * F.map σ) * T = S * E.map σ * (T * S) * F.map σ * T := by rw [h2]; simp only [mul_one, mul_assoc]
      _ = _ := by simp only [mul_assoc]
  map_zero' := by simp
  map_add' E F := by
    rw [← map_add (f := _), Matrix.map_add _ (map_add σ), mul_add, add_mul]

theorem emb_single (σ : K →+* ℂ) (S : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    emb σ S (Pi.single i 1) = Matrix.toEuclideanLin S (EuclideanSpace.basisFun (Fin n) ℂ i) := by
  apply WithLp.ofLp_injective
  change S *ᵥ (fun k => σ ((Pi.single i (1 : K) : Fin n → K) k)) = S *ᵥ (EuclideanSpace.basisFun (Fin n) ℂ i).ofLp
  congr 1
  ext k
  rw [EuclideanSpace.basisFun_apply]
  by_cases h : k = i
  · subst h; simp
  · simp [h]

theorem bij (S T : Matrix (Fin n) (Fin n) ℂ) (h1 : S * T = 1) (h2 : T * S = 1) :
    Function.Bijective (Matrix.toEuclideanLin S) := by
  constructor
  · intro x y hxy
    have h := congrArg (fun v => (Matrix.toEuclideanLin T v).ofLp) hxy
    change T *ᵥ (S *ᵥ x.ofLp) = T *ᵥ (S *ᵥ y.ofLp) at h
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, Matrix.one_mulVec] at h
    exact WithLp.ofLp_injective 2 h
  · intro y
    refine ⟨Matrix.toEuclideanLin T y, WithLp.ofLp_injective 2 ?_⟩
    change S *ᵥ (T *ᵥ y.ofLp) = y.ofLp
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

theorem emb_injective (σ : K →+* ℂ) (S T : Matrix (Fin n) (Fin n) ℂ) (h1 : S * T = 1) (h2 : T * S = 1) :
    Function.Injective (emb σ S) := by
  intro x y hxy
  have h : (WithLp.toLp 2 fun i => σ (x i) : EuclideanSpace ℂ (Fin n)) = WithLp.toLp 2 fun i => σ (y i) :=
    (bij S T h1 h2).1 (show Matrix.toEuclideanLin S (WithLp.toLp 2 fun i => σ (x i)) =
      Matrix.toEuclideanLin S (WithLp.toLp 2 fun i => σ (y i)) from hxy)
  funext i
  exact σ.injective (congrFun (congrArg WithLp.ofLp h) i)

theorem emb_span (σ : K →+* ℂ) (S T : Matrix (Fin n) (Fin n) ℂ) (h1 : S * T = 1) (h2 : T * S = 1) :
    Submodule.span ℂ (Set.range fun i => emb σ S (Pi.single i 1)) = ⊤ := by
  have hs : (fun i => emb σ S (Pi.single i 1)) =
      (Matrix.toEuclideanLin S) ∘ (EuclideanSpace.basisFun (Fin n) ℂ) :=
    funext (emb_single σ S)
  rw [hs, Set.range_comp, Submodule.span_image, ← OrthonormalBasis.coe_toBasis, Module.Basis.span_eq,
    Submodule.map_top, LinearMap.range_eq_top]
  exact (bij S T h1 h2).2

theorem formsTie [NumberField K] [StarRing K] (σ : K →+* ℂ) (hσ : ∀ x, σ (star x) = starRingEnd ℂ (σ x))
    (H : Matrix (Fin n) (Fin n) K) (S T : Matrix (Fin n) (Fin n) ℂ) (h0 : Sᴴ * S = H.map σ) (h1 : S * T = 1)
    (h2 : T * S = 1) (E : Matrix (Fin n) (Fin n) K) : FormsTie σ (emb σ S) H E (act σ S T h1 h2 E) := by
  refine ⟨?_, emb_span σ S T h1 h2, ?_, ?_⟩
  · rw [show (fun i => emb σ S (Pi.single i 1)) =
        (Matrix.toEuclideanLin S) ∘ (EuclideanSpace.basisFun (Fin n) ℂ) from funext (emb_single σ S)]
    exact (EuclideanSpace.basisFun (Fin n) ℂ).orthonormal.linearIndependent.map'
      _ (LinearMap.ker_eq_bot.mpr (bij S T h1 h2).1)
  · intro x y
    rw [EuclideanSpace.inner_eq_star_dotProduct, emb_ofLp, emb_ofLp, Matrix.star_mulVec, dotProduct_comm,
      ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h0]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, map_sum, map_mul, smul_eq_mul, dotProduct,
      Matrix.mulVec, Finset.mul_sum, Pi.star_apply, Matrix.map_apply, RingHom.id_apply, starRingEnd_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [hσ, starRingEnd_apply]
    ring
  · intro x
    apply WithLp.ofLp_injective
    change (S * E.map σ * T) *ᵥ (S *ᵥ fun i => σ (x i)) = S *ᵥ fun i => σ ((E *ᵥ x) i)
    rw [Matrix.mulVec_mulVec, mul_assoc (S * E.map σ), h2, mul_one, ← Matrix.mulVec_mulVec]
    congr 1
    funext i
    exact (RingHom.map_mulVec σ E x i).symm

theorem exists_lat [NumberField K] {O : Type} [CommRing O] (o : O →+* K) (σ : K →+* ℂ) {W : Type} [AddCommGroup W]
    [Module ℂ W] (j : (Fin n → K) →ₛₗ[σ] W) (hj : Function.Injective j)
    (hsp : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤)
    (N : Submodule (𝓞 K) (Fin n → K)) (hN : Submodule.IsFullLattice K N) :
    ∃ M : Rows.OLat O (σ.comp o) W, OLatTie σ M j N ∧
      ((∀ y, IsIntegral ℤ (o y)) → (M.carrier : Set W) = j '' (N : Set (Fin n → K))) := by
  classical

  obtain ⟨G, hG⟩ := hN.fg.restrictScalars (R := ℤ)
  have hGN : ∀ g ∈ G, g ∈ N := fun g hg => by
    have : g ∈ Submodule.span ℤ (G : Set (Fin n → K)) := Submodule.subset_span hg
    rw [hG] at this
    exact this

  have hsum : ∀ φ : W → ℂ, ∑ v ∈ G.image j, φ v • v = ∑ g ∈ G, φ (j g) • j g := fun φ =>
    Finset.sum_image fun a _ b _ h => hj h

  have key : ∀ y ∈ Submodule.span K (G : Set (Fin n → K)),
      j y ∈ Submodule.span ℂ ((G.image j : Finset W) : Set W) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem j (Finset.mem_coe.mp hx)))
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  have hGK : Submodule.span K (G : Set (Fin n → K)) = ⊤ := by
    rw [← Submodule.span_span_of_tower ℤ K (G : Set (Fin n → K)), hG]
    exact hN.span_eq_top
  have hspan : Submodule.span ℂ ((G.image j : Finset W) : Set W) = ⊤ := by
    apply top_unique
    rw [← hsp]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact key _ (by rw [hGK]; trivial)
  have hZ : ∀ x ∈ N, ∃ f : (Fin n → K) → ℤ, j x = ∑ g ∈ G, (f g : ℂ) • j g := by
    intro x hx
    have hx' : x ∈ Submodule.span ℤ (G : Set (Fin n → K)) := by rw [hG]; exact hx
    obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp hx'
    refine ⟨f, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hf, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_zsmul, Int.cast_smul_eq_zsmul]

  have hcomb : ∀ a : (Fin n → K) → K, ∑ g ∈ G, σ (a g) • j g = j (∑ g ∈ G, a g • g) := fun a => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun g _ => (LinearMap.map_smulₛₗ j (a g) g).symm
  refine ⟨⟨G.image j, hspan⟩, ⟨fun v hv => ?_, fun x => ⟨fun hx => ?_, fun ⟨c, hc⟩ => ?_⟩⟩, fun hint => ?_⟩
  · obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨g, rfl⟩
  · obtain ⟨f, hf⟩ := hZ x hx
    refine ⟨fun w => (f (Function.invFun j w) : 𝓞 K), ?_⟩
    change j x = ∑ v ∈ G.image j, σ ((f (Function.invFun j v) : 𝓞 K) : K) • v
    rw [hsum, hf]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Function.leftInverse_invFun hj g]
    simp
  · change j x = ∑ v ∈ G.image j, σ (c v : K) • v at hc
    rw [hsum, hcomb] at hc
    rw [hj hc]
    refine Submodule.sum_mem _ fun g hg => ?_
    have hm := N.smul_mem (c (j g)) (hGN g hg)
    rwa [← algebraMap_smul K (c (j g)) g] at hm
  · ext w
    constructor
    · rintro ⟨c, rfl⟩
      let a : (Fin n → K) → 𝓞 K := fun g => ⟨o (c (j g)), hint _⟩
      refine ⟨∑ g ∈ G, (a g : K) • g, ?_, ?_⟩
      · refine Submodule.sum_mem _ fun g hg => ?_
        have hm := N.smul_mem (a g) (hGN g hg)
        rwa [← algebraMap_smul K (a g) g] at hm
      · change j (∑ g ∈ G, (a g : K) • g) = ∑ v ∈ G.image j, σ (o (c v)) • v
        rw [hsum, ← hcomb]
        rfl
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨f, hf⟩ := hZ x hx
      refine ⟨fun w => (f (Function.invFun j w) : O), ?_⟩
      change j x = ∑ v ∈ G.image j, σ (o (f (Function.invFun j v) : O)) • v
      rw [hsum, hf]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Function.leftInverse_invFun hj g]
      simp

theorem exists_formsTie_oLatTie : ∀ (K O : Type) [Field K] [NumberField K] [StarRing K] [CommRing O] (o : O →+* K) (σ : K →+* ℂ) (n : ℕ) (H : Matrix (Fin n) (Fin n) K) (N : Submodule (𝓞 K) (Fin n → K)), (∀ x, σ (star x) = starRingEnd ℂ (σ x)) → (H.map σ).PosDef → Submodule.IsFullLattice K N → ∃ (j : (Fin n → K) →ₛₗ[σ] EuclideanSpace ℂ (Fin n)) (M : Rows.OLat O (σ.comp o) (EuclideanSpace ℂ (Fin n))) (ρ : Matrix (Fin n) (Fin n) K →+* Module.End ℂ (EuclideanSpace ℂ (Fin n))), (∀ E, FormsTie σ j H E (ρ E)) ∧ OLatTie σ M j N ∧ ((∀ y, IsIntegral ℤ (o y)) → (M.carrier : Set (EuclideanSpace ℂ (Fin n))) = j '' (N : Set (Fin n → K))) := by
  intro K O _ _ _ _ o σ n H N hσ hH hN
  obtain ⟨S, T, h0, h1, h2⟩ := exists_sqrt (H.map σ) hH
  obtain ⟨M, hM, hcar⟩ := exists_lat o σ (emb σ S) (emb_injective σ S T h1 h2) (emb_span σ S T h1 h2) N hN
  exact ⟨emb σ S, M, act σ S T h1 h2, fun E => formsTie σ hσ H S T h0 h1 h2 E, hM, hcar⟩

end GlobalTheory.Mem.CoordForms
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexificationOfDefiniteGroupForms
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw.SpOfMat

open MonoidAlgebra

variable {G : Type} [Group G] [Fintype G]

theorem eq_sum_single {R : Type} [Semiring R] (a : MonoidAlgebra R G) : a = ∑ g, single g (a.coeff g) := by
  classical
  apply MonoidAlgebra.ext
  ext g
  simp [MonoidAlgebra.coeff_sum, Finsupp.single_apply]

noncomputable def conjSum (R : Type) [Semiring R] (g : G) : MonoidAlgebra R G := ∑ h, single (h * g * h⁻¹) 1

theorem conjSum_mem_center (R : Type) [CommSemiring R] (g : G) : conjSum R g ∈ Subalgebra.center R (MonoidAlgebra R G) := by
  rw [Subalgebra.mem_center_iff]
  intro b
  induction b using MonoidAlgebra.induction_on with
  | of k =>
    simp only [conjSum, MonoidAlgebra.of_apply, Finset.mul_sum, Finset.sum_mul, single_mul_single, one_mul, mul_one]
    refine Fintype.sum_equiv (Equiv.mulLeft k) _ _ fun h => ?_
    simp only [Equiv.coe_mulLeft]
    congr 1
    group
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

theorem mapRange_conjSum {R S : Type} [Semiring R] [Semiring S] (f : R →+* S) (g : G) :
    mapRingHom G f (conjSum R g) = conjSum S g := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [conjSum, map_sum, MonoidAlgebra.mapRingHom_single]

theorem card_smul_eq {R : Type} [CommSemiring R] (z : MonoidAlgebra R G) (hz : z ∈ Subalgebra.center R (MonoidAlgebra R G)) :
    (Fintype.card G : R) • z = ∑ g, z.coeff g • conjSum R g := by
  rw [Subalgebra.mem_center_iff] at hz
  have h1 : ∀ h : G, single h (1 : R) * z * single h⁻¹ 1 = z := fun h => by
    rw [hz, mul_assoc, single_mul_single, mul_inv_cancel, one_mul, ← one_def, mul_one]
  have h2 : ∀ h : G, single h (1 : R) * z * single h⁻¹ 1 = ∑ g, single (h * g * h⁻¹) (z.coeff g) := fun h => by
    conv_lhs => rw [eq_sum_single z]
    simp only [Finset.mul_sum, Finset.sum_mul, single_mul_single, one_mul, mul_one]
  calc (Fintype.card G : R) • z = ∑ h : G, z := by rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    _ = ∑ h : G, ∑ g, single (h * g * h⁻¹) (z.coeff g) := Finset.sum_congr rfl fun h _ => (h1 h).symm.trans (h2 h)
    _ = ∑ g, z.coeff g • conjSum R g := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp only [conjSum, Finset.smul_sum, smul_single, smul_eq_mul, mul_one]

end GlobalTheory.Mem.R3.Rw.SpOfMat

namespace GlobalTheory.Mem.R3.Rw.SpOfMat

open MonoidAlgebra

variable {G : Type} [Group G] [Fintype G]

theorem coeff_mapRingHom {R S : Type} [Semiring R] [Semiring S] (f : R →+* S) (a : MonoidAlgebra R G) (g : G) :
    (mapRingHom G f a).coeff g = f (a.coeff g) := by
  classical
  conv_lhs => rw [eq_sum_single a]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.coeff_sum, Finsupp.single_apply, apply_ite f]

section Act

variable {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} {σ : K →+* ℂ}
  {j : (Fin n → K) →ₛₗ[σ] EuclideanSpace ℂ (Fin n)} {H : Matrix (Fin n) (Fin n) K}
  {ρ : Matrix (Fin n) (Fin n) K →+* Module.End ℂ (EuclideanSpace ℂ (Fin n))}

theorem rho_smul (hρ : ∀ E, FormsTie σ j H E (ρ E)) (c : K) (E : Matrix (Fin n) (Fin n) K) :
    ρ (c • E) = σ c • ρ E := by
  refine LinearMap.ext_on_range (hρ E).span fun i => ?_
  rw [(hρ _).op_eq, LinearMap.smul_apply, (hρ E).op_eq, Matrix.smul_mulVec, map_smulₛₗ]

theorem rho_symm (hρ : ∀ E, FormsTie σ j H E (ρ E)) (E : Matrix (Fin n) (Fin n) K)
    (hsa : ∀ x y, Formalism.DivisionValues.hform H (E.mulVec x) y = Formalism.DivisionValues.hform H x (E.mulVec y)) : (ρ E).IsSymmetric := by
  let b := Module.Basis.mk (hρ E).li (hρ E).span.ge
  have hB : (innerₛₗ ℂ).comp (ρ E) = (innerₛₗ ℂ).compl₂ (ρ E) := by
    refine LinearMap.ext_basis b b fun i k => ?_
    simp only [b, Module.Basis.mk_apply, LinearMap.comp_apply, LinearMap.compl₂_apply, (hρ E).op_eq]
    change inner ℂ (j _) (j _) = inner ℂ (j _) (j _)
    rw [(hρ E).inner, (hρ E).inner, hsa]
  intro x y
  have := DFunLike.congr_fun (DFunLike.congr_fun hB x) y
  exact this

noncomputable def lin (ρ : Matrix (Fin n) (Fin n) K →+* Module.End ℂ (EuclideanSpace ℂ (Fin n)))
    (op : MonoidAlgebra K G → Matrix (Fin n) (Fin n) K) :
    MonoidAlgebra ℂ G →ₗ[ℂ] Module.End ℂ (EuclideanSpace ℂ (Fin n)) where
  toFun a := ∑ g, a.coeff g • ρ (op (single g 1))
  map_add' a b := by simp [MonoidAlgebra.coeff_add, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp [MonoidAlgebra.coeff_smul, Finset.smul_sum, smul_smul]

theorem lin_map (hρ : ∀ E, FormsTie σ j H E (ρ E)) (op : MonoidAlgebra K G → Matrix (Fin n) (Fin n) K)
    (hadd : ∀ a b, op (a + b) = op a + op b) (hsmul : ∀ (c : K) a, op (c • a) = c • op a) (a : MonoidAlgebra K G) :
    lin ρ op (mapRingHom G σ a) = ρ (op a) := by
  let opL : MonoidAlgebra K G →ₗ[K] Matrix (Fin n) (Fin n) K := ⟨⟨op, hadd⟩, hsmul⟩
  change _ = ρ (opL a)
  conv_rhs => rw [eq_sum_single a]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  have h1 : single g (a.coeff g) = a.coeff g • single g (1 : K) := by rw [smul_single, smul_eq_mul, mul_one]
  rw [h1, map_smul, rho_smul hρ, coeff_mapRingHom]
  rfl

theorem lin_mul (hρ : ∀ E, FormsTie σ j H E (ρ E)) (op : MonoidAlgebra K G → Matrix (Fin n) (Fin n) K)
    (hadd : ∀ a b, op (a + b) = op a + op b) (hsmul : ∀ (c : K) a, op (c • a) = c • op a)
    (hmul : ∀ a ∈ Subalgebra.center K (MonoidAlgebra K G), ∀ b ∈ Subalgebra.center K (MonoidAlgebra K G),
      op (a * b) = op a * op b)
    (z w : MonoidAlgebra ℂ G) (hz : z ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G))
    (hw : w ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G)) : lin ρ op (z * w) = lin ρ op z * lin ρ op w := by
  have hone : ∀ α : G → ℂ, lin ρ op (∑ g, α g • conjSum ℂ g) = ∑ g, α g • ρ (op (conjSum K g)) := fun α => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smul, ← mapRange_conjSum σ, lin_map hρ op hadd hsmul]
  have key : ∀ α β : G → ℂ, lin ρ op ((∑ g, α g • conjSum ℂ g) * ∑ h, β h • conjSum ℂ h) =
      lin ρ op (∑ g, α g • conjSum ℂ g) * lin ρ op (∑ h, β h • conjSum ℂ h) := fun α β => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hone, hone, Finset.sum_mul_sum, Finset.sum_mul_sum, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [smul_mul_smul_comm, smul_mul_smul_comm, map_smul, ← mapRange_conjSum σ, ← mapRange_conjSum σ, ← map_mul,
      lin_map hρ op hadd hsmul, hmul _ (conjSum_mem_center K g) _ (conjSum_mem_center K h), map_mul]
  have h := key z.coeff w.coeff
  rw [← card_smul_eq z hz, ← card_smul_eq w hw, smul_mul_smul_comm, map_smul, map_smul, map_smul,
    smul_mul_smul_comm] at h
  have hc : ((Fintype.card G : ℂ) * (Fintype.card G : ℂ)) ≠ 0 := by
    have : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    exact mul_ne_zero this this
  exact smul_right_injective _ hc h

noncomputable def actC (hρ : ∀ E, FormsTie σ j H E (ρ E)) (op : MonoidAlgebra K G → Matrix (Fin n) (Fin n) K)
    (hadd : ∀ a b, op (a + b) = op a + op b) (hsmul : ∀ (c : K) a, op (c • a) = c • op a)
    (hmul : ∀ a ∈ Subalgebra.center K (MonoidAlgebra K G), ∀ b ∈ Subalgebra.center K (MonoidAlgebra K G),
      op (a * b) = op a * op b) (hone : op 1 = 1) :
    Subalgebra.center ℂ (MonoidAlgebra ℂ G) →ₐ[ℂ] Module.End ℂ (EuclideanSpace ℂ (Fin n)) where
  toFun z := lin ρ op z
  map_one' := by
    change lin ρ op 1 = 1
    rw [← map_one (mapRingHom G σ), lin_map hρ op hadd hsmul, hone, map_one]
  map_mul' z w := lin_mul hρ op hadd hsmul hmul z w z.2 w.2
  map_zero' := map_zero _
  map_add' z w := map_add _ _ _
  commutes' c := by
    change lin ρ op (algebraMap ℂ (MonoidAlgebra ℂ G) c) = _
    rw [Algebra.algebraMap_eq_smul_one, map_smul, ← map_one (mapRingHom G σ), lin_map hρ op hadd hsmul, hone, map_one,
      Algebra.algebraMap_eq_smul_one]

end Act

end GlobalTheory.Mem.R3.Rw.SpOfMat

namespace GlobalTheory.Mem.R3.Rw.SpOfMat

open MonoidAlgebra

theorem exists_complexification_of_definiteGroupForms : ∀ (K O : Type) [Field K] [NumberField K] [StarRing K] [CommRing O] (o : O →+* K) (σ : K →+* ℂ) (G : Type) [Group G] [Fintype G] (m : Mat1 K G) (e : MonoidAlgebra K G), (∀ x, σ (star x) = starRingEnd ℂ (σ x)) → (∀ y, IsIntegral ℤ (o y)) → m.Laws σ e → ∃ s : Sp1 O (σ.comp o) G, Nonempty (Tie1 σ m s) := by
  intro K O _ _ _ _ o σ G _ _ m e hσ ho hm
  obtain ⟨j, M, ρ, hρ, hM, hcar⟩ :=
    GlobalTheory.Mem.CoordForms.exists_formsTie_oLatTie K O o σ m.n m.H m.N hσ hm.pos hm.lat
  have hcar' := hcar ho
  have hEE : m.E * m.E = m.E := by
    rw [hm.E_eq, ← hm.mul e hm.cen e hm.cen, hm.idem.eq]
  let s : Sp1 O (σ.comp o) G :=
    { A := Hs.mk (EuclideanSpace ℂ (Fin m.n))
      lat := M
      e := ρ m.E
      idem := by rw [← Module.End.mul_eq_comp, ← map_mul, hEE]
      sa := rho_symm hρ m.E hm.sa
      act := actC hρ m.op hm.add hm.smul hm.mul hm.one }
  refine ⟨s, ⟨{ j := j, forms := hρ m.E, latT := hM, stable := ?_, cen := ?_ }⟩⟩
  · intro a y hy
    change y ∈ (M.carrier : Set (EuclideanSpace ℂ (Fin m.n))) at hy
    change σ (a : K) • y ∈ (M.carrier : Set (EuclideanSpace ℂ (Fin m.n)))
    rw [hcar'] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨(a : K) • x, ?_, by rw [map_smulₛₗ]⟩
    have := m.N.smul_mem a hx
    rwa [← algebraMap_smul K] at this
  · intro z a hza x
    have hz : (z : MonoidAlgebra ℂ G) = mapRingHom G σ a := by
      apply MonoidAlgebra.ext
      ext g
      rw [coeff_mapRingHom]
      exact (hza g).symm
    change lin ρ m.op z (j x) = _
    rw [hz, lin_map hρ m.op hm.add hm.smul, (hρ _).op_eq]

end GlobalTheory.Mem.R3.Rw.SpOfMat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexificationOfDefiniteGroupFormsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complexification_of_definiteGroupForms' : ∀ (K O : Type) [Field K] [NumberField K] [StarRing K] [CommRing O] (o : O →+* K) (σ : K →+* ℂ) (G : Type) [Group G] [Fintype G] (m : Mat1 K G) (e : MonoidAlgebra K G), (∀ x, σ (star x) = starRingEnd ℂ (σ x)) → (∀ y, IsIntegral ℤ (o y)) → m.Laws σ e → ∃ s : Sp1 O (σ.comp o) G, Nonempty (Tie1 σ m s) := by
  exact @_root_.GlobalTheory.Mem.R3.Rw.SpOfMat.exists_complexification_of_definiteGroupForms
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowLiftReadingDefiniteFormCoordinates
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw.PkRead


set_option maxHeartbeats 4000000 in
theorem exists_pkT : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat), ∀ (mA : Bool → D.what₂.Tup → Mat1 D.what₂.LL G) (mL : D.what₂.Tup → ℕ → Mat1 D.what₂.LL G), (∀ b μ, (mA b μ).Laws D.what₂.embLL (idemOf A3.A.X)) → (∀ μ j, (mL μ j).Laws D.what₂.embLL (idemOf A3.A.X)) → (∀ b t, mA b (y.tup t) = rMat A3.A (levP F.lv2 b).1 (levP F.lv2 b).2 t) → (∀ (i : Fin D.R.m) t, mL (y.tup t) ((i : ℕ) + 1) = lMat A3.A F.lv2.P0 F.lv2.ψ0 i t) → ∃ p : PkD D G, p.mL = mL ∧ Nonempty (PkT F y mA p) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hO hI hP hH y mA mL hA hL hAe hLe
  obtain ⟨Φ, rep, hrep⟩ := GlobalTheory.T.exists_finite_representatives_rowFiniteTypes D G Pl0 I0 T A3 Ks R F cG hI hP hH y
  have hstar : ∀ x, D.what₂.embLL (star x) = starRingEnd ℂ (D.what₂.embLL x) := D.starLL_cx
  have hint : ∀ z, IsIntegral ℤ (D.what₂.OtoLL z) := D.O_int
  choose sA tA using fun b μ =>
    GlobalTheory.T.exists_complexification_of_definiteGroupForms' D.what₂.LL D.what₂.O D.what₂.OtoLL D.what₂.embLL G (mA b μ) (idemOf A3.A.X) hstar hint (hA b μ)
  choose sL tL using fun μ j =>
    GlobalTheory.T.exists_complexification_of_definiteGroupForms' D.what₂.LL D.what₂.O D.what₂.OtoLL D.what₂.embLL G (mL μ j) (idemOf A3.A.X) hstar hint (hL μ j)
  let tA' : ∀ b μ, Tie1 D.what₂.embLL (mA b μ) (sA b μ) := fun b μ => (tA b μ).some
  let tL' : ∀ μ j, Tie1 D.what₂.embLL (mL μ j) (sL μ j) := fun μ j => (tL μ j).some
  choose c hc using fun b =>
    GlobalTheory.T.exists_levelChain_over_top_spaces D G Pl0 I0 T A3 Ks R F cG hI hP hH y Φ rep hrep b (mA b) (sA b) (tA' b) (hAe b)
  obtain ⟨l, hl⟩ := GlobalTheory.T.exists_lift_spaces_over_definite_forms D G Pl0 I0 T A3 Ks R F cG hO hI hP hH y Φ rep hrep mL sL tL' hLe
  let chT := fun b => (hc b).some
  obtain ⟨nR, cR, Xo, hrr⟩ := GlobalTheory.T.exists_rowBasis_from_referenceTuple_quotient D G Pl0 I0 T A3 Ks R F cG hP hH y true (c true).EE (chT true).jE
    (chT true).jE_inj (chT true).jE_range
  haveI : Finite Φ := hrep.fin
  letI : Fintype Φ := Fintype.ofFinite Φ
  classical

  have hθ : IsInfFam R.θ := hP.char.base.models.inf
  have hfin : FiniteDimensional ℂ (Mult.Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))
      (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))) :=
    hI.hc (Yc D 0) (D.sp.Y_sig _) _ R.θ (R.MY 0) _ _ hθ (hI.lev (Yc D 0) (R.βY 0) _).2
  set Dall := Module.finrank ℂ (Mult.Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))
      (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))) with hDall
  have hn : Dall = 0 → (c true).n = 0 := by
    intro h0
    have hM : Mult.Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))
        (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true))) = ⊥ :=
      Submodule.finrank_eq_zero.1 h0
    have hE : (y.C F.lv2).EEc true = ⊥ := by
      show (Mult.goodPart R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))
        (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true))) R.e0).map _ = ⊥
      rw [eq_bot_iff.2 ((Mult.goodPart_le _ _ _ _ _).trans hM.le)]
      exact Submodule.map_bot _
    have hr := (chT true).jE_range
    rw [hE] at hr
    have h1 := LinearMap.finrank_range_of_inj (chT true).jE_inj
    rw [hr, finrank_bot] at h1
    have h2 := Module.finrank_eq_card_basis (c true).bs.toBasis
    rw [← h1, Fintype.card_fin] at h2
    exact h2.symm
  let dp : ℝ := if Dall = 0 then 0 else 1 - ((c true).n : ℝ) / Dall
  have hdelp : dp ≤ 1 := by
    simp only [dp]
    split_ifs
    · norm_num
    · have : (0 : ℝ) ≤ ((c true).n : ℝ) / Dall := by positivity
      linarith
  have hD : (((c true).n : ℕ) : ℝ) = (1 - dp) * Dall := by
    simp only [dp]
    split_ifs with h
    · rw [hn h, h]; simp
    · have : (Dall : ℝ) ≠ 0 := by exact_mod_cast h
      field_simp
      ring
  refine ⟨{ Φ := Φ, sA := sA, mL := mL, sL := sL, tL := tL', ch := c, lf := l, Dall := Dall, delp := dp, delp_le_one := hdelp, D_eq := hD, nR := nR, cR := cR, Xo := Xo }, rfl, ⟨?_⟩⟩
  exact { rep := rep, reps := hrep, tA := tA', lawsA := hA, lawsL := hL, hA := hAe, hL := hLe, ch := chT, lf := hl.some, dall := rfl, rr := hrr }

end GlobalTheory.Mem.R3.Rw.PkRead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowLiftReadingDefiniteFormCoordinatesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rowLiftReading_definiteFormCoordinates : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat), ∀ (mA : Bool → D.what₂.Tup → Mat1 D.what₂.LL G) (mL : D.what₂.Tup → ℕ → Mat1 D.what₂.LL G), (∀ b μ, (mA b μ).Laws D.what₂.embLL (idemOf A3.A.X)) → (∀ μ j, (mL μ j).Laws D.what₂.embLL (idemOf A3.A.X)) → (∀ b t, mA b (y.tup t) = rMat A3.A (levP F.lv2 b).1 (levP F.lv2 b).2 t) → (∀ (i : Fin D.R.m) t, mL (y.tup t) ((i : ℕ) + 1) = lMat A3.A F.lv2.P0 F.lv2.ψ0 i t) → ∃ p : PkD D G, p.mL = mL ∧ Nonempty (PkT F y mA p) := by
  first | exact @GlobalTheory.Mem.R3.Rw.PkRead.exists_pkT | exact GlobalTheory.Mem.R3.Rw.PkRead.exists_pkT | (intros; apply GlobalTheory.Mem.R3.Rw.PkRead.exists_pkT <;> assumption)
end
