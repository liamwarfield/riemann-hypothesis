module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.CxCutEP
public import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
public import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
public import Formalism.LocalToGlobal.IndefiniteReal.MemRangeAdjointOfKerStable

@[expose] public section

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.AutomorphicFormsHyp
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Filter Topology
  IsDedekindDomain NumberField Matrix

namespace Formalism.IndefR.AutomorphicFormsHyp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section General

variable {N : ℕ}

def hK (K : Matrix (Fin N) (Fin N) D.host.E) (x y : Mx D N 1) : AE D :=
  ∑ a, ∑ b, cA D (y a 0) * incA D (K a b) * x b 0

end General

def WeilExistsO (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle),
    IsStdChar D ψ (-1) → IsHeckeChar D χS → IsHeckeChar D χT → ResEta D χS S.rank → ResEta D χT T.rank →
    ∃ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeilDatumO ψ S T χS χT om

end Formalism.IndefR.AutomorphicFormsHyp

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.CxCutPO
open Module NumberField IsDedekindDomain Polynomial
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.DIV.CyclotomicLifting Formalism.IndefR.Cx.EigenprojectionMatrices

namespace OrthogonalPartDecomposition

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  {B : BlockDat K G Pl0} {ℓ : Lvl K G} {v0 : InfinitePlace K} {s : ℕ} {Z : Submodule K B.S.Forms}

theorem map_conjTranspose_of_mem_cmMax {n d : ℕ} (σ : K →+* ℂ) (E : Matrix (Fin n) (Fin d) K) (hE : ∀ i a, E i a ∈ cmMax K) :
    (Eᴴ).map σ = (E.map σ)ᴴ :=
  map_conjTranspose' σ E fun i a => ConjugateWeightGram.isCMSub_cmMax σ _ (hE i a)

theorem HV_map (h : BlockHyp B ℓ v0 s) (σ : K →+* ℂ) :
    (B.HV ℓ).map σ = σ (Nat.card ℓ.P : K)⁻¹ • (((B.vE ℓ).map σ)ᴴ * B.S.H.map σ * (B.vE ℓ).map σ) := by
  have e : B.HV ℓ = (Nat.card ℓ.P : K)⁻¹ • ((B.vE ℓ)ᴴ * B.S.H * B.vE ℓ) := rfl
  rw [e, ← map_conjTranspose_of_mem_cmMax σ _ (hv_spec h).1, ← Matrix.map_mul, ← Matrix.map_mul]
  ext a b
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

theorem adjC (h : BlockHyp B ℓ v0 s) (hH : B.OkH) (σ : K →+* ℂ) (i : B.Pl × ℕ) :
    ∃ i', (B.HV ℓ).map σ * (tV B ℓ i).map σ = ((tV B ℓ i').map σ)ᴴ * (B.HV ℓ).map σ := by
  obtain ⟨i', hi'⟩ := opMat_adj hH i
  have hHh : B.S.Hᴴ = B.S.H := FinitelyNonzeroLinear.herm_of_pos h.conj (h.ok.hpos v0)
  have h2 : B.S.H * B.opMat i = (B.opMat i')ᴴ * B.S.H := by
    have := congrArg Matrix.conjTranspose hi'
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHh] at this
    exact this
  have h2' : B.S.H.map σ * (B.opMat i).map σ = ((B.opMat i').map σ)ᴴ * B.S.H.map σ := by
    rw [← Matrix.map_mul, h2, Matrix.map_mul, map_conjTranspose_of_mem_cmMax σ _ (hH.rat i')]
  have hT : ∀ k, (B.vE ℓ).map σ * (tV B ℓ k).map σ = (B.opMat k).map σ * (B.vE ℓ).map σ := by
    intro k
    rw [← Matrix.map_mul, ← Matrix.map_mul, vE_tV h]
  refine ⟨i', ?_⟩
  rw [HV_map h σ]
  exact adj_transfer _ _ _ _ _ _ _ (hT i) (hT i') h2'

end OrthogonalPartDecomposition

section Main

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
variable (A : FamIn K G Pl0 T m) (X : CxData A.fam.amb)
variable (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
  (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
  (Zsc : DefSub A.fam.amb → IndefScale A.fam.base)

end Main

end Formalism.IndefR.Cx
end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.ExistsGADet
section -- merged from Formalism.LocalToGlobal.IndefiniteReal.WeilDatumUniqueOfDeterminants
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis Formalism.IndefR.InjectiveDecompositionAction
  IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.flipTwoThree

def DeterminantInUnitaryOne : Prop :=
  ∀ (D : D7) (V : HSp D) (g : GA D V), (mt V g).det * cA D (mt V g).det = 1

def SplitDetP : Prop :=
  ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ e, IsSplitIdem D e → ∀ x : (AE D)ˣ, (x : AE D) * cA D (x : AE D) = 1 →
    SuppAtU D e x → ∃ g : GA D V, SuppAt e V g ∧ (∃ x', IsDetAt e V g x') ∧ (mt V g).det = x

variable {D : D7}

theorem mt_one' (V : HSp D) : L2.Theta.mt V 1 = 1 := by
  simp [L2.Theta.mt, map_one]

section Scalar

variable (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χ χ' : (AE D)ˣ →* Circle)
    (ω ω' : GA D V × GA D W →* Module.End ℂ (Hth ψ V W))

end Scalar

section Side

end Side

end Formalism.IndefR.flipTwoThree

end
end

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis Formalism.IndefR.InjectiveDecompositionAction
  IsDedekindDomain NumberField Formalism.IndefR.DeterminantProjection Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.flipTwoThree

variable {D : D7}

abbrev sigE (D : D7) : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E)

theorem sigE_sigE (a : D.host.E) : sigE D (sigE D a) = a := star_star a

theorem gram_herm (V : HSp D) (i j : Fin V.rank) : sigE D (V.gram i j) = V.gram j i :=
  V.herm.eq (V.frame i) (V.frame j)

theorem cA_incA' (a : D.host.E) : cA D (incA D a) = incA D (sigE D a) := by
  simp [cA, incA, sigR, inclR]

theorem gramA_herm (V : HSp D) (i j : Fin V.rank) :
    cA D (V.gram.map (incA D) i j) = V.gram.map (incA D) j i := by
  simp only [Matrix.map_apply, cA_incA', gram_herm]

def mkGA (V : HSp D) (M : Matrix (Fin V.rank) (Fin V.rank) (AE D))
    (hM : (M.map (cA D))ᵀ * V.gram.map (incA D) * M = V.gram.map (incA D)) (hd : IsUnit M.det) : GA D V :=
  let g : HR (AF D.host.F) D.sp.cm.sig V.gram := ⟨Matrix.nonsingInvUnit M hd, hM⟩
  g

theorem aniso_data (V : HSp D) (hn : 0 < V.rank) :
    ∃ (u : Fin V.rank → D.host.E) (ainv : D.host.E), ainv * hsq (sigE D) V.gram u = 1 ∧ sigE D ainv = ainv := by
  have : Nonempty (Fin V.rank) := ⟨⟨0, hn⟩⟩
  obtain ⟨u, hu⟩ := exists_aniso (sigE D) sigE_sigE V.gram (gram_herm V) (gram_det_ne V)
  refine ⟨u, (hsq (sigE D) V.gram u)⁻¹, inv_mul_cancel₀ hu, ?_⟩
  rw [map_inv₀, sigma_hsq (sigE D) sigE_sigE V.gram (gram_herm V) u]

theorem exists_GA_det (V : HSp D) (hn : 0 < V.rank) (x : AE D) (hx : cA D x * x = 1) (hxu : IsUnit x) :
    ∃ (R : Matrix (Fin V.rank) (Fin V.rank) (AE D)) (g : GA D V), mt V g = 1 + (x - 1) • R ∧ (mt V g).det = x := by
  obtain ⟨u, ainv, ha, hainv⟩ := aniso_data V hn
  have haA : incA D ainv * hsq (cA D) (V.gram.map (incA D)) (fun i => incA D (u i)) = 1 := by
    rw [← hsq_map (incA D) (sigE D) (cA D) (fun a => (cA_incA' a).symm), ← map_mul, ha, map_one]
  have hainvA : cA D (incA D ainv) = incA D ainv := by rw [cA_incA', hainv]
  set R := proj (cA D) (V.gram.map (incA D)) (fun i => incA D (u i)) (incA D ainv)
  have hM := proj_unitary (cA D) cA_cA (V.gram.map (incA D)) (gramA_herm V) (fun i => incA D (u i))
    (incA D ainv) haA hainvA x hx
  have hdet := det_proj' (cA D) (V.gram.map (incA D)) (fun i => incA D (u i)) (incA D ainv) haA x
  exact ⟨R, mkGA V _ hM (by rw [hdet]; exact hxu), rfl, hdet⟩

theorem splitDet : SplitDetP := by
  intro D V hn e he x hx hsupp
  obtain ⟨R, g, hg, hdet⟩ := exists_GA_det V hn (x : AE D) (by rw [mul_comm]; exact hx) x.isUnit
  refine ⟨g, ?_, ?_, hdet⟩
  · intro i j
    rw [hg, add_sub_cancel_left, Matrix.smul_apply, smul_eq_mul, ← mul_assoc]
    unfold SuppAtU at hsupp
    rw [hsupp]
  · have hxi : (x : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := x.mul_inv
    set xi : AE D := ((x⁻¹ : (AE D)ˣ) : AE D) with hxi_def
    set x0 : AE D := (x : AE D) with hx0
    have p1 : (e * x0 + (1 - e)) * (e * xi + (1 - e)) = 1 := by
      linear_combination (x0 * xi - x0 - xi + 1) * he.1 + e * hxi
    have p2 : (e * xi + (1 - e)) * (e * x0 + (1 - e)) = 1 := by
      linear_combination (x0 * xi - x0 - xi + 1) * he.1 + e * hxi
    obtain ⟨y, hy⟩ : ∃ y : (AE D)ˣ, (y : AE D) = e * x0 + (1 - e) := ⟨⟨_, _, p1, p2⟩, rfl⟩
    refine ⟨y, ?_⟩
    unfold IsDetAt
    rw [hy, hdet]

end Formalism.IndefR.flipTwoThree

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.EigSumLeComapSemi
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Col

section Gen

variable {K : Type} [Field K] {σ : K →+* ℂ}

def cxSys {I : Type} (σ : K →+* ℂ) (C : (I → K) → Prop) : (I → ℂ) → Prop :=
  fun y => ∃ x, C x ∧ y = fun i => σ (x i)

variable {V E : Type} [AddCommGroup V] [Module K V] [AddCommGroup E] [Module ℂ E]

theorem map_pow_sub (f : V →ₛₗ[σ] E) (T : Module.End K V) (S : Module.End ℂ E)
    (h : ∀ v, f (T v) = S (f v)) (a : K) (k : ℕ) (v : V) :
    f (((T - a • 1) ^ k) v) = ((S - σ a • 1) ^ k) (f v) := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
    congr 1
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smulₛₗ, h]

theorem map_maxGen (f : V →ₛₗ[σ] E) {T : Module.End K V} {S : Module.End ℂ E}
    (h : ∀ v, f (T v) = S (f v)) {a : K} {v : V} (hv : v ∈ T.maxGenEigenspace a) :
    f v ∈ S.maxGenEigenspace (σ a) := by
  rw [Module.End.mem_maxGenEigenspace] at hv ⊢
  obtain ⟨k, hk⟩ := hv
  exact ⟨k, by rw [← map_pow_sub f T S h a k v, hk, map_zero]⟩

variable {I : Type}

theorem map_eigAt (f : V →ₛₗ[σ] E) {op : I → Module.End K V} {h : I → Module.End ℂ E}
    (hf : ∀ i v, f (op i v) = h i (f v)) {x : I → K} {v : V} (hv : v ∈ eigAt op x) :
    f v ∈ eigAt h (fun i => σ (x i)) := by
  unfold eigAt at hv ⊢
  rw [Submodule.mem_iInf] at hv ⊢
  exact fun i => map_maxGen f (hf i) (hv i)

theorem eigSum_le_comap_semi (f : V →ₛₗ[σ] E) {op : I → Module.End K V} {h : I → Module.End ℂ E}
    (hf : ∀ i v, f (op i v) = h i (f v)) (C : (I → K) → Prop) :
    eigSum op C ≤ (eigSum h (cxSys σ C)).comap f := by
  show (⨆ (x : I → K) (_ : C x), eigAt op x) ≤ _
  refine iSup₂_le fun x hx => ?_
  intro v hv
  rw [Submodule.mem_comap]
  exact eigAt_le_eigSum (op := h) ⟨x, hx, rfl⟩ (map_eigAt f hf hv)

theorem mem_eigSum_iff_map [FiniteDimensional K V] [FiniteDimensional ℂ E] (f : V →ₛₗ[σ] E)
    {op : I → Module.End K V} (hc : PairComm op) (hs : SplitOver op)
    {h : I → Module.End ℂ E} (hch : PairComm h) (hf : ∀ i v, f (op i v) = h i (f v))
    {Z : Submodule K V} (hZ : ∀ i, Z ≤ Z.comap (op i)) (hinj : ∀ z ∈ Z, f z = 0 → z = 0)
    (C : (I → K) → Prop) {v : V} (hv : v ∈ Z) :
    v ∈ eigSum op C ↔ f v ∈ eigSum h (cxSys σ C) := by
  constructor
  · intro hv'
    exact eigSum_le_comap_semi f hf C hv'
  · intro hfv
    have hpv : eigProj hc hs C v ∈ eigSum op C := eigProj_apply_mem hc hs C v
    have h2 : v - eigProj hc hs C v ∈ eigSum op (fun x => ¬ C x) := sub_eigProj_mem hc hs C v
    have hZ2 : v - eigProj hc hs C v ∈ Z := Z.sub_mem hv (eigProj_mem_of_stable hc hs C hZ hv)
    have hf1 : f (v - eigProj hc hs C v) ∈ eigSum h (cxSys σ C) := by
      rw [map_sub]
      exact Submodule.sub_mem _ hfv (eigSum_le_comap_semi f hf C hpv)
    have hf2 : f (v - eigProj hc hs C v) ∈ eigSum h (cxSys σ fun x => ¬ C x) :=
      eigSum_le_comap_semi f hf _ h2
    have hdis : Disjoint (eigSum h (cxSys σ C)) (eigSum h (cxSys σ fun x => ¬ C x)) := by
      apply disjoint_eigSum hch
      rintro y ⟨x, hx, rfl⟩ ⟨x', hx', hxx⟩
      apply hx'
      have e : x' = x := funext fun i => (σ.injective (congrFun hxx i)).symm
      rw [e]
      exact hx
    have h0 : f (v - eigProj hc hs C v) = 0 := (Submodule.disjoint_def.1 hdis) _ hf1 hf2
    have e := hinj _ hZ2 h0
    rw [sub_eq_zero] at e
    rw [e]
    exact hpv

theorem inj_of_li {ι : Type*} (b : Basis ι K V) (f : V →ₛₗ[σ] E)
    (h : LinearIndependent ℂ fun k => f (b k)) : Function.Injective f := by
  refine (injective_iff_map_eq_zero f).2 fun v hv => ?_
  have e := b.linearCombination_repr v
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at e
  have h3 : ∑ i ∈ (b.repr v).support, σ (b.repr v i) • f (b i) = f v := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← congrArg f e, map_sum]
    simp only [map_smulₛₗ]
  have hall := linearIndependent_iff'.1 h _ _ (h3.trans hv)
  have hr : b.repr v = 0 := by
    ext i
    by_contra hi
    exact hi (σ.injective ((hall i (Finsupp.mem_support_iff.2 hi)).trans (map_zero σ).symm))
  simpa using congrArg b.repr.symm hr

end Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)

theorem theta_jR_inj (hR : X.KFormR) (t : Bs.Tup) (z : A.FR t) (hz : z ∈ X.Z t)
    (h0 : X.Θ t (X.jR t z) = 0) : z = 0 := by
  simp only [CxData.Z, Submodule.mem_comap, LinearMap.mem_range] at hz
  obtain ⟨w, hw⟩ := hz
  have h1 : X.jR t z = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℂ), ← hw, LinearMap.adjoint_inner_left, hw, h0, inner_zero_right]
  exact inj_of_li (bR (A := A) t) (X.jR t) (hR t).1 (h1.trans (map_zero _).symm)

theorem theta_jL_inj (hL : X.KFormL) (j : Bs.J) (t : Bs.Tup) (z : A.FL j t) (hz : z ∈ X.Zl j t)
    (h0 : X.θ' j t (X.jL j t z) = 0) : z = 0 := by
  simp only [CxData.Zl, Submodule.mem_comap, LinearMap.mem_range] at hz
  obtain ⟨w, hw⟩ := hz
  have h1 : X.jL j t z = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℂ), ← hw, LinearMap.adjoint_inner_left, hw, h0, inner_zero_right]
  exact inj_of_li (bL (A := A) j t) (X.jL j t) (hL j t).1 (h1.trans (map_zero _).symm)

variable {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

theorem iC_cpt_eq (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dQ t) → K) :
    X.iC cr b t (cpt Bs.v0.embedding x) = X.Θ t (X.jR t (cr.toR X.zs b t x)) := by
  have hx : x = ∑ k, x k • Pi.single k (1 : K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, map_smulₛₗ, CxData.iC, lin, Fintype.linearCombination_apply, cpt]

theorem tC_cpt_eq (j : Bs.J) (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dZ j t) → K) :
    X.tC cr b j t (cpt Bs.v0.embedding x) = X.θ' j t (X.jL j t (cr.toL X.zs b j t x)) := by
  have hx : x = ∑ k, x k • Pi.single k (1 : K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, map_smulₛₗ, CxData.tC, lin, Fintype.linearCombination_apply, cpt]

end CxData

section Concrete

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
variable (A : FamIn K G Pl0 T m) (X : CxData A.fam.amb)

variable {A X}

theorem toF_mem_Z {B : BlockDat K G Pl0} (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) :
    B.toF ℓ Z y ∈ Z := by
  have h1 : (B.zE ℓ Z).mulVec y ∈ B.Z0 ℓ Z := by
    rw [BlockDat.zE, subE_mulVec]
    exact Submodule.coe_mem _
  simp only [BlockDat.Z0, BlockDat.inV0, BlockDat.coord, Submodule.mem_comap, Submodule.mem_map,
    Matrix.mulVecLin_apply] at h1
  obtain ⟨w, hw, hwe⟩ := h1
  have e : B.toF ℓ Z y = w := by
    simp only [BlockDat.toF, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      Matrix.mulVecLin_apply]
    rw [← hwe]
    simp
  rw [e]
  exact hw

variable (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
  (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
  (Zsc : DefSub A.fam.amb → IndefScale A.fam.base)

end Concrete

end Formalism.IndefR.Cx
end
end
