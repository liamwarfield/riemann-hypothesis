module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarisationBaseFunctionProperties
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsToricTorsionCubicalWeilOneComplexPoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodCharactersExtendedDataEqMapSmallerData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFormsReferenceTupleExtensionSpan
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftSubspaceExtendedDataEqSpanSmallerLifts

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockBaseChangeAt
noncomputable section

namespace GlobalTheory.Mem.R3.LiftLatBC

open Module NumberField _root_.Formalism.L2.DIV Formalism.DivisionValues
open scoped Matrix

variable {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K']
  {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 Pl0' : Type}

def bcF (φ : K →+* K') (B : BlockDat K G Pl0) (B' : BlockDat K' G' Pl0') (C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K')
    (f : B.S.Forms) : B'.S.Forms :=
  B'.S.basis.equivFun.symm (C *ᵥ fun k => φ (B.S.basis.equivFun f k))

structure BlockBaseChangeAt (φ : K →+* K') (e : G ≃* G') (B : BlockDat K G Pl0) (B' : BlockDat K' G' Pl0')
    (ℓ : Lvl K G) (ℓ' : Lvl K' G') (Z : Submodule K B.S.Forms) (Z' : Submodule K' B'.S.Forms)
    (C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K') : Prop where

  bij : Function.Bijective C.mulVec

  H : Cᴴ * B'.S.H * C = B.S.H.map φ

  act : ∀ g : G, B'.S.actMat B'.r (e g) * C = C * (B.S.actMat B.r g).map φ

  nab : B'.S.nabLat = Submodule.span (𝓞 K') ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.S.nabLat : Set (Fin B.S.dim → K)))

  sub : B'.coord Z' = Submodule.span K' ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.coord Z : Set (Fin B.S.dim → K)))

  X : ∀ χ' : G' → K', χ' ∈ ℓ'.X ↔ ∃ χ ∈ ℓ.X, χ' = fun g => φ (χ (e.symm g))

  P : ℓ'.P = ℓ.P.map e.toMonoidHom

  ψ : ∀ h : ℓ.P, ((ℓ'.ψ ⟨e h, P ▸ Subgroup.mem_map_of_mem e.toMonoidHom h.2⟩ : K'ˣ) : K') = φ (ℓ.ψ h : K)

section Cx

open Formalism.IndefR.Cx _root_.Formalism.L2.Indef

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
  {fc : DefSub A → DefFace Bs}

theorem tC_cpt (cr : Crd A fc) (b : Bool) (j : Bs.J) (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dZ j t) → K) :
    X.tC cr b j t (cpt Bs.v0.embedding x) = X.θ' j t (X.jL j t (cr.toL X.zs b j t x)) := by
  have hx : x = ∑ k, x k • Pi.single k 1 := by
    funext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, map_smulₛₗ, CxData.tC, lin, Fintype.linearCombination_apply, cpt]

end Cx

end GlobalTheory.Mem.R3.LiftLatBC

end
end

section -- merged from Development.AutomorphicArithmetic.SemilinearForms.LiftMatAt
open Module NumberField Formalism.L2.DIV Formalism.DivisionValues
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.LiftLatBC

open GlobalTheory.Mem.R3.DefLatBC

variable {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K']
  {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 Pl0' : Type}

theorem forms_of_semilinear_at (φ : K →+* K') (e : G ≃* G') (B : BlockDat K G Pl0) (B' : BlockDat K' G' Pl0')
    (Z : Submodule K B.S.Forms) (Z' : Submodule K' B'.S.Forms) (L : B.S.Forms →+ B'.S.Forms)
    (hsm : ∀ (a : K) (f : B.S.Forms), L (a • f) = φ a • L f)
    (hli : LinearIndependent K' (fun k => L (B.S.basis k)))
    (hsp : ⊤ ≤ Submodule.span K' (Set.range fun k => L (B.S.basis k)))
    (hcs : ∀ f g : B.S.Forms, B'.S.csum (L f : B'.S.Cl → B'.S.V) (L g) = φ (B.S.csum f g))
    (hact : ∀ (g : G) (f : B.S.Forms), B'.r (e g) (L f) = L (B.r g f))
    (hnab : ∀ f' : B'.S.Forms, (∀ c, (f' : B'.S.Cl → B'.S.V) c ∈ B'.S.Nab c) ↔
      f' ∈ Submodule.span (𝓞 K') (L '' {f : B.S.Forms | ∀ c, (f : B.S.Cl → B.S.V) c ∈ B.S.Nab c}))
    (hZ : Z' = Submodule.span K' (L '' (Z : Set B.S.Forms))) :
    ∃ C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K', (∀ f, GlobalTheory.Mem.R3.LiftLatBC.bcF φ B B' C f = L f) ∧ Function.Bijective C.mulVec ∧
      Cᴴ * B'.S.H * C = B.S.H.map φ ∧
      (∀ g : G, B'.S.actMat B'.r (e g) * C = C * (B.S.actMat B.r g).map φ) ∧
      B'.S.nabLat = Submodule.span (𝓞 K') ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.S.nabLat : Set (Fin B.S.dim → K))) ∧
      B'.coord Z' = Submodule.span K' ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.coord Z : Set (Fin B.S.dim → K))) := by
  classical
  let v : Fin B.S.dim → B'.S.Forms := fun k => L (B.S.basis k)
  let bv : Basis (Fin B.S.dim) K' B'.S.Forms := Basis.mk hli hsp
  have hbv : ∀ k, bv k = L (B.S.basis k) := fun k => Basis.mk_apply hli hsp k
  let C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K' := B'.S.basis.toMatrix v
  have hCe : ∀ a i, C a i = B'.S.basis.equivFun (L (B.S.basis i)) a := by
    intro a i
    simp [C, v, Basis.toMatrix_apply]
  have hC : ∀ x, C *ᵥ x = B'.S.basis.equivFun (bv.equivFun.symm x) := by
    intro x
    ext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, hCe, Basis.equivFun_symm_apply, hbv, map_sum, map_smul,
      Basis.equivFun_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, mul_comm]
  have hL : ∀ f, L f = bv.equivFun.symm (fun k => φ (B.S.basis.equivFun f k)) := by
    intro f
    conv_lhs => rw [← B.S.basis.sum_equivFun f]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Basis.equivFun_symm_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsm, hbv]
  have hψ : ∀ x : Fin B.S.dim → K, C *ᵥ (fun k => φ (x k)) =
      B'.S.basis.equivFun (L (B.S.basis.equivFun.symm x)) := by
    intro x
    simp only [hL, LinearEquiv.apply_symm_apply, hC]
  have hbc : ∀ f, GlobalTheory.Mem.R3.LiftLatBC.bcF φ B B' C f = L f := by
    intro f
    simp only [GlobalTheory.Mem.R3.LiftLatBC.bcF]
    rw [hC, LinearEquiv.symm_apply_apply, hL]
  have hbij : Function.Bijective C.mulVec := by
    have he : C.mulVec = ⇑(bv.equivFun.symm.trans B'.S.basis.equivFun) := funext fun x => by
      rw [hC]
      rfl
    rw [he]
    exact LinearEquiv.bijective _
  have hH : Cᴴ * B'.S.H * C = B.S.H.map φ := by
    ext i j
    have h1 := csum_coords B'.S (B'.S.basis.equivFun (L (B.S.basis i)))
      (B'.S.basis.equivFun (L (B.S.basis j)))
    simp only [LinearEquiv.symm_apply_apply, hcs] at h1
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Formalism.L2.DIV.CSD.H,
      Matrix.of_apply, hCe]
    rw [h1]
    simp only [Finset.sum_mul]
    exact Finset.sum_comm
  have hrep : ∀ (T : Module.End K B.S.Forms) (f : B.S.Forms),
      LinearMap.toMatrix B.S.basis B.S.basis T *ᵥ B.S.basis.equivFun f = B.S.basis.equivFun (T f) :=
    fun T f => LinearMap.toMatrix_mulVec_repr _ _ _ _
  have hrep' : ∀ (T : Module.End K' B'.S.Forms) (f : B'.S.Forms),
      LinearMap.toMatrix B'.S.basis B'.S.basis T *ᵥ B'.S.basis.equivFun f = B'.S.basis.equivFun (T f) :=
    fun T f => LinearMap.toMatrix_mulVec_repr _ _ _ _
  have hact' : ∀ g : G, B'.S.actMat B'.r (e g) * C = C * (B.S.actMat B.r g).map φ := by
    intro g
    apply Matrix.ext_of_mulVec_single
    intro k
    have hs : (Pi.single k 1 : Fin B.S.dim → K') = fun j => φ ((Pi.single k 1 : Fin B.S.dim → K) j) := by
      funext j
      by_cases h : j = k <;> simp [h]
    have hk : (Pi.single k 1 : Fin B.S.dim → K) = B.S.basis.equivFun (B.S.basis k) := by
      funext j
      rw [Basis.equivFun_self, Pi.single_apply]
      by_cases h : j = k
      · subst h
        simp
      · simp [h, Ne.symm h]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hs]
    have hm : (B.S.actMat B.r g).map φ *ᵥ (fun j => φ ((Pi.single k 1 : Fin B.S.dim → K) j)) =
        fun i => φ (((B.S.actMat B.r g) *ᵥ Pi.single k 1) i) := by
      funext i
      exact (RingHom.map_mulVec φ _ _ i).symm
    rw [hm, hψ, hψ, hk]
    simp only [Formalism.L2.DIV.CSD.actMat, hrep, hrep', LinearEquiv.symm_apply_apply, hact]
  have hnab' : B'.S.nabLat = Submodule.span (𝓞 K')
      ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.S.nabLat : Set (Fin B.S.dim → K))) := by
    have hset : (fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.S.nabLat : Set (Fin B.S.dim → K)) =
        (fun f => B'.S.basis.equivFun (L f)) '' {f : B.S.Forms | ∀ c, (f : B.S.Cl → B.S.V) c ∈ B.S.Nab c} := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨B.S.basis.equivFun.symm x, (mem_nabLat_iff B.S x).mp hx, (hψ x).symm⟩
      · rintro ⟨f, hf, rfl⟩
        refine ⟨B.S.basis.equivFun f, (mem_nabLat_iff B.S _).mpr (by simpa using hf), ?_⟩
        simp only [hψ, LinearEquiv.symm_apply_apply]
    rw [hset]
    ext y
    rw [mem_nabLat_iff, hnab (B'.S.basis.equivFun.symm y)]
    let E := B'.S.basis.equivFun.restrictScalars (𝓞 K')
    have hE : (fun f => B'.S.basis.equivFun (L f)) '' {f : B.S.Forms | ∀ c, (f : B.S.Cl → B.S.V) c ∈ B.S.Nab c} =
        (E : B'.S.Forms →ₗ[𝓞 K'] (Fin B'.S.dim → K')) '' (L '' {f : B.S.Forms | ∀ c, (f : B.S.Cl → B.S.V) c ∈ B.S.Nab c}) := by
      rw [Set.image_image]
      rfl
    rw [hE, ← Submodule.map_span, Submodule.mem_map_equiv]
    exact Iff.rfl
  have hcoord : B'.coord Z' = Submodule.span K'
      ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.coord Z : Set (Fin B.S.dim → K))) := by
    rw [hZ]
    simp only [Formalism.L2.DIV.BlockDat.coord, Submodule.map_span, Submodule.map_coe, LinearEquiv.coe_coe]
    congr 1
    rw [Set.image_image, Set.image_image]
    refine Set.image_congr fun f _ => ?_
    rw [hψ, LinearEquiv.symm_apply_apply]
  exact ⟨C, hbc, hbij, hH, hact', hnab', hcoord⟩

end GlobalTheory.Mem.R3.LiftLatBC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendedDataLiftBlockDatumBaseChangeOneMatrix
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.LiftLatBC

private theorem app_heq {Γ Γ' W W' : Type} (hΓ : Γ' = Γ) {nW : NormedAddCommGroup W} {nW' : NormedAddCommGroup W'}
    {iW : InnerProductSpace ℂ W} {iW' : InnerProductSpace ℂ W'} (h1 : HEq W' W) (h2 : HEq nW' nW) (h3 : HEq iW' iW)
    {H : HMod (Γ → W)} {H' : HMod (Γ' → W')} (hH : HEq H' H) (inj : Function.Injective H.e)
    {Y Y' : Type} {nY : NormedAddCommGroup Y} {nY' : NormedAddCommGroup Y'}
    {iY : InnerProductSpace ℂ Y} {iY' : InnerProductSpace ℂ Y'} (g1 : Y' = Y) (g2 : HEq nY' nY) (g3 : HEq iY' iY)
    {θ : H.H →ₗ[ℂ] Y} {θ' : H'.H →ₗ[ℂ] Y'} (hθ : HEq θ' θ) {y : H.H} {y' : H'.H} (he : HEq (H'.e y') (H.e y)) :
    HEq (θ' y') (θ y) := by
  subst hΓ g1
  cases h1; cases h2; cases h3; cases hH; cases g2; cases g3; cases hθ
  rw [inj (eq_of_heq he)]


set_option maxHeartbeats 4000000 in
private theorem hmod_fields' {B B' : Base} (q : B'.toPre = B.toPre) {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'}
    {w : ColW B f T} {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt}
    (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i')
    {S : (w.st Z).toD7.what₂.Tau → SPar} {S' : (w'.st Z').toD7.what₂.Tau → SPar}
    (M : Formalism.IndefR.Mult.DSModel (Wc (w.st Z).toD7 i) S) (M' : Formalism.IndefR.Mult.DSModel (Wc (w'.st Z').toD7 i') S')
    (a : HEq M'.H M.H) (b : HEq M'.nacg M.nacg) (c : HEq M'.ips M.ips) (d : HEq M'.σ M.σ) (l : HEq M'.lam M.lam) (e : HEq M'.ε M.ε)
    (g : HEq M'.fr M.fr) (X : HMod (Formalism.IndefR.Mult.MMap M)) (X' : HMod (Formalism.IndefR.Mult.MMap M')) (hX : HEq X' X) :
    (X'.H = X.H ∧ HEq X'.nH X.nH ∧ HEq X'.iH X.iH) ∧
      @Eq Type (Bridge.Gf (Vc (w'.st Z').toD7 i')) (Bridge.Gf (Vc (w.st Z).toD7 i)) := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  cases M
  cases M'
  dsimp only at a b c d l e g
  cases a; cases b; cases c; cases d; cases l; cases e; cases g
  have e' : X' = X := eq_of_heq hX
  subst e'
  exact ⟨⟨rfl, HEq.rfl, HEq.rfl⟩, rfl⟩

private theorem theta_jL {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (i : Fin D.R.m) (t : T)
    (h : R.phs i = 1) (x : A3.A.fam.amb.FL i t) :
    HEq ((R.toCx3 F).θ' i t ((R.toCx3 F).jL i t x)) (R.thG i t (R.jV i t x)) := by
  have e : Links.cj (twAt D.what₂.embLL A3.A.v0) (R.phs i) • R.thG i t (R.jV i t x) = R.thG i t (R.jV i t x) :=
    (congrArg (· • R.thG i t (R.jV i t x)) ((congrArg (Links.cj (twAt D.what₂.embLL A3.A.v0)) h).trans (map_one _))).trans (one_smul ℂ _)
  exact (by with_unfolding_all exact ((heq_of_eq e) :))


set_option maxHeartbeats 4000000 in
private theorem thG_extN {B B' : Base} (q : B'.toPre = B.toPre) {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'}
    {w : ColW B f T} {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok}
    {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl} {z : Dat (w.st Z) w.I hX T Wt} {z' : Dat (w'.st Z') w'.I hX' T' Wt'}
    (hE : ExtN z z') (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m) (hj : (j : ℕ) = j') (x) (x')
    (hx : HEq (z'.R.B.jL j' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) x')
      (z.R.B.jL j (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) x)) :
    HEq (z'.R.thG j' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) (z'.R.jV j' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) x'))
      (z.R.thG j (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) (z.R.jV j (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) x)) := by
  letI := z.alg
  letI := z'.alg
  have hM := hE.MW j j' hj
  have h0 := hmod_fields' q j j' hj _ _ hM.1 hM.2.1 hM.2.2.1 hM.2.2.2.1 hM.2.2.2.2.1 hM.2.2.2.2.2.1 hM.2.2.2.2.2.2.1 _ _
    hM.2.2.2.2.2.2.2.2.1
  have s := (sgAt_mk _ z.R.hv0).symm
  have s' := (sgAt_mk _ z'.R.hv0).symm
  have key : ∀ σ σ', (w.st Z).toD7.what₂.embLL = σ → (w'.st Z').toD7.what₂.embLL = σ' →
      (z'.R.HW j' σ').H = (z.R.HW j σ).H ∧ HEq (z'.R.HW j' σ').nH (z.R.HW j σ).nH ∧ HEq (z'.R.HW j' σ').iH (z.R.HW j σ).iH :=
    fun σ σ' h h' => h ▸ h' ▸ h0.1
  have g := key _ _ s s'
  have hr := hE.ref j j' hj
  have m := z.pins.char.base.models
  have m' := z'.pins.char.base.models
  have he := HEq.trans (heq_of_eq (m'.jV j' _ x')) (HEq.trans hx (heq_of_eq (m.jV j _ x)).symm)
  exact app_heq h0.2 (hE.BV j j' hj).1 (hE.cV j j' hj).1 (hE.cV j j' hj).2 hr.2.1 (m.HV j _).1 g.1 g.2.1 g.2.2 hr.2.2.2.1 he

end GlobalTheory.Mem.R3.LiftLatBC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extendedData_lift_blockDatum_baseChange_one_matrix : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ (e : _ ≃* _) (C : Matrix (Fin ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.dim) (Fin ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.dim) (w'.st Z').toD7.what₂.LL),
          GlobalTheory.Mem.R3.LiftLatBC.BlockBaseChangeAt φ e ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0)
            ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.lvlA z.F.P0 z.F.ψ0) ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.lvlA z'.F.P0 z'.F.ψ0)
            ((zsOf z.R z.F).Zl j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) ((zsOf z'.R z'.F).Zl j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0) C ∧
          ∀ f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms,
            HEq ((z'.R.toCx3 z'.F).θ' j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0 ((z'.R.toCx3 z'.F).jL j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0 (GlobalTheory.Mem.R3.LiftLatBC.bcF φ _ _ C f)))
              ((z.R.toCx3 z.F).θ' j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0 ((z.R.toCx3 z.F).jL j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0 f))) := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine StepW.trans (StepW.and (GlobalTheory.T.typePrimeFiniteGroup_eq_extendedData h1 h2 h3 h4 h5 h6 h7) (StepW.and (GlobalTheory.T.baseLevelLift_extendedData_eq_map_smallerField h1 h2 h3 h4 h5 h6 h7)
    (StepW.and (GlobalTheory.T.goodCharacters_extendedData_eq_map_smallerData h1 h2 h3 h4 h5 h6 h7) (StepW.and (GlobalTheory.T.exists_semilinearFormsLift_sameComplexValues h1 h2 h3 h4 h5 h6 h7) (StepW.and (GlobalTheory.T.liftForms_referenceTuple_basis_extended h1 h2 h3 h4 h5 h6 h7)
    (StepW.and (GlobalTheory.T.formsLift_extendedData_carries_classSum h1 h2 h3 h4 h5 h6 h7) (StepW.and (GlobalTheory.T.formsLift_extendedData_intertwines_finiteGroup h1 h2 h3 h4 h5 h6 h7) (StepW.and (GlobalTheory.T.integralForms_referenceTuple_extension_span h1 h2 h3 h4 h5 h6 h7)
    (GlobalTheory.T.liftSubspace_extendedData_eq_span_smallerLifts h1 h2 h3 h4 h5 h6 h7))))))))) (StepW.of_all ?_)
  intro K B' f' T' w' _ _ H B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ
  obtain ⟨Hg, Hl, Hx, HL, Hb, Hc, Ha, Hn, Hs⟩ := H
  obtain ⟨e, he⟩ := Hg B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ
  obtain ⟨hP, hψ⟩ := Hl B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ e he
  have hXg := Hx B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ e he
  obtain ⟨L, hL, hC⟩ := HL B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ
  obtain ⟨hli, hsp⟩ := Hb B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ L hL hC
  have hcs := Hc B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ L hL hC
  have hac := Ha B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ e he L hL hC
  have hnb := Hn B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ L hL hC
  have hsb := Hs B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ L hL hC
  obtain ⟨C, hCL, c1, c2, c3, c4, c5⟩ := GlobalTheory.Mem.R3.LiftLatBC.forms_of_semilinear_at φ e _ _ _ _ L hL hli hsp hcs hac hnb hsb
  refine ⟨e, C, ⟨c1, c2, c3, c4, c5, hXg, hP, hψ⟩, fun x => ?_⟩
  letI := z.alg
  letI := z'.alg
  have hj0 := hExt.jL j j' hj (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))
    (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1)) _ _ (hC x)
  have hj1 : HEq (z'.R.B.jL j' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))) ((by with_unfolding_all exact ((L x) :))))
      (z.R.B.jL j (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) ((by with_unfolding_all exact (x :)))) :=
    HEq.trans (heq_of_eq (congrArg _ ((by with_unfolding_all exact ((LinearEquiv.apply_symm_apply (Formalism.L2.Col.GSD.res (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)) (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))) ((by with_unfolding_all exact ((L x) :)))).symm :)))))
      (HEq.trans hj0 (heq_of_eq (congrArg _ ((by with_unfolding_all exact ((LinearEquiv.apply_symm_apply (Formalism.L2.Col.GSD.res (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)) (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))) ((by with_unfolding_all exact (x :)))) :))))))
  have h2 := GlobalTheory.Mem.R3.LiftLatBC.thG_extN hE.1 hExt j j' hj _ _ hj1
  refine HEq.trans (heq_of_eq (congrArg (fun y => (z'.R.toCx3 z'.F).θ' j' _ ((z'.R.toCx3 z'.F).jL j' _ y)) (hCL x))) ?_
  refine HEq.trans (GlobalTheory.Mem.R3.LiftLatBC.theta_jL z'.R z'.F j' _ (z'.pins.phs j') _) (HEq.trans ?_ (GlobalTheory.Mem.R3.LiftLatBC.theta_jL z.R z.F j _ (z.pins.phs j) _).symm)
  exact (by with_unfolding_all exact (h2 :))
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockDatumBaseChangeDefiniteLatticeCompatible
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockDatumBaseChangeDefiniteLatticeCompatible
noncomputable section

namespace GlobalTheory.Mem.R3.LiftLatBC

open Module NumberField _root_.Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.Mem.R3.DefLatBC
open scoped Matrix

theorem tl_bcF_of_blockBCAt : ∀ {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K']
  {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 Pl0' : Type}
  (φ : K →+* K'), (∀ x : K, φ (star x) = star (φ x)) → ∀ (e : G ≃* G') (B : Formalism.L2.DIV.BlockDat K G Pl0) (B' : Formalism.L2.DIV.BlockDat K' G' Pl0')
    (ℓ : Formalism.L2.DIV.Lvl K G) (ℓ' : Formalism.L2.DIV.Lvl K' G') (Z : Submodule K B.S.Forms) (Z' : Submodule K' B'.S.Forms) (s : ℕ)
    (C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K'), B.Ok s → GlobalTheory.Mem.R3.LiftLatBC.BlockBaseChangeAt φ e B B' ℓ ℓ' Z Z' C →
    ∃ Gm : Matrix (Fin (B'.dZ ℓ' Z')) (Fin (B.dZ ℓ Z)) K', Function.Bijective Gm.mulVec ∧
      B'.Tl ℓ' Z' = Submodule.span (𝓞 K') ((fun x : Fin (B.dZ ℓ Z) → K => Matrix.mulVec Gm (fun k => φ (x k))) '' (B.Tl ℓ Z : Set (Fin (B.dZ ℓ Z) → K))) ∧
      ∀ x : Fin (B.dZ ℓ Z) → K, B'.toF ℓ' Z' (Matrix.mulVec Gm fun k => φ (x k)) = GlobalTheory.Mem.R3.LiftLatBC.bcF φ B B' C (B.toF ℓ Z x) := by
  intro K K' _ _ _ _ _ _ G G' _ _ _ _ Pl0 Pl0' φ hφ e B B' ℓ ℓ' Z Z' s C _ h
  obtain ⟨hC, hH, hact, hnab, hZ, hX, hP, hψ⟩ := h
  obtain ⟨X', P', ψ'⟩ := ℓ'
  dsimp only at hX hP hψ
  subst hP
  obtain ⟨m, b, F, hF, hI, hb⟩ := GlobalTheory.Mem.R3.DefLatBC.exists_dual_family φ
  have hc : Nat.card (ℓ.P.map e.toMonoidHom) = Nat.card ℓ.P :=
    (Nat.card_congr (ℓ.P.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm
  have hl := lvlIdem_baseChange φ e B.S B.r B'.S B'.r C hact ℓ.P ℓ.ψ ψ' hψ
  have hg : B'.S.gaMat B'.r (goodAt X' (ℓ.P.map e.toMonoidHom) ψ') * C = C * (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ)).map φ := by
    unfold goodAt
    rw [(group_action_matrix_hom K' B'.S G' B'.r).2, (group_action_matrix_hom K B.S G B.r).2, Matrix.mul_assoc, hl, ← Matrix.mul_assoc,
      idemOf_baseChange φ e B.S B.r B'.S B'.r C hact ℓ.X X' hX, Matrix.map_mul, Matrix.mul_assoc]
  set ℓ' : Lvl K' G' := ⟨X', ℓ.P.map e.toMonoidHom, ψ'⟩ with hℓ'
  obtain ⟨A0, hA0, hE0⟩ := subE_baseChange φ C hC.1 _ _ (range_baseChange φ C hC.2 C _ _ hl)
  obtain ⟨A1, hA1, hE1⟩ := subE_baseChange φ C hC.1 _ _ (range_baseChange φ C hC.2 C _ _ hg)
  change B'.S.lvlE B'.r ℓ'.P ℓ'.ψ * A0 = C * (B.S.lvlE B.r ℓ.P ℓ.ψ).map φ at hE0
  change B'.vE ℓ' * A1 = C * (B.vE ℓ).map φ at hE1
  have hZ0 : B'.Z0 ℓ' Z' = Submodule.span K' ((fun x : Fin (B.nV ℓ) → K => A1 *ᵥ (fun k => φ (x k))) '' (B.Z0 ℓ Z : Set _)) :=
    comap_baseChange (R := K) (R' := K') φ (fun i => algebraMap (𝓞 K') K' (b i)) F hF (fun i a => ⟨F i a, rfl⟩) hb
      C hC.1 A1 hA1.2 _ _ hE1 _ _ hZ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  obtain ⟨Gm, hGm, hE2⟩ := subE_baseChange φ A1 hA1.1 _ _ hZ0
  change B'.zE ℓ' Z' * Gm = A1 * (B.zE ℓ Z).map φ at hE2
  have hvPr : B'.vPr ℓ' * C = A1 * (B.vPr ℓ).map φ := orthPr_baseChange φ hφ C A1 hA1 _ _ hH _ _ hE1
  have hHV : A1ᴴ * B'.HV ℓ' * A1 = (B.HV ℓ).map φ := by
    have h1 := gram_baseChange φ hφ C A1 _ _ hH _ _ hE1
    change A1ᴴ * ((Nat.card (ℓ.P.map e.toMonoidHom) : K')⁻¹ • ((B'.vE ℓ')ᴴ * B'.S.H * B'.vE ℓ')) * A1 =
      ((Nat.card ℓ.P : K)⁻¹ • ((B.vE ℓ)ᴴ * B.S.H * B.vE ℓ)).map φ
    rw [Matrix.mul_smul, Matrix.smul_mul, h1, hc]
    generalize (B.vE ℓ)ᴴ * B.S.H * B.vE ℓ = M
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, map_natCast]
  have hPq : B'.Pq ℓ' Z' * A1 = Gm * (B.Pq ℓ Z).map φ := orthPr_baseChange φ hφ A1 Gm hGm _ _ hHV _ _ hE2
  have hlPr : B'.lPr ℓ' Z' * A0 = Gm * (B.lPr ℓ Z).map φ := by
    unfold BlockDat.lPr
    rw [Matrix.mul_assoc, hE0, Matrix.mul_assoc, ← Matrix.mul_assoc (B'.vPr ℓ'), hvPr, Matrix.mul_assoc A1,
      ← Matrix.mul_assoc (B'.Pq ℓ' Z'), hPq, Matrix.map_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  have hN : B'.S.lvlNab B'.r ℓ'.P ℓ'.ψ = Submodule.span (𝓞 K')
      ((fun x : Fin (B.S.lvlDim B.r ℓ.P ℓ.ψ) → K => A0 *ᵥ (fun k => φ (x k))) '' (B.S.lvlNab B.r ℓ.P ℓ.ψ : Set _)) :=
    comap_baseChange (R := 𝓞 K) (R' := 𝓞 K') φ b F hF hI hb
      C hC.1 A0 hA0.2 _ _ hE0 _ _ hnab _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  refine ⟨Gm, hGm, ?_, fun x => ?_⟩
  · unfold BlockDat.Tl matLat
    rw [hN]
    exact map_baseChange φ A0 Gm _ _ hlPr _
  · have hv : B'.vE ℓ' *ᵥ (B'.zE ℓ' Z' *ᵥ (Gm *ᵥ fun k => φ (x k))) =
        C *ᵥ fun k => φ ((B.vE ℓ *ᵥ (B.zE ℓ Z *ᵥ x)) k) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hE2, ← Matrix.mul_assoc, hE1,
        Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.mulVec_mulVec, map_mulVec', ← Matrix.mulVec_mulVec]
    simp only [BlockDat.toF, bcF, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rw [hv]

end GlobalTheory.Mem.R3.LiftLatBC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockDatumBaseChangeDefiniteLatticeCompatibleStatement
open NumberField
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockDatum_baseChange_definiteLattice_compatible : ∀ {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K']
  {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 Pl0' : Type}
  (φ : K →+* K'), (∀ x : K, φ (star x) = star (φ x)) → ∀ (e : G ≃* G') (B : Formalism.L2.DIV.BlockDat K G Pl0) (B' : Formalism.L2.DIV.BlockDat K' G' Pl0')
    (ℓ : Formalism.L2.DIV.Lvl K G) (ℓ' : Formalism.L2.DIV.Lvl K' G') (Z : Submodule K B.S.Forms) (Z' : Submodule K' B'.S.Forms) (s : ℕ)
    (C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K'), B.Ok s → GlobalTheory.Mem.R3.LiftLatBC.BlockBaseChangeAt φ e B B' ℓ ℓ' Z Z' C →
    ∃ Gm : Matrix (Fin (B'.dZ ℓ' Z')) (Fin (B.dZ ℓ Z)) K', Function.Bijective Gm.mulVec ∧
      B'.Tl ℓ' Z' = Submodule.span (𝓞 K') ((fun x : Fin (B.dZ ℓ Z) → K => Matrix.mulVec Gm (fun k => φ (x k))) '' (B.Tl ℓ Z : Set (Fin (B.dZ ℓ Z) → K))) ∧
      ∀ x : Fin (B.dZ ℓ Z) → K, B'.toF ℓ' Z' (Matrix.mulVec Gm fun k => φ (x k)) = GlobalTheory.Mem.R3.LiftLatBC.bcF φ B B' C (B.toF ℓ Z x) := by
  first | exact @GlobalTheory.Mem.R3.LiftLatBC.tl_bcF_of_blockBCAt | exact GlobalTheory.Mem.R3.LiftLatBC.tl_bcF_of_blockBCAt | (intros; apply GlobalTheory.Mem.R3.LiftLatBC.tl_bcF_of_blockBCAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteLiftLatticeBaseChangeExtendedData
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.LiftLatBC


set_option maxHeartbeats 4000000 in
theorem lift_lattice_bc : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ N : Matrix (Fin (((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).dZ j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0)) (Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0)) (w'.st Z').toD7.what₂.LL, Function.Bijective N.mulVec ∧
          (((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).Tl j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0) = Submodule.span (𝓞 (w'.st Z').toD7.what₂.LL) ((fun x : Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) → (w.st Z).toD7.what₂.LL => Matrix.mulVec N fun k => φ (x k)) '' ((((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) : Set (Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) → (w.st Z).toD7.what₂.LL))) ∧
          ∀ x : Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) → (w.st Z).toD7.what₂.LL, HEq ((z'.R.toCx3 z'.F).tC z'.F.cr false j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0 (Formalism.IndefR.Cx.cpt (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.base3.v0.embedding (Matrix.mulVec N fun k => φ (x k)))) ((z.R.toCx3 z.F).tC z.F.cr false j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0 (Formalism.IndefR.Cx.cpt (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.base3.v0.embedding x))) := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine StepW.trans (GlobalTheory.T.extendedData_lift_blockDatum_baseChange_one_matrix h1 h2 h3 h4 h5 h6 h7) (StepW.of_all fun K B' f' T' w' _ _ hQ => ?_)
  intro B f T w hE hf hP hpx Z hX Wt z hG hGA hFine hL Z' hX' hG' hGA' hV z' hFine' hExt j j' hj φ hφ
  obtain ⟨e, C, hC, hθ⟩ := hQ B f T w hE hf hP hpx Z hX Wt z hG hGA hFine hL Z' hX' hG' hGA' hV z' hFine' hExt j j' hj φ hφ
  have hstar : ∀ x, φ (star x) = star (φ x) := fun x => (w'.st Z').toD7.what₂.embLL.injective (by
    rw [hφ, (w.st Z).toD7.starLL_cx, (w'.st Z').toD7.starLL_cx, hφ])
  obtain ⟨N, hN, hTl, hF⟩ := GlobalTheory.T.blockDatum_baseChange_definiteLattice_compatible φ hstar e _ _ _ _ _ _ 1 C (hL.ok.ok2.lifts j _) hC
  refine ⟨N, hN, hTl, fun x => ?_⟩
  refine HEq.trans (heq_of_eq (tC_cpt (z'.R.toCx3 z'.F) z'.F.cr false j' _ _)) (HEq.trans ?_ (heq_of_eq (tC_cpt (z.R.toCx3 z.F) z.F.cr false j _ x)).symm)
  have e1 : z'.F.cr.toL (z'.R.toCx3 z'.F).zs false j' _ (Matrix.mulVec N fun k => φ (x k)) =
      GlobalTheory.Mem.R3.LiftLatBC.bcF φ _ _ C (z.F.cr.toL (z.R.toCx3 z.F).zs false j _ x) := hF x
  exact HEq.trans (heq_of_eq (congrArg (fun y => (z'.R.toCx3 z'.F).θ' j' _ ((z'.R.toCx3 z'.F).jL j' _ y)) e1)) (hθ _)

end GlobalTheory.Mem.R3.LiftLatBC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteLiftLatticeBaseChangeExtendedDataStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteLiftLattice_baseChange_extendedData : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ N : Matrix (Fin (((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).dZ j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0)) (Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0)) (w'.st Z').toD7.what₂.LL, Function.Bijective N.mulVec ∧
          (((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).Tl j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0) = Submodule.span (𝓞 (w'.st Z').toD7.what₂.LL) ((fun x : Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) → (w.st Z).toD7.what₂.LL => Matrix.mulVec N fun k => φ (x k)) '' ((((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) : Set (Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) → (w.st Z).toD7.what₂.LL))) ∧
          ∀ x : Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) → (w.st Z).toD7.what₂.LL, HEq ((z'.R.toCx3 z'.F).tC z'.F.cr false j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0 (Formalism.IndefR.Cx.cpt (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.base3.v0.embedding (Matrix.mulVec N fun k => φ (x k)))) ((z.R.toCx3 z.F).tC z.F.cr false j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0 (Formalism.IndefR.Cx.cpt (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.base3.v0.embedding x))) := by
  first | exact @GlobalTheory.Mem.R3.LiftLatBC.lift_lattice_bc | exact GlobalTheory.Mem.R3.LiftLatBC.lift_lattice_bc | (intros; apply GlobalTheory.Mem.R3.LiftLatBC.lift_lattice_bc <;> assumption)
end
