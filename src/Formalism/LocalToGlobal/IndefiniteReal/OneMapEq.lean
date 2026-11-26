module

public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
public import Formalism.LocalToGlobal.UnitaryNorms.CharTransport
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.Divisibility.LinkDIVL2R3Col

@[expose] public section

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
noncomputable section

open NumberField
open scoped TensorProduct

namespace Formalism.IndefR.FWT

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))

def phiAt (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (c : (T.U ((i : ℕ) + 1) σ).Comp → ℂ)
    (f : T.R ((i : ℕ) + 1)) : GA D (Wc D i) → ℂ :=
  castDict hV (adel (T.V ((i : ℕ) + 1) σ) (T.dict ((i : ℕ) + 1) σ)
    (muPin (T.V ((i : ℕ) + 1) σ) (T.dict ((i : ℕ) + 1) σ) (T.mu ((i : ℕ) + 1) σ) c) (rdU (T.U ((i : ℕ) + 1) σ) f))

def EqAt {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup) (σ : T.Q.c.F →+* ℂ)
    (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (c : (T.U ((i : ℕ) + 1) σ).Comp → ℂ) : Prop :=
  ∀ g k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k →
    ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n,
      actLev T.Q.c O.lev2 g f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n ∧
      ∃ y : T.Q.c.F, D.what₂.embLL (algebraMap T.Q.c.F D.what₂.LL y) =
          ∏ PP : R.Pg, ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g PP)) : ℂˣ) : ℂ) ∧
        ∀ h, phiAt T i σ hV c (actLev T.Q.c O.lev2 g f) h = σ y * phiAt T i σ hV c f (h * k)

def EquivAll (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) : Prop :=
  ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
    (∃ c', CUnit c' ∧ EqAt T R κ (O i) σ hV c') → EqAt T R κ (O i) σ hV (T.cE ((i : ℕ) + 1) σ)

variable (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))

def CTie (i : Fin D.R.m) : Prop :=
  OneMapRow0 T R κ v₀ O i → ∃ ph', (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph'

end Formalism.IndefR.FWT
end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.SpOfRwRange
open Module NumberField IsDedekindDomain
open scoped Matrix InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.BasicNotions Formalism.L2.Col Formalism.IndefR.Links

section Face

variable {Fl : Fields} {Pr : Primes Fl} {Rk : Ranks} (W : Wts Fl Pr.Word Rk) (Ch : Chars Fl Pr Rk.m)
  (sel : HeightOneSpectrum (𝓞 Fl.F) → HeightOneSpectrum (𝓞 Fl.E)) {Sg : Set ℕ}
  {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

end Face

section Sp

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

structure PerW (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word) where

  Dt : Set X.B.I.GA
  hD : IsReps X u Dt
  hin : InHH X u hK
  hlin : PuLinear X u hK Dt

  F : Formalism.L2.Forms.Forms0 D u

  Tr : Transport X u F
  hI : ColDictInto X Tr hK
  hB : ColDictBij X Tr hK

variable {X}

def PerW.op {hK : X.LevelSubgroupCharacter} {u : D.what₂.Word} (p : PerW X hK u) : (D.mem u).A.Mu0 →ₗ[ℂ] HHX X :=
  Formalism.L2.SG.PoincareInHH.PoincareSetting.Pu X u hK p.Dt p.hD p.hin p.hlin ∘ₗ (colDict X p.Tr hK p.hI p.hB).symm.toLinearMap

def ramCrd {u : D.what₂.Word} {n : ℕ} (bR : Fin n → (D.mem u).A.Mram) : (Fin n → ℂ) →ₗ[ℂ] (D.mem u).A.Mu0 :=
  Submodule.inclusion inf_le_left ∘ₗ Fintype.linearCombination ℂ bR

def cjVec (s : Bool) (n : ℕ) : (Fin n → ℂ) →ₛₗ[cj s] (Fin n → ℂ) where
  toFun φ i := cj s (φ i)
  map_add' φ ψ := by funext i; simp
  map_smul' a φ := by funext i; simp

def perTw (s : Bool) {n : ℕ} (f : (Fin n → ℂ) →ₗ[ℂ] HHX X) : (Fin n → ℂ) →ₗ[ℂ] Tw s (HHX X) :=
  Tw.semi (σ := cj s) (σ' := RingHom.id ℂ) s (fun a => (cj_cj s a).symm) (f.comp (cjVec s n))

def spOf (s : Bool) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} (Dc : DefCols Df) (hK : X.LevelSubgroupCharacter) (G : GoodOp X)
    (wdD : Dc.Mem → D.what₂.Word) (pw : ∀ x, PerW X hK (wdD x)) (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram) : SPer Dc where
  HH := Tw s (HHX X)
  nHH := inferInstance
  iHH := inferInstance
  Pu x := perTw s ((pw x).op ∘ₗ ramCrd (bR x))
  Rw := Tw.sub s ((goodSub X G).comap (HHX X).subtype)

section Facts

variable (s : Bool) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} (Dc : DefCols Df) (hK : X.LevelSubgroupCharacter) (G : GoodOp X)
  (wdD : Dc.Mem → D.what₂.Word) (pw : ∀ x, PerW X hK (wdD x)) (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram)

theorem spOf_Pu (x : Dc.Mem) (φ : Fin (Dc.a x) → ℂ) :
    Tw.out (s := s) ((spOf s Dc hK G wdD pw bR).Pu x φ) = (pw x).op (ramCrd (bR x) (cjVec s _ φ)) := rfl

end Facts

end Sp

section Seam


end Seam

section FaceSp

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}

end FaceSp

end Formalism.IndefR.Cx
end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.EvTieP
open Matrix
open scoped Matrix

noncomputable section

namespace Formalism.IndefR.Links.EvTie

open Formalism.L2.DIV Formalism.IndefR.Cx

section Block

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}

theorem dot_eq (S : CSD K) (u w : Fin S.dim → K) :
    S.csum (S.I u) (S.I w) = star u ⬝ᵥ S.H *ᵥ w := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [CSD.csum, CSD.I, CSD.H, LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply,
    Submodule.subtype_apply, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, map_sum,
    map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum,
    Finset.sum_mul, smul_eq_mul, starRingEnd_apply, RingHom.id_apply]
  conv_lhs => rw [Finset.sum_comm]; enter [2, j]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Fintype.sum_congr _ _ fun i => Fintype.sum_congr _ _ fun j => Fintype.sum_congr _ _ fun c => ?_
  rw [Pi.star_apply]
  ring

theorem proj_key (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms)
    (hdet : IsUnit (B.HZ ℓ Z).det) :
    ((B.vE ℓ * B.zE ℓ Z)ᴴ * B.S.H * B.vE ℓ) * (B.zE ℓ Z * B.Pq ℓ Z) =
      (B.vE ℓ * B.zE ℓ Z)ᴴ * B.S.H * B.vE ℓ := by
  have hc : (Nat.card ℓ.P : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hM : (B.vE ℓ)ᴴ * B.S.H * B.vE ℓ = (Nat.card ℓ.P : K) • B.HV ℓ := by
    simp only [BlockDat.HV, BlockDat.vE, CSD.goodPartHermitianForm, CSD.cutH, CSD.V0E, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hinv : B.HZ ℓ Z * (B.HZ ℓ Z)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  calc ((B.vE ℓ * B.zE ℓ Z)ᴴ * B.S.H * B.vE ℓ) * (B.zE ℓ Z * B.Pq ℓ Z)
      = (B.zE ℓ Z)ᴴ * ((B.vE ℓ)ᴴ * B.S.H * B.vE ℓ) * B.zE ℓ Z * B.Pq ℓ Z := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (Nat.card ℓ.P : K) • (B.HZ ℓ Z * (B.HZ ℓ Z)⁻¹ * ((B.zE ℓ Z)ᴴ * B.HV ℓ)) := by
        rw [hM]
        simp only [BlockDat.HZ, BlockDat.Pq, orthPr, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = (B.vE ℓ * B.zE ℓ Z)ᴴ * B.S.H * B.vE ℓ := by
        rw [hinv, Matrix.one_mul, Matrix.conjTranspose_mul,
          show (B.zE ℓ Z)ᴴ * (B.vE ℓ)ᴴ * B.S.H * B.vE ℓ = (B.zE ℓ Z)ᴴ * ((B.vE ℓ)ᴴ * B.S.H * B.vE ℓ) by
            simp only [Matrix.mul_assoc], hM, Matrix.mul_smul]

theorem dot_key (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (x : Fin (B.dZ ℓ Z) → K)
    (w : Fin (B.nV ℓ) → K) :
    star ((B.vE ℓ) *ᵥ ((B.zE ℓ Z) *ᵥ x)) ⬝ᵥ B.S.H *ᵥ ((B.vE ℓ) *ᵥ w) =
      star x ⬝ᵥ (((B.vE ℓ * B.zE ℓ Z)ᴴ * B.S.H * B.vE ℓ) *ᵥ w) := by
  rw [Matrix.mulVec_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem evTie_block (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms)
    (hdet : IsUnit (B.HZ ℓ Z).det) (x : Fin (B.dZ ℓ Z) → K) (y : Fin (B.nV ℓ) → K) :
    CSDForm.csumForm B.S (B.toF ℓ Z x) (B.S.basis.equivFun.symm ((B.vE ℓ) *ᵥ y)) =
      CSDForm.csumForm B.S (B.toF ℓ Z x) (B.toF ℓ Z ((B.Pq ℓ Z) *ᵥ y)) := by
  have key : ∀ a b : Fin B.S.dim → K, CSDForm.csumForm B.S (B.S.basis.equivFun.symm a)
      (B.S.basis.equivFun.symm b) = star a ⬝ᵥ B.S.H *ᵥ b := fun a b => dot_eq B.S a b
  have hT : ∀ v, B.toF ℓ Z v = B.S.basis.equivFun.symm (B.vE ℓ *ᵥ (B.zE ℓ Z *ᵥ v)) := fun v => rfl
  rw [hT, hT, key, key, dot_key, dot_key, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc ((B.vE ℓ * B.zE ℓ Z)ᴴ * B.S.H * B.vE ℓ), proj_key B ℓ Z hdet]

end Block

section Face

open Formalism.BasicNotions Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem evTie_of_det {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} (F : Face3 D A3) (X : CxData A3.fam3.amb3)
    (hdet : ∀ t, IsUnit ((A3.A.fam.R t).HZ (A3.A.fam.lvl F.P1 F.ψ1) (X.zs.Z t)).det) :
    X.EVTie F.cr F.cv (F.eV X.zs) := by
  refine ⟨fun t y => ⟨y, rfl⟩, fun t y x => ?_⟩
  exact evTie_block (A3.A.fam.R t) (A3.A.fam.lvl F.P1 F.ψ1) (X.zs.Z t) (hdet t) x y

end Face

section Ok

open Formalism.BasicNotions Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem evTie_of_ok {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {s : ℕ} (hOk : A3.fam3.Ok3 s) (F : Face3 D A3)
    (X : CxData A3.fam3.amb3) : X.EVTie F.cr F.cv (F.eV X.zs) :=
  evTie_of_det F X fun t =>
    BlockDat.HZ_det hOk.ok2.conj (hOk.ok2.what₂ t) (fun χ hχ => hOk.ok2.irr χ hχ)

theorem evTie_real {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (hOk : ∃ s, A3.fam3.Ok3 s) (R : RealDat3 D A3 Ks) (F : Face3 D A3) :
    (R.toCx3 F).EVTie F.cr F.cv (F.eV (R.toCx3 F).zs) := by
  obtain ⟨s, hs⟩ := hOk
  exact evTie_of_ok hs F (R.toCx3 F)

end Ok

end Formalism.IndefR.Links.EvTie

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Matrix IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.IndefR.Mult
open scoped TensorProduct ContDiff InnerProductSpace

namespace Formalism.IndefR.AutomorphicEvaluation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def ev (M : DSModel V S) (v₀ : M.Vec) : MMap M →ₗ[ℂ] (GA D V → ℂ) where
  toFun T := T v₀
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ev_apply (M : DSModel V S) (v₀ : M.Vec) (T : MMap M) : ev M v₀ T = T v₀ := rfl


end Formalism.IndefR.AutomorphicEvaluation

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.LinIndepOfOrth
noncomputable section

open NumberField IsDedekindDomain
open Formalism.L2.Theta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory
open scoped TensorProduct

namespace Formalism.IndefR.principalLevelFrame

section ConjIso

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def cj (f : Formalism.AUTREP.GAf L n → ℂ) : Formalism.AUTREP.GAf L n → ℂ := fun g => star (f g)

theorem cj_cj (f : Formalism.AUTREP.GAf L n → ℂ) : cj (cj f) = f := by
  funext g
  simp [cj]

theorem cj_add (f f' : Formalism.AUTREP.GAf L n → ℂ) : cj (f + f') = cj f + cj f' := by
  funext g
  simp [cj]

theorem cj_smul (a : ℂ) (f : Formalism.AUTREP.GAf L n → ℂ) : cj (a • f) = star a • cj f := by
  funext g
  simp [cj, mul_comm]

def toU {U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)} (f : conjSub U) : U := ⟨cj f.1, f.2⟩

def ofU {U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)} (u : U) : conjSub U :=
  ⟨cj u.1, by
    show cj (cj u.1) ∈ U
    rw [cj_cj]
    exact u.2⟩

def conjMap {U U' : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)} (T : U →ₗ[ℂ] U') : conjSub U →ₗ[ℂ] conjSub U' where
  toFun f := ofU (T (toU f))
  map_add' f f' := by
    have : toU (f + f') = toU f + toU f' := Subtype.ext (cj_add f.1 f'.1)
    apply Subtype.ext
    show cj ((T (toU (f + f')) : U') : Formalism.AUTREP.GAf L n → ℂ) =
      cj ((T (toU f) : U') : Formalism.AUTREP.GAf L n → ℂ) + cj ((T (toU f') : U') : Formalism.AUTREP.GAf L n → ℂ)
    rw [this, map_add (f := _), Submodule.coe_add, cj_add]
  map_smul' a f := by
    have : toU (a • f) = star a • toU f := Subtype.ext (cj_smul a f.1)
    apply Subtype.ext
    show cj ((T (toU (a • f)) : U') : Formalism.AUTREP.GAf L n → ℂ) = a • cj ((T (toU f) : U') : Formalism.AUTREP.GAf L n → ℂ)
    rw [this, map_smul, Submodule.coe_smul, cj_smul, star_star]

theorem toU_ofU {U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)} (u : U) : toU (ofU u) = u :=
  Subtype.ext (cj_cj u.1)

theorem conjT_iso {π π' : Formalism.L2.NG.FinTyp L n} (h : π.Iso π') : (FinTyp.conjT π).Iso (FinTyp.conjT π') := by
  obtain ⟨T, hT⟩ := h
  let E : conjSub π.S ≃ₗ[ℂ] conjSub π'.S :=
    { conjMap T.toLinearMap with
      invFun := conjMap T.symm.toLinearMap
      left_inv := fun f => by
        apply Subtype.ext
        show cj ((T.symm (toU (ofU (T (toU f)))) : π.S) : Formalism.AUTREP.GAf L n → ℂ) = f.1
        rw [toU_ofU, LinearEquiv.symm_apply_apply]
        exact cj_cj f.1
      right_inv := fun f => by
        apply Subtype.ext
        show cj ((T (toU (ofU (T.symm (toU f)))) : π'.S) : Formalism.AUTREP.GAf L n → ℂ) = f.1
        rw [toU_ofU, LinearEquiv.apply_symm_apply]
        exact cj_cj f.1 }
  refine ⟨E, fun h f f' hf => ?_⟩
  show cj ((T (toU f') : π'.S) : Formalism.AUTREP.GAf L n → ℂ) = Formalism.L2.NG.rt L n h (cj ((T (toU f) : π'.S) : Formalism.AUTREP.GAf L n → ℂ))
  have h1 : ((toU f' : π.S) : Formalism.AUTREP.GAf L n → ℂ) = Formalism.L2.NG.rt L n h ((toU f : π.S) : Formalism.AUTREP.GAf L n → ℂ) := by
    show cj f'.1 = Formalism.L2.NG.rt L n h (cj f.1)
    rw [hf]
    rfl
  rw [hT h _ _ h1]
  rfl

theorem not_iso_conjT {π π' : Formalism.L2.NG.FinTyp L n} (h : ¬ π.Iso π') : ¬ (FinTyp.conjT π).Iso (FinTyp.conjT π') := by
  intro hc
  apply h
  have := conjT_iso hc
  unfold Formalism.L2.NG.FinTyp.Iso at this ⊢
  rwa [conjT_S, conjT_S, conjT_S, conjT_S, conjSub_conjSub, conjSub_conjSub] at this

end ConjIso

section LinIndep

variable {A : Type} [AddCommGroup A] [Module ℂ A]

theorem hp_smul_right {C : Submodule ℂ A} {ip : A → A → ℂ} (hp : PeterssonHilbertSpace.IsHermPos C ip) (x y : C) (a : ℂ) :
    ip x (a • (y : A)) = a * ip x y := by
  have h1 := hp.herm x (a • y)
  have h2 := hp.smul a y x
  have h3 := hp.herm y x
  rw [Submodule.coe_smul] at h1
  calc ip x (a • (y : A)) = starRingEnd ℂ (starRingEnd ℂ (ip x (a • (y : A)))) := by simp
    _ = starRingEnd ℂ (ip (a • (y : A)) x) := by rw [h1]
    _ = starRingEnd ℂ (starRingEnd ℂ a * ip y x) := by rw [h2]
    _ = a * starRingEnd ℂ (ip y x) := by simp
    _ = a * ip x y := by rw [h3]

theorem linIndep_of_orth {C : Submodule ℂ A} {ip : A → A → ℂ} (hp : PeterssonHilbertSpace.IsHermPos C ip) {ι : Type} (x : ι → C)
    (hx : ∀ i, x i ≠ 0) (horth : ∀ i j, i ≠ j → ip (x i) (x j) = 0) : LinearIndependent ℂ x := by
  classical
  rw [linearIndependent_iff']
  intro s g hg j hj
  have h0 := congrArg (fun z : C => ip (x j) (z : A)) hg
  simp only [Submodule.coe_zero, Submodule.coe_sum] at h0
  rw [hp_zero_right hp, hp_sum_right hp (x j) s (fun i => g i • x i)] at h0
  have hterm : ∀ i ∈ s, ip (x j) ((g i • x i : C) : A) = if i = j then g j * ip (x j) (x j) else 0 := by
    intro i _
    rw [Submodule.coe_smul, hp_smul_right hp]
    split_ifs with hij
    · rw [hij]
    · rw [horth j i (Ne.symm hij), mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' s j, if_pos hj] at h0
  have hne : ip (x j) (x j) ≠ 0 := by
    intro h
    have := hp.pos (x j) (hx j)
    rw [h, Complex.zero_re] at this
    exact lt_irrefl _ this
  exact (mul_eq_zero.1 h0).resolve_right hne

end LinIndep

section Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {Y : Formalism.BasicNotions.TH.HSp D} {n : ℕ} {Sp : D.what₂.Tau → SPar}
variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))

theorem finite_FTR (P : RowPsi Y n) (M : Mult.DSModel Y Sp) (J : Bool → Set (GA D Y)) (χ : Bool → GA D Y → ℂ)
    (e : Bool → (GA D Y → ℂ) →ₗ[ℂ] (GA D Y → ℂ)) (μ : Bool → Measure (GA D Y)) (𝓕 : Bool → Set (GA D Y))
    (hD : ∀ b, IsotDecomp θ P M (J b) (χ b) (e b) (μ b) (𝓕 b))
    (hp : ∀ b, PeterssonHilbertSpace.IsHermPos (Mult.goodPart θ M (J b) (χ b) (e b)) (Mult.ipM M (μ b) (𝓕 b))) : Finite (FTR θ P M J χ e) := by
  classical
  have hfin : ∀ b, Finite {σ : FTR θ P M J χ e // isotE θ P M (J b) (χ b) (e b) (rowRepR θ σ) ≠ ⊥} := by
    intro b
    haveI := (hp b).fd
    let x : {σ : FTR θ P M J χ e // isotE θ P M (J b) (χ b) (e b) (rowRepR θ σ) ≠ ⊥} → Mult.goodPart θ M (J b) (χ b) (e b) :=
      fun σ => ⟨(Submodule.exists_mem_ne_zero_of_ne_bot σ.2).choose,
        ((Submodule.exists_mem_ne_zero_of_ne_bot σ.2).choose_spec.1).1⟩
    have hx0 : ∀ σ, x σ ≠ 0 := fun σ h0 =>
      (Submodule.exists_mem_ne_zero_of_ne_bot σ.2).choose_spec.2 (congrArg Subtype.val h0)
    have horth : ∀ σ σ', σ ≠ σ' → Mult.ipM M (μ b) (𝓕 b) (x σ) (x σ') = 0 := by
      intro σ σ' hne
      refine (hD b).2 _ _ (not_iso_conjT fun h => hne (Subtype.ext (rowRepR_inj θ σ.1 σ'.1 h))) _
        (Submodule.exists_mem_ne_zero_of_ne_bot σ.2).choose_spec.1 _ (Submodule.exists_mem_ne_zero_of_ne_bot σ'.2).choose_spec.1
    exact (linIndep_of_orth (hp b) x hx0 horth).finite
  have hcover : ∀ σ : FTR θ P M J χ e, ∃ b, isotE θ P M (J b) (χ b) (e b) (rowRepR θ σ) ≠ ⊥ := fun σ => rowRepR_occ θ σ
  have : Finite ((Σ b : Bool, {σ : FTR θ P M J χ e // isotE θ P M (J b) (χ b) (e b) (rowRepR θ σ) ≠ ⊥})) := by
    haveI := hfin true
    haveI := hfin false
    infer_instance
  exact Finite.of_surjective (fun p : (Σ b : Bool, {σ : FTR θ P M J χ e // isotE θ P M (J b) (χ b) (e b) (rowRepR θ σ) ≠ ⊥}) =>
    p.2.1) fun σ => by
      obtain ⟨b, hb⟩ := hcover σ
      exact ⟨⟨b, σ, hb⟩, rfl⟩

end Fin

end Formalism.IndefR.principalLevelFrame
end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.LinksComap
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}

end Formalism.L2.DIV

namespace Formalism.IndefR.Bridge

open Formalism.L2.Theta Formalism.L2.DIV Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.HermitianLatticesTheory Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {G : Type} [Group G] [Fintype G] {Pl0 T T' : Type} {m : ℕ}
  {A : FamIn D.what₂.LL G Pl0 T' m} {cR : CoefDat D D.sp.X'} {cL : ∀ i : Fin m, CoefDat D (D.sp.V ((i : ℕ) + 1))}
  {lR : ∀ t, LevEnv D D.sp.X' (A.ok t × ℕ)} {lL : ∀ (i : Fin m) t, LevEnv D (D.sp.V ((i : ℕ) + 1)) (A.ok t × ℕ)}

def FamReal.comap (B : FamReal D A cR cL lR lL) (f : T → T') (t0 : T) :
    FamReal D (A.comap f t0) cR cL (fun t => lR (f t)) (fun i t => lL i (f t)) where
  R t := B.R (f t)
  L i t := B.L i (f t)
  rankR := B.rankR
  rankL := B.rankL

theorem FamTie.comap {B : FamReal D A cR cL lR lL} {pl : Pl0 → Pl D.host.E} {S : Set (Pl D.host.E)}
    {Qt : T' → Finset (Pl D.host.E)} {tauL : D.what₂.Tau → (D.host.E →+* D.what₂.LL)}
    {lamR : D.what₂.Tau → DomWeight D.sp.X'.rank} {lamL : ∀ (i : Fin m), D.what₂.Tau → DomWeight (D.sp.V ((i : ℕ) + 1)).rank}
    {gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E}
    {c0R : VV D.what₂.LL lamR →ₛₗ[D.what₂.embLL] cR.W} {c0L : ∀ i : Fin m, VV D.what₂.LL (lamL i) →ₛₗ[D.what₂.embLL] (cL i).W}
    (h : FamTie B pl S Qt tauL lamR lamL gramR c0R c0L) (f : T → T') (t0 : T) :
    FamTie (B.comap f t0) pl S (fun t => Qt (f t)) tauL lamR lamL gramR c0R c0L :=
  { ranks := h.ranks
    v0 := h.v0
    tauL_ok := h.tauL_ok
    pl_inj := h.pl_inj
    q := h.q
    S_fin := h.S_fin
    ok t P := h.ok (f t) P
    gramR_eq := h.gramR_eq
    mapR := h.mapR
    mapL := h.mapL
    coefR t := h.coefR (f t)
    coefL i t := h.coefL i (f t) }

end Formalism.IndefR.Bridge

namespace Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Comap

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

def LevCh.comap {T T' : Type} (L : LevCh D T') (f : T → T') : LevCh D T where
  C := L.C
  xiH t := L.xiH (f t)
  mu0 := L.mu0
  eta := L.eta
  xi t := L.xi (f t)
  Pg := L.Pg
  Q t := L.Q (f t)
  chi := L.chi
  xiR t := L.xiR (f t)
  ΛY := L.ΛY
  ΛX := L.ΛX
  ΛV := L.ΛV
  ΛW := L.ΛW
  βY := L.βY
  βX := L.βX
  βV := L.βV
  βW := L.βW

theorem LevCh.comap_is {T T' : Type} {L : LevCh D T'} {μ0 : T'} (h : L.Is μ0) {f : T → T'} (hf : Function.Injective f) {t0 : T}
    (h0 : f t0 = μ0) : (L.comap f).Is t0 :=
  { mu0 := h.mu0
    eta := h.eta
    xi t := h.xi (f t)
    xi_inj := h.xi_inj.comp hf
    xi_base := by
      show L.xiH (f t0) = 1
      rw [h0]
      exact h.xi_base
    xi_fin t := h.xi_fin (f t)
    xi_triv t := h.xi_triv (f t)
    xi_tame t := h.xi_tame (f t)
    Pg := h.Pg
    Q_pl t := h.Q_pl (f t)
    Q_off t := h.Q_off (f t)
    Q_de p hp := by
      obtain ⟨P, hP⟩ := h.Q_de p hp
      exact ⟨P, fun t => hP (f t)⟩
    Q_ram t := h.Q_ram (f t)
    chi := h.chi
    xiR t := h.xiR (f t)
    βY := h.βY
    βX := h.βX
    βV := h.βV
    βW := h.βW }

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T T' : Type} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


set_option maxHeartbeats 2000000 in
def RealDat.comap {A : FamIn D.what₂.LL G Pl0 T' D.R.m} (R : RealDat D A Ks) (f : T → T') (t0 : T)
    (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T) (twPl : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) (FW : type_of% R.FW) (kap : ℝ)
    (lam : Fin D.R.m → T → (A.comap f t0).fam.base.Ix → InfinitePlace D.what₂.LL → ℝ) (err0 : type_of% R.err0) :
    RealDat D (A.comap f t0) Ks where
  toLevCh := R.toLevCh.comap f
  hv0 := R.hv0
  eG := R.eG
  pl := R.pl
  Sb := R.Sb
  θ := R.θ
  ψ := R.ψ
  MY := R.MY
  MX := R.MX
  MW := R.MW
  cX := R.cX
  cV := R.cV
  B := R.B.comap f t0
  prX := R.prX
  HX t := R.HX (f t)
  HV i t := R.HV i (f t)
  HE := R.HE
  HW := R.HW
  gE := R.gE
  gW := R.gW
  jX t := R.jX (f t)
  jV i t := R.jV i (f t)
  νY t := R.νY (f t)
  fdY t := R.fdY (f t)
  ν0 := R.ν0
  fd0 := R.fd0
  νX t := R.νX (f t)
  fdX t := R.fdX (f t)
  νV i t := R.νV i (f t)
  fdV i t := R.fdV i (f t)
  νW := R.νW
  fdW := R.fdW
  ωY t := R.ωY (f t)
  ωX t := R.ωX (f t)
  ωP i t := R.ωP i (f t)
  vac := R.vac
  vacX := R.vacX
  vacP := R.vacP
  vY t := R.vY (f t)
  vX t := R.vX (f t)
  vP i t := R.vP i (f t)
  ItY := R.ItY
  ItX := R.ItX
  ioY t := R.ioY (f t)
  ioX t := R.ioX (f t)
  Th t := R.Th (f t)
  BV := R.BV
  ioP := R.ioP
  thF i t := R.thF i (f t)
  thG i t := R.thG i (f t)
  nW := R.nW
  FW := FW
  mu := mu
  twPl := twPl
  kap := kap
  lam := lam
  err0 := err0

def RealDat3.comap {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T' D.R.m} (R : RealDat3 D A3 Ks) (f : T → T') (t0 : T)
    (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T) (twPl : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) (FW : type_of% R.FW) (kap : ℝ)
    (lam : Fin D.R.m → T → (A3.comap f t0).A.fam.base.Ix → InfinitePlace D.what₂.LL → ℝ) (err0 : type_of% R.err0)
    (phs : Fin D.R.m → ℂ) (lam3 : Fin D.R.m → T → (A3.comap f t0).fam3.base3.Ix → InfinitePlace D.what₂.LL → ℝ) :
    RealDat3 D (A3.comap f t0) Ks where
  toRealDat := R.toRealDat.comap f t0 mu twPl FW kap lam err0
  plI := R.plI
  SF := R.SF
  phs := phs
  lam3 := lam3


end Comap

end Formalism.IndefR.Links

namespace Formalism.L2.DIV

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.DivisionValues Formalism.L2.Indef

section ColComap

variable {X : Col.Fields} {Pr : Col.Primes X} {R : Ranks} (W : Col.Wts X Pr.Word R) (Ch : Col.Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)

end ColComap

end Formalism.L2.DIV

end
end
