module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalHeckeOperatorsAdelicReading
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricFrameEqRiemannFormAtInteriorPoint
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HypothesesX
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTied
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section
namespace GlobalTheory.HeightCounting.Up.RealOfReading

open _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef _root_.Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie

def realOfRead {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A3.A Ks) (F : Face D A3.A) {X0 : BaseLevelRowSide D} (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R F X0)
    {cf : CharFrame D} {nch : NChoice D} (tp : TupTied D cf nch) (hC : R.C = cf) (Xd : DivX D) (E : EigIdx D Xd)
    (labPi : E.Pi → A3.A.fam.base.Ix) (hbase : R.BaseW F)
    (htup : ∀ μ, Used0 D μ → R.toLevCh.xiH (Y.tupT μ) = tp.xi μ) (hg : GlobalTheory.LiftRows.Given R F) (hf : R.FullP) :
    GlobalTheory.NJoin.RealAt D cf nch tp where
  G := G
  Pl0 := Pl0
  T := T
  A := A3.A
  Ks := Ks
  R := R
  F := F
  tupT := Y.tupT
  hm := Y.hm
  hTop := Y.hTop
  hinj := Y.hinj
  X0 := X0
  Ish := Y.Ish
  I0 := Y.Iz
  IL := Y.IL
  K := Y.Kc
  Xd := Xd
  E := E
  labPi := labPi
  PY := Y.PY
  PW := Y.PW
  eFT := Y.eFT
  piOf := fun _ _ _ => 0
  ι := Y.ιW
  Tp := hC.symm ▸ tp
  cfEq := hC
  tpEq := by subst hC; rfl
  recR := by
    subst hC
    exact ⟨hbase, Y.tied, Y.prtE, Y.prtE0, Y.prtWE, Y.xi, htup,
      fun w => by rw [Y.muAt w, Y.tupT_tup], Y.isomFin, Y.frameMatch⟩
  given := hg
  full := hf

end GlobalTheory.HeightCounting.Up.RealOfReading
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompOfOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CenFrame

section Local

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

abbrev Os (s : ReciprocityTheory.Aut.SplitPlace L) : Type := ↥(s.v.adicCompletionIntegers (maximalRealSubfield L))

structure IsResidue (s : ReciprocityTheory.Aut.SplitPlace L) {k : Type} [CommRing k] (φ : Os s →+* k) : Prop where
  surj : Function.Surjective φ
  ker : ∀ x : Os s, φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield L)) < 1

def IsCompOf (s : ReciprocityTheory.Aut.SplitPlace L) (κ : Formalism.AUTREP.GAf L n) (y : GL (Fin n) (Os s)) : Prop :=
  ∀ a c, ((y.val a c : Os s) : s.v.adicCompletion (maximalRealSubfield L)) = (s.loc n κ).val a c

end Local

def colMat {k : Type} [CommRing k] {n : ℕ} (v : Fin n → k) (m : Fin n) : Matrix (Fin n) (Fin n) k :=
  1 + Matrix.vecMulVec v (Pi.single m 1)

variable {D : D7}

def FrameRed {V : HSp D} {n : ℕ} (hn : V.rank = n) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D))
    (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : Os s →+* kP s.w) (b : GL (Fin n) (kP s.w)) : Prop :=
  ∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E n, ∀ y, IsCompOf s κ y → ∀ a c : Fin n,
    (redFn β s.w (finE V (P.ψ κ))).val (Fin.cast hn.symm a) (Fin.cast hn.symm c) =
      (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val a c

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A3.A Ks} {F : Face D A3.A} {X0 : BaseLevelRowSide D}

def CenRead (Y : R3.Read (A3 := A3) R F X0) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) : Prop :=
  ∀ (i : Fin D.R.m) (t : T) (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) (a : MonoidAlgebra D.what₂.LL G),
    (∀ g, D.what₂.embLL (a.coeff g) = (z : MonoidAlgebra ℂ (G0g D.nd)).coeff ((R.eG.trans cG) g)) → ∀ x,
      D.ntypes.cenMt (Y.tup t) ((i : ℕ) + 1) z (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x)) =
        D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (((A3.A.fam.L i t).S.lvlOp (A3.A.fam.L i t).r (A3.A.fam.lvlA F.P0 F.ψ0).P
          (A3.A.fam.lvlA F.P0 F.ψ0).ψ a).mulVec x))

end GlobalTheory.CenFrame

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CenterEqSum
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.CenLocAt

def avgC {G : Type} [Group G] [Fintype G] (g : G) : MonoidAlgebra ℂ G :=
  ((Fintype.card G : ℂ)⁻¹) • ∑ h : G, MonoidAlgebra.of ℂ G (h * g * h⁻¹)

theorem center_eq_sum {G : Type} [Group G] [Fintype G] (z : MonoidAlgebra ℂ G)
    (hz : z ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G)) : z = ∑ g : G, z.coeff g • avgC g := by
  rw [Subalgebra.mem_center_iff] at hz
  have h1 : ∀ h : G, MonoidAlgebra.of ℂ G h * z * MonoidAlgebra.of ℂ G h⁻¹ = z := by
    intro h
    rw [hz, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  have h2 : z = ∑ g : G, z.coeff g • MonoidAlgebra.of ℂ G g := by
    conv_lhs => rw [← MonoidAlgebra.sum_coeff_single z]
    rw [Finsupp.sum_fintype _ _ (by simp)]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single']
  have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  calc z = (Fintype.card G : ℂ)⁻¹ • ∑ h : G, MonoidAlgebra.of ℂ G h * z * MonoidAlgebra.of ℂ G h⁻¹ := by
        simp only [h1, Finset.sum_const, Finset.card_univ]
        rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = ∑ g : G, z.coeff g • avgC g := by
        conv_lhs => rw [h2]
        simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, avgC, Finset.smul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun h _ => ?_
        rw [← map_mul, ← map_mul, smul_comm]

theorem avgC_mem {G : Type} [Group G] [Fintype G] (g : G) : avgC g ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G) := by
  rw [Subalgebra.mem_center_iff]
  intro b
  induction b using MonoidAlgebra.induction_on with
  | of x =>
    simp only [avgC, mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, ← map_mul]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulLeft x) _ _ fun h => by simp [mul_assoc]
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

def avgK (K : Type) [Field K] {G : Type} [Group G] [Fintype G] (g : G) : MonoidAlgebra K G :=
  ((Fintype.card G : K)⁻¹) • ∑ h : G, MonoidAlgebra.of K G (h * g * h⁻¹)

theorem avgK_coeff {K : Type} [Field K] {G H : Type} [Group G] [Fintype G] [Group H] [Fintype H] (σ : K →+* ℂ) (e : G ≃* H)
    (g y : G) : σ ((avgK K g).coeff y) = (avgC (e g)).coeff (e y) := by
  simp only [avgK, avgC, MonoidAlgebra.of_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single,
    Finsupp.smul_apply, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply, smul_eq_mul, map_mul, map_inv₀,
    map_natCast, map_sum, apply_ite, map_one, map_zero]
  rw [Fintype.card_congr e.toEquiv]
  congr 1
  refine Fintype.sum_equiv e.toEquiv _ _ fun h => ?_
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, ← map_mul, ← map_inv]
  classical
  rw [Finsupp.single_apply, Finsupp.single_apply]
  by_cases hy : h * g * h⁻¹ = y
  · rw [if_pos hy, if_pos (congrArg e hy), map_one]
  · rw [if_neg hy, if_neg (fun h' => hy (e.injective h')), map_zero]

theorem lin_center {G W : Type} [Group G] [Fintype G] [AddCommGroup W] [Module ℂ W]
    (Φ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ G)) →ₗ[ℂ] W) (v : G → W)
    (h : ∀ g₁, Φ ⟨avgC g₁, avgC_mem g₁⟩ = ∑ g₀, (avgC g₁).coeff g₀ • v g₀)
    (z : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ G))) :
    Φ z = ∑ g₀, (z : MonoidAlgebra ℂ G).coeff g₀ • v g₀ := by
  have hz : z = ∑ g₁, (z : MonoidAlgebra ℂ G).coeff g₁ •
      (⟨avgC g₁, avgC_mem g₁⟩ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ G))) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [SetLike.val_smul]
    exact center_eq_sum _ z.2
  conv_lhs => rw [hz]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul, h, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g₀ _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  conv_rhs => rw [center_eq_sum _ z.2]
  simp [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_smul, Finsupp.coe_finsetSum, Finset.sum_apply]

theorem avgK_comm (K : Type) [Field K] {G : Type} [Group G] [Fintype G] (g : G) (b : MonoidAlgebra K G) :
    b * avgK K g = avgK K g * b := by
  induction b using MonoidAlgebra.induction_on with
  | of x =>
    simp only [avgK, mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, ← map_mul]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulLeft x) _ _ fun h => by simp [mul_assoc]
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

theorem avgK_conj (K : Type) [Field K] {G : Type} [Group G] [Fintype G] (g c y : G) :
    (avgK K g).coeff (c * y * c⁻¹) = (avgK K g).coeff y := by
  classical
  simp only [avgK, MonoidAlgebra.of_apply]
  simp only [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single,
    Finsupp.smul_apply, Finsupp.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
  congr 1
  refine (Fintype.sum_equiv (Equiv.mulLeft c) _ _ fun h => ?_).symm
  rw [Finsupp.single_apply, Finsupp.single_apply]
  refine if_congr ⟨fun e => ?_, fun e => ?_⟩ rfl rfl
  · rw [← e]; simp [mul_assoc]
  · have e' : c * (h * g * h⁻¹) * c⁻¹ = c * y * c⁻¹ := by rw [← e]; simp [mul_assoc]
    exact mul_left_cancel (mul_right_cancel e')

theorem actSum_apply (D : D7) {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (L : G0g D.nd → Formalism.AUTREP.GAf D.host.E n)
    (z : MonoidAlgebra ℂ (G0g D.nd)) (f : Formalism.AUTREP.GAf D.host.E n → W) (g : Formalism.AUTREP.GAf D.host.E n) :
    GlobalTheory.PendOf.actSum D L z f g = ∑ g₀ : G0g D.nd, z.coeff g₀ • f (g * L g₀) := by
  unfold GlobalTheory.PendOf.actSum
  rw [Finsupp.sum_fintype _ _ (by intros; simp)]
  simp only [Finset.sum_apply, Pi.smul_apply]
  rfl

section Rows

open _root_.Formalism.L2.DIV _root_.Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.RecTie

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)

def ratForm (k : Fin D.R.m) (s : T) (x : Fin (lDim D A3.A F.lv2.P0 F.lv2.ψ0 k s) → D.what₂.LL) : D.what₂.Mt (Y.tup s) ((k : ℕ) + 1) :=
  D.what₂.jMt (Y.tup s) ((k : ℕ) + 1) (Y.eMt k s x)


variable (F) in
def lvlAct (k : Fin D.R.m) (s : T) (a : MonoidAlgebra D.what₂.LL G) (x : Fin (lDim D A3.A F.lv2.P0 F.lv2.ψ0 k s) → D.what₂.LL) :
    Fin (lDim D A3.A F.lv2.P0 F.lv2.ψ0 k s) → D.what₂.LL :=
  ((A3.A.fam.L k s).S.lvlOp (A3.A.fam.L k s).r (A3.A.fam.lvlA F.lv2.P0 F.lv2.ψ0).P (A3.A.fam.lvlA F.lv2.P0 F.lv2.ψ0).ψ a).mulVec x

def adForm (μ : D.what₂.Tup) (h : Used0 D μ) (k : Fin D.R.m) :
    D.what₂.Mt μ ((k : ℕ) + 1) →ₗ[ℂ] (GA D (Vc D k) → (R.cV k).W) where
  toFun x := (Y.IL.jMt μ h k x).1
  map_add' x y := by rw [map_add (f := _)]; rfl
  map_smul' c x := by rw [map_smul]; rfl

def CenRat : Prop :=
  ∀ (s : T) (k : Fin D.R.m) (z : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) (a : MonoidAlgebra D.what₂.LL G),
    (∀ g, D.what₂.embLL (a.coeff g) = (z : MonoidAlgebra ℂ (G0g D.nd)).coeff ((R.eG.trans cG) g)) →
    ∀ x, D.ntypes.cenMt (Y.tup s) ((k : ℕ) + 1) z (ratForm Y k s x) = ratForm Y k s (lvlAct F k s a x)

def ActRead : Prop :=
  ∀ (s : T) (h : Used0 D (Y.tup s)) (k : Fin D.R.m) (a : MonoidAlgebra D.what₂.LL G), (∀ b, b * a = a * b) →
    ∀ κ : G → GA D (Vc D k), (∀ g, Lev.IsLevelLift (Vc D k) (R.βV k) (R.datVt k s) (R.eG g) (κ g)) →
    ∀ x y, adForm Y (Y.tup s) h k (ratForm Y k s (lvlAct F k s a x)) y =
      ∑ g : G, (D.what₂.embLL (a.coeff g) * (Lev.levChi (Vc D k) (R.βV k) (Lev.flagL (R.datVt k s)) (κ g))⁻¹) •
        adForm Y (Y.tup s) h k (ratForm Y k s x) (y * κ g)

def FrameAt (k : Fin D.R.m) (P : principalLevelFrame.RowPsi (Vc D k) D.R.nV) (s : T) : Prop :=
  ∃ L : G0g D.nd → Formalism.AUTREP.GAf D.host.E D.R.nV, GlobalTheory.PendOf.IsTypeGroupBlockLift D D.R.nV L ∧
    (Nontrivial (D.what₂.Mt (Y.tup s) ((k : ℕ) + 1)) → ∃ c : G, ∀ g : G,
      Lev.IsLevelLift (Vc D k) (R.βV k) (R.datVt k s) (R.eG g) (P.ψ (L ((R.eG.trans cG) (c * g * c⁻¹)))) ∧
      Lev.levChi (Vc D k) (R.βV k) (Lev.flagL (R.datVt k s)) (P.ψ (L ((R.eG.trans cG) (c * g * c⁻¹)))) = 1)


set_option maxHeartbeats 1000000 in
theorem cenLoc_of (M : MtFam D) (ad : MtAd Y M) (h1 : CenRat Y cG) (h2 : ActRead Y)
    (h3 : ∀ (i : D.nd.Loc) (s : T) (k : Fin D.R.m), Y.tup s = D.nd.mu i → FrameAt Y cG k (ad.PV k) s) : CenLoc D M := by
  intro i
  suffices H : ∀ μ, Used0 D μ → ∀ (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ D.R.m),
      (∀ (s : T) (k : Fin D.R.m), Y.tup s = μ → FrameAt Y cG k (ad.PV k) s) →
      ∃ L : G0g D.nd → Formalism.AUTREP.GAf D.host.E D.R.nV, GlobalTheory.PendOf.IsTypeGroupBlockLift D D.R.nV L ∧
        ∀ (z : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) (x : D.what₂.Mt μ j),
          (M μ j hj1 hj2).real (D.ntypes.cenMt μ j z x) =
            GlobalTheory.PendOf.actSum D L (z : MonoidAlgebra ℂ (G0g D.nd)) ((M μ j hj1 hj2).real x) from
    H _ (Model.used_loc i) _ (D.nd.j_range i).1 (D.nd.j_range i).2 (h3 i)
  intro μ hμ j hj1 hj2 h3
  obtain ⟨k, rfl⟩ : ∃ k : Fin D.R.m, j = (k : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  obtain ⟨s, rfl⟩ : ∃ s, Y.tup s = μ := ⟨_, Y.tupTie μ hμ⟩
  obtain ⟨L, hL, hc⟩ := h3 s k rfl
  refine ⟨L, hL, fun z x => funext fun g => ?_⟩
  rw [actSum_apply]
  rcases subsingleton_or_nontrivial (D.what₂.Mt (Y.tup s) ((k : ℕ) + 1)) with h0 | h0
  · rw [Subsingleton.elim x 0]; simp
  obtain ⟨c, hc⟩ := hc h0
  have key : ∀ g₁ : G0g D.nd,
      adForm Y (Y.tup s) hμ k (D.ntypes.cenMt (Y.tup s) ((k : ℕ) + 1) ⟨avgC g₁, avgC_mem g₁⟩ x) ((ad.PV k).ψ g) =
        ∑ g₀ : G0g D.nd, (avgC g₁).coeff g₀ • adForm Y (Y.tup s) hμ k x ((ad.PV k).ψ (g * L g₀)) := by
    intro g₁
    have tie : ∀ y, D.what₂.embLL ((avgK D.what₂.LL ((R.eG.trans cG).symm g₁)).coeff y) = (avgC g₁).coeff ((R.eG.trans cG) y) :=
      fun y => by rw [avgK_coeff D.what₂.embLL (R.eG.trans cG), MulEquiv.apply_symm_apply]
    let F1 : D.what₂.Mt (Y.tup s) ((k : ℕ) + 1) →ₗ[ℂ] (R.cV k).W :=
      (LinearMap.proj ((ad.PV k).ψ g)).comp ((adForm Y (Y.tup s) hμ k).comp
        (D.ntypes.cenMt (Y.tup s) ((k : ℕ) + 1) ⟨avgC g₁, avgC_mem g₁⟩))
    let F2 : D.what₂.Mt (Y.tup s) ((k : ℕ) + 1) →ₗ[ℂ] (R.cV k).W :=
      { toFun := fun y => ∑ g₀ : G0g D.nd, (avgC g₁).coeff g₀ • adForm Y (Y.tup s) hμ k y ((ad.PV k).ψ (g * L g₀))
        map_add' := fun y y' => by simp only [map_add (f := _), Pi.add_apply, smul_add, Finset.sum_add_distrib]
        map_smul' := fun c y => by
          simp only [map_smul, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
          exact Finset.sum_congr rfl fun _ _ => smul_comm _ _ _ }
    have hb := (D.what₂.jMt_basis (Y.tup s) ((k : ℕ) + 1)
      (Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (Y.tup s) ((k : ℕ) + 1)))).2
    have hF : F1 = F2 := by
      refine LinearMap.ext_on_range hb (fun b => ?_)
      obtain ⟨x', hx'⟩ := (Y.eMt k s).surjective (Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (Y.tup s) ((k : ℕ) + 1)) b)
      rw [← hx']
      show adForm Y (Y.tup s) hμ k (D.ntypes.cenMt (Y.tup s) ((k : ℕ) + 1) ⟨avgC g₁, avgC_mem g₁⟩ (ratForm Y k s x'))
        ((ad.PV k).ψ g) = ∑ g₀ : G0g D.nd, (avgC g₁).coeff g₀ • adForm Y (Y.tup s) hμ k (ratForm Y k s x') ((ad.PV k).ψ (g * L g₀))
      rw [h1 s k ⟨avgC g₁, avgC_mem g₁⟩ _ tie x', h2 s hμ k _ (avgK_comm _ _) _ (fun y => (hc y).1) x']
      refine Fintype.sum_equiv ((MulAut.conj c).toEquiv.trans (R.eG.trans cG).toEquiv) _ _ fun y => ?_
      rw [(hc y).2, inv_one, mul_one, ← avgK_conj _ _ c y, tie, ← map_mul]
      rfl
    exact LinearMap.congr_fun hF x
  apply (ad.eW _ hμ k).injective
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ad.read, map_sum]
  let Φ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) →ₗ[ℂ] (R.cV k).W :=
    { toFun := fun z' => adForm Y (Y.tup s) hμ k (D.ntypes.cenMt (Y.tup s) ((k : ℕ) + 1) z' x) ((ad.PV k).ψ g)
      map_add' := fun y y' => by simp only [map_add (f := _), LinearMap.add_apply, Pi.add_apply]
      map_smul' := fun c y => by simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply] }
  refine (lin_center Φ (fun g₀ => adForm Y (Y.tup s) hμ k x ((ad.PV k).ψ (g * L g₀))) key z).trans ?_
  refine Finset.sum_congr rfl fun g₀ _ => ?_
  rw [map_smul, ad.read]
  rfl

end Rows

end GlobalTheory.CenLocAt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGreenCuspidalLabellingSameGenerators
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGreenCuspidalLabellingSameGenerators
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.GreenSide

open Polynomial

theorem eSerC_eq_of_gen (hG : GlobalTheory.Published.GreenCuspidal) (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g)
    (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y)
    (z : ℕ → Formalism.CyclotomicNorms.Fbar g) (hz : IsGenSys z) (he : z = L.gen) (htL : t = L.teich)
    (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) (convC t ht z hz))
    (hO : ∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) (ZMod g))), 1 ≤ d → CategoryTheory.Simple τ →
      Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) τ → Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel (convC t ht z hz) τ (O.lab d τ))
    (r : ℕ) (f : (ZMod g)[X]) (hr : 1 ≤ r) : GlobalTheory.GLq.eSerC L r f = eSerO O r f := by
  subst he
  exact GlobalTheory.T.greenSeriesIdempotent_eq_classFunctionIdempotent hG g L t ht hz htL O hO r f hr

theorem exists_greenLab : GlobalTheory.Published.GreenCuspidal → ∀ (D : D7) (cf : CharFrame D) (Γ : GrpSide D), TypesTrue D.ntypes cf.P cf.W → (∀ k, Γ.ζ k = @GlobalTheory.GLq.LabelDatum.gen _ ⟨D.host.g_prime k⟩ (@GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩)) → ∃ Γ' : GrpSide D, GlobalTheory.PendOf.GreenLab Γ' ∧ ∀ k, Γ'.ζ k = Γ.ζ k := by
  intro hG D cf Γ hT hζ
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  have key : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      ∃ O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k))
          (convC (D.ntypes.teichC k) (D.ntypes.teichC_inj k) (Γ.ζ k) (Γ.ζ_gen k)),
        Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O ∧ LabTwLawO O ∧
        (∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) (ZMod (D.host.g k)))), 1 ≤ d → CategoryTheory.Simple τ →
          Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod (D.host.g k)) τ →
          Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel (convC (D.ntypes.teichC k) (D.ntypes.teichC_inj k) (Γ.ζ k) (Γ.ζ_gen k)) τ
            (O.lab d τ)) ∧
        ∀ f, D.ntypes.eSer k f = eSerO O D.R.r f := by
    intro k
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    obtain ⟨O, h1, h2, hO⟩ := GlobalTheory.CuspTwist.exists_labelMap_twist_cuspLabel (ZMod (D.host.g k)) _
      (GlobalTheory.T.cuspParam_of_greenParametrisation hG (D.host.g k) (D.ntypes.teichC k) (D.ntypes.teichC_inj k) (Γ.ζ k) (Γ.ζ_gen k))
    exact ⟨O, h1, h2, hO, fun f => (hT.ser k f).trans
      (eSerC_eq_of_gen hG _ _ _ _ _ _ (hζ k) (hT.teich k) O hO D.R.r f hr)⟩
  refine ⟨{ Γ with
    O := fun k => (key k).choose
    eSer_def := fun k f => (key k).choose_spec.2.2.2 f
    O_equiv := fun k => (key k).choose_spec.1
    O_tw := fun k => (key k).choose_spec.2.1 }, ?_, fun _ => rfl⟩
  intro k d
  exact (key k).choose_spec.2.2.1 d

end GlobalTheory.GreenSide

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGreenCuspidalLabellingSameGeneratorsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_green_cuspidal_labelling_same_generators : GlobalTheory.Published.GreenCuspidal → ∀ (D : D7) (cf : CharFrame D) (Γ : GrpSide D), TypesTrue D.ntypes cf.P cf.W → (∀ k, Γ.ζ k = @GlobalTheory.GLq.LabelDatum.gen _ ⟨D.host.g_prime k⟩ (@GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩)) → ∃ Γ' : GrpSide D, GlobalTheory.PendOf.GreenLab Γ' ∧ ∀ k, Γ'.ζ k = Γ.ζ k := by
  first | exact @GlobalTheory.GreenSide.exists_greenLab | exact GlobalTheory.GreenSide.exists_greenLab | (intros; apply GlobalTheory.GreenSide.exists_greenLab <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneLabelsAllPlacesOfFixedAndConj
section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPlacesOverOfIsConjPl
noncomputable section

namespace GlobalTheory.HeightCounting.LabConjModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal _root_.Formalism.L2.Host NumberField IsDedekindDomain Polynomial
open GlobalTheory.WeilDeligne Pointwise

section General

variable {Ω : Type} [Field Ω]

variable {E : Type} [Field E] [NumberField E] [Algebra E Ω]

end General

section Host

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

def conjInt (H : Host R) : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv

theorem coe_conjInt (x : 𝓞 H.E) : ((conjInt H x : 𝓞 H.E) : H.E) = H.conj (x : H.E) := rfl

theorem isConjPl_iff {w w' : PlE H} : IsConjPl H w w' ↔ ∀ x, x ∈ w.asIdeal ↔ conjInt H x ∈ w'.asIdeal := by
  refine ⟨fun h x => h x _ (coe_conjInt x), fun h x y hy => ?_⟩
  have : y = conjInt H x := RingOfIntegers.ext (hy.trans (coe_conjInt x).symm)
  rw [this]; exact h x

theorem eq_of_isConjPl {w₀ w₁ w : PlE H} (h₀ : IsConjPl H w₀ w) (h₁ : IsConjPl H w₁ w) : w₀ = w₁ := by
  apply HeightOneSpectrum.ext
  ext x
  rw [isConjPl_iff.1 h₀, isConjPl_iff.1 h₁]

end Host


end GlobalTheory.HeightCounting.LabConjModel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneLabelsAllPlacesOfFixedAndConj
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.LabAllOf

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem labAll_of_labTrue_labConj : ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), LabTrue D T → LabConj D T →
    GlobalTheory.PendOf.LabAll D T := by
  intro D T hT hC
  have key : ∀ (k : Fin 2) (w : PlE D.host), ∃ γ : G D.host.E D.nd.Om,
      (∀ v, w = D.naut.plGw k v → γ = D.ntypes.tg k v) ∧
      ∀ v, IsConjPl D.host (D.naut.plGw k v) w → ∃ c : D.nd.Om ≃+* D.nd.Om,
        (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) ∧
        (∀ x, x ∈ D.nd.plOm.1 (D.naut.plGw k v) ↔ c x ∈ D.nd.plOm.1 w) ∧ (∀ x, γ (c x) = c (D.ntypes.tg k v x)) ∧
        ∀ a : D.naut.LP w, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
          D.naut.items₂ k w a = GlobalTheory.WeilDeligne.WD.lab (D.ntypes.teichC k) γ (T.e w a) := by
    intro k w
    by_cases h : ∃ v, IsConjPl D.host (D.naut.plGw k v) w
    · obtain ⟨v, hv⟩ := h
      obtain ⟨c, γ, h1, h2, h3, h4⟩ := hC k v w hv
      refine ⟨γ, fun v' e => absurd (e ▸ hv) (D.naut.plGw_nconj k v v'), fun v' hv' => ?_⟩
      obtain rfl : v = v' := D.naut.plGw_inj k (GlobalTheory.HeightCounting.LabConjModel.eq_of_isConjPl hv hv')
      exact ⟨c, h1, h2, h3, h4⟩
    · refine ⟨Function.extend (D.naut.plGw k) (D.ntypes.tg k) (fun _ => 1) w, fun v e => ?_,
        fun v hv => absurd ⟨v, hv⟩ h⟩
      rw [e]; exact (D.naut.plGw_inj k).extend_apply _ _ v
  choose γ h1 h2 using key
  refine ⟨γ, fun k v => h1 k _ v rfl, fun k v w' hw' => ?_, fun k w hw a => ?_⟩
  · obtain ⟨c, hc1, hc2, hc3, -⟩ := h2 k w' v hw'
    exact ⟨c, hc1, hc2, hc3⟩
  · obtain ⟨v, rfl | hv⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hw
    · rw [h1 k _ v rfl]; exact hT k v a
    · obtain ⟨c, -, -, -, h4⟩ := h2 k w v hv
      exact h4 a

end GlobalTheory.LabAllOf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneLabelsAllPlacesOfFixedAndConjStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDeligneLabels_all_places_of_fixed_and_conj : ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), LabTrue D T → LabConj D T → GlobalTheory.PendOf.LabAll D T := by
  first | exact @GlobalTheory.LabAllOf.labAll_of_labTrue_labConj | exact GlobalTheory.LabAllOf.labAll_of_labTrue_labConj | (intros; apply GlobalTheory.LabAllOf.labAll_of_labTrue_labConj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPlaceLocalIndex
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.HeightCounting.Up.LocEx

theorem exists_loc_of_thetaT {D : D7} {M : MtFam D} (T : NormalizedLocalCompatibility D M) {v : D.what₂.places.Pl} (hv : TwistedAt D v) {j : ℕ}
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hne : ∃ f, D.what₂.thetaT (D.what₂.muTw v) j f ≠ 0) :
    ∃ i : D.nd.Loc, D.nd.w i = v ∧ D.nd.j i = j := by
  obtain ⟨f, hf⟩ := hne
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw v) j)
  have hidx : Nonempty (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw v) j)) := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    have h3 := (D.what₂.jMt_basis (D.what₂.muTw v) j b).2
    rw [Set.range_eq_empty, Submodule.span_empty] at h3
    exact hf ((Submodule.mem_bot ℂ).1 (h3 ▸ Submodule.mem_top))
  obtain ⟨k⟩ := hidx
  haveI : Nontrivial (T.B.V j v) := ⟨⟨_, 0, (T.B.iV_basis j v b).1.ne_zero k⟩⟩
  haveI : Nontrivial (Formalism.L2.heckeAlg T.B j v) := inferInstance
  obtain ⟨I, hI⟩ := Ideal.exists_maximal (Formalism.L2.heckeAlg T.B j v)
  obtain ⟨i, hi, -⟩ := T.mx_all j v h1 h2 hv I hI
  obtain ⟨ej, ew⟩ := (D.nd.locs_mem _ _ _).1 hi
  exact ⟨i, ew, ej⟩

theorem thetaT_ne_of_lamTr {D : D7} {μ : D.what₂.Tup} {j : ℕ} {σ : D.what₂.FT} (hpos : 0 < DV.lamTr D μ j σ) :
    ∃ f ∈ D.what₂.isot j σ, D.what₂.thetaT μ j f ≠ 0 := by
  by_contra h
  push_neg at h
  have hT : D.what₂.thetaP μ j ∘ₗ D.what₂.thetaT μ j ∘ₗ ((D.what₂.isot j σ).starProjection : D.what₂.Mj j →ₗ[ℂ] D.what₂.Mj j) = 0 := by
    ext y
    simp [h _ ((D.what₂.isot j σ).starProjection_apply_mem y)]
  unfold DV.lamTr at hpos
  rw [hT, map_zero, Complex.zero_re, zero_div] at hpos
  exact lt_irrefl _ hpos

end GlobalTheory.HeightCounting.Up.LocEx

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodPlaceCuspidalType
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.HeightCounting.CuspOfParam

theorem goodRow_cuspidal : ∀ (D : D7) (Rw : RowSide D), Nonempty D.nd.Loc → (∀ i σ w, D.naut.locW i σ w = Rw.locR σ w) → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw → ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ → D.ntypes.cuspidal σ := by
  intro D Rw hLoc hW hG j hj1 hj2 σ hσ hgood
  obtain ⟨i⟩ := hLoc
  obtain ⟨π, hcsd, hralg, hsplit, -, -, -⟩ := hG j hj1 hj2 σ hσ hgood
  have hr : 1 ≤ D.R.r := by
    have := D.R.m_add_three_le_k
    simp only [Ranks.r]
    omega
  have hiso : ∀ w, Formalism.MainNotions.N.isoLoc D.nd D.naut [(⟨D.R.r, π, 1⟩ : Part D.naut.CG)] w = D.naut.locG π w := by
    intro w
    simp [Formalism.MainNotions.N.isoLoc, Formalism.MainNotions.N.spehLoc, D.naut.lpSum_zero, D.naut.lpTw_zero]
  have hpar : Formalism.MainNotions.N.HasParamW D.nd D.naut i σ [(⟨D.R.r, π, 1⟩ : Part D.naut.CG)] := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact ⟨hr, le_refl 1⟩
    · simp [Formalism.MainNotions.N.rankIso]
    · intro w hw
      rw [hiso w, hsplit w hw, hW i σ w]
  have h := D.bc_tie i σ _ hpar
    (by
      intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact hcsd)
    (by
      intro p hp τ
      simp only [List.mem_singleton] at hp
      subst hp
      obtain ⟨hnd, hz⟩ := (D.naut.ralg_def π).1 hralg τ
      refine ⟨hnd, fun z hz' => ?_⟩
      obtain ⟨n, hn⟩ := hz z hz'
      exact ⟨n, by rw [hn]; simp⟩)
  show D.ntypes.bc σ = {(D.R.r, 1)}
  rw [h]
  simp

end GlobalTheory.HeightCounting.CuspOfParam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHeckeAtZeroOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

namespace GlobalTheory.HeightCounting.RatSide.HeckeAtState

open Formalism.BasicNotions.TH Formalism.IndefR.Mult

theorem isDC_one' {G : Type} [Group G] (J : Subgroup G) : Formalism.IndefR.Bridge.IsDC J 1 {1} := by
  refine ⟨fun a ha => ⟨1, 1, by simpa using ha⟩, ?_⟩
  rintro g ⟨k, k', rfl⟩
  exact ⟨1, ⟨Finset.mem_singleton_self _, by simpa using J.mul_mem k.2 k'.2⟩, fun a ha => Finset.mem_singleton.1 ha.1⟩

theorem isHeckeAt_zero_one' {D : D7} (V : HSp D) {P : PlE D.host} (hP : Formalism.BasicNotions.IsSplitPl D.host P) :
    IsHeckeAt V P 0 1 := by
  obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt P ((GlobalTheory.HeckeTieCompare.isSplitPl_iff P).1 hP)
  obtain ⟨ϖ, h1, h2⟩ := SetLike.exists_of_lt (Ideal.pow_lt_self P.asIdeal P.ne_bot P.isPrime.ne_top 2 le_rfl)
  exact ⟨e, ϖ, he, h1, h2, GlobalTheory.HeckeParts.isHeckeElt_one V he.1 ϖ⟩

section
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem heckeScalar_eq (R : RealDat3 D A3 Ks) (i : Fin D.R.m) (P : PlE D.host) (k : ℕ) :
    GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.heckeScalar R.toRealDat i P k = hkNorm R i k P := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.heckeScalar, hkNorm, zpow_neg, zpow_natCast, inv_pow]
end

theorem heckeOn_one {D : D7} {V : HSp D} {S} (M : DSModel V S) (F : MMap M) : heckeOn M {1} F = F := by
  ext v g
  simp [heckeOn, postOn, heckeLin]

end GlobalTheory.HeightCounting.RatSide.HeckeAtState

namespace GlobalTheory.HeightCounting.RatSide.HeckeAtState

open Formalism.BasicNotions.TH Formalism.IndefR.Mult

section Gen
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


open Classical in
def famOf (R : RealDat3 D A3 Ks) (hq : ∀ i : Fin D.R.m, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke R.toRealDat i) (j : ℕ) (k : ℕ)
    (Pl : PlE D.host) : Module.End D.what₂.LL (Fin (R.nW (idxOf D j)) → D.what₂.LL) :=
  if h : k ≠ 0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.GoodPlace R.toRealDat Pl ∧ k ≤ D.R.r then
    Classical.choose (hq (idxOf D j) Pl h.2.1 k h.2.2)
  else 1

theorem famOf_zero (R : RealDat3 D A3 Ks) (hq : ∀ i : Fin D.R.m, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke R.toRealDat i) (j : ℕ)
    (Pl : PlE D.host) : famOf R hq j 0 Pl = 1 := by
  unfold famOf
  rw [dite_eq_right (fun h => h.1 rfl)]

theorem exists_heckeRd (R : RealDat3 D A3 Ks) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0)
    (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x) (Sb : Finset (PlE D.host))
    (hq : ∀ i : Fin D.R.m, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke R.toRealDat i)
    (hg : ∀ v : PlE D.host, IsSplitPl D.host v → v ∉ Sb → GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.GoodPlace R.toRealDat v) :
    ∃ hL' : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL ((ratDatR R cG kKs hk).WL j),
      StabC (ratDatR R cG kKs hk) hL' ∧ (∀ j Pl, hL' j 0 Pl = 1) ∧ HeckeRd R cG kKs hk Sb hL' := by
  refine ⟨famOf R hq, ?_, fun j Pl => famOf_zero R hq j Pl, ?_⟩
  · intro j _ _ k Pl y hy
    change famOf R hq j k Pl y ∈ (R.FW (idxOf D j)).WK
    unfold famOf
    split_ifs with h
    · exact (Classical.choose_spec (hq (idxOf D j) Pl h.2.1 k h.2.2)).2 y hy
    · exact hy
  · intro j k Pl α Rr _ _ hd y
    have hg' : GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.GoodPlace R.toRealDat Pl := hg Pl hd.split hd.offS
    by_cases hk0 : k = 0
    · subst hk0
      have hr := (Classical.choose_spec (hq (idxOf D j) Pl hg' 0 (Nat.zero_le _))).1
      have e1 := (GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.readAs_iff _ _ _ _ _ _).1 (hr Rr ⟨α, hd.elt, hd.reps⟩) y
      have e2 := (GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.readAs_iff _ _ _ _ _ _).1
        (hr {1} ⟨1, isHeckeAt_zero_one' _ hd.split, isDC_one' _⟩) y
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.heckeScalar_zero, one_smul] at e1 e2
      have e4 := (e2.trans (heckeOn_one _ _)).symm.trans e1
      have hn : hkNorm R (idxOf D j) 0 Pl = 1 := by simp [hkNorm]
      rw [famOf_zero, hn, one_smul]
      exact e4
    · have h : k ≠ 0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.GoodPlace R.toRealDat Pl ∧ k ≤ D.R.r := ⟨hk0, hg', hd.le⟩
      have e1 := (GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.readAs_iff _ _ _ _ _ _).1
        ((Classical.choose_spec (hq (idxOf D j) Pl h.2.1 k h.2.2)).1 Rr ⟨α, hd.elt, hd.reps⟩) y
      have h1 : famOf R hq j k Pl = Classical.choose (hq (idxOf D j) Pl h.2.1 k h.2.2) := by
        unfold famOf
        rw [dite_eq_left h]
      rw [h1, ← heckeScalar_eq]
      exact e1
end Gen

end GlobalTheory.HeightCounting.RatSide.HeckeAtState

namespace GlobalTheory.HeightCounting.RatSide.HeckeAtState

end GlobalTheory.HeightCounting.RatSide.HeckeAtState

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesRatOfSeriesRatS
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Mem.LiteralAutomorphy

namespace GlobalTheory.SerStdFit

theorem seriesRat_of_seriesRatS : GlobalTheory.SerStd.SeriesRatS → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat := fun h => h

end GlobalTheory.SerStdFit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOnBallOfEqOnPunctPolydiscCoveringExpImage
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOnBallOfEqOnPunctPolydiscCoveringExpImage
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem eq_on_ball_of_eq_on_logExp_image : ∀ (n a : ℕ) (ρ₁ : ℝ) (X : Type) [TopologicalSpace X] [T2Space X] (f h : (Fin n → ℂ) → X), ρ₁ ≤ 1 → ContinuousOn f (Metric.ball 0 ρ₁) → ContinuousOn h (Metric.ball 0 ρ₁) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → f (logExp a s) = h (logExp a s)) → ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, f z = h z := by
  intro n a ρ₁ X _ _ f h hρ hf hh hagree
  set U := Metric.ball (0 : Fin n → ℂ) ρ₁ with hUdef
  set D : Set (Fin n → ℂ) := {z | z ∈ U ∧ ∀ k : Fin n, (k:ℕ) < a → z k ≠ 0} with hDdef
  have hD : Set.EqOn f h D := by
    rintro z ⟨hzU, hz0⟩
    set s : Fin n → ℂ := fun k => if (k:ℕ) < a then Complex.log (z k) else z k with hsdef
    have hexp : logExp a s = z := by
      funext k
      simp only [logExp, s]
      split_ifs with hk
      · exact Complex.exp_log (hz0 k hk)
      · rfl
    have hz1 : ‖z‖ < ρ₁ := by simpa [U] using hzU
    have hnorm : ∀ k, ‖z k‖ < 1 := fun k =>
      lt_of_le_of_lt (norm_le_pi_norm z k) (lt_of_lt_of_le hz1 hρ)
    have hs : s ∈ logDom n a := by
      intro k
      simp only [s]
      split_ifs with hk
      · rw [Complex.log_re]
        exact Real.log_neg (norm_pos_iff.mpr (hz0 k hk)) (hnorm k)
      · exact hnorm k
    have := hagree s hs (by rw [hexp]; exact hzU)
    rwa [hexp] at this
  have hsub : U ⊆ closure D := by
    intro z hz
    let g : ℂ → (Fin n → ℂ) := fun t k => if (k:ℕ) < a then z k + t else z k
    have hg : Continuous g := by
      refine continuous_pi fun k => ?_
      by_cases hk : (k:ℕ) < a
      · simp only [g, hk, if_true]; fun_prop
      · simp only [g, hk, if_false]; fun_prop
    let T : Set ℂ := Set.range (fun k : Fin n => - z k)
    have hT : T.Finite := Set.finite_range _
    have hS : Dense (Set.univ \ T) := dense_univ.diff_finite hT
    have h0 : g 0 = z := by funext k; simp [g]
    have h1 : z ∈ closure (g '' (Set.univ \ T)) := by
      rw [← h0]
      exact image_closure_subset_closure_image hg
        (Set.mem_image_of_mem g (by rw [hS.closure_eq]; exact Set.mem_univ _))
    have h2 : U ∩ g '' (Set.univ \ T) ⊆ D := by
      rintro _ ⟨hU, t, ⟨-, htT⟩, rfl⟩
      refine ⟨hU, fun k hk => ?_⟩
      simp only [g, hk, if_true]
      intro heq
      exact htT ⟨k, by linear_combination -heq⟩
    exact closure_mono h2 (Metric.isOpen_ball.inter_closure ⟨hz, h1⟩)
  exact fun z hz => hD.of_subset_closure hf hh (fun x hx => hx.1) hsub hz

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOnBallOfEqOnPunctPolydiscCoveringExpImageStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eqOn_ball_of_eqOn_punctPolydiscCoveringExp_image : ∀ (n a : ℕ) (ρ₁ : ℝ) (X : Type) [TopologicalSpace X] [T2Space X] (f h : (Fin n → ℂ) → X), ρ₁ ≤ 1 → ContinuousOn f (Metric.ball 0 ρ₁) → ContinuousOn h (Metric.ball 0 ρ₁) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → f (logExp a s) = h (logExp a s)) → ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, f z = h z := by
  first | exact @GlobalTheory.eq_on_ball_of_eq_on_logExp_image | exact GlobalTheory.eq_on_ball_of_eq_on_logExp_image | (intros; apply GlobalTheory.eq_on_ball_of_eq_on_logExp_image <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadTw
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.RowTriple

open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal

def ReadTw (D : D7) (a : D.nd.Loc) : Prop :=
  ∃ (φ : FractionRing (D.ntw.O0 (D.ntw.twOf a)) →+* Qbar (D.ntw.l (D.ntw.twOf a)))
    (ι : Qbar (D.ntw.l (D.ntw.twOf a)) ≃+* ℂ),
    (∀ z : ℤ_[D.ntw.l (D.ntw.twOf a)], φ (algebraMap (D.ntw.O0 (D.ntw.twOf a)) _
        (algebraMap ℤ_[D.ntw.l (D.ntw.twOf a)] (D.ntw.O0 (D.ntw.twOf a)) z)) =
      algebraMap ℚ_[D.ntw.l (D.ntw.twOf a)] (Qbar (D.ntw.l (D.ntw.twOf a))) (z : ℚ_[D.ntw.l (D.ntw.twOf a)])) ∧
    (∀ x : ↥D.LL0, ι (φ ((if D.ntw.twSide a then D.ntw.emb0 (D.ntw.twOf a) else D.ntw.emb0b (D.ntw.twOf a)) x)) =
      embLL0 D x) ∧
    ∀ y : D.ntw.O0 (D.ntw.twOf a), ι (φ (algebraMap _ (FractionRing (D.ntw.O0 (D.ntw.twOf a))) y)) =
      iotaO D.nd D.naut a (D.ntw.twist₂ a y)

end GlobalTheory.RowTriple

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelFamilyBoundaryDivisor
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegChart

theorem isAdmissibleBase_of_completeNormalLocalCharZero {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] (hA : IsCN A) : LN.admitted A (maximalIdeal A) :=
  ⟨admissibleBase_of_completeNormalLocalCharZero hA, hA.2.2.1, hA.2.2.2, inferInstance, inferInstanceAs (IsIntegrallyClosed (ResidueField A))⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l}

end GlobalTheory.SiegChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MtInputOf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HeightCounting.JumpsSt

theorem mtInput_of {D : D7} {cf : CharFrame D} {M : MtFam D} {ch : NChoice D} (tp : TupTied D cf ch)
    {xi : D.what₂.Tup → HChar D.host.E} {Q : D.what₂.places.Pl → Finset (PlE D.host)}
    (h : MtInput D M (fun μ j => cf.mu0 j * xi μ) Q) (hx : tp.xi = xi) (hQ : ch.Q = Q) : MtInput D M tp.tup ch.Q := by
  subst hx hQ
  exact h


end GlobalTheory.HeightCounting.JumpsSt
end
end
