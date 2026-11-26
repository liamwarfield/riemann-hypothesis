module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHorizontalVectorOfBreuilKisinJump
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletionFiltrationIffDeRhamFiltration

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFixedVectorFiltrationJumpBreuilKisin
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisTensorLatticeToDeRhamEquivariant
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisTensorLatticeToDeRhamEquivariant
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.BKGal.JumpDR

theorem cB_gal {l : ℕ} [Fact l.Prime] {Pl : LocPrime l} {AI : LocAinf l Pl} (Td : LocTied l Pl AI)
    (g : Gl l) (b : Per.Bcris l) :
    cB Td (Per.σB (sQ l g) b) = Pl.actQdR (sQ l g) (cB Td b) := by
  have h1 : Td.eB.symm (Per.σB (sQ l g) b) = Pl.actQ (sQ l g) (Td.eB.symm b) := by
    apply Td.eB.injective
    rw [RingEquiv.apply_symm_apply, Td.actB, RingEquiv.apply_symm_apply]
  have h2 := (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).ι_comm g (Td.eB.symm b)
  rw [Pl.PD_ι, Pl.PD_ι, Pl.PD_actB, Pl.PD_actdR] at h2
  change Pl.ιB (Td.eB.symm (Per.σB (sQ l g) b)) = Pl.actQdR (sQ l g) (Pl.ιB (Td.eB.symm b))
  rw [h1]; exact h2

theorem X_equivariant (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI)
    (LL : FinExt l) (T : QLat LL) (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)
    (hX : ∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T),
      X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b)
    (g : Gl l) (b : TW (OB l ↥(OL LL)) T) :
    X (actB (sQ l) T g b) = actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (X b) := by
  induction b using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add u v hu hv => simp only [map_add (f := _), hu, hv]
  | tmul u x =>
    induction u using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.zero_tmul, map_zero]
    | add u v hu hv => simp only [TensorProduct.add_tmul, map_add (f := _), hu, hv]
    | tmul o b =>
      have e1 : actB (sQ l) T g ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) =
          (o ⊗ₜ[ℤ_[l]] Per.σB (sQ l g) b) ⊗ₜ[↥(OL LL)] T.actT g x := rfl
      rw [e1, hX, hX]
      have e2 : ((T.actT g x : ↥T.L.T) : T.V) = T.ρ g (x : T.V) := rfl
      rw [e2, cB_gal]
      show _ = (T.ρ g ((o : ↥LL.1) • (x : T.V))) ⊗ₜ[ℚ_[l]] ((Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actdR g (cB Td b))
      rw [map_smul, Pl.PD_actdR]
      rfl

end GlobalTheory.BKGal.JumpDR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisTensorLatticeToDeRhamEquivariantStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.bcrisTensorLattice_to_deRham_equivariant : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (LL : FinExt l) (T : QLat LL) (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (g : Gl l) (b : TW (OB l ↥(OL LL)) T), X (actB (sQ l) T g b) = actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (X b) := by
  exact @GlobalTheory.BKGal.JumpDR.X_equivariant
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBcrisTensorLatticeToDeRhamMap
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBcrisTensorLatticeToDeRhamMap
set_option synthInstance.maxHeartbeats 400000

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.BKGal.CrisTensDR

variable {l : ℕ} [Fact l.Prime] {Pl : LocPrime l} {AI : LocAinf l Pl} (Td : LocTied l Pl AI)
  {LL : FinExt l} (T : QLat LL)

theorem coe_smul_lat (o : ↥(OL LL)) (x : ↥T.L.T) :
    ((o • x : ↥T.L.T) : T.V) = (o : ↥LL.1) • (x : T.V) := by
  rw [Submodule.coe_smul]
  exact (algebraMap_smul (↥LL.1) o (x : T.V)).symm

def gx (o : ↥(OL LL)) (b : Per.Bcris l) : ↥T.L.T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR :=
  AddMonoidHom.mk' (fun x => ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b)
    (fun x y => by
      simp only [Submodule.coe_add, smul_add, TensorProduct.add_tmul])

def gb (o : ↥(OL LL)) : Per.Bcris l →+ (↥T.L.T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR) :=
  AddMonoidHom.mk' (fun b => gx Td T o b)
    (fun b c => by
      ext x
      simp only [gx, AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add (f := _), TensorProduct.tmul_add])

def g : ↥(OL LL) →+ Per.Bcris l →+ (↥T.L.T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR) :=
  AddMonoidHom.mk' (fun o => gb Td T o)
    (fun o o' => by
      ext b x
      simp only [gb, gx, AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, Subalgebra.coe_add, add_smul,
        TensorProduct.add_tmul])

theorem cB_smul (z : ℤ_[l]) (b : Per.Bcris l) :
    GlobalTheory.BKGal.JumpDR.cB Td (z • b) = (z : ℚ_[l]) • GlobalTheory.BKGal.JumpDR.cB Td b := by
  rw [Algebra.smul_def, map_mul, GlobalTheory.BKGal.JumpDR.cB_algebraMap, ← Algebra.smul_def]

theorem zsmul_lat (z : ℤ_[l]) (o : ↥(OL LL)) (x : ↥T.L.T) :
    (((z • o : ↥(OL LL)) : ↥LL.1) • (x : T.V)) = (z : ℚ_[l]) • ((o : ↥LL.1) • (x : T.V)) := by
  show ((z : ℚ_[l]) • (o : ↥LL.1)) • (x : T.V) = _
  exact smul_assoc _ _ _

theorem g_balanced (z : ℤ_[l]) (o : ↥(OL LL)) (b : Per.Bcris l) : g Td T (z • o) b = g Td T o (z • b) := by
  ext x
  have h1 := congrArg (fun v => v ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) (zsmul_lat T z o x)
  have h2 := congrArg (fun w => ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] w) (cB_smul Td z b)
  exact h1.trans ((TensorProduct.smul_tmul _ _ _).trans h2.symm)

def f1 : OB l ↥(OL LL) →+ (↥T.L.T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR) :=
  TensorProduct.liftAddHom (g Td T) (g_balanced Td T)

theorem mul_smul_lat (o o' : ↥(OL LL)) (x : ↥T.L.T) :
    (((o * o' : ↥(OL LL)) : ↥LL.1) • (x : T.V)) = (o' : ↥LL.1) • ((o • x : ↥T.L.T) : T.V) := by
  rw [coe_smul_lat, smul_smul, Subalgebra.coe_mul, mul_comm]

theorem crisTensorDRLiftFromCoeffBcris_smul_comm (o : ↥(OL LL)) :
    (f1 Td T).comp (DistribSMul.toAddMonoidHom (OB l ↥(OL LL)) o) =
      (AddMonoidHom.compHom' (DistribSMul.toAddMonoidHom (↥T.L.T) o)).comp (f1 Td T) := by
  refine AddMonoidHom.ext fun u => ?_
  induction u using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul o' b =>
    refine AddMonoidHom.ext fun x => ?_
    show g Td T (o * o') b x = g Td T o' b (o • x)
    exact congrArg (fun v => v ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) (mul_smul_lat T o o' x)
  | add u v hu hv => exact (map_add _ u v).trans ((congrArg₂ (· + ·) hu hv).trans (map_add _ u v).symm)

theorem main : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (LL : FinExt l) (T : QLat LL), ∃ X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR, ∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b := by
  intro l _ Pl AI Td LL T
  exact ⟨TensorProduct.liftAddHom (f1 Td T) fun o u x =>
    DFunLike.congr_fun (DFunLike.congr_fun (crisTensorDRLiftFromCoeffBcris_smul_comm Td T o) u) x, fun o b x => rfl⟩

end GlobalTheory.BKGal.CrisTensDR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBcrisTensorLatticeToDeRhamMapStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.exists_bcrisTensorLattice_to_deRham_map : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (LL : FinExt l) (T : QLat LL), ∃ X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR, ∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b := by
  exact @GlobalTheory.BKGal.CrisTensDR.main
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffDeRhamPlusActionOnVTensorBdR
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffDeRhamPlusActionOnVTensorBdR
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.JumpDR


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem exists_odAction : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI)
    (LL : FinExt l) (T : QLat LL), ∃ A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR),
    ∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR),
      A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c) := by
  intro l _ Pl AI Td LL T
  let φ : ↥(OL LL) → T.V →ₗ[ℚ_[l]] T.V := fun o =>
    { toFun := fun v => (o : ↥LL.1) • v
      map_add' := fun v w => smul_add _ v w
      map_smul' := fun q v => by
        simp only [RingHom.id_apply]
        rw [← algebraMap_smul (↥LL.1) q v, ← algebraMap_smul (↥LL.1) q ((o : ↥LL.1) • v), smul_smul, smul_smul,
          mul_comm] }
  let F : ↥(OL LL) → Per.BdRp l → (T.V ⊗[ℚ_[l]] Pl.R.BdR →ₗ[ℚ_[l]] T.V ⊗[ℚ_[l]] Pl.R.BdR) := fun o b =>
    TensorProduct.map (φ o) (LinearMap.mulLeft ℚ_[l] (cD Td b))
  have hF : ∀ o b v c, F o b (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (cD Td b * c) := fun o b v c => rfl
  have hb : ∀ o b b', F o (b + b') = F o b + F o b' := fun o b b' => by
    apply TensorProduct.ext'
    intro v c
    rw [LinearMap.add_apply, hF, hF, hF, map_add (f := _), add_mul, tmul_add]
  have ho : ∀ o o' b, F (o + o') b = F o b + F o' b := fun o o' b => by
    apply TensorProduct.ext'
    intro v c
    rw [LinearMap.add_apply, hF, hF, hF, Subalgebra.coe_add, add_smul, add_tmul]
  let f : ↥(OL LL) →+ Per.BdRp l →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR) :=
    AddMonoidHom.mk' (fun o => AddMonoidHom.mk' (fun b => (F o b).toAddMonoidHom)
      (fun b b' => AddMonoidHom.ext fun x => by
        show F o (b + b') x = F o b x + F o b' x
        rw [hb]; rfl))
      (fun o o' => AddMonoidHom.ext fun b => AddMonoidHom.ext fun x => by
        show F (o + o') b x = F o b x + F o' b x
        rw [ho]; rfl)
  have hbal : ∀ (z : ℤ_[l]) (o : ↥(OL LL)) (b : Per.BdRp l), f (z • o) b = f o (z • b) := by
    intro z o b
    apply AddMonoidHom.ext
    intro x
    show F (z • o) b x = F o (z • b) x
    congr 1
    apply TensorProduct.ext'
    intro v c
    rw [hF, hF, Algebra.smul_def z b, map_mul, cD_algebraMap, mul_assoc, ← Algebra.smul_def,
      ← TensorProduct.smul_tmul (R := ℚ_[l])]
    congr 1
    show ((z : ℚ_[l]) • (o : ↥LL.1)) • v = (z : ℚ_[l]) • ((o : ↥LL.1) • v)
    rw [smul_assoc]
  refine ⟨TensorProduct.liftAddHom f hbal, fun o b v c => ?_⟩
  rw [TensorProduct.liftAddHom_tmul]
  rfl

end GlobalTheory.BKGal.JumpDR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffDeRhamPlusActionOnVTensorBdRStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coeffDeRhamPlus_action_on_VTensorBdR : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (LL : FinExt l) (T : QLat LL), ∃ A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), ∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c) := by
  first | exact @GlobalTheory.BKGal.JumpDR.exists_odAction | exact GlobalTheory.BKGal.JumpDR.exists_odAction | (intros; apply GlobalTheory.BKGal.JumpDR.exists_odAction <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDeRhamPlusActionConstantsGaloisComm
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDeRhamPlusActionConstantsGaloisComm
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.JumpConst

variable {l : ℕ} [hl : Fact l.Prime]

theorem σDp_aDp (g : GQ l) (w : Ainf l) :
    Per.σDp g (GlobalTheory.MemLoc.aDp l w) = GlobalTheory.MemLoc.aDp l (Per.σA g w) := by
  change Per.σDp g (algebraMap (Per.AinfP l) (Per.BdRp l) (algebraMap (Per.Ainf l) (Per.AinfP l) w)) = _
  rw [GlobalTheory.MemLoc.CrisUnique.σDp_alg, GlobalTheory.RingBasics.awayMap_algebraMap₂]
  rfl

def galDp (g : GQ l) : Per.BdRp l →ₐ[ℤ_[l]] Per.BdRp l where
  toRingHom := Per.σDp g
  commutes' z := by
    change Per.σDp g (GlobalTheory.MemLoc.aDp l (algebraMap ℤ_[l] (Ainf l) z)) =
      GlobalTheory.MemLoc.aDp l (algebraMap ℤ_[l] (Ainf l) z)
    rw [σDp_aDp]
    exact congrArg (GlobalTheory.MemLoc.aDp l) ((galA g).commutes z)

variable (O : Type) [CommRing O] [Algebra ℤ_[l] O]

def galOD (g : GQ l) : OD l O →ₐ[O] OD l O := Algebra.TensorProduct.map (AlgHom.id O O) (galDp g)

theorem galOD_tmul (g : GQ l) (o : O) (b : Per.BdRp l) : galOD O g (o ⊗ₜ b) = o ⊗ₜ Per.σDp g b := rfl

theorem galOD_zero (g : GQ l) : galOD O g 0 = 0 := map_zero _

theorem galOD_add (g : GQ l) (x y : OD l O) : galOD O g (x + y) = galOD O g x + galOD O g y := map_add _ _ _

theorem galOD_toOD (g : GQ l) (x : OA l O) : galOD O g (toOD l O x) = toOD l O (galOA O g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w => exact congrArg (fun y : Per.BdRp l => o ⊗ₜ[ℤ_[l]] y) (σDp_aDp g w)
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

variable {O}

theorem isUnit_natCast_OD {e : ℕ} (he : e ≠ 0) : IsUnit (e : OD l O) := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd he l hl.out.ne_one
  have h1 : IsUnit (m : ℤ_[l]) :=
    PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hm))
  have h2 : IsUnit (m : OD l O) := by
    simpa only [map_natCast] using h1.map (algebraMap ℤ_[l] (OD l O))
  rw [Nat.cast_mul, Nat.cast_pow]
  exact (isUnit_l_OD.pow k).mul h2

theorem eq_of_pow_eq {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R] {e : ℕ} (he : IsUnit (e : R))
    {x y : R} (hx : IsUnit x) (hxy : x ^ e = y ^ e) (h : x - y ∈ I) : x = y := by
  set S := ∑ i ∈ Finset.range e, x ^ i * y ^ (e - 1 - i) with hSdef
  have hq : Ideal.Quotient.mk I y = Ideal.Quotient.mk I x := (Ideal.Quotient.eq.2 h).symm
  have h1 : Ideal.Quotient.mk I S = Ideal.Quotient.mk I ((e : R) * x ^ (e - 1)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hSdef, map_sum, map_mul, map_natCast, map_pow]
    simp only [map_mul, map_pow, hq]
    rw [Finset.sum_congr rfl fun i hi => by
      rw [← pow_add, Nat.add_sub_cancel' (by have := Finset.mem_range.1 hi; omega)]]
    simp
  have h2 : S - (e : R) * x ^ (e - 1) ∈ (⊥ : Ideal R).jacobson :=
    IsAdicComplete.le_jacobson_bot I (Ideal.Quotient.eq.1 h1)
  have hu : IsUnit ((e : R) * x ^ (e - 1)) := he.mul (hx.pow _)
  have h3 : IsUnit S := by
    obtain ⟨u, hu'⟩ := hu
    have := Ideal.mem_jacobson_bot.1 h2 (↑u⁻¹ : R)
    have h4 : S = ((S - (e : R) * x ^ (e - 1)) * ↑u⁻¹ + 1) * u := by
      rw [add_mul, mul_assoc, Units.inv_mul, mul_one, one_mul, hu']; ring
    rw [h4]
    exact this.mul u.isUnit
  have h5 := geom_sum₂_mul x y e
  rw [← hSdef, hxy, sub_self] at h5
  exact sub_eq_zero.1 ((h3.mul_right_eq_zero).1 h5)

section Root

variable {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  {e : ℕ} [NeZero e] (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (ϖ : PiSys l e)


variable (O) in
def piHat : Ahat O K l e :=
  AhatEq.equivAhat O K l e (PowerSeries.C (AdjoinRoot.root (Polynomial.X ^ e + Polynomial.C (l : K))))

theorem root_pow_add : AdjoinRoot.root (Polynomial.X ^ e + Polynomial.C (l : K)) ^ e + (l : AdjoinRoot _) = 0 := by
  have := AdjoinRoot.eval₂_root (Polynomial.X ^ e + Polynomial.C (l : K))
  simpa using this

variable (O) in
theorem piHat_pow_add : piHat O K ^ e + (l : Ahat O K l e) = 0 := by
  rw [piHat, ← map_pow, ← map_natCast (AhatEq.equivAhat O K l e) l, ← map_add (f := _),
    ← map_natCast (PowerSeries.C (R := AdjoinRoot (Polynomial.X ^ e + Polynomial.C (l : K)))) l, ← map_pow, ← map_add,
    root_pow_add, map_zero, map_zero]


variable (O) in
theorem exists_uhat_eq : ∃ w : Ahat O K l e, uhat O K l e = piHat O K + Ehat O K l e * w := by
  obtain ⟨v, hv⟩ := AhatEq.associated_taylor (AhatEq.separable_E K l e)
  refine ⟨AhatEq.equivAhat O K l e v, ?_⟩
  have h1 : AhatEq.equivAhat O K l e (AhatEq.taylor (Polynomial.X ^ e + Polynomial.C (l : K)) Polynomial.X) =
      uhat O K l e := by
    have := AhatEq.toAhat_taylor O K l e Polynomial.X
    rw [AhatEq.incl, Polynomial.aeval_X] at this
    exact this
  have h2 : AhatEq.equivAhat O K l e (AhatEq.taylor (Polynomial.X ^ e + Polynomial.C (l : K))
      (Polynomial.X ^ e + Polynomial.C (l : K))) = Ehat O K l e := by
    have := AhatEq.toAhat_taylor O K l e (Polynomial.X ^ e + Polynomial.C (l : K))
    exact this.trans (congrArg (ofAl O K l e) (AhatEq.incl_E O K l e))
  rw [← h1, ← h2, ← map_mul, hv, piHat, ← map_add (f := _)]
  congr 1
  rw [AhatEq.taylor, Polynomial.aeval_X]

theorem iHat_uhat : ϖ.iHat O K (uhat O K l e) = 1 ⊗ₜ GlobalTheory.MemLoc.aDp l ϖ.teich := by
  rw [uhat, PiSys.iHat_ofAl]
  exact (ϖ.iAl_of_mem O K (HasU.X_mem (B := A O K)) (uIn (invL l (A O K))).2).trans
    (congrArg (toOD l O) (ϖ.iA_u O K))

theorem iAl_E : ϖ.iAl O K (EIn l e _) = 1 ⊗ₜ GlobalTheory.MemLoc.aDp l (ϖ.ev 1 (eis l 1 e)) :=
  (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E 1 O K))

theorem iHat_Ehat : ϖ.iHat O K (Ehat O K l e) = ϖ.iAl O K (EIn l e _) := ϖ.iHat_ofAl O K _

end Root

section Gal

variable {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  {e : ℕ} [NeZero e] (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (ϖ : PiSys l e)

theorem dvd_σA_ev (g : GQ l) : ϖ.ev 1 (eis l 1 e) ∣ Per.σA g (ϖ.ev 1 (eis l 1 e)) := by
  rw [← Ideal.mem_span_singleton, ϖ.span_ev_eis 1, RingHom.mem_ker, GlobalTheory.RingBasics.θ_σA, ϖ.theta_ev_eis 1, map_zero]

theorem dvd_mu {g : GQ l} (hg : g (ϖ.seq 0) = ϖ.seq 0) : ϖ.ev 1 (eis l 1 e) ∣ ϖ.mu g := by
  rw [← Ideal.mem_span_singleton, ϖ.span_ev_eis 1, RingHom.mem_ker]
  exact ϖ.theta_mu hg

theorem one_tmul_mul (u v : Per.BdRp l) : (1 : O) ⊗ₜ[ℤ_[l]] (u * v) = (1 ⊗ₜ u) * (1 ⊗ₜ v) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem galOD_mem_I (g : GQ l) {x : OD l O} (hx : x ∈ Ideal.span {ϖ.iAl O K (EIn l e _)}) :
    galOD O g x ∈ Ideal.span {ϖ.iAl O K (EIn l e _)} := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 hx
  obtain ⟨d, hd⟩ := dvd_σA_ev ϖ g
  rw [map_mul, iAl_E, galOD_tmul, σDp_aDp, hd, map_mul, one_tmul_mul, mul_assoc]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem galOD_teich_sub {g : GQ l} (hg : g (ϖ.seq 0) = ϖ.seq 0) :
    galOD O g (1 ⊗ₜ GlobalTheory.MemLoc.aDp l ϖ.teich) - 1 ⊗ₜ GlobalTheory.MemLoc.aDp l ϖ.teich ∈
      Ideal.span {ϖ.iAl O K (EIn l e _)} := by
  obtain ⟨d, hd⟩ := dvd_mu ϖ hg
  rw [galOD_tmul, σDp_aDp, ϖ.gal_teich, hd, add_mul, one_mul, map_add (f := _), tmul_add, add_sub_cancel_left, mul_assoc,
    map_mul, one_tmul_mul, iAl_E]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem galOD_iHat_piHat {g : GQ l} (hg : g (ϖ.seq 0) = ϖ.seq 0) :
    galOD O g (ϖ.iHat O K (piHat O K)) = ϖ.iHat O K (piHat O K) := by
  haveI := ϖ.complete_OD O K
  have hx : ϖ.iHat O K (piHat O K) ^ e = -(l : OD l O) := by
    have := congrArg (ϖ.iHat O K) (piHat_pow_add O K (l := l) (e := e))
    rw [map_add (f := _), map_pow, map_natCast, map_zero] at this
    exact eq_neg_of_add_eq_zero_left this
  have hux : IsUnit (ϖ.iHat O K (piHat O K)) :=
    (isUnit_pow_iff (NeZero.ne e)).1 (hx ▸ (isUnit_l_OD (O := O)).neg)
  obtain ⟨w, hw⟩ := exists_uhat_eq O K (l := l) (e := e)
  have h1 : ϖ.iHat O K (piHat O K) - 1 ⊗ₜ GlobalTheory.MemLoc.aDp l ϖ.teich ∈ Ideal.span {ϖ.iAl O K (EIn l e _)} := by
    have := congrArg (ϖ.iHat O K) hw
    rw [iHat_uhat, map_add (f := _), map_mul, iHat_Ehat] at this
    rw [this, sub_add_cancel_left]
    exact (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  refine eq_of_pow_eq (Ideal.span {ϖ.iAl O K (EIn l e _)}) (isUnit_natCast_OD (NeZero.ne e))
    (hux.map (galOD O g)) (by rw [← map_pow, hx, map_neg, map_natCast]) ?_
  have h2 := galOD_mem_I K ϖ g h1
  have h3 := galOD_teich_sub K ϖ (O := O) hg
  rw [map_sub] at h2
  have := Ideal.add_mem _ (Ideal.sub_mem _ h2 h1) h3
  convert this using 1
  ring

theorem exists_l_pow_mul (k : K) : ∃ (n : ℕ) (o : O), (l : K) ^ n * k = algebraMap O K o := by
  rcases eq_or_ne k 0 with rfl | hk
  · exact ⟨0, 0, by simp⟩
  have hl1 : ‖(l : K)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] K), norm_algebraMap']
    exact Padic.norm_p_lt_one
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (norm_pos_iff.2 hk)) hl1
  obtain ⟨o, ho⟩ := (IsUnitBall.mem_range_iff (O := O) ((l : K) ^ n * k)).2 (by
    rw [norm_mul, norm_pow]
    have := norm_pos_iff.2 hk
    have h2 := mul_lt_mul_of_pos_right hn this
    rw [inv_mul_cancel₀ this.ne'] at h2
    exact h2.le)
  exact ⟨n, o, ho.symm⟩

theorem galOD_iHat_algebraMap (g : GQ l) (k : K) :
    galOD O g (ϖ.iHat O K (algebraMap K (Ahat O K l e) k)) = ϖ.iHat O K (algebraMap K (Ahat O K l e) k) := by
  obtain ⟨n, o, h⟩ := exists_l_pow_mul K (O := O) (l := l) k
  have h1 : (l : OD l O) ^ n * ϖ.iHat O K (algebraMap K (Ahat O K l e) k) = algebraMap O (OD l O) o := by
    rw [← (ϖ.iHat O K).commutes o, IsScalarTower.algebraMap_apply O K (Ahat O K l e), ← h]
    simp only [map_mul, map_pow, map_natCast]
  refine ((isUnit_l_OD (O := O)).pow n).mul_left_cancel ?_
  rw [h1, ← map_natCast (galOD O g), ← map_pow, ← map_mul, h1, AlgHom.commutes]

end Gal

section Const

variable {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  {e : ℕ} [NeZero e] (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (ϖ : PiSys l e)

theorem galOD_iHat_C {g : GQ l} (hg : g (ϖ.seq 0) = ϖ.seq 0)
    (c : AdjoinRoot (Polynomial.X ^ e + Polynomial.C (l : K))) :
    galOD O g (ϖ.iHat O K (AhatEq.equivAhat O K l e (PowerSeries.C c))) =
      ϖ.iHat O K (AhatEq.equivAhat O K l e (PowerSeries.C c)) := by
  let F : Subring (Ahat O K l e) :=
    RingHom.eqLocus ((galOD O g).toRingHom.comp (ϖ.iHat O K).toRingHom) (ϖ.iHat O K).toRingHom
  change AhatEq.equivAhat O K l e (PowerSeries.C c) ∈ F
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective c
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _)]; exact F.add_mem hp hq
  | monomial n k =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X, map_mul, map_pow,
      map_mul, map_pow]
    refine F.mul_mem ?_ (F.pow_mem (galOD_iHat_piHat K ϖ hg) n)
    have : PowerSeries.C (AdjoinRoot.of (Polynomial.X ^ e + Polynomial.C (l : K)) k) =
        algebraMap K (AdjoinRoot (Polynomial.X ^ e + Polynomial.C (l : K)))⟦X⟧ k := by
      rw [PowerSeries.algebraMap_apply]; rfl
    rw [this, AlgEquiv.commutes]
    exact galOD_iHat_algebraMap K ϖ g k

theorem galOD_idem {a : ℕ} [NeZero a] (t : Wq l a →ₐ[ℤ_[l]] O) {g : GQ l} (hg : ∀ x ∈ Kunr l a, g x = x)
    (τ : ZMod a) : galOD O g (idem (constD t) τ) = idem (constD t) τ := by
  change galOD O g (toOD l O (constA t (Pi.single τ 1))) = toOD l O (constA t (Pi.single τ 1))
  rw [galOD_toOD, galOA_constA t hg]

theorem galOD_iD_kLift {a : ℕ} [NeZero a] (t : Wq l a →ₐ[ℤ_[l]] O) {g : GQ l} (hK : ∀ x ∈ Kunr l a, g x = x)
    (hg : g (ϖ.seq 0) = ϖ.seq 0) (c : ZMod a → AdjoinRoot (Polynomial.X ^ e + Polynomial.C (l : K))) :
    galOD O g (ϖ.iD t K (GlobalTheory.BKGal.JumpDR.kLift O c)) = ϖ.iD t K (GlobalTheory.BKGal.JumpDR.kLift O c) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [PiSys.iD, glue_apply, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_mul, galOD_idem t hK]
  exact congrArg _ (galOD_iHat_C K ϖ hg (c τ))

end Const

theorem cD_σDp {Pl : LocPrime l} {AI : LocAinf l Pl} (Td : LocTied l Pl AI) (g : GQ l) (b : Per.BdRp l) :
    GlobalTheory.BKGal.JumpDR.cD Td (Per.σDp g b) = Pl.actQdR g (GlobalTheory.BKGal.JumpDR.cD Td b) := by
  apply Td.eD.injective
  rw [Td.actD]
  change Td.eD (Td.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g b))) =
    Per.σD g (Td.eD (Td.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) b)))
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  exact (GlobalTheory.MemLoc.ActLaws.σD_alg g b).symm

theorem actVdR_A {Pl : LocPrime l} {AI : LocAinf l Pl} (Td : LocTied l Pl AI) {LL : FinExt l} (T : QLat LL)
    (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR))
    (hA : ∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR),
      A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c))
    (g : Gl l) (w : OD l ↥(OL LL)) (y : T.V ⊗[ℚ_[l]] Pl.R.BdR) :
    actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (A w y) =
      A (galOD ↥(OL LL) (g : GQ l) w) (actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g y) := by
  have hact : ∀ (v : T.V) (b : Pl.R.BdR), actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (v ⊗ₜ[ℚ_[l]] b) =
      T.ρ g v ⊗ₜ[ℚ_[l]] Pl.actQdR (g : GQ l) b := fun v b => by
    rw [← Pl.PD_actdR]; rfl
  induction w using TensorProduct.induction_on generalizing y with
  | zero => simp only [galOD_zero, AddMonoidHom.map_zero, AddMonoidHom.zero_apply, LinearMap.map_zero]
  | add w w' hw hw' => simp only [galOD_add, AddMonoidHom.map_add (f := _), AddMonoidHom.add_apply, LinearMap.map_add (f := _), hw, hw']
  | tmul o b =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add y y' hy hy' => simp only [map_add (f := _), hy, hy']
    | tmul v x =>
      simp only [hA, galOD_tmul, hact, cD_σDp, map_smul, map_mul]

end GlobalTheory.BKGal.JumpConst


open GlobalTheory.BKGal.JumpConst in
theorem GlobalTheory.BKGal.JumpConst.actVdR_comm_kLift : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (LL : FinExt l) (T : QLat LL) (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (c : ZMod a → AdjoinRoot (Polynomial.X ^ e + Polynomial.C (l : ↥LL.1))) (g : Gl l), (g : GQ l) ∈ GK (ϖ.field a) → ∀ y : T.V ⊗[ℚ_[l]] Pl.R.BdR, actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (A (ϖ.iD (thetaW a LL) ↥LL.1 (GlobalTheory.BKGal.JumpDR.kLift ↥(OL LL) c)) y) = A (ϖ.iD (thetaW a LL) ↥LL.1 (GlobalTheory.BKGal.JumpDR.kLift ↥(OL LL) c)) (actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g y) := by
  intro l _ Pl AI Td LL T A hA a e _ _ ϖ _ _ c g hg y
  have hπ : (g : GQ l) (ϖ.seq 0) = ϖ.seq 0 := ϖ.gal_pi a ⟨g, hg⟩
  have hK : ∀ x ∈ Kunr l a, (g : GQ l) x = x := fun x hx =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x (ϖ.Kunr_le_field a hx)
  have hz := galOD_iD_kLift (↥LL.1) ϖ (thetaW a LL) hK hπ c
  exact (actVdR_A Td T A hA g _ y).trans (congrArg (fun w => A w (actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g y)) hz)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDeRhamPlusActionConstantsGaloisCommStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffDeRhamPlusAction_constants_galois_comm : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (LL : FinExt l) (T : QLat LL) (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (c : ZMod a → AdjoinRoot (Polynomial.X ^ e + Polynomial.C (l : ↥LL.1))) (g : Gl l), (g : GQ l) ∈ GK (ϖ.field a) → ∀ y : T.V ⊗[ℚ_[l]] Pl.R.BdR, actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (A (ϖ.iD (thetaW a LL) ↥LL.1 (GlobalTheory.BKGal.JumpDR.kLift ↥(OL LL) c)) y) = A (ϖ.iD (thetaW a LL) ↥LL.1 (GlobalTheory.BKGal.JumpDR.kLift ↥(OL LL) c)) (actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g y) := by
  first | exact @GlobalTheory.BKGal.JumpConst.actVdR_comm_kLift | exact GlobalTheory.BKGal.JumpConst.actVdR_comm_kLift | (intros; apply GlobalTheory.BKGal.JumpConst.actVdR_comm_kLift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFixedVectorFiltrationJumpBreuilKisin
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.BKGal.JumpDR.jump_gives_fixed_vector : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → (∀ m ∈ P.M, P.EN m ∈ P.Man) → ∀ i ∈ P.jumps, ∃ x : T.V ⊗[ℚ_[l]] Pl.R.BdR, (∀ g : Gl l, (g : GQ l) ∈ GK (ϖ.field a) → actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g x = x) ∧ x ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) i ∧ x ∉ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (i + 1) := by
  intro hF l _ a e _ _ ϖ LL _ _ hl ι _ _ P T I jB Pl AI hStd hCmp hHor hEN i hi
  have Td : LocTied l Pl AI := hStd.some
  obtain ⟨X, hX⟩ := GlobalTheory.T.exists_bcrisTensorLattice_to_deRham_map l Pl AI Td LL T
  obtain ⟨A, hA⟩ := GlobalTheory.T.exists_coeffDeRhamPlus_action_on_VTensorBdR l Pl AI Td LL T
  obtain ⟨n, d, c, hd, h1, h2⟩ := GlobalTheory.T.exists_horizontal_vector_of_breuilKisin_jump l a e LL hl ι P hEN i hi
  let m : Fin n → P.MMl := fun k => ⟨P.xi (d k), hd k⟩
  have key := fun j => GlobalTheory.T.mem_completionFiltration_iff_deRhamFiltration hF l a e ϖ LL hl ι P T I jB Pl AI Td hCmp X hX A hA n
    (fun k => GlobalTheory.BKGal.JumpDR.kLift ↥(OL LL) (c k)) m j
  refine ⟨∑ k, A (ϖ.iD (thetaW a LL) ↥LL.1 (GlobalTheory.BKGal.JumpDR.kLift ↥(OL LL) (c k)))
    (X (jB (toBcris (thetaW a LL) ϖ P (m k)))), ?_, (key i).1 h1, fun h => h2 ((key (i + 1)).2 h)⟩
  intro g hg
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e1 := GlobalTheory.T.coeffDeRhamPlusAction_constants_galois_comm l Pl AI Td LL T A hA a e ϖ (c k) g hg (X (jB (toBcris (thetaW a LL) ϖ P (m k))))
  have e2 := GlobalTheory.T.bcrisTensorLattice_to_deRham_equivariant l Pl AI Td LL T X hX g (jB (toBcris (thetaW a LL) ϖ P (m k)))
  have e3 := hHor g hg (d k) (hd k)
  rw [e1, ← e2]
  exact congrArg _ (congrArg X e3)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFixedVectorFiltrationJumpBreuilKisinStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fixed_vector_filtration_jump_breuilKisin : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → (∀ m ∈ P.M, P.EN m ∈ P.Man) → ∀ i ∈ P.jumps, ∃ x : T.V ⊗[ℚ_[l]] Pl.R.BdR, (∀ g : Gl l, (g : GQ l) ∈ GK (ϖ.field a) → actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g x = x) ∧ x ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) i ∧ x ∉ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (i + 1) := by
  first | exact @GlobalTheory.BKGal.JumpDR.jump_gives_fixed_vector | exact GlobalTheory.BKGal.JumpDR.jump_gives_fixed_vector | (intros; apply GlobalTheory.BKGal.JumpDR.jump_gives_fixed_vector <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsHodgeTateJumpOfGaloisFixedFiltrationVector
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsHodgeTateJumpOfGaloisFixedFiltrationVector
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal

theorem mem_DdRE_qlExt {l : ℕ} [Fact l.Prime] (Pl : LocPrime l) {LL : Type} [Field LL]
    [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] LL V] (ρ : Representation LL ↥(GK (Formalism.MainNotions.ElementDenominator.qlExt l)) V)
    (τ : ↥(Formalism.MainNotions.ElementDenominator.qlExt l).1 →ₐ[ℚ_[l]] LL) (y : V ⊗[ℚ_[l]] Pl.R.BdR)
    (hy : y ∈ DdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) ρ) :
    y ∈ DdRE (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) ρ τ := by
  refine Submodule.mem_inf.mpr ⟨hy, ?_⟩
  clear hy
  refine Submodule.mem_iInf _ |>.mpr fun c => ?_
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, LinearMap.id_apply]
  obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp c.2
  obtain rfl : c = algebraMap ℚ_[l] _ r := Subtype.ext hr.symm
  rw [AlgHom.commutes, algebraMap_smul]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    simp only [mulVdR, AlgebraTensorModule.map_tmul, LinearMap.id_apply,
      LinearMap.mulLeft_apply]
    rw [← IsScalarTower.algebraMap_apply, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      TensorProduct.tmul_smul]
  | add a b ha hb => rw [map_add (f := _), ha, hb, smul_add]

theorem isJumpV_of_fixed : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (LL : FinExt l) (T : QLat LL) (F : FinExt l), IsGalois ℚ_[l] ↥F.1 → ∀ (i : ℤ) (x : T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ g : Gl l, (g : GQ l) ∈ GK F → actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g x = x) → x ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) i → x ∉ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (i + 1) → ∀ τ, IsJumpV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ i := by
  intro l _ Pl LL T F _ i x hfix hi hni τ
  have h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ F.1 := bot_le
  have hE : ∀ u, DdRE (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ ⊓ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) u =
      DdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ ⊓ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) u := by
    intro u
    refine le_antisymm (inf_le_inf_right _ inf_le_left) (inf_le_inf_right _ fun y hy => ?_)
    exact mem_DdRE_qlExt Pl T.ρ τ y hy
  unfold IsJumpV FildR
  rw [hE, hE]
  refine (GlobalTheory.JumpDescent.jump_iff l Pl (Formalism.MainNotions.ElementDenominator.qlExt l) F LL h T i).mp ?_
  intro heq
  have hxD : x ∈ DdR (Pl.PD F) (T.ρ.comp (Subgroup.inclusion (GK_le h))) := by
    refine (GlobalTheory.JumpDescent.mem_DdR Pl F _ x).mpr fun g => ?_
    rw [GlobalTheory.JumpDescent.actVdR_comp Pl h]
    exact hfix _ g.2
  have hx : x ∈ DdR (Pl.PD F) (T.ρ.comp (Subgroup.inclusion (GK_le h))) ⊓
      FilV (Pl.PD F) (LL := ↥LL.1) (V := T.V) i :=
    ⟨hxD, by rw [GlobalTheory.JumpDescent.FilV_eq Pl (Formalism.MainNotions.ElementDenominator.qlExt l) F]; exact hi⟩
  rw [← heq] at hx
  exact hni (by rw [← GlobalTheory.JumpDescent.FilV_eq Pl (Formalism.MainNotions.ElementDenominator.qlExt l) F]; exact hx.2)

end GlobalTheory.BKGal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsHodgeTateJumpOfGaloisFixedFiltrationVectorStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHodgeTateJump_of_galois_fixed_filtration_vector : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (LL : FinExt l) (T : QLat LL) (F : FinExt l), IsGalois ℚ_[l] ↥F.1 → ∀ (i : ℤ) (x : T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ g : Gl l, (g : GQ l) ∈ GK F → actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g x = x) → x ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) i → x ∉ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (i + 1) → ∀ τ, IsJumpV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ i := by
  first | exact @GlobalTheory.BKGal.isJumpV_of_fixed | exact GlobalTheory.BKGal.isJumpV_of_fixed | (intros; apply GlobalTheory.BKGal.isJumpV_of_fixed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiltrationJumpsBreuilKisinSubsetGaloisJumps
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.JumpsOfM

theorem main : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → (∀ m ∈ P.M, P.EN m ∈ P.Man) → ∀ U : Set ℤ, (∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ U) → P.jumps ⊆ U := by
  intro hF l _ a e _ _ ϖ LL _ hT hl ι _ _ P T I jB Pl AI hStd hCmp hHor hEN U hU i hi
  obtain ⟨x, hfix, hx, hx'⟩ := GlobalTheory.T.exists_fixed_vector_filtration_jump_breuilKisin hF l a e ϖ LL hl ι P T I jB Pl AI hStd hCmp hHor hEN i hi
  have hdvd : e ∣ l ^ a - 1 := ⟨1, by rw [← hT.succ_eq]; simp⟩
  have hG := PiSys.isGalois_field a ϖ hdvd
  let τ : ↥(Formalism.MainNotions.ElementDenominator.qlExt l).1 →ₐ[ℚ_[l]] ↥LL.1 :=
    (Algebra.ofId ℚ_[l] ↥LL.1).comp (IntermediateField.botEquiv ℚ_[l] (Om l)).toAlgHom
  exact hU τ i (GlobalTheory.T.isHodgeTateJump_of_galois_fixed_filtration_vector l Pl LL T (ϖ.field a) hG i x hfix hx hx' τ)

end GlobalTheory.JumpsOfM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiltrationJumpsBreuilKisinSubsetGaloisJumpsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtration_jumps_breuilKisin_subset_galoisJumps : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → (∀ m ∈ P.M, P.EN m ∈ P.Man) → ∀ U : Set ℤ, (∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ U) → P.jumps ⊆ U := by
  first | exact @GlobalTheory.JumpsOfM.main | exact GlobalTheory.JumpsOfM.main | (intros; apply GlobalTheory.JumpsOfM.main <;> assumption)
end
