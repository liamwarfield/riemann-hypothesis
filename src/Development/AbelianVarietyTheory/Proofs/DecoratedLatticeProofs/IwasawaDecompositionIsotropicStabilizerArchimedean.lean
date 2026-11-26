module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoubledUnitaryChartSplitPlace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittHyperbolicIsotropicColumnsAtRealPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittHyperbolicIsotropicColumnsAtRealPlace
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.AdelicU Formalism.UG

namespace GlobalTheory.IsoColReal

theorem compInf_incA {D : D7} (w : InfinitePlace D.host.F) (x : D.host.E) :
    compInf D.host.F D.host.E w (incA D x) = inclR (F := D.host.F) w.Completion x := by
  simp [compInf, incA, inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]

theorem sigR_inclR_real {D : D7} (w : InfinitePlace D.host.F) (x : D.host.E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion D.sp.cm.sig (inclR (F := D.host.F) w.Completion x) = inclR (F := D.host.F) w.Completion (star x) := by
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  rfl

theorem isotropic_at_real : ∀ {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (w : InfinitePlace D.host.F), (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion D.sp.cm.sig) (Matrix.map d.jX (compInf D.host.F D.host.E w)) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion T.gram : Matrix (Fin r) (Fin T.rank) (TensorProduct D.host.F w.Completion D.host.E)) * Matrix.map d.jX (compInf D.host.F D.host.E w) = 0 := by
  intro D T T₀ r d w
  have hm : Matrix.map d.jX (compInf D.host.F D.host.E w) = d.e.map (inclR (F := D.host.F) w.Completion) := by
    ext i j
    simp [HypDec.jX, rat, compInf_incA]
  have hc : Formalism.UG.cT (sigR w.Completion D.sp.cm.sig) (d.e.map (inclR (F := D.host.F) w.Completion)) =
      (d.eᴴ).map (inclR (F := D.host.F) w.Completion) := by
    ext i j
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply, sigR_inclR_real]
  have hJ : JR w.Completion T.gram = T.gram.map (inclR (F := D.host.F) w.Completion) := rfl
  rw [hm, hc, hJ]
  have h0 := congrArg (fun M => M.map (inclR (F := D.host.F) w.Completion)) d.ee
  simp only [Matrix.map_mul, Matrix.map_zero, map_zero] at h0
  exact h0

end GlobalTheory.IsoColReal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittHyperbolicIsotropicColumnsAtRealPlaceStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.AdelicU Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittHyperbolic_isotropic_columns_at_real_place : ∀ {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (w : InfinitePlace D.host.F), (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion D.sp.cm.sig) (Matrix.map d.jX (compInf D.host.F D.host.E w)) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion T.gram : Matrix (Fin r) (Fin T.rank) (TensorProduct D.host.F w.Completion D.host.E)) * Matrix.map d.jX (compInf D.host.F D.host.E w) = 0 := by
  first | exact @GlobalTheory.IsoColReal.isotropic_at_real | exact GlobalTheory.IsoColReal.isotropic_at_real | (intros; apply GlobalTheory.IsoColReal.isotropic_at_real <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemWittStabilizerOfKeepsIsotropicRealPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemWittStabilizerOfKeepsIsotropicRealPlaces
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.AdelicU Formalism.UG

noncomputable section

namespace GlobalTheory.Core.Rk.IwGlob

open GlobalTheory.MixModel
open scoped TensorProduct

theorem tens_prod_ext {F E A B : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] {z z' : (A × B) ⊗[F] E}
    (a : Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z')
    (b : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z') : z = z' := by
  have hz : ∀ z : (A × B) ⊗[F] E, z = LinearMap.rTensor E (LinearMap.inl F A B)
        (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z) +
      LinearMap.rTensor E (LinearMap.inr F A B)
        (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z) := by
    intro z
    induction z with
    | tmul x y => simp [← TensorProduct.add_tmul]
    | add x y hx hy =>
      simp only [map_add (f := _)]
      rw [add_add_add_comm, ← hx, ← hy]
  rw [hz z, hz z', a, b]

theorem adTens_ext {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {z z' : AF F ⊗[F] E}
    (h1 : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.compInf F E w z = GlobalTheory.AdelicU.compInf F E w z')
    (h2 : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z') : z = z' := by
  refine tens_prod_ext (A := Ainf F) (B := Af F) (GlobalTheory.AutFunCompare.infTens_ext fun w => ?_) h2
  have e : ∀ y : AF F ⊗[F] E, Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)
      (Algebra.TensorProduct.map (AlgHom.fst F (Ainf F) (Af F)) (AlgHom.id F E) y) =
      GlobalTheory.AdelicU.compInf F E w y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => erw [map_zero]
    | tmul a x => rfl
    | add x y hx hy => erw [map_add, map_add, map_add, hx, hy]
  rw [e, e]
  exact h1 w

theorem map_mul_eq_of_keeps {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R) {n r : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (X : Matrix (Fin n) (Fin r) A) (P : Matrix (Fin r) (Fin n) A)
    (hPX : P * X = 1) (β : Matrix (Fin r) (Fin r) R) (h : M.map φ * X.map φ = X.map φ * β) :
    (M * X).map φ = (X * (P * M * X)).map φ := by
  have hPX' : P.map φ * X.map φ = 1 := by
    rw [← Matrix.map_mul, hPX, Matrix.map_one _ (map_zero φ) (map_one φ)]
  simp only [Matrix.map_mul]
  rw [h, Matrix.mul_assoc (P.map φ), h, ← Matrix.mul_assoc (P.map φ), hPX', Matrix.one_mul]

theorem mat_projArch {D : D7} {T : HSp D} (q : GA D T) (w : InfinitePlace D.host.F) :
    (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig T.gram (GlobalTheory.AdelicU.projArch D.sp.cm.sig T.gram w q)).1 =
                 (Formalism.L2.Theta.mt T q).map (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) :=
  Matrix.ext fun _ _ => rfl

theorem mt_inv_mul_self {D : D7} {T : HSp D} (q : GA D T) :
    Formalism.L2.Theta.mt T q⁻¹ * Formalism.L2.Theta.mt T q = 1 := by
  show (Formalism.L2.Theta.matHom T q⁻¹).1 * (Formalism.L2.Theta.matHom T q).1 = 1
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

theorem keeps_map {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (q : GA D T) (w : InfinitePlace D.host.F)
    (β : Matrix (Fin r) (Fin r) (TensorProduct D.host.F w.Completion D.host.E))
    (h : (matHom _ D.sp.cm.sig T.gram (projArch D.sp.cm.sig T.gram w q)).1 * Matrix.map d.jX (compInf D.host.F D.host.E w) = Matrix.map d.jX (compInf D.host.F D.host.E w) * β) :
    (Formalism.L2.Theta.mt T q).map (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) * Matrix.map d.jX (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) =
      Matrix.map d.jX (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) * β := by
  rw [← mat_projArch q w]
  exact h

theorem arch_comp {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (q : GA D T) (w : InfinitePlace D.host.F)
    (β : Matrix (Fin r) (Fin r) (TensorProduct D.host.F w.Completion D.host.E))
    (h : (matHom _ D.sp.cm.sig T.gram (projArch D.sp.cm.sig T.gram w q)).1 * Matrix.map d.jX (compInf D.host.F D.host.E w) = Matrix.map d.jX (compInf D.host.F D.host.E w) * β)
    (i : Fin T.rank) (j : Fin r) :
    GlobalTheory.AdelicU.compInf D.host.F D.host.E w ((Formalism.L2.Theta.mt T q ⬝ d.jX) i j) =
      GlobalTheory.AdelicU.compInf D.host.F D.host.E w ((d.jX ⬝ (d.pX ⬝ Formalism.L2.Theta.mt T q ⬝ d.jX)) i j) := by
  have h2 := keeps_map d q w β h
  have h3 := map_mul_eq_of_keeps (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) (Formalism.L2.Theta.mt T q) d.jX d.pX
    d.pX_jX β h2
  rw [← Matrix.map_apply (f := GlobalTheory.AdelicU.compInf D.host.F D.host.E w), h3]
  rfl

theorem mul_jX_eq {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (q : GA D T) (hq : q ∈ GinfC T)
    (hw : ∀ w : InfinitePlace D.host.F, ∃ β : Matrix (Fin r) (Fin r) (TensorProduct D.host.F w.Completion D.host.E), (matHom _ D.sp.cm.sig T.gram (projArch D.sp.cm.sig T.gram w q)).1 * Matrix.map d.jX (compInf D.host.F D.host.E w) = Matrix.map d.jX (compInf D.host.F D.host.E w) * β) :
    Formalism.L2.Theta.mt T q ⬝ d.jX = d.jX ⬝ (d.pX ⬝ Formalism.L2.Theta.mt T q ⬝ d.jX) := by
  let φf : AE D →+* Af D.host.F ⊗[D.host.F] D.host.E :=
    (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hf : (Formalism.L2.Theta.mt T q).map φf = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hq)
  have hfin := map_mul_eq_of_keeps φf (Formalism.L2.Theta.mt T q) d.jX d.pX d.pX_jX 1
    (by rw [hf, Matrix.one_mul, Matrix.mul_one])
  funext i j
  exact adTens_ext (F := D.host.F) (E := D.host.E) (fun w => Exists.elim (hw w) fun β hβ => arch_comp d q w β hβ i j)
    (congrFun (congrFun hfin i) j)

theorem mem_stab_of_keeps : ∀ {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (q : GA D T), q ∈ GinfC T → (∀ w : InfinitePlace D.host.F, ∃ β : Matrix (Fin r) (Fin r) (TensorProduct D.host.F w.Completion D.host.E), (matHom _ D.sp.cm.sig T.gram (projArch D.sp.cm.sig T.gram w q)).1 * Matrix.map d.jX (compInf D.host.F D.host.E w) = Matrix.map d.jX (compInf D.host.F D.host.E w) * β) → q ∈ stab d := by
  intro D T T₀ r d q hq hw
  have hPX : d.pX ⬝ d.jX = 1 := d.pX_jX
  have key := mul_jX_eq d q hq hw
  have hinv : Formalism.L2.Theta.mt T q⁻¹ ⬝ Formalism.L2.Theta.mt T q = 1 := mt_inv_mul_self q
  have h1 : (d.pX ⬝ Formalism.L2.Theta.mt T q⁻¹ ⬝ d.jX) ⬝ (d.pX ⬝ Formalism.L2.Theta.mt T q ⬝ d.jX) = 1 := by
    calc (d.pX ⬝ Formalism.L2.Theta.mt T q⁻¹ ⬝ d.jX) ⬝ (d.pX ⬝ Formalism.L2.Theta.mt T q ⬝ d.jX)
        = (d.pX ⬝ Formalism.L2.Theta.mt T q⁻¹) ⬝ (d.jX ⬝ (d.pX ⬝ Formalism.L2.Theta.mt T q ⬝ d.jX)) := by
          rw [Matrix.mul_assoc]
      _ = (d.pX ⬝ Formalism.L2.Theta.mt T q⁻¹) ⬝ (Formalism.L2.Theta.mt T q ⬝ d.jX) := by rw [← key]
      _ = d.pX ⬝ ((Formalism.L2.Theta.mt T q⁻¹ ⬝ Formalism.L2.Theta.mt T q) ⬝ d.jX) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hinv, Matrix.one_mul, hPX]
  exact ⟨⟨_, _, mul_eq_one_comm.mp h1, h1⟩, key⟩

end GlobalTheory.Core.Rk.IwGlob
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemWittStabilizerOfKeepsIsotropicRealPlacesStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.AdelicU Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_wittStabilizer_of_keeps_isotropic_real_places : ∀ {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (q : GA D T), q ∈ GinfC T → (∀ w : InfinitePlace D.host.F, ∃ β : Matrix (Fin r) (Fin r) (TensorProduct D.host.F w.Completion D.host.E), (matHom _ D.sp.cm.sig T.gram (projArch D.sp.cm.sig T.gram w q)).1 * Matrix.map d.jX (compInf D.host.F D.host.E w) = Matrix.map d.jX (compInf D.host.F D.host.E w) * β) → q ∈ stab d := by
  first | exact @GlobalTheory.Core.Rk.IwGlob.mem_stab_of_keeps | exact GlobalTheory.Core.Rk.IwGlob.mem_stab_of_keeps | (intros; apply GlobalTheory.Core.Rk.IwGlob.mem_stab_of_keeps <;> assumption)
end
end

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

namespace GlobalTheory.Core.Rk.IwIso

open GlobalTheory.AdelicU Formalism.UG

theorem local_decomp {A : Type} [CommRing A] {n r : ℕ} (σ : A →+* A) (f : A →+* ℂ) (hf : Function.Bijective f)
    (hσ : ∀ x, f (σ x) = star (f x)) {J : Matrix (Fin n) (Fin n) A} (b : GL (Fin n) A) (ε : Fin n → Bool)
    (hb : Formalism.UG.cT σ b.1 * J * b.1 = Matrix.diagonal fun i => if ε i then 1 else -1)
    (X : Matrix (Fin n) (Fin r) A) (hX : Formalism.UG.cT σ X * J * X = 0) (g : GL (Fin n) A) (hg : g ∈ UJ σ J) :
    ∃ k ∈ UJ σ J, b⁻¹ * k * b ∈ UJ σ (1 : Matrix (Fin n) (Fin n) A) ∧
      ∃ β : Matrix (Fin r) (Fin r) A, (g * k⁻¹).1 * X = X * β :=
  GlobalTheory.T.iwasawa_isotropic_columns_ring_iso_complex σ f hf hσ b ε hb X hX g hg

theorem iso_arch {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (w : InfinitePlace D.host.F) :
    (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion D.sp.cm.sig) (Matrix.map d.jX (compInf D.host.F D.host.E w)) *
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion T.gram : Matrix (Fin r) (Fin T.rank) _) *
      Matrix.map d.jX (compInf D.host.F D.host.E w) = 0 :=
  GlobalTheory.T.wittHyperbolic_isotropic_columns_at_real_place d w

theorem mem_stab_of_arch {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (q : GA D T) (hfin : q ∈ GinfC T)
    (harch : ∀ w : InfinitePlace D.host.F, ∃ β : Matrix (Fin r) (Fin r) (TensorProduct D.host.F w.Completion D.host.E),
      (matHom _ D.sp.cm.sig T.gram (projArch D.sp.cm.sig T.gram w q)).1 * Matrix.map d.jX (compInf D.host.F D.host.E w) =
        Matrix.map d.jX (compInf D.host.F D.host.E w) * β) :
    q ∈ stab d :=
  GlobalTheory.T.mem_wittStabilizer_of_keeps_isotropic_real_places d q hfin harch

theorem glue {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (k : ∀ w : InfinitePlace F, GArch σ J w) :
    ∃ g : GAd σ J, (∀ w, projArch σ J w g = k w) ∧ projFin σ J g = 1 := by
  classical
  have key : ∀ s : Finset (InfinitePlace F), ∃ g : GAd σ J, (∀ w ∈ s, projArch σ J w g = k w) ∧
      (∀ w ∉ s, projArch σ J w g = 1) ∧ projFin σ J g = 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by simp, fun _ _ => map_one _, map_one _⟩
    | insert a s ha ih =>
      obtain ⟨g, h1, h2, h3⟩ := ih
      refine ⟨g * embArch σ J a (k a), fun w hw => ?_, fun w hw => ?_, ?_⟩
      · rw [map_mul]
        rcases Finset.mem_insert.1 hw with rfl | hw
        · rw [h2 w ha, projArch_embArch_self, one_mul]
        · have hne : w ≠ a := fun e => ha (e ▸ hw)
          rw [h1 w hw, projArch_embArch_ne σ J hne, mul_one]
      · have hne : w ≠ a := fun e => hw (e ▸ Finset.mem_insert_self a s)
        rw [map_mul, h2 w (fun h => hw (Finset.mem_insert_of_mem h)), projArch_embArch_ne σ J hne, mul_one]
      · rw [map_mul, h3, projFin_embArch, mul_one]
  obtain ⟨g, h1, -, h3⟩ := key Finset.univ
  exact ⟨g, fun w => h1 w (Finset.mem_univ w), h3⟩

theorem local_at_arch {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hc : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (w : InfinitePlace F)
    (b : GL (Fin n) (TensorProduct F w.Completion E)) (ε : Fin n → Bool)
    (hb : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) b.1 * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion J * b.1 =
      Matrix.diagonal fun i => if ε i then 1 else -1)
    (X : Matrix (Fin n) (Fin r) (TensorProduct F w.Completion E))
    (hX : (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) X * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion J :
      Matrix (Fin r) (Fin n) _) * X = 0)
    (g : GL (Fin n) (TensorProduct F w.Completion E))
    (hg : g ∈ UJ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion J)) :
    ∃ k ∈ UJ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion J),
      b⁻¹ * k * b ∈ UJ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) (1 : Matrix (Fin n) (Fin n) _) ∧
      ∃ β : Matrix (Fin r) (Fin r) (TensorProduct F w.Completion E), (g * k⁻¹).1 * X = X * β := by
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  exact local_decomp _ (infEmb τ) (infEmb_bijective hc τ) (fun x => (infEmb_sigR hc τ x).symm) b ε hb X hX g hg

theorem mem_stabArch_of {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (w : InfinitePlace F)
    (b : GL (Fin n) (TensorProduct F w.Completion E)) (g : GArch σ J w)
    (h : b⁻¹ * matHom _ σ J g * b ∈ UJ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) 1) : g ∈ stabArch σ J w b := by
  show (MulAut.conj b⁻¹) (matHom _ σ J g) ∈ UJ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) (1 : Matrix (Fin n) (Fin n) _)
  rwa [MulAut.conj_apply, inv_inv]


set_option maxHeartbeats 2000000 in
theorem iwasawa_stab_arch : ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r) (b : GL (Fin T.rank) (AE D)), IsMaj T b → ∀ y ∈ GinfC T, ∃ q ∈ stab d, ∃ k ∈ Kmax T b, q ∈ GinfC T ∧ y = q * k := by
  intro D T T₀ r d b hb y hy
  have hloc := fun w : InfinitePlace D.host.F => local_at_arch (isCMExt_host D) T.gram w _ (hb w).choose
    (hb w).choose_spec _ (iso_arch d w) (matHom _ D.sp.cm.sig T.gram (projArch D.sp.cm.sig T.gram w y))
    (projArch D.sp.cm.sig T.gram w y).2
  choose kk hk hk1 hβ using hloc
  obtain ⟨k, hkw, hkf⟩ := glue D.sp.cm.sig T.gram (fun w => ⟨kk w, hk w⟩)
  have hfk : finHom T k = 1 := by
    have e : finHom T k = GlobalTheory.AdelicU.matHom (Af D.host.F) D.sp.cm.sig T.gram (projFin D.sp.cm.sig T.gram k) := rfl
    rw [e, hkf, map_one]
  refine ⟨y * k⁻¹, ?_, k, ?_, ?_, by group⟩
  · refine mem_stab_of_arch d _ ?_ fun w => ?_
    · show finHom T (y * k⁻¹) = 1
      rw [map_mul, map_inv, hfk, inv_one, mul_one]
      exact hy
    · obtain ⟨β, h⟩ := hβ w
      refine ⟨β, ?_⟩
      rw [MonoidHom.map_mul (projArch D.sp.cm.sig T.gram w), MonoidHom.map_inv (projArch D.sp.cm.sig T.gram w), hkw w,
        MonoidHom.map_mul]
      exact h
  · rw [Kmax, levelAll, Subgroup.mem_inf, mem_levelOpen, Subgroup.mem_iInf]
    refine ⟨fun v => ?_, fun w => ?_⟩
    · rw [← projFinLoc_projFin, hkf, map_one]
      exact one_mem _
    · refine Subgroup.mem_comap.2 ?_
      have h3 := mem_stabArch_of D.sp.cm.sig T.gram w _ ⟨kk w, hk w⟩ (hk1 w)
      rw [← hkw w] at h3
      exact h3
  · show finHom T (y * k⁻¹) = 1
    rw [map_mul, map_inv, hfk, inv_one, mul_one]
    exact hy

end GlobalTheory.Core.Rk.IwIso
