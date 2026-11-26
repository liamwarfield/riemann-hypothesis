module

public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCT
public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCX
public import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.THProvA

@[expose] public section

section -- merged from Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCN
section -- merged from Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCR
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.MainNotions.DIV.Inh

section Cover

variable (p q : ℕ)

end Cover


variable {D : D7}

theorem gram_coord (V : HSp D) (x y : V.V) :
    V.hT x y = ∑ i, ∑ j, star (V.frame.repr x i) * V.gram i j * V.frame.repr y j := by
  conv_lhs => rw [← V.frame.sum_repr x, ← V.frame.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply,
    RingHom.id_apply, HSpace.gram, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

def colM (V : HSp D) {n : ℕ} (v : Fin n → V.V) : Matrix (Fin V.rank) (Fin n) D.host.E := fun i k => V.frame.repr (v k) i

theorem colM_gram (V : HSp D) {n m : ℕ} (v : Fin n → V.V) (w : Fin m → V.V) (a : Fin n) (b : Fin m) :
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (colM V v) * V.gram * colM V w) a b = V.hT (v a) (w b) := by
  rw [gram_coord, Matrix.mul_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  rfl

theorem colM_vec (V : HSp D) {n : ℕ} (v : Fin n → V.V) (z : V.V) (a : Fin n) :
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (colM V v) * V.gram).mulVec (V.frame.repr z) a = V.hT (v a) z :=
  (colM_gram V v (fun _ : Fin 1 => z) a 0)

theorem frameMat_eq (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V) : frameMat A B ι = colM A fun k => ι (B.frame k) := by
  ext i k
  rw [frameMat, LinearMap.toMatrix_apply]
  rfl

theorem frame_rel {A B : HSp D} {ι : B.V →ₗ[D.host.E] A.V} (h : HSpace.IsIsomEmb B A ι) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat A B ι) * A.gram * frameMat A B ι = B.gram := by
  ext a b
  rw [frameMat_eq, colM_gram, h]
  rfl

def besselFlagHyperbolic (D : D7) (c : Fin D.R.rS → D.host.E) (hc : ∀ i, c i ≠ 0) (y : GfC (D.sp.Y 0)) :
    BesDat (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) where
  ρ := D.R.rS
  codim := by
    rw [D.sp.X_rank 0 (Nat.zero_le _), D.sp.Y_rank 0 (Nat.zero_le _)]
    have := D.R.rS_two
    show D.R.k + 0 * (D.R.t + 1) + 2 * D.R.rS + 1 = D.R.k + D.R.m - 1 + 0 * D.R.t
    omega
  e := colM (D.sp.Y 0) D.sp.hypE
  e_iso := ⟨by
    have h1 : LinearIndependent D.host.E D.sp.hypE := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      have e := congrArg (fun x => (D.sp.Y 0).hT (D.sp.hypF i) x) hg
      have hfe : ∀ k, (D.sp.Y 0).hT (D.sp.hypF i) (D.sp.hypE k) = if k = i then 1 else 0 := fun k => by
        rw [← (D.sp.Y 0).herm.eq, D.sp.hyp_ef]
        split_ifs <;> simp
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum, hfe] using e
    exact h1.map' (D.sp.Y 0).frame.equivFun.toLinearMap (LinearEquiv.ker _),
    by ext a b; rw [colM_gram, D.sp.hyp_ee]; rfl⟩
  e_perp := by ext a b; rw [frameMat_eq, colM_gram, (D.sp.hyp_orthX b _).1]; rfl
  z := (D.sp.Y 0).frame.repr D.sp.zm
  z_perpA := by funext a; rw [frameMat_eq, colM_vec, D.sp.zm_orth]; rfl
  z_perpE := by
    funext a
    rw [colM_vec, ← (D.sp.Y 0).herm.eq, (D.sp.hyp_orthz a).1]
    simp
  z_ne := by
    have e : Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.Y 0).gram ((D.sp.Y 0).frame.repr D.sp.zm)
      ((D.sp.Y 0).frame.repr D.sp.zm) = (D.sp.Y 0).hT D.sp.zm D.sp.zm := (gram_coord _ _ _).symm
    rw [e, D.sp.zm_norm, neg_ne_zero]
    exact Nat.cast_ne_zero.2 D.sp.T_prime.ne_zero
  c := c
  c_ne := hc
  y := y

variable {ψ : AddChar (AF D.host.F) ℂ}

section Emb

variable {A B : HSp D} {ι : B.V →ₗ[D.host.E] A.V}

def prM (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V) : Matrix (Fin B.rank) (Fin A.rank) D.host.E :=
  B.gram⁻¹ * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat A B ι) * A.gram)

theorem perp_rel (h : HSpace.IsIsomEmb B A ι) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat A B ι) * A.gram * (1 - frameMat A B ι * prM A B ι) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, frame_rel h, prM, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (gram_det_ne B).isUnit, Matrix.one_mul, sub_self]

theorem emb_gen {E R : Type} [CommRing E] [CommRing R] {a b : ℕ} (f : E →+* R) (M : Matrix (Fin a) (Fin b) E)
    (P : Matrix (Fin b) (Fin a) E) (Q : Matrix (Fin a) (Fin a) E) (hQ : M * P + Q = 1) (g : Matrix (Fin a) (Fin a) R)
    (x : Matrix (Fin b) (Fin b) R) (e1 : g * M.map f = M.map f * x)
    (e2 : ∀ j, g.mulVec (fun i => f (Q i j)) = fun i => f (Q i j)) : g = M.map f * x * P.map f + Q.map f := by
  have e2' : g * Q.map f = Q.map f := by
    ext i j
    exact congrFun (e2 j) i
  have e3 : M.map f * P.map f + Q.map f = 1 := by
    rw [← Matrix.map_mul, ← Matrix.map_add f f.map_add, hQ, Matrix.map_one _ f.map_zero f.map_one]
  rw [← e1, ← e2', Matrix.mul_assoc, ← Matrix.mul_add, e3, Matrix.mul_one]

def coM (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V) : Matrix (Fin A.rank) (Fin A.rank) D.host.E :=
  1 - frameMat A B ι * prM A B ι

theorem embU (D : D7) : EmbU D := by
  intro A B ι h g g' x a b
  have hQ : frameMat A B ι * prM A B ι + coM A B ι = 1 := add_sub_cancel _ _
  have hp : ∀ j, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat A B ι) * A.gram).mulVec
      (fun k => coM A B ι k j) = 0 := fun j => funext fun i => congrFun (congrFun (perp_rel h) i) j
  exact Subtype.ext (Units.ext ((emb_gen (incA D) _ _ _ hQ (mt A g) (mt B x) a.1 fun j => a.2 _ (hp j)).trans
    (emb_gen (incA D) _ _ _ hQ (mt A g') (mt B x) b.1 fun j => b.2 _ (hp j)).symm))

end Emb

section Rows

variable (X : ThetaX D)

end Rows

end Formalism.L2.Fam.ThC

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Tri

variable {R : Type} [CommRing R] {ρ : ℕ}

def UTri (T : Matrix (Fin ρ) (Fin ρ) R) : Prop := ∀ j i, i ≤ j → (T - 1) j i = 0

theorem left_inv {K : Type} [Field K] {n : ℕ} (C : Matrix (Fin n) (Fin ρ) K) (h : LinearIndependent K C.transpose) :
    ∃ L : Matrix (Fin ρ) (Fin n) K, L * C = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' C)
    (LinearMap.ker_eq_bot.2 (Matrix.mulVec_injective_iff.2 h))
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' C, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]

end Tri

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : BesDat A B ι)

def eA : Matrix (Fin B.rank) (Fin d.ρ) (AE D) := d.e.map (incA D)

def lA : Matrix (Fin d.ρ) (Fin B.rank) (AE D) := (left_inv d.e d.e_iso.1).choose.map (incA D)

def tM (n : GA D B) : Matrix (Fin d.ρ) (Fin d.ρ) (AE D) := HMul.hMul (lA d) (HMul.hMul (mt B n) (eA d))

def bV (n : GA D B) (x : Fin B.rank → D.host.E) : Fin d.ρ → AE D := (lA d).mulVec ((mt B n).mulVec (ratV x) - ratV x)

def Perp (x : Fin B.rank → D.host.E) : Prop :=
  (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) d.e * B.gram).mulVec x = 0

def Good (n : GA D B) : Prop :=
  HMul.hMul (mt B n) (eA d) = HMul.hMul (eA d) (tM d n) ∧ UTri (tM d n) ∧
    ∀ x, Perp d x → (mt B n).mulVec (ratV x) = ratV x + (eA d).mulVec (bV d n x)

variable {d}


theorem trace_gen {F E R : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [CommRing R] [Algebra F R] (r : E) :
    Algebra.trace R (R ⊗[F] E) (inclR R r) = algebraMap F R (Algebra.trace F E r) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange, Algebra.baseChange_lmul]
  rfl

end Formalism.L2.Fam.ThC

end
end

section -- merged from Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCJ
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

theorem alg_trace_gen {F E R : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (h : ∀ e, algebraMap F E (Algebra.trace F E e) = e + σ e) (z : R ⊗[F] E) :
    algebraMap R (R ⊗[F] E) (Algebra.trace R (R ⊗[F] E) z) = z + sigR R σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), add_add_add_comm]
  | tmul a e =>
    have h4 : (a ⊗ₜ[F] e : R ⊗[F] E) = a • inclR R e := by
      show _ = a • ((1 : R) ⊗ₜ[F] e)
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h5 : sigR R σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := rfl
    rw [h5, ← TensorProduct.tmul_add, ← h, h4, map_smul, trace_gen, smul_eq_mul, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, Algebra.algebraMap_eq_smul_one (A := E), ← TensorProduct.smul_tmul,
      Algebra.smul_def, mul_comm]

end Gen

variable {D : D7}

variable {V W : HSp D}


end Formalism.L2.Fam.ThC

end
end

section -- merged from Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCD
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Gen

theorem map_aff {E R S : Type} [CommRing E] [CommRing R] [CommRing S] (i : E →+* R) (f : R →+* S) {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) E) (P : Matrix (Fin n) (Fin m) E) (Q : Matrix (Fin m) (Fin m) E) (x : Matrix (Fin n) (Fin n) R) :
    (M.map i * x * P.map i + Q.map i).map f = M.map (f.comp i) * x.map f * P.map (f.comp i) + Q.map (f.comp i) := by
  rw [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, Matrix.map_map, Matrix.map_map,
    Matrix.map_map]
  rfl

theorem map_aff_one {E R S : Type} [CommRing E] [CommRing R] [CommRing S] (i : E →+* R) (f : R →+* S) {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) E) (P : Matrix (Fin n) (Fin m) E) (Q : Matrix (Fin m) (Fin m) E) (h : M * P + Q = 1)
    (x : Matrix (Fin n) (Fin n) R) (hx : x.map f = 1) : (M.map i * x * P.map i + Q.map i).map f = 1 := by
  rw [map_aff, hx, Matrix.mul_one]
  have e : (M * P + Q).map (f.comp i) = 1 := by
    rw [h, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [← e, Matrix.map_add _ (map_add _), Matrix.map_mul]

end Gen

section Emb

variable {A B : HSp D} {ι : B.V →ₗ[D.host.E] A.V} (hι : HSpace.IsIsomEmb B A ι) {s : GA D B → GA D A}
  (hs : ∀ h, EmbRel A B ι (s h) h)

include hι hs

theorem emb_mat (h : GA D B) : mt A (s h) =
    HMul.hMul (HMul.hMul ((frameMat A B ι).map (incA D)) (mt B h)) ((prM A B ι).map (incA D)) + (coM A B ι).map (incA D) :=
  emb_gen (incA D) _ _ _ (add_sub_cancel _ _) (mt A (s h)) (mt B h) (hs h).1 fun j =>
    (hs h).2 (fun k => coM A B ι k j) (funext fun i => congrFun (congrFun (perp_rel hι) i) j)

theorem emb_fin {k : GA D B} (hk : k ∈ GfC B) : s k ∈ GfC A := by
  have a : infHom B k = 1 := hk
  refine Units.ext (?_ : (mt A (s k)).map (infPart D) = 1)
  rw [emb_mat hι hs]
  exact map_aff_one _ _ _ _ _ (add_sub_cancel _ _) _ (congrArg Units.val a)

end Emb

end Formalism.L2.Fam.ThC

end
end
