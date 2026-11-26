module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibLatF
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibLatB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GpHerm

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.InvMulOfUnitri
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NEqApply
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsoGenLeft
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.HSumRight
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.PWOfInW
noncomputable section

open NumberField Formalism.BasicNotions Matrix
open scoped BigOperators

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
  (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)

def Ym : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E := (X0⁻¹)ᴴ

def om (a : Fin D.R.rS) : (VS D).V := -∑ b, Ym X0 b a • xs b

def nE (a : Fin D.R.rS) : (VS D).V := ∑ b, X0 b a • X.eX b

def nF (a : Fin D.R.rS) : (VS D).V := ∑ c, Ym X0 c a • X.fY c + om X0 xs a + ∑ b, (X0 * M) b a • X.eX b

def nWL : (VS D).V →ₗ[D.host.E] (VS D).V := LinearMap.id + ∑ b, ((VS D).hT (xs b)).smulRight (X.eX b)

def pWL : (VS D).V →ₗ[D.host.E] (VS D).V :=
  LinearMap.id - ∑ c, ((VS D).hT (X.fY c)).smulRight (X.eX c) - ∑ c, ((VS D).hT (X.eX c)).smulRight (X.fY c)

theorem pWL_apply (y : (VS D).V) : pWL X y = pW X y := by
  simp [pWL, pW, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smulRight_apply]

def nL : (VS D).V →ₗ[D.host.E] (VS D).V :=
  ∑ c, ((VS D).hT (X.fY c)).smulRight (nE X X0 c) + ∑ c, ((VS D).hT (X.eX c)).smulRight (nF X X0 xs M c) +
    (nWL X xs).comp (pWL X)

theorem nL_apply (y : (VS D).V) : nL X X0 xs M y =
    ∑ c, (VS D).hT (X.fY c) y • nE X X0 c + ∑ c, (VS D).hT (X.eX c) y • nF X X0 xs M c +
      (pW X y + ∑ b, (VS D).hT (xs b) (pW X y) • X.eX b) := by
  simp [nL, nWL, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.comp_apply, pWL_apply]

theorem pW_of_inW {w : (VS D).V} (hw : InW X w) : pW X w = w := by
  unfold pW
  simp [(hw _).1, (hw _).2]

theorem pW_e (a : Fin D.R.rS) : pW X (X.eX a) = 0 := by
  unfold pW
  simp [h_fe, X.ee, Finset.sum_ite_eq']

theorem pW_f (a : Fin D.R.rS) : pW X (X.fY a) = 0 := by
  unfold pW
  simp [X.ef, X.ff, Finset.sum_ite_eq']

theorem nL_e (a : Fin D.R.rS) : nL X X0 xs M (X.eX a) = nE X X0 a := by
  rw [nL_apply, pW_e]
  simp [h_fe, X.ee, Finset.sum_ite_eq']

theorem nL_f (a : Fin D.R.rS) : nL X X0 xs M (X.fY a) = nF X X0 xs M a := by
  rw [nL_apply, pW_f]
  simp [X.ef, X.ff, Finset.sum_ite_eq']

theorem nL_w {w : (VS D).V} (hw : InW X w) : nL X X0 xs M w = w + ∑ b, (VS D).hT (xs b) w • X.eX b := by
  rw [nL_apply, pW_of_inW X hw]
  simp [(hw _).1, (hw _).2]

end Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex
end
end

noncomputable section

open NumberField Formalism.BasicNotions Matrix
open scoped BigOperators

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
  (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)

theorem h_sum_left (a : Fin D.R.rS → D.host.E) (x : Fin D.R.rS → (VS D).V) (y : (VS D).V) :
    (VS D).hT (∑ c, a c • x c) y = ∑ c, star (a c) * (VS D).hT (x c) y := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ₂, starRingEnd_apply]

theorem h_sum_right (a : Fin D.R.rS → D.host.E) (x : Fin D.R.rS → (VS D).V) (y : (VS D).V) :
    (VS D).hT y (∑ c, a c • x c) = ∑ c, a c * (VS D).hT y (x c) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_smul]

theorem h_e_nF (hxs : ∀ b, InW X (xs b)) (c b : Fin D.R.rS) : (VS D).hT (X.eX c) (nF X X0 xs M b) = Ym X0 c b := by
  unfold nF om
  rw [map_add (f := _), map_add (f := _), map_neg, h_sum_right, h_sum_right, h_sum_right]
  have hx1 : ∀ c d, (VS D).hT (X.eX c) (xs d) = 0 := fun c d => (hxs d c).1
  simp [X.ef, X.ee, hx1, Finset.sum_ite_eq]

theorem h_f_nF (hxs : ∀ b, InW X (xs b)) (c b : Fin D.R.rS) : (VS D).hT (X.fY c) (nF X X0 xs M b) = (X0 * M) c b := by
  unfold nF om
  rw [map_add (f := _), map_add (f := _), map_neg, h_sum_right, h_sum_right, h_sum_right]
  have hx2 : ∀ c d, (VS D).hT (X.fY c) (xs d) = 0 := fun c d => (hxs d c).2
  simp [X.ff, h_fe, hx2, Finset.sum_ite_eq]

theorem h_xs_nF (hxs : ∀ b, InW X (xs b)) (c b : Fin D.R.rS) :
    (VS D).hT (xs c) (nF X X0 xs M b) = -∑ d, Ym X0 d b * (VS D).hT (xs c) (xs d) := by
  unfold nF om
  rw [map_add (f := _), map_add (f := _), map_neg, h_sum_right, h_sum_right, h_sum_right]
  simp [(inW_left X (hxs c) _).1, (inW_left X (hxs c) _).2]

theorem h_nF_left (a : Fin D.R.rS) (y : (VS D).V) :
    (VS D).hT (nF X X0 xs M a) y = ∑ c, star (Ym X0 c a) * (VS D).hT (X.fY c) y -
      ∑ c, star (Ym X0 c a) * (VS D).hT (xs c) y + ∑ c, star ((X0 * M) c a) * (VS D).hT (X.eX c) y := by
  unfold nF om
  rw [LinearMap.map_add₂, LinearMap.map_add₂, LinearMap.map_neg₂, h_sum_left, h_sum_left, h_sum_left]
  ring

theorem h_nE_left (a : Fin D.R.rS) (y : (VS D).V) :
    (VS D).hT (nE X X0 a) y = ∑ c, star (X0 c a) * (VS D).hT (X.eX c) y := by
  unfold nE
  rw [h_sum_left]

theorem g_ee (a b : Fin D.R.rS) : (VS D).hT (nE X X0 a) (nE X X0 b) = (VS D).hT (X.eX a) (X.eX b) := by
  rw [h_nE_left, X.ee]
  unfold nE
  simp [h_sum_right, X.ee]

theorem g_ef (hinv : X0⁻¹ * X0 = 1) (hxs : ∀ b, InW X (xs b)) (a b : Fin D.R.rS) :
    (VS D).hT (nE X X0 a) (nF X X0 xs M b) = (VS D).hT (X.eX a) (X.fY b) := by
  rw [h_nE_left, X.ef]
  simp_rw [h_e_nF X X0 xs M hxs]
  have h1 : (X0ᴴ * Ym X0) a b = ∑ c, star (X0 c a) * Ym X0 c b := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have h2 : X0ᴴ * Ym X0 = 1 := by
    unfold Ym
    rw [← Matrix.conjTranspose_mul, hinv, Matrix.conjTranspose_one]
  rw [← h1, h2, Matrix.one_apply]

theorem g_ff (hinv : X0⁻¹ * X0 = 1) (hxs : ∀ b, InW X (xs b)) (hM : M + Mᴴ = -Gp D X0 xs) (a b : Fin D.R.rS) :
    (VS D).hT (nF X X0 xs M a) (nF X X0 xs M b) = (VS D).hT (X.fY a) (X.fY b) := by
  rw [h_nF_left, X.ff]
  simp_rw [h_f_nF X X0 xs M hxs, h_xs_nF X X0 xs M hxs, h_e_nF X X0 xs M hxs]
  have hY : (Ym X0)ᴴ = X0⁻¹ := by unfold Ym; rw [Matrix.conjTranspose_conjTranspose]
  have e1 : ∑ c, star (Ym X0 c a) * (X0 * M) c b = M a b := by
    have : ((Ym X0)ᴴ * (X0 * M)) a b = ∑ c, star (Ym X0 c a) * (X0 * M) c b := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [← this, hY, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  have e2 : ∑ c, star ((X0 * M) c a) * Ym X0 c b = Mᴴ a b := by
    have : ((X0 * M)ᴴ * Ym X0) a b = ∑ c, star ((X0 * M) c a) * Ym X0 c b := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [← this, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    unfold Ym
    rw [← Matrix.conjTranspose_mul, hinv, Matrix.conjTranspose_one, Matrix.mul_one]
  have e3 : ∑ c, star (Ym X0 c a) * -∑ d, Ym X0 d b * (VS D).hT (xs c) (xs d) = -(Gp D X0 xs) a b := by
    have : ((Ym X0)ᴴ * Gq D xs * Ym X0) a b = ∑ c, star (Ym X0 c a) * ∑ d, Ym X0 d b * (VS D).hT (xs c) (xs d) := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Gq, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
      ring
    simp only [mul_neg, Finset.sum_neg_distrib]
    rw [← this, hY]
    rfl
  rw [e1, e3, e2]
  have := congrFun (congrFun hM a) b
  simp only [Matrix.add_apply, Matrix.neg_apply] at this
  rw [sub_neg_eq_add]
  linear_combination this

end Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex
end
end

noncomputable section

open NumberField Formalism.BasicNotions Matrix
open scoped BigOperators

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
  (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)

theorem h_e_nLw (hxs : ∀ b, InW X (xs b)) {w : (VS D).V} (hw : InW X w) (c : Fin D.R.rS) :
    (VS D).hT (X.eX c) (nL X X0 xs M w) = 0 := by
  rw [nL_w X X0 xs M hw, map_add (f := _), h_sum_right]
  simp [(hw c).1, X.ee]

theorem h_f_nLw (hxs : ∀ b, InW X (xs b)) {w : (VS D).V} (hw : InW X w) (c : Fin D.R.rS) :
    (VS D).hT (X.fY c) (nL X X0 xs M w) = (VS D).hT (xs c) w := by
  rw [nL_w X X0 xs M hw, map_add (f := _), h_sum_right]
  simp [(hw c).2, h_fe, Finset.sum_ite_eq]

theorem h_xs_nLw (hxs : ∀ b, InW X (xs b)) {w : (VS D).V} (hw : InW X w) (c : Fin D.R.rS) :
    (VS D).hT (xs c) (nL X X0 xs M w) = (VS D).hT (xs c) w := by
  rw [nL_w X X0 xs M hw, map_add (f := _), h_sum_right]
  simp [(inW_left X (hxs c) _).1]

theorem g_ew (hxs : ∀ b, InW X (xs b)) {w : (VS D).V} (hw : InW X w) (a : Fin D.R.rS) :
    (VS D).hT (nE X X0 a) (nL X X0 xs M w) = (VS D).hT (X.eX a) w := by
  rw [h_nE_left, (hw a).1]
  simp [h_e_nLw X X0 xs M hxs hw]

theorem g_fw (hxs : ∀ b, InW X (xs b)) {w : (VS D).V} (hw : InW X w) (a : Fin D.R.rS) :
    (VS D).hT (nF X X0 xs M a) (nL X X0 xs M w) = (VS D).hT (X.fY a) w := by
  rw [h_nF_left, (hw a).2]
  simp [h_e_nLw X X0 xs M hxs hw, h_f_nLw X X0 xs M hxs hw, h_xs_nLw X X0 xs M hxs hw]

theorem g_ww (hxs : ∀ b, InW X (xs b)) {w w' : (VS D).V} (hw : InW X w) (hw' : InW X w') :
    (VS D).hT (nL X X0 xs M w) (nL X X0 xs M w') = (VS D).hT w w' := by
  rw [nL_w X X0 xs M hw, nL_w X X0 xs M hw', LinearMap.map_add₂, map_add (f := _), map_add (f := _), h_sum_left, h_sum_left,
    h_sum_right]
  simp [h_sum_right, (hw' _).1, (inW_left X hw _).1, X.ee]

theorem iso_gen_left (hinv : X0⁻¹ * X0 = 1) (hxs : ∀ b, InW X (xs b)) (hM : M + Mᴴ = -Gp D X0 xs)
    (g : (VS D).V) (hg : ∀ c, (VS D).hT (nL X X0 xs M g) (nL X X0 xs M (X.eX c)) = (VS D).hT g (X.eX c) ∧
      (VS D).hT (nL X X0 xs M g) (nL X X0 xs M (X.fY c)) = (VS D).hT g (X.fY c))
    (hgw : ∀ w, InW X w → (VS D).hT (nL X X0 xs M g) (nL X X0 xs M w) = (VS D).hT g w) (y : (VS D).V) :
    (VS D).hT (nL X X0 xs M g) (nL X X0 xs M y) = (VS D).hT g y := by
  conv_lhs => rw [decomp X y]
  conv_rhs => rw [decomp X y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, map_smul, smul_eq_mul]
  rw [hgw _ (inW_pW X y)]
  simp only [(hg _).1, (hg _).2]

end Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex
end
end

noncomputable section

open NumberField Formalism.BasicNotions Matrix
open scoped BigOperators

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
  (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)

theorem nL_isom (hinv : X0⁻¹ * X0 = 1) (hxs : ∀ b, InW X (xs b)) (hM : M + Mᴴ = -Gp D X0 xs)
    (x y : (VS D).V) : (VS D).hT (nL X X0 xs M x) (nL X X0 xs M y) = (VS D).hT x y := by
  have he : ∀ a y, (VS D).hT (nL X X0 xs M (X.eX a)) (nL X X0 xs M y) = (VS D).hT (X.eX a) y := fun a y =>
    iso_gen_left X X0 xs M hinv hxs hM (X.eX a)
      (fun c => ⟨by rw [nL_e, nL_e]; exact g_ee X X0 a c, by rw [nL_e, nL_f]; exact g_ef X X0 xs M hinv hxs a c⟩)
      (fun w hw => by rw [nL_e]; exact g_ew X X0 xs M hxs hw a) y
  have hf : ∀ a y, (VS D).hT (nL X X0 xs M (X.fY a)) (nL X X0 xs M y) = (VS D).hT (X.fY a) y := fun a y =>
    iso_gen_left X X0 xs M hinv hxs hM (X.fY a)
      (fun c => ⟨by
          rw [nL_f, nL_e, h_symm, g_ef X X0 xs M hinv hxs c a, ← h_symm],
        by rw [nL_f, nL_f]; exact g_ff X X0 xs M hinv hxs hM a c⟩)
      (fun w hw => by rw [nL_f]; exact g_fw X X0 xs M hxs hw a) y
  have hw : ∀ w, InW X w → ∀ y, (VS D).hT (nL X X0 xs M w) (nL X X0 xs M y) = (VS D).hT w y := fun w hw y =>
    iso_gen_left X X0 xs M hinv hxs hM w
      (fun c => ⟨by rw [nL_e, h_symm, g_ew X X0 xs M hxs hw c, ← h_symm],
        by rw [nL_f, h_symm, g_fw X X0 xs M hxs hw c, ← h_symm]⟩)
      (fun w' hw' => g_ww X X0 xs M hxs hw hw') y
  conv_lhs => rw [decomp X x]
  conv_rhs => rw [decomp X x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
    LinearMap.smul_apply, smul_eq_mul]
  simp only [he, hf, hw _ (inW_pW X x)]

theorem nL_inj (hinv : X0⁻¹ * X0 = 1) (hxs : ∀ b, InW X (xs b)) (hM : M + Mᴴ = -Gp D X0 xs) :
    Function.Injective (nL X X0 xs M) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  refine (VS D).nondeg.1 x fun y => ?_
  rw [← nL_isom X X0 xs M hinv hxs hM x y, hx, map_zero, LinearMap.zero_apply]

def nEq (hinv : X0⁻¹ * X0 = 1) (hxs : ∀ b, InW X (xs b)) (hM : M + Mᴴ = -Gp D X0 xs) :
    (VS D).V ≃ₗ[D.host.E] (VS D).V :=
  LinearEquiv.ofInjectiveEndo (nL X X0 xs M) (nL_inj X X0 xs M hinv hxs hM)

end Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex
end
end

noncomputable section

open NumberField Formalism.BasicNotions Matrix
open scoped BigOperators

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

theorem inv_mul_of_unitri {X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E}
    (h0 : ∀ b a : Fin D.R.rS, a < b → X0 b a = 0) (h1 : ∀ a, X0 a a = 1) : X0⁻¹ * X0 = 1 := by
  have hdet : X0.det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i j hij => h0 i j hij)]
    simp [h1]
  exact Matrix.nonsing_inv_mul X0 (by rw [hdet]; exact isUnit_one)

theorem inW_sub {x y : (VS D).V} (hx : InW X x) (hy : InW X y) : InW X (x - y) := by
  intro c
  rw [map_sub, map_sub, (hx c).1, (hy c).1, (hx c).2, (hy c).2, sub_self]
  exact ⟨rfl, rfl⟩

theorem h_pW_left (y : (VS D).V) {w : (VS D).V} (hw : InW X w) : (VS D).hT y w = (VS D).hT (pW X y) w := by
  conv_lhs => rw [decomp X y]
  rw [LinearMap.map_add₂, LinearMap.map_add₂, h_sum_left, h_sum_left]
  simp [(hw _).1, (hw _).2]

theorem dictEx_holds : DictEx := by
  intro D X u X0 xs M hD
  obtain ⟨h0, h1, hxs, hM⟩ := hD
  have hinv := inv_mul_of_unitri h0 h1
  set n := nEq X X0 xs M hinv hxs hM with hn
  have hnx : ∀ y, n y = nL X X0 xs M y := fun y => rfl
  have hFe : (X.Fu u).e = X.eX := X.Fu_e u
  refine ⟨n, ⟨fun x y => ?_, fun j x hx => ?_, fun x hx => ?_⟩, ?_, ?_, ?_⟩
  ·
    show (VS D).hT (n x) (n y) = (VS D).hT x y
    rw [hnx, hnx]
    exact nL_isom X X0 xs M hinv hxs hM x y
  ·
    show n x - x ∈ (X.Fu u).Xa j
    have hx' : x ∈ (X.Fu u).Xa (j + 1) := hx
    unfold FlagG.Xa at hx' ⊢
    rw [hFe] at hx' ⊢
    refine Submodule.span_induction (p := fun x _ => n x - x ∈ Submodule.span D.host.E (X.eX '' {i | i.1 < j}))
      ?_ ?_ ?_ ?_ hx'
    · rintro _ ⟨i, hi, rfl⟩
      rw [hnx, nL_e]
      unfold nE
      have e1 : ∑ b, X0 b i • X.eX b - X.eX i = ∑ b, (X0 b i - if b = i then 1 else 0) • X.eX b := by
        simp [sub_smul, Finset.sum_sub_distrib, ite_smul]
      rw [e1]
      refine Submodule.sum_mem _ fun b _ => ?_
      by_cases hb : (b : ℕ) < j
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
      · have hbi : i ≤ b := by
          have : (i : ℕ) < j + 1 := hi
          exact Fin.le_def.2 (by omega)
        rcases hbi.lt_or_eq with hlt | heq
        · rw [h0 b i hlt, if_neg (ne_of_gt hlt), sub_zero, zero_smul]
          exact Submodule.zero_mem _
        · subst heq
          rw [h1, if_pos rfl, sub_self, zero_smul]
          exact Submodule.zero_mem _
    · simp
    · intro a b _ _ ha hb
      rw [map_add (f := _), add_sub_add_comm]
      exact Submodule.add_mem _ ha hb
    · intro c a _ ha
      rw [map_smul, ← smul_sub]
      exact Submodule.smul_mem _ _ ha
  ·
    show n x - x ∈ (X.Fu u).X
    have horth : ∀ c, (VS D).hT (X.eX c) x = 0 := by
      intro c
      have hxo : x ∈ Lat.orth (VS D) (X.Fu u).X := hx
      unfold Lat.orth at hxo
      have := (Submodule.mem_iInf _).1 hxo (X.eX c)
      rw [Submodule.mem_iInf] at this
      have hmem : X.eX c ∈ (X.Fu u).X := by
        unfold FlagG.X
        rw [hFe]
        exact Submodule.subset_span ⟨c, rfl⟩
      exact LinearMap.mem_ker.1 (this hmem)
    unfold FlagG.X
    rw [hFe]
    have hdec := decomp X x
    simp only [horth, zero_smul, Finset.sum_const_zero, add_zero] at hdec
    have e1 : n x - x = ∑ c, (VS D).hT (X.fY c) x • (nE X X0 c - X.eX c) +
        ∑ b, (VS D).hT (xs b) (pW X x) • X.eX b := by
      calc n x - x = (∑ c, (VS D).hT (X.fY c) x • nE X X0 c +
            (pW X x + ∑ b, (VS D).hT (xs b) (pW X x) • X.eX b)) -
            (∑ c, (VS D).hT (X.fY c) x • X.eX c + pW X x) := by
            rw [← hdec, hnx, nL_apply]
            simp only [horth, zero_smul, Finset.sum_const_zero, add_zero]
        _ = _ := by
            simp only [smul_sub, Finset.sum_sub_distrib]
            abel
    rw [e1]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ ?_)
      (Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩))
    unfold nE
    exact Submodule.sub_mem _ (Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩))
      (Submodule.subset_span ⟨c, rfl⟩)
  ·
    funext b a
    show (VS D).hT (X.fY b) (n (X.eX a)) = X0 b a
    rw [hnx, nL_e]
    unfold nE
    rw [h_sum_right]
    simp [h_fe, Finset.sum_ite_eq]
  ·
    funext b
    set y := n.symm (X.fY b) with hy
    have hny : n y = X.fY b := n.apply_symm_apply _
    have hd : InW X (pW X y - xs b) := inW_sub X (inW_pW X y) (hxs b)
    have hw0 : ∀ w, InW X w → (VS D).hT (pW X y - xs b) w = 0 := by
      intro w hw
      rw [LinearMap.map_sub₂, ← h_pW_left X y hw]
      have : (VS D).hT y w = (VS D).hT (n y) (n w) := (nL_isom X X0 xs M hinv hxs hM y w).symm
      rw [this, hny, hnx, h_f_nLw X X0 xs M hxs hw, sub_self]
    show pW X y = xs b
    rw [← sub_eq_zero]
    refine (VS D).nondeg.1 _ fun v => ?_
    conv_lhs => rw [decomp X v]
    rw [map_add (f := _), map_add (f := _), h_sum_right, h_sum_right, hw0 _ (inW_pW X v)]
    simp [(inW_left X (inW_pW X y) _).1, (inW_left X (inW_pW X y) _).2, (inW_left X (hxs b) _).1,
      (inW_left X (hxs b) _).2]
  ·
    have hA : Aq X n = X0 * M := by
      funext b a
      show (VS D).hT (X.fY b) (n (X.fY a)) = (X0 * M) b a
      rw [hnx, nL_f, h_f_nF X X0 xs M hxs]
    show (Xq X n)⁻¹ * Aq X n = M
    have hXq : Xq X n = X0 := by
      funext b a
      show (VS D).hT (X.fY b) (n (X.eX a)) = X0 b a
      rw [hnx, nL_e]
      unfold nE
      rw [h_sum_right]
      simp [h_fe, Finset.sum_ite_eq]
    rw [hXq, hA, ← Matrix.mul_assoc, hinv, Matrix.one_mul]

end Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibOnto
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemClosureImage
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Onto

theorem mem_closure_image {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) (H : AddSubgroup A)
    (y : B) : y ∈ AddSubgroup.closure (f '' (H : Set A)) ↔ ∃ t ∈ H, f t = y := by
  rw [← AddSubgroup.coe_map, AddSubgroup.closure_eq, AddSubgroup.mem_map]

variable {D : D7} (X : HidaSetting D)

def embHom : D.host.E →+ (InfinitePlace X.B.I.F → ℂ) where
  toFun := embV X
  map_zero' := by funext v; simp [embV]
  map_add' x y := by funext v; simp [embV]

theorem mem_cl_emb (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)
    (y : InfinitePlace X.B.I.F → ℂ) :
    y ∈ AddSubgroup.closure (embV X '' (I : Set D.host.E)) ↔ ∃ t ∈ I, embV X t = y := by
  have := mem_closure_image (embHom X) ((I : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup) y
  exact this

theorem theta_spec (D : D7) : IsIntegral ℤ (theta D) ∧ theta D + D.host.conj (theta D) = 1 := by
  have h := thetaEx_holds D
  unfold theta
  rw [dite_eq_left h]
  exact h.choose_spec

end Onto

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Onto

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem hc_congr (x y : BV X) (hX : ∀ p, x (Sum.inl (Sum.inl p)) = y (Sum.inl (Sum.inl p)))
    (hR : ∀ b, x (Sum.inl (Sum.inr b)) = y (Sum.inl (Sum.inr b))) : Hc X u x = Hc X u y := by
  funext v
  have h1 : Xc X x v = Xc X y v := by
    ext b a
    simp only [Xc, hX]
  have h2 : Gc X u x v = Gc X u y v := by
    ext b c
    simp only [Gc, hR]
  simp only [Hc, h1, h2]

theorem aaLb_inW {b : Fin D.R.rS} {y : (VS D).V} (hy : y ∈ aaLb X b) : InW X y := by
  rw [aaLb, SetLike.mem_coe] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, -, l, hl, rfl⟩ := hz
    intro a
    obtain ⟨h1, h2⟩ := X.Lb_perp l hl a
    simp only [map_smul, h1, h2, smul_zero, and_self]
  | zero =>
    intro a
    simp only [map_zero, and_self]
  | add z w _ _ hz hw =>
    intro a
    simp only [map_add (f := _), (hz a).1, (hz a).2, (hw a).1, (hw a).2, add_zero, and_self]
  | smul r z _ hz =>
    intro a
    simp only [LinearMap.map_smul_of_tower, (hz a).1, (hz a).2, smul_zero, and_self]

theorem mem_cl_row (b : Fin D.R.rS) (z : InfinitePlace X.B.I.F → Fin (D.R.k + 1) → ℂ) :
    z ∈ AddSubgroup.closure (rowV X u '' aaLb X b) ↔ ∃ y ∈ aaLb X b, rowV X u y = z := by
  exact mem_closure_image (rowHom X u)
    (Submodule.span (𝓞 D.host.E) {y | ∃ c ∈ (aaD D b : Set D.host.E), ∃ l ∈ X.Lb, y = c • l}).toAddSubgroup z

def imH (a : Fin D.R.rS) : AddSubgroup D.host.E where
  carrier := {t | t ∈ ((aaD D a * aaD D a : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
      Set D.host.E) ∧ D.host.conj t = -t}
  zero_mem' := ⟨Submodule.zero_mem _, by simp⟩
  add_mem' := by
    rintro s t ⟨hs1, hs2⟩ ⟨ht1, ht2⟩
    exact ⟨Submodule.add_mem _ hs1 ht1, by rw [map_add (f := _), hs2, ht2, neg_add]⟩
  neg_mem' := by
    rintro s ⟨hs1, hs2⟩
    exact ⟨Submodule.neg_mem _ hs1, by rw [map_neg, hs2]⟩

def imHom : D.host.E →+ (InfinitePlace X.B.I.F → ℝ) where
  toFun t := fun v => (embS D (X.pl v) t).im
  map_zero' := by funext v; simp
  map_add' s t := by funext v; simp

theorem mem_cl_im (a : Fin D.R.rS) (z : InfinitePlace X.B.I.F → ℝ) :
    z ∈ cLat X u (Sum.inr (Sum.inr a)) ↔ ∃ t ∈ imH a, imHom X t = z := by
  exact mem_closure_image (imHom X) (imH a) z

end Onto


open Onto in
theorem fibOnto_holds : FibOnto := by
  intro D X u x hx
  have hA : ∀ p : LsNc5.LtPair D.R.rS, ∃ t ∈ aaD D p.1.1 * (aaD D p.1.2)⁻¹,
      embV X t = x (Sum.inl (Sum.inl p)) := by
    intro p
    have h := hx (Sum.inl (Sum.inl p))
    simp only [tauQ, sub_zero] at h
    exact (mem_cl_emb X _ _).1 h
  have hB : ∀ b : Fin D.R.rS, ∃ y ∈ aaLb X b, rowV X u y = x (Sum.inl (Sum.inr b)) := by
    intro b
    have h := hx (Sum.inl (Sum.inr b))
    simp only [tauQ, sub_zero] at h
    exact (mem_cl_row X u b _).1 h
  have hC : ∀ p : LsNc5.LtPair D.R.rS, ∃ s ∈ aaD D p.1.1 * aaD D p.1.2,
      embV X s = fun v => x (Sum.inr (Sum.inl p)) v - Hc X u x v p.1.1 p.1.2 / 2 :=
    fun p => (mem_cl_emb X _ _).1 (hx (Sum.inr (Sum.inl p)))
  have hD : ∀ a : Fin D.R.rS, ∃ t ∈ imH a, imHom X t =
      fun v => x (Sum.inr (Sum.inr a)) v - -((Hc X u x v a a).re * (embS D (X.pl v) (theta D)).im) :=
    fun a => (mem_cl_im X u a _).1 (hx (Sum.inr (Sum.inr a)))
  choose tA htA htA' using hA
  choose xs hxs hxs' using hB
  choose sC hsC hsC' using hC
  choose tD htD htD' using hD
  obtain ⟨X0, hX0⟩ : ∃ X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E,
      X0 = fun b a => if h : b < a then tA ⟨(b, a), h⟩ else if b = a then 1 else 0 := ⟨_, rfl⟩
  have hup : ∀ b a : Fin D.R.rS, a < b → X0 b a = 0 := by
    intro b a h
    simp [hX0, not_lt_of_gt h, ne_of_gt h]
  have hdg : ∀ a, X0 a a = 1 := by
    intro a
    simp [hX0]
  have hX0p : ∀ p : LsNc5.LtPair D.R.rS, X0 p.1.1 p.1.2 = tA p := by
    intro p
    simp [hX0, p.2]
  have hW : ∀ b, InW X (xs b) := fun b => aaLb_inW X (hxs b)
  have hGh : ∀ i j, star (Gp D X0 xs j i) = Gp D X0 xs i j := by
    intro i j
    have := congrFun (congrFun (Gp_herm X0 xs) i) j
    rwa [Matrix.conjTranspose_apply] at this
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E,
      M = fun b a => if h : b < a then sC ⟨(b, a), h⟩
        else if h' : a < b then -Gp D X0 xs b a - star (sC ⟨(a, b), h'⟩)
        else tD a - Gp D X0 xs a a * theta D := ⟨_, rfl⟩
  have hMlt : ∀ p : LsNc5.LtPair D.R.rS, M p.1.1 p.1.2 = sC p := by
    intro p
    simp [hM, p.2]
  have hMgt : ∀ p : LsNc5.LtPair D.R.rS,
      M p.1.2 p.1.1 = -Gp D X0 xs p.1.2 p.1.1 - star (sC p) := by
    intro p
    simp [hM, p.2, not_lt_of_gt p.2]
  have hMd : ∀ a, M a a = tD a - Gp D X0 xs a a * theta D := by
    intro a
    simp [hM]
  have hth : star (theta D) = 1 - theta D := by
    rw [Inh.tie_star]
    exact eq_sub_of_add_eq' (theta_spec D).2
  have hData : DataOK X X0 xs M := by
    refine ⟨hup, hdg, hW, ?_⟩
    ext i j
    simp only [Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.neg_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · rw [hMlt ⟨(i, j), h⟩, hMgt ⟨(i, j), h⟩, star_sub, star_neg, star_star, hGh]
      ring
    · obtain ⟨-, hc⟩ := htD i
      rw [hMd, star_sub, star_mul', Inh.tie_star D (tD i), hc, hth, hGh]
      ring
    · rw [hMlt ⟨(j, i), h⟩, hMgt ⟨(j, i), h⟩]
      ring
  have hXb : ∀ p, x (Sum.inl (Sum.inl p)) = blkQ X u X0 xs M (Sum.inl (Sum.inl p)) := by
    intro p
    show _ = embV X (X0 p.1.1 p.1.2)
    rw [hX0p]
    exact (htA' p).symm
  have hRb : ∀ b, x (Sum.inl (Sum.inr b)) = blkQ X u X0 xs M (Sum.inl (Sum.inr b)) := by
    intro b
    exact (hxs' b).symm
  have hHc : ∀ v, Hc X u x v = (Gp D X0 xs).map (embS D (X.pl v)) := by
    intro v
    rw [hc_congr X u x _ hXb hRb]
    exact Hc_blkQ X u X0 xs M hup hdg hW v
  refine ⟨X0, xs, M, hData, ?_⟩
  funext p
  rcases p with ((p | b) | (p | a))
  · exact (hXb p).symm
  · exact (hRb b).symm
  · funext v
    show (embS D (X.pl v) (M p.1.1 p.1.2) - star (embS D (X.pl v) (M p.1.2 p.1.1))) / 2 = _
    have hs := congrFun (hsC' p) v
    simp only [embV, hHc v, Matrix.map_apply] at hs
    have e1 : star (embS D (X.pl v) (M p.1.2 p.1.1)) =
        -embS D (X.pl v) (Gp D X0 xs p.1.1 p.1.2) - embS D (X.pl v) (sC p) := by
      rw [hMgt, ← emb_star X, star_sub, star_neg, star_star, hGh, map_sub, map_neg]
    rw [e1, hMlt]
    linear_combination hs
  · funext v
    show (embS D (X.pl v) (M a a)).im = _
    have hs := congrFun (htD' a) v
    simp only [imHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hHc v, Matrix.map_apply] at hs
    have hr : (embS D (X.pl v) (Gp D X0 xs a a)).im = 0 := by
      have := congrArg (embS D (X.pl v)) (hGh a a)
      rw [emb_star X] at this
      exact Complex.conj_eq_iff_im.mp this
    rw [hMd, map_sub, map_mul, Complex.sub_im, Complex.mul_im, hr]
    linear_combination hs

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibPl
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.Pf.NcReal.JX Formalism.L2.SG.TermOp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pl

variable {D : D7} (X : HidaSetting D)

theorem umat_rv {x : X.B.I.GA} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hRL : RatLink X x n) (v : InfinitePlace X.B.I.F)
    (y : (VS D).V) : uMat (x.1 v) *ᵥ rv X.B.I v (X.crd y) = rv X.B.I v (X.crd (n y)) := by
  obtain ⟨M, -, hv, -, hcrd⟩ := hRL
  rw [hv v, Formalism.L2.SG.Pf.rv_mulVec, ← hcrd]

theorem inv_map_emb {m : ℕ} {K L : Type*} [Field K] [Field L] (f : K →+* L) (A : Matrix (Fin m) (Fin m) K) :
    (A.map f)⁻¹ = A⁻¹.map f := by
  have h1 : (A.map f).det = f A.det := (f.map_det A).symm
  have h2 : (A.map f).adjugate = A.adjugate.map f := (f.map_adjugate A).symm
  rw [Matrix.inv_def, Matrix.inv_def, h1, h2, Ring.inverse_eq_inv', Ring.inverse_eq_inv', ← map_inv₀]
  ext i j
  simp [Matrix.smul_apply]

theorem hJ_span_ef (v : InfinitePlace X.B.I.F) (α β : Fin D.R.rS → D.host.E) (w : Fin X.B.I.n → ℂ)
    (he : ∀ c, hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.eX c))) w = 0)
    (hf : ∀ c, hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.fY c))) w = 0) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.crd (∑ c, α c • X.eX c + ∑ c, β c • X.fY c))) w = 0 := by
  rw [Formalism.L2.SG.NormCut.crd_add', Formalism.L2.SG.NormCut.crd_sum', Formalism.L2.SG.NormCut.crd_sum']
  simp only [Formalism.L2.SG.NormCut.crd_smul']
  have rv_add (a b : Fin X.B.I.n → X.B.I.E) : rv X.B.I v (a + b) = rv X.B.I v a + rv X.B.I v b := by
    unfold rv
    rw [← Matrix.mulVec_add]
    congr 1
    ext i
    simp
  rw [rv_add, Formalism.L2.SG.RealObj.RealFramesCharacters.rv_sum, Formalism.L2.SG.RealObj.RealFramesCharacters.rv_sum,
    Formalism.L2.SG.RealObj.InfCut.ProductExactness.hJ_add_l, Formalism.L2.SG.RealObj.HermitianSumRootCoordinateFrames.hJ_sum_left,
    Formalism.L2.SG.RealObj.HermitianSumRootCoordinateFrames.hJ_sum_left]
  simp only [he, hf, mul_zero, Finset.sum_const_zero, add_zero]

end Pl

section Main

theorem dictionary_place_holds : DictPlace := by
  intro D X u x n hRL hNF
  set ψ : InfinitePlace X.B.I.F → D.host.E →+* ℂ := fun v => embS D (X.pl v) with hψ
  have hxM : ∀ v, LsNc5.xMat X v x.1 = (Xq X n).map (ψ v) := fun v => by
    ext b a
    simp only [LsNc5.xMat, LsNc5.fV, LsNc5.eV, Matrix.map_apply]
    rw [show X.eR a = X.crd (X.eX a) from rfl, umat_rv X hRL v, show X.fR b = X.crd (X.fY b) from rfl,
      Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX]
    rfl
  have haM : ∀ v, LsNc5.aMat X v x.1 = (Aq X n).map (ψ v) := fun v => by
    ext b a
    simp only [LsNc5.aMat, LsNc5.fV, Matrix.map_apply]
    rw [show X.fR a = X.crd (X.fY a) from rfl, umat_rv X hRL v, show X.fR b = X.crd (X.fY b) from rfl,
      Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX]
    rfl
  have hmM : ∀ v, LsNc5.mMat X v x.1 = (Mq X n).map (ψ v) := fun v => by
    unfold LsNc5.mMat Mq
    rw [hxM, haM, inv_map_emb, Matrix.map_mul]

  have hrow : ∀ v b (w : Fin X.B.I.n → ℂ), (∀ c, hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.eX c))) w = 0) →
      (∀ c, hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.fY c))) w = 0) →
      hJ (X.B.I.ε v) (LsNc5.fV X v b) (uMat (x.1 v) *ᵥ w) = hJ (X.B.I.ε v) (rv X.B.I v (X.crd (xq X n b))) w := by
    intro v b w he hf
    have h1 := Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.hJ_inv_r (X.B.I.ε v) (x.1 v)⁻¹ (LsNc5.fV X v b) w
    rw [inv_inv] at h1
    rw [h1]
    have h2 : uMat (x.1 v)⁻¹ *ᵥ LsNc5.fV X v b = rv X.B.I v (X.crd (n.symm (X.fY b))) :=
      umat_rv X (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X hRL) v (X.fY b)
    rw [h2]
    have hy : n.symm (X.fY b) = xq X n b + (∑ c, (VS D).hT (X.fY c) (n.symm (X.fY b)) • X.eX c +
        ∑ c, (VS D).hT (X.eX c) (n.symm (X.fY b)) • X.fY c) := by
      simp only [xq, pW]; abel
    have rv_add (a b : Fin X.B.I.n → X.B.I.E) : rv X.B.I v (a + b) = rv X.B.I v a + rv X.B.I v b := by
      unfold rv
      rw [← Matrix.mulVec_add]
      congr 1
      ext i
      simp
    rw [hy, Formalism.L2.SG.NormCut.crd_add', rv_add, Formalism.L2.SG.RealObj.InfCut.ProductExactness.hJ_add_l,
      hJ_span_ef X v _ _ w he hf, add_zero]
  funext p
  rcases p with ((p | b) | (p | a))
  · funext v
    show LsNc5.xMat X v x.1 p.1.1 p.1.2 = embS D (X.pl v) (Xq X n p.1.1 p.1.2)
    rw [hxM]; rfl
  · funext v j
    show (if h : j.val < D.R.k then LsNc5.phiMat X u v x.1 b ⟨j.val, h⟩ else LsNc5.yVec X u v x.1 b) =
      rowV X u (xq X n b) v j
    unfold rowV
    split_ifs with h
    · exact hrow v b _ (fun c => ((X.wfr_perp u v ⟨j.val, h⟩).1 c).1) (fun c => ((X.wfr_perp u v ⟨j.val, h⟩).1 c).2)
    · refine hrow v b _ (fun c => ?_) (fun c => ?_)
      · show hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.eX c))) (rv X.B.I v (X.crd (X.zu u))) = 0
        rw [Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX, (X.zu_orth u c).1, map_zero]
      · show hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.fY c))) (rv X.B.I v (X.crd (X.zu u))) = 0
        rw [Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX, (X.zu_orth u c).2, map_zero]
  · funext v
    show (LsNc5.mMat X v x.1 p.1.1 p.1.2 - star (LsNc5.mMat X v x.1 p.1.2 p.1.1)) / 2 =
      (embS D (X.pl v) (Mq X n p.1.1 p.1.2) - star (embS D (X.pl v) (Mq X n p.1.2 p.1.1))) / 2
    rw [hmM]; rfl
  · funext v
    show (LsNc5.mMat X v x.1 a a).im = (embS D (X.pl v) (Mq X n a a)).im
    rw [hmM]; rfl

end Main

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

theorem nofibLat_of_rest (hL : DictLat) (hE : DictEx) (hF : FibQ) (hO : FibOnto) : NOfibLat := by
  have hR : NOratC := by first | exact @noratC_holds | exact @noratC_proved | exact @noratC | exact @nOratC_holds | exact @noratC_of | exact @NOratC_holds
  have hG : DictGram := by first | exact @dictGram_holds | exact @dictGram_proved | exact @dictGram | exact @DictGram_holds | exact @dictGram_of
  have hP : DictPlace := by first | exact @dictionary_place_holds | exact @dictPlace_holds | exact @dictPlace_proved | exact @dictPlace | exact @DictPlace_holds | exact @dictPlace_of
  exact @nofibLat_of hR hG hL hE hP hF hO

theorem nofib_of_rest (hL : DictLat) (hE : DictEx) (hF : FibQ) (hO : FibOnto) : NOfib := @Formalism.L2.SG.Pf.NcReal.JX.nofib_of (@nofibLat_of_rest hL hE hF hO)

theorem nOfib_of_dict_fib (hB : DictLatB) (hF : FibQ) (hO : FibOnto) : NOfib := by
  have hLF : DictLatF := by first | exact @dictLatF_proof | exact @dictLatF_holds | exact @dictLatF_proved | exact @dictLatF | exact @DictLatF_holds | exact @dictLatF_of
  have hL : DictLat := @dictLat_of hLF hB
  have hE : DictEx := @Ex.dictEx_holds
  exact @nofib_of_rest hL hE hF hO

theorem nofib_of_fib (hF : FibQ) (hO : FibOnto) : NOfib := by
  have hB : DictLatB := by first | exact @dictLatB_proof | exact @dictLatB_holds | exact @dictLatB_proved | exact @dictLatB | exact @DictLatB_holds | exact @dictLatB_of
  exact @nOfib_of_dict_fib hB hF hO

theorem nofib_of_fibQ (hF : FibQ) : NOfib := by
  have hO : FibOnto := by first | exact @fibOnto_proof | exact @fibOnto_holds | exact @fibOnto_proved | exact @fibOnto | exact @FibOnto_holds | exact @fibOnto_of
  exact @nofib_of_fib hF hO

end Formalism.L2.SG.Pf.NcReal.JX.NOf
