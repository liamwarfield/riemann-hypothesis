module

public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.RowActSrcN

@[expose] public section

section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.NuTAntitone
section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.HinjX
section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.ProdRowAct
section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.PolyKTorsionFree
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.L2.G.Model.TS Formalism.L2.G.Model

section dual

variable {O K : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] [CharZero K]

lemma toK_eq_map {σ : Type} (f : MvPolynomial σ O) : toK O K f = map (algebraMap O K) f := rfl

lemma polyK_torsionFree {σ : Type} : Module.IsTorsionFree O (MvPolynomial σ K) := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun a f h => ?_
  rw [← algebraMap_smul K a f, smul_eq_zero] at h
  rcases h with h | h
  · left; exact (IsFractionRing.injective O K) (by rw [h, map_zero])
  · right; exact h

lemma weylK_fg {n : ℕ} (ν : Fin n → ℕ) (hν : Antitone ν) :
    ((weyl O n n le_rfl ν).map (toK O K)).FG := by
  have hM : ((dualWeyl O n n ν).map (toK O K)).FG := by
    apply Submodule.FG.map
    obtain ⟨b, hb, -⟩ := sSBasis O n n ν
    rw [← hb.2.1]
    have := (sSIdxFinite n n ν).to_subtype
    exact Submodule.fg_span (Set.finite_range b)
  have hle : (weyl O n n le_rfl ν).map (toK O K) ≤ (dualWeyl O n n ν).map (toK O K) :=
    Submodule.map_mono (weylLeDual O n n le_rfl ν hν)
  have := isNoetherian_of_fg_of_noetherian _ hM
  have h := IsNoetherian.noetherian (((weyl O n n le_rfl ν).map (toK O K)).comap
    ((dualWeyl O n n ν).map (toK O K)).subtype)
  have h2 := h.map ((dualWeyl O n n ν).map (toK O K)).subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hle] at h2

end dual

theorem dual_bases_holds : DualBases := by
  intro O K _ _ _ _ _ _ _ n ν hν
  classical
  set c := fockR (hw K (le_rfl : n ≤ n) ν) (hw K le_rfl ν) with hc
  set D := (weyl O n n le_rfl ν).map (toK O K) with hD
  have : Module.IsTorsionFree O (MvPolynomial (Fin n × Fin n) K) := polyK_torsionFree
  have : Module.Finite O D := Module.Finite.iff_fg.mpr (weylK_fg ν hν)
  obtain ⟨N, bD⟩ := Module.basisOfFiniteTypeTorsionFree' (R := O) (M := D)
  set e : Fin N → MvPolynomial (Fin n × Fin n) K := fun i => (bD i : MvPolynomial (Fin n × Fin n) K) with he_def
  have he : ∀ i, e i ∈ D := fun i => (bD i).2
  have hDV : ∀ x ∈ D, x ∈ dualWeyl K n n ν := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    rw [toK_eq_map]
    exact weylLeDual K n n le_rfl ν hν (sw_weyl_map (algebraMap O K) le_rfl ν y hy)
  have hrep : ∀ x (hx : x ∈ D), x = ∑ i, bD.repr ⟨x, hx⟩ i • e i := by
    intro x hx
    have h := congrArg Subtype.val (bD.sum_repr ⟨x, hx⟩)
    rw [Submodule.coe_sum] at h
    simpa [he_def] using h.symm
  have hsm : ∀ (a : O) (f : MvPolynomial (Fin n × Fin n) K), a • f = algebraMap O K a • f :=
    fun a f => (algebraMap_smul K a f).symm
  have hDspan : ∀ x ∈ D, x ∈ Submodule.span K (Set.range e) := by
    intro x hx
    rw [hrep x hx]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hsm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hspan : dualWeyl K n n ν ≤ Submodule.span K (Set.range e) := by
    rw [← sw_weyl_eq K n n le_rfl ν hν]
    unfold weyl
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    apply hDspan
    refine Submodule.mem_map.mpr ⟨applyWord O w (hw O le_rfl ν), Submodule.subset_span ⟨w, rfl⟩, ?_⟩
    rw [toK_eq_map, ← lclosedeq_applyWord_map, lclosedeq_hw_map]
  have hliO : LinearIndependent O e := bD.linearIndependent.map' D.subtype (Submodule.ker_subtype D)
  have hli : LinearIndependent K e := (LinearIndependent.iff_fractionRing O K).mp hliO
  set W := Submodule.span K (Set.range e) with hW
  have hWV : W = dualWeyl K n n ν := by
    refine le_antisymm ?_ hspan
    rw [hW, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hDV _ (he i)
  let bW : Module.Basis (Fin N) K W := Module.Basis.span hli
  have hbW : ∀ i, (bW i : MvPolynomial (Fin n × Fin n) K) = e i := fun i =>
    congrArg Subtype.val (Module.Basis.span_apply hli i)
  let Bf : LinearMap.BilinForm K W := LinearMap.mk₂ K (fun x y : W => fockR (x : MvPolynomial (Fin n × Fin n) K) y)
    (fun x x' y => by simp [fockR_add_left]) (fun a x y => by simp [fockR_smul_left])
    (fun x y y' => by simp [fockR_add_right]) (fun a x y => by simp [fockR_smul_right])
  have hBf : ∀ x y : W, Bf x y = fockR (x : MvPolynomial (Fin n × Fin n) K) y := fun _ _ => rfl
  have hnd : Bf.Nondegenerate := by
    constructor
    · intro x hx
      apply Subtype.ext
      refine Top.nondegK K n n le_rfl ν hν x.1 (hWV ▸ x.2) fun P hP => ?_
      rw [fockR_symm]
      exact hx ⟨P, hWV ▸ hP⟩
    · intro y hy
      apply Subtype.ext
      exact Top.nondegK K n n le_rfl ν hν y.1 (hWV ▸ y.2) fun P hP => hy ⟨P, hWV ▸ hP⟩
  let d := Bf.dualBasis hnd bW
  have hd : ∀ i k, fockR (e i) (d k : MvPolynomial (Fin n × Fin n) K) = if i = k then 1 else 0 := by
    intro i k
    have h := LinearMap.BilinForm.apply_dualBasis_left hnd bW k i
    rw [hBf, hbW, fockR_symm] at h
    exact h
  refine ⟨Fin N, inferInstance, inferInstance, e, fun k => c • (d k : MvPolynomial (Fin n × Fin n) K),
    he, ?_, ?_, hspan⟩
  · intro k
    have hkV : c • (d k : MvPolynomial (Fin n × Fin n) K) ∈ dualWeyl K n n ν :=
      Submodule.smul_mem _ _ (hWV ▸ (d k).2)
    refine Top.dualWeylIn O K n n le_rfl ν hν _ hkV fun P hP => ⟨bD.repr ⟨P, hP⟩ k, ?_⟩
    show fockR P (c • (d k : MvPolynomial (Fin n × Fin n) K)) = _
    conv_lhs => rw [hrep P hP]
    rw [fockR_sum_left]
    simp_rw [hsm, fockR_smul_left, fockR_smul_right, hd]
    simp [hc]
  · intro i k
    rw [fockR_smul_right, hd]
    split_ifs <;> simp

end Formalism.L2.PairingIndexBounds.Ent
end
end

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

theorem mF_mul (j : ℕ) (b : BX X) (A B : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq b.1)) :
    mF X j b A * mF X j b B = mF X j b (A * B) := by
  simp only [mF]
  rw [Matrix.submatrix_mul_equiv]
  congr 1
  ext i k
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul]

theorem mF_one (j : ℕ) (b : BX X) : mF X j b 1 = 1 := by
  ext i k
  by_cases h : i = k <;> simp [mF, Matrix.one_apply, h]

theorem mF_inv_mul (j : ℕ) (b : BX X) (g : GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq b.1)) :
    mF X j b ((g⁻¹ : GL _ _) : Matrix _ _ (X.G.P.Qq b.1)) * mF X j b (g : Matrix _ _ (X.G.P.Qq b.1)) = 1 := by
  rw [mF_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, mF_one]

theorem mF_det_ne (j : ℕ) (b : BX X) (g : GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq b.1)) :
    (mF X j b (g : Matrix _ _ (X.G.P.Qq b.1))).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (mF_inv_mul X j b g)
  rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at this
  exact zero_ne_one this

variable (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc]

def PhiX (j : ℕ) (l : XspC (X.Pj (j + 1)) Kc →ₗ[Kc] Kc) (a : Kc) (f : MvPowerSeries (X.ZA j) Kc) :
    (X.Pj j).Xsp →ₗ[X.G.Kf] Kc :=
  ((LinearMap.mulLeft Kc a).restrictScalars X.G.Kf) ∘ₗ (l.restrictScalars X.G.Kf) ∘ₗ ((delF X Kc j).flip f)

theorem PhiX_apply (j : ℕ) (l : XspC (X.Pj (j + 1)) Kc →ₗ[Kc] Kc) (a : Kc) (f : MvPowerSeries (X.ZA j) Kc) (G : (X.Pj j).Xsp) :
    PhiX X Kc j l a f G = a * l (delF X Kc j G f) := rfl

def WT (j : ℕ) : Submodule Kc (XspC (X.Pj (j + 1)) Kc) :=
  Submodule.span Kc {z | ∃ F : BX X → MvPolynomial (Fin (NJ X (j + 1)) × Fin (NJ X (j + 1))) X.G.Kf,
    (∀ b, F b ∈ dualWeyl X.G.Kf (NJ X (j + 1)) (NJ X (j + 1)) (nuT X j b)) ∧
      z = map (algebraMap X.G.Kf Kc) (∏ b, rename (emX X (j + 1) b) (F b))}

private theorem prod_rowAct_lemma {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (d : K) :
    rowAct K M (C d : MvPolynomial (Fin n × Fin n) K) = C d := by
  simp [rowAct]

private theorem prod_rowAct_lemma_2 {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    (yV K n).map (rowAct K M) = M.map C * yV K n := by
  ext a t
  simp [yV, BidetPairing.rowAct_X', Matrix.mul_apply]

private theorem prod_rowAct_lemma_3 {K : Type} [Field K] {n : ℕ} (A B : Matrix (Fin n) (Fin n) K)
    (y : Fin n → ℕ → K) : mulC A (mulC B y) = mulC (A * B) y := by
  funext a i
  simp only [mulC, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

private theorem prod_rowAct_lemma_4 {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (y : Fin n → ℕ → K) :
    mulC (M.map (C : K →+* MvPolynomial (Fin n × Fin n) K)) (fun a i => C (y a i)) =
      fun a i => C (mulC M y a i) := by
  funext a i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [mulC, map_sum, map_mul]

private theorem prod_rowAct_lemma_5 {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (hM : M.det ≠ 0) (y : Fin n → ℕ → K) (c : ℕ) (h : Fin c → ℕ) :
    rowAct K M (hvO (fun a i => C (y a i)) (yV K n) c h) =
      C (M.det ^ c) * hvO (fun a i => C (mulC M⁻¹ y a i)) (yV K n) c h := by
  show (rowAct K M).toRingHom _ = _
  rw [map_hvO]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, prod_rowAct_lemma]
  rw [prod_rowAct_lemma_2]
  have hy : (fun a i => (C (y a i) : MvPolynomial (Fin n × Fin n) K)) =
      mulC (M.map (C : K →+* MvPolynomial (Fin n × Fin n) K)) (fun a i => C (mulC M⁻¹ y a i)) := by
    rw [prod_rowAct_lemma_4, prod_rowAct_lemma_3, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hM),
      mulC_one']
  rw [hy, hvO_mul]
  congr 1
  rw [map_pow, RingHom.map_det, RingHom.mapMatrix_apply]

private theorem prod_rowAct_lemma_6 {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (y : Fin n → ℕ → K) (c : ℕ) (h : Fin c → ℕ) (hh : ∀ k : Fin c, h k ≤ n) :
    rowAct K M (hvE (fun a i => C (y a i)) (yV K n) c h hh) =
      hvE (fun a i => C (mulC M.transpose y a i)) (yV K n) c h hh := by
  show (rowAct K M).toRingHom _ = _
  rw [map_hvE]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, prod_rowAct_lemma]
  rw [prod_rowAct_lemma_2, hvE_mul, ← Matrix.transpose_map, prod_rowAct_lemma_4]

private theorem prod_rowAct_lemma_7 (j : ℕ) (b : BX X) (M : Matrix (Fin (NJ X j)) (Fin (NJ X j)) X.G.Kf)
    (hM : M.det ≠ 0) (y : Fin (NJ X j) → ℕ → X.G.Kf) :
    ∃ (c : X.G.Kf) (y'' : Fin (NJ X j) → ℕ → X.G.Kf),
      rowAct X.G.Kf M (srcN X j b y) = c • srcN X j b y'' := by
  unfold srcN
  split_ifs with hb
  · exact ⟨M.det ^ cX X j b, mulC M⁻¹ y, by rw [prod_rowAct_lemma_5 M hM, MvPolynomial.smul_eq_C_mul]⟩
  · refine ⟨(M.det ^ eX X j b)⁻¹, mulC M.transpose y, ?_⟩
    rw [map_mul, prod_rowAct_lemma, prod_rowAct_lemma_6, MvPolynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul]
    congr 2
    have hd : (Matrix.of fun (a i : Fin (NJ X j)) => mulC M.transpose y a ↑i) =
        M.transpose * Matrix.of fun (a i : Fin (NJ X j)) => y a ↑i := by
      ext a i
      simp [mulC, Matrix.mul_apply]
    rw [hd, Matrix.det_mul, Matrix.det_transpose, mul_pow, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ hM), one_mul]

theorem prod_rowAct (j : ℕ) (g : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) (x : X.FrI j → X.G.Kf) :
    ∃ (a : X.G.Kf) (x'' : ∀ b : BX X, Fin (NJ X j) → ℕ → X.G.Kf),
      ∏ b, rename (emX X j b) (rowAct X.G.Kf (mF X j b ((g b.1)⁻¹ : GL _ _))
        (evX (fun s => x (xmX X j b s)) (HgX X X.G.Kf j b))) = a • ∏ b, rename (emX X j b) (srcN X j b (x'' b)) := by
  have key : ∀ b : BX X, ∃ (c : X.G.Kf) (y'' : Fin (NJ X j) → ℕ → X.G.Kf),
      rename (emX X j b) (rowAct X.G.Kf (mF X j b ((g b.1)⁻¹ : GL _ _))
        (evX (fun s => x (xmX X j b s)) (HgX X X.G.Kf j b))) =
        c • rename (emX X j b) (srcN X j b y'') := by
    intro b
    rw [evX_HgX]
    obtain ⟨c, y'', hc⟩ := prod_rowAct_lemma_7 X j b _ (mF_det_ne X j b (g b.1)⁻¹) _
    exact ⟨c, y'', by rw [hc, MvPolynomial.smul_eq_C_mul, map_mul, rename_C, MvPolynomial.smul_eq_C_mul]⟩
  choose c y'' hc using key
  refine ⟨∏ b, c b, y'', ?_⟩
  rw [Finset.prod_congr rfl (fun b _ => hc b)]
  simp only [MvPolynomial.smul_eq_C_mul, Finset.prod_mul_distrib, map_prod]

end Formalism.L2.PairingIndexBounds.Ent
end
end

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf]
  (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] [CharZero Kc]

theorem hinjX : Function.Injective (algebraMap X.G.O X.G.Kf) := IsFractionRing.injective X.G.O X.G.Kf

theorem phi_mem (hS : XShape) (hBrS : XBrS) (hInj : XInj) (j : ℕ) (L : (X.Pj j).Tup)
    (g : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
    (hg : ∀ v, X.latAt v j L = colSpan (X.G.P.W v) (g v : Matrix _ _ (X.G.P.Qq v)))
    (M : AddSubgroup Kc) (hM : ∀ (o : X.G.O), ∀ a ∈ M, algebraMap X.G.Kf Kc (algebraMap X.G.O X.G.Kf o) * a ∈ M)
    (Φ : (X.Pj j).Xsp →ₗ[X.G.Kf] Kc) (A : MvPolynomial (X.FrI j) Kc) (hA : ∀ m, AddMonoidAlgebra.coeff A m ∈ M)
    (hnum : ∀ x : X.FrI j → X.G.Kf, Φ (sX X j (fun v => g v) • ∏ b, rename (emX X j b) (rowAct X.G.Kf (mF X j b ((g b.1)⁻¹ : GL _ _))
      (evX (fun s => x (xmX X j b s)) (HgX X X.G.Kf j b)))) = eval (fun t => algebraMap X.G.Kf Kc (x t)) A) :
    ∀ G ∈ (X.Pj j).HtupW L, Φ G ∈ M := by
  have : CharZero X.G.Kf := (algebraMap X.G.Kf Kc).charZero
  let T : Submodule X.G.O (X.Pj j).Xsp :=
    { carrier := {G | Φ G ∈ M}
      add_mem' := fun {a b} ha hb => by
        show Φ (a + b) ∈ M
        rw [map_add (f := _)]; exact M.add_mem ha hb
      zero_mem' := by show Φ 0 ∈ M; rw [map_zero]; exact M.zero_mem
      smul_mem' := fun o G hG => by
        show Φ (o • G) ∈ M
        rw [← algebraMap_smul X.G.Kf o G, map_smul, Algebra.smul_def]
        exact hM o _ hG }
  refine hBrS p X (hinjX X) j L (fun v => g v) (fun v => (Matrix.isUnit_iff_isUnit_det _).1 (g v).isUnit) hg T ?_
  intro F hF
  let Φ' : (X.Pj j).Xsp →ₗ[X.G.Kf] Kc := Φ ∘ₗ (LinearMap.lsmul X.G.Kf (X.Pj j).Xsp (sX X j fun v => g v))
  exact src_abs (O := X.G.O) (emX X j) (xmX X j) (hInj p X j).2 (nuM X j) (fun b => mF X j b (g b.1))
    (fun b => mF X j b ((g b.1)⁻¹ : GL _ _)) (fun b => mF_inv_mul X j b (g b.1)) M hM (HgX X X.G.Kf j) (hQX X hS j) Φ' A hA hnum
    interpolation_holds coefficient_product_holds F hF

theorem xSpan (hS : XShape) (hBrS : XBrS) (hInj : XInj) (hSp : XSpanN) (j : ℕ) (L : (X.Pj j).Tup)
    (g : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
    (hg : ∀ v, X.latAt v j L = colSpan (X.G.P.W v) (g v : Matrix _ _ (X.G.P.Qq v)))
    (f : MvPowerSeries (X.ZA j) Kc) (G : (X.Pj j).Xsp) (hG : G ∈ (X.Pj j).HtupW L) : delF X Kc j G f ∈ WT X Kc j := by
  by_contra hne
  obtain ⟨l, hl1, hl2⟩ := Submodule.exists_le_ker_of_notMem hne
  have h0 := phi_mem X Kc hS hBrS hInj j L g hg ⊥ (fun o a ha => by
    rw [AddSubgroup.mem_bot] at ha ⊢; rw [ha, mul_zero]) (PhiX X Kc j l 1 f) 0 (fun m => by simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, AddSubgroup.zero_mem])
    (fun x => by
      obtain ⟨a, x'', hx⟩ := prod_rowAct X j g x
      rw [hx, map_zero, PhiX_apply, one_mul, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply]
      have h1 : delF X Kc j (∏ b, rename (emX X j b) (srcN X j b (x'' b))) f ∈ WT X Kc j := hSp p X Kc j x'' f
      have h2 : l (delF X Kc j (∏ b, rename (emX X j b) (srcN X j b (x'' b))) f) = 0 := hl2 h1
      rw [← algebraMap_smul Kc (sX X j fun v => g v), ← algebraMap_smul Kc a, map_smul, map_smul, h2, smul_zero, smul_zero]) G hG
  rw [AddSubgroup.mem_bot, PhiX_apply, one_mul] at h0
  exact hl1 h0

end Formalism.L2.PairingIndexBounds.Ent
end
end

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf]
  (Kc : Type) [Field Kc] [Algebra (MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] [CharZero Kc]

theorem nuT_antitone (hS : XShape) (j : ℕ) (b : BX X) : Antitone (nuT X j b) := by
  obtain ⟨-, -, hanti, -⟩ := hS p X j b
  unfold nuT
  split_ifs
  · exact BidetPairing.kap_antitone (hanti _) _
  · exact hanti _

theorem shape_szT (hS : XShape) (j : ℕ) (b : BX X) : shapeDeg (szT X j b) = nuT X j b := by
  obtain ⟨-, -, hanti, hle, -⟩ := hS p X j b
  by_cases ho : IsOddPos b.2
  · have h1 : szT X j b = fun k => NJ X (j + 1) - colH (muX X j (NJ X (j + 1)) b) k.val := by
      funext k; exact if_pos ho
    rw [h1, show nuT X j b = _ from if_pos ho]
    exact shape_odd_holds _ _ (hanti _) _ (hle _)
  · have h1 : szT X j b = fun k => colH (muX X j (NJ X (j + 1)) b) k.val := by
      funext k; exact if_neg ho
    rw [h1, show nuT X j b = _ from if_neg ho]
    exact shape_even_holds _ _ (hanti _) _ (hle _)

theorem xPair (hS : XShape) (hBrS : XBrS) (hInj : XInj) (hMid : XMid) (hU : XUnit)
    (Oc : Subring Kc) (hval : ∀ x : Kc, x ∈ Oc ∨ x⁻¹ ∈ Oc)
    (hO : ∀ o : X.G.O, algebraMap X.G.Kf Kc (algebraMap X.G.O X.G.Kf o) ∈ Oc)
    (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) (φ : Frm X j La La') (i0 : X.Pl → ℕ) (h3 : ∀ v, i0 v ≤ X.G.P.r)
    (f : MvPowerSeries (X.ZA j) Kc) (gg : ℝ)
    (hf : ∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ), geX p Oc (AddMonoidAlgebra.coeff (applyD (X.PI j I i0) f) n) gg)
    (G : (X.Pj j).Xsp) (hG : G ∈ (X.Pj j).HtupW La.2)
    (I : ∀ (b : BX X) (k : Fin (cX X j b)), Fin (szT X j b k) → Fin (NJ X (j + 1))) :
    ∃ a ∈ MG p Oc hval gg,
      fockR ((((∏ v : X.Pl, (p : X.G.Kf) ^ (Nprime (X.G.P.lam0 v) (X.w v) (j + 1) (i0 v))) *
            ((∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v j La.2)) *
              (∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v (j + 1) La'.2))⁻¹)) *
            (∏ b : BX X, (mF X (j + 1) b (φ.g' b.1).val * DgX X X.G.Kf j i0 b.1).det ^ (-(eJ X (j + 1) b.1 b.2)))⁻¹) •
          delF X Kc j G (linSub (bc Kc φ) f))
        (map (algebraMap X.G.Kf Kc) (∏ b, rename (emX X (j + 1) b)
          (rowAct X.G.Kf (mF X (j + 1) b (φ.g' b.1).val * DgX X X.G.Kf j i0 b.1).transpose
            (bideterminant X.G.Kf (szT X j b) (szT_le X j b) (I b))))) = a * ∏ b, cN Kc (nuT X j b) := by
  classical
  by_cases hI : ∀ b k, Function.Injective (I b k)
  · obtain ⟨Ist, ε, hε, hmid⟩ := hMid p X Kc j La La' φ i0 I hI
    set TI := map (algebraMap X.G.Kf Kc) (∏ b, rename (emX X (j + 1) b)
      (rowAct X.G.Kf (mF X (j + 1) b (φ.g' b.1).val * DgX X X.G.Kf j i0 b.1).transpose
        (bideterminant X.G.Kf (szT X j b) (szT_le X j b) (I b)))) with hTI
    set cc : Kc := ∏ b, cN Kc (nuT X j b) with hcc
    have hcc0 : cc ≠ 0 := Finset.prod_ne_zero_iff.2 fun b _ => cN_ne Kc _
    set S1 : X.G.Kf := ((∏ v : X.Pl, (p : X.G.Kf) ^ (Nprime (X.G.P.lam0 v) (X.w v) (j + 1) (i0 v))) *
            ((∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v j La.2)) *
              (∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v (j + 1) La'.2))⁻¹)) with hS1
    set s1 : X.G.Kf := (∏ b : BX X, (mF X (j + 1) b (φ.g' b.1).val * DgX X X.G.Kf j i0 b.1).det ^ (-(eJ X (j + 1) b.1 b.2)))⁻¹ with hs1
    have hp0 : (p : Kc) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
    have hu := hU p X Kc Oc hO hp0 j La.2 La'.2 φ.g φ.g' φ.hg φ.hg' i0 h3
    rw [← hS1, ← hs1] at hu
    set U0 := numericalIdentityScalar X Kc j (fun v => φ.g v) (fun v => φ.g' v) i0 with hU0
    have hεO : ε ∈ Oc := by
      rcases hε with h | h
      · rw [h]; exact Oc.one_mem
      · rw [h]; exact Oc.neg_mem Oc.one_mem
    have key := phi_mem X Kc hS hBrS hInj j La.2 φ.g φ.hg (MG p Oc hval gg) (fun o a ha => geX_mul (hO o) ha)
      (PhiX X Kc j (fockL TI) (cc⁻¹ * algebraMap X.G.Kf Kc (S1 * s1)) (linSub (bc Kc φ) f))
      (C (ε * (algebraMap X.G.Kf Kc (S1 * sX X j (fun v => φ.g v) * s1) * U0)) * applyD (X.PI j Ist i0) f)
      (fun m => by
        rw [coeff_C_mul]
        exact geX_mul (Oc.mul_mem hεO hu) (hf Ist m))
      (fun x => by
        rw [PhiX_apply, map_smul, LinearMap.smul_apply, ← algebraMap_smul Kc (sX X j fun v => φ.g v), map_smul, smul_eq_mul]
        show _ * (_ * fockR _ TI) = _
        rw [hmid f x]
        simp only [map_mul, eval_C]
        field_simp) G hG
    refine ⟨_, key, ?_⟩
    rw [PhiX_apply, ← algebraMap_smul Kc (S1 * s1), fockR_smul_left]
    show _ = _ * _ * fockR _ TI * cc
    field_simp
  · push Not at hI
    obtain ⟨b0, k0, hk⟩ := hI
    refine ⟨0, AddSubgroup.zero_mem _, ?_⟩
    have hb : bideterminant X.G.Kf (szT X j b0) (szT_le X j b0) (I b0) = 0 := by
      unfold bideterminant
      exact Finset.prod_eq_zero (Finset.mem_univ k0) (minor_zero_holds _ _ _ _ _ _ hk)
    have hz : (∏ b, rename (emX X (j + 1) b)
        (rowAct X.G.Kf (mF X (j + 1) b (φ.g' b.1).val * DgX X X.G.Kf j i0 b.1).transpose
          (bideterminant X.G.Kf (szT X j b) (szT_le X j b) (I b)))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ b0) (by rw [hb, map_zero, map_zero])
    rw [hz, map_zero, fockR_comm, fockR_zero_left, zero_mul]

end Formalism.L2.PairingIndexBounds.Ent
end
end

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf]
  (Kc : Type) [Field Kc] [Algebra (MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] [CharZero Kc]

theorem admissible_general_lattice_tuple (hS : XShape) (hBrS : XBrS) (hBrT : XBrT) (hInj : XInj) (hSp : XSpanN) (hMid : XMid) (hU : XUnit) (hE : XEdge)
    (Oc : Subring Kc) (hval : ∀ x : Kc, x ∈ Oc ∨ x⁻¹ ∈ Oc)
    (hO : ∀ o : X.G.O, algebraMap X.G.Kf Kc (algebraMap X.G.O X.G.Kf o) ∈ Oc)
    (j : ℕ) (La : X.Lt j) (c' : X.Lv.comp (j + 1)) (L' L'' : (X.Pj (j + 1)).Tup) (i0 : X.Pl → ℕ)
    (h1 : (X.Pj j).IsLatTup La.2) (h2 : (X.Pj (j + 1)).IsLatTup L') (h3 : ∀ v, i0 v ≤ X.G.P.r)
    (h4 : ∀ v' : Fin (X.Pj (j + 1)).nV, (i0 (X.vB (j + 1) v') = 0 ∧ L'' v' = L' v') ∨
      (1 ≤ i0 (X.vB (j + 1) v') ∧ IsEdge p ((X.Pj (j + 1)).n' v') (i0 (X.vB (j + 1) v')) ⟨L'' v', L' v'⟩)) :
    ∃ φ : Frm X j La (c', L''), ∀ (f : MvPowerSeries (X.ZA j) Kc) (gg : ℝ),
      (∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ), geX p Oc (AddMonoidAlgebra.coeff (applyD (X.PI j I i0) f) n) gg) →
      ∀ G ∈ (X.Pj j).HtupW La.2,
        ((∏ v : X.Pl, (p : X.G.Kf) ^ (Nprime (X.G.P.lam0 v) (X.w v) (j + 1) (i0 v))) •
          (((∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v j La.2)) *
            (∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v (j + 1) L''))⁻¹) •
              delF X Kc j G (linSub (bc Kc φ) f))) ∈
        AddSubgroup.closure {y' | ∃ a : Kc, geX p Oc a gg ∧ ∃ z ∈ (X.Pj (j + 1)).HtupW L',
          y' = a • map (algebraMap X.G.Kf Kc) z} := by
  classical
  have cz : CharZero X.G.Kf := (algebraMap X.G.Kf Kc).charZero
  obtain ⟨g', h', hg', hh', hmF⟩ := hE p X j L' L'' i0 h2 h4
  obtain ⟨φ0⟩ := exists_frm X j La (c', L') h1 h2
  let φ : Frm X j La (c', L'') := ⟨φ0.g, g', φ0.hg, hg'⟩
  refine ⟨φ, fun f gg hf G hG => ?_⟩
  set ft := linSub (bc Kc φ) f with hft
  set S1 : X.G.Kf := ((∏ v : X.Pl, (p : X.G.Kf) ^ (Nprime (X.G.P.lam0 v) (X.w v) (j + 1) (i0 v))) *
    ((∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v j La.2)) *
      (∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v (j + 1) L''))⁻¹)) with hS1
  set s' : X.G.Kf := sX X (j + 1) (fun v => (h' v : Matrix _ _ _)) with hs'
  have hs'0 : s' ≠ 0 := Finset.prod_ne_zero_iff.2 fun b _ => zpow_ne_zero _ (mF_det_ne X (j + 1) b (h' b.1))
  have hs'e : s' = ∏ b : BX X, (mF X (j + 1) b (g' b.1 : Matrix _ _ _) * DgX X X.G.Kf j i0 b.1).det ^ (-(eJ X (j + 1) b.1 b.2)) :=
    Finset.prod_congr rfl fun b _ => by rw [hmF b]
  have hy1 := tgt_bidet (O := X.G.O) (Kc := Kc) (emX X (j + 1)) (hInj p X (j + 1)).1 (nuT X j) (nuT_antitone X hS j)
    (fun b => mF X (j + 1) b (h' b.1)) (fun b => mF X (j + 1) b ((h' b.1)⁻¹ : GL _ _)) (fun b => mF_inv_mul X (j + 1) b (h' b.1))
    (MG p Oc hval gg) (fun o a ha => geX_mul (hO o) ha) dual_bases_holds fock_product_holds reorder_holds (cX X j) (szT X j)
    (szT_le X j) (shape_szT X hS j) ((S1 * s'⁻¹) • delF X Kc j G ft)
    (by
      rw [← algebraMap_smul Kc (S1 * s'⁻¹)]
      exact Submodule.smul_mem _ _ (xSpan X Kc hS hBrS hInj hSp j La.2 φ0.g φ0.hg ft G hG))
    (fun I => by
      have := xPair X Kc hS hBrS hInj hMid hU Oc hval hO j La (c', L'') φ i0 h3 f gg hf G hG I
      rw [← hS1, ← hs'e] at this
      simp only [hmF]
      exact this)
  have htr : ∀ z ∈ AddSubgroup.closure {z | ∃ a ∈ MG p Oc hval gg,
      ∃ F : BX X → MvPolynomial (Fin (NJ X (j + 1)) × Fin (NJ X (j + 1))) X.G.Kf,
        (∀ b, F b ∈ deltaL X.G.O X.G.Kf (NJ X (j + 1)) (nuT X j b) (mF X (j + 1) b (h' b.1))) ∧
          z = a • map (algebraMap X.G.Kf Kc) (∏ b, rename (emX X (j + 1) b) (F b))},
      s' • z ∈ AddSubgroup.closure {y' | ∃ a : Kc, geX p Oc a gg ∧ ∃ z ∈ (X.Pj (j + 1)).HtupW L',
        y' = a • map (algebraMap X.G.Kf Kc) z} := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, F, hF, rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨a, ha, s' • ∏ b, rename (emX X (j + 1) b) (F b), ?_, ?_⟩
      · refine hBrT p X (hinjX X) (j + 1) L' (fun v => h' v) (fun v => (Matrix.isUnit_iff_isUnit_det _).1 (h' v).isUnit) hh' F ?_
        intro b
        rw [(hS p X j b).2.1]
        exact hF b
      · rw [smul_comm, smul_eq_C_mul (a := s'), map_mul, map_C, ← smul_eq_C_mul, algebraMap_smul]
    | zero => rw [smul_zero]; exact AddSubgroup.zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact AddSubgroup.add_mem _ hx hy
    | neg x _ hx => rw [smul_neg]; exact AddSubgroup.neg_mem _ hx
  have := htr _ hy1
  rw [smul_smul, mul_comm s', mul_assoc, inv_mul_cancel₀ hs'0, mul_one, hS1, mul_smul] at this
  exact this

end Formalism.L2.PairingIndexBounds.Ent
