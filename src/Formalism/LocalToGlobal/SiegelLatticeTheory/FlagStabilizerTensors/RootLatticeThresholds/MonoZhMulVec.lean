module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotStVKer
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipBasis

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowLast
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.YcUnitary
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotStVFix
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.Pf.Carrier.JointQuot

open Formalism.L2.SG.RealObj

section FixLoc

variable {n r : ℕ} (ε : Fin n → Bool)

theorem hJ_sub_r' (x a b : Fin n → ℂ) :
    Formalism.L2.SG.HidaSetting.hJ ε x (a - b) = Formalism.L2.SG.HidaSetting.hJ ε x a - Formalism.L2.SG.HidaSetting.hJ ε x b := by
  simp only [Formalism.L2.SG.HidaSetting.hJ, Matrix.mulVec_sub, dotProduct_sub]

theorem mem_spanLt_r (e : Fin r → Fin n → ℂ) (x : Fin n → ℂ) (hx : x ∈ Formalism.L2.SG.HidaSetting.spanLt e r) :
    ∃ α : Fin r → ℂ, ∑ a, α a • e a = x := by
  have hset : e '' {b : Fin r | b.1 < r} = Set.range e := by
    rw [← Set.image_univ]
    congr 1
    ext b
    simp [b.isLt]
  unfold Formalism.L2.SG.HidaSetting.spanLt at hx
  rw [hset] at hx
  exact (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx

theorem fix_loc (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (G Gi Y T : Matrix (Fin n) (Fin n) ℂ)
    (hGGi : G * Gi = 1) (hG : ∀ x x', Formalism.L2.SG.HidaSetting.hJ ε (G *ᵥ x) (G *ᵥ x') = Formalism.L2.SG.HidaSetting.hJ ε x x')
    (hee : ∀ a b, Formalism.L2.SG.HidaSetting.hJ ε (e a) (e b) = 0) (hez : ∀ a, Formalism.L2.SG.HidaSetting.hJ ε (e a) z = 0)
    (hez' : ∀ a, Formalism.L2.SG.HidaSetting.hJ ε (e a) z' = 0)
    (π : Fin (r + 1) → Fin (r + 1)) (hπ : ∀ a, π (π a) = a)
    (hP1 : ∀ c b, RealObj.Zhat ε (fam e z) (fam e z') G c b ≠ 0 ↔ c = π b)
    (hYN : ∀ x, (∀ a, Formalism.L2.SG.HidaSetting.hJ ε (e a) x = 0) → (Y - 1) *ᵥ x ∈ Formalism.L2.SG.HidaSetting.spanLt e r)
    (hTN : ∀ x, (∀ a, Formalism.L2.SG.HidaSetting.hJ ε (e a) x = 0) → (T - 1) *ᵥ x ∈ Formalism.L2.SG.HidaSetting.spanLt e r)
    (hYG : Y * G = G * T)
    (hYF : ∀ a, Y *ᵥ fam e z a = fam e z a) (hYGF : ∀ b, Y *ᵥ (G *ᵥ fam e z' b) = G *ᵥ fam e z' b) :
    Y = 1 := by
  set Z := RealObj.Zhat ε (fam e z) (fam e z') G with hZdef
  have hZne : ∀ b, Z (π b) b ≠ 0 := fun b => (hP1 _ _).2 rfl
  have hZ0 : ∀ c b, c ≠ π b → Z c b = 0 := fun c b h => by by_contra h'; exact h ((hP1 c b).1 h')
  have hπi : Function.Injective π := fun a b h => by rw [← hπ a, h, hπ b]
  have hZe : ∀ i c, Formalism.L2.SG.HidaSetting.hJ ε (fam e z i) (G *ᵥ e c) = Z i c.castSucc := by
    intro i c; simp only [hZdef, RealObj.Zhat, fam_castSucc]
  have hZf : ∀ i j, Formalism.L2.SG.HidaSetting.hJ ε (fam e z i) (G *ᵥ fam e z' j) = Z i j := fun i j => rfl
  have hef : ∀ (w : Fin n → ℂ), (∀ a, Formalism.L2.SG.HidaSetting.hJ ε (e a) w = 0) →
      ∀ a (i : Fin (r + 1)), Formalism.L2.SG.HidaSetting.hJ ε (e a) (fam (fun c => e c) w i) = 0 := by
    intro w hw a i
    induction i using Fin.lastCases with
    | last => rw [fam_last]; exact hw a
    | cast c => rw [fam_castSucc]; exact hee a c
  have hfe' : ∀ i a, Formalism.L2.SG.HidaSetting.hJ ε (fam e z i) (e a) = 0 := by
    intro i a
    rw [hJ_cj', hef z hez a i, map_zero]
  have hGi : ∀ x, G *ᵥ (Gi *ᵥ x) = x := fun x => by rw [Matrix.mulVec_mulVec, hGGi, Matrix.one_mulVec]

  have hQ : ∀ q, (∀ a, Formalism.L2.SG.HidaSetting.hJ ε (e a) q = 0) → (∀ a, Formalism.L2.SG.HidaSetting.hJ ε (G *ᵥ e a) q = 0) →
      Y *ᵥ q = q := by
    intro q h1 h2
    obtain ⟨α, hα⟩ := mem_spanLt_r e _ (hYN q h1)
    have h3 : ∀ a, Formalism.L2.SG.HidaSetting.hJ ε (e a) (Gi *ᵥ q) = 0 := by
      intro a; rw [← hG, hGi]; exact h2 a
    obtain ⟨β, hβ⟩ := mem_spanLt_r e _ (hTN _ h3)
    have hD : (Y - 1) *ᵥ q = ∑ b, β b • (G *ᵥ e b) := by
      have e1 : Y *ᵥ q = G *ᵥ (T *ᵥ (Gi *ᵥ q)) := by
        rw [Matrix.mulVec_mulVec (Gi *ᵥ q) G T, ← hYG, ← Matrix.mulVec_mulVec, hGi]
      have : (Y - 1) *ᵥ q = G *ᵥ ((T - 1) *ᵥ (Gi *ᵥ q)) := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, e1, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, hGi]
      rw [this, ← hβ, Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul]
    have hβ0 : ∀ b, β b = 0 := by
      intro b
      have h := congrArg (Formalism.L2.SG.HidaSetting.hJ ε (fam e z (π b.castSucc))) (hα.trans hD)
      rw [hJ_sum_r', hJ_sum_r'] at h
      simp only [hfe', mul_zero, Finset.sum_const_zero, hZe] at h
      rw [Finset.sum_eq_single b] at h
      · rcases mul_eq_zero.1 h.symm with h1 | h1
        · exact h1
        · exact absurd h1 (hZne _)
      · intro c _ hcb
        rw [hZ0 (π b.castSucc) c.castSucc (fun h' => hcb (Fin.castSucc_injective _ (hπi h')).symm), mul_zero]
      · intro h'; exact absurd (Finset.mem_univ b) h'
    have : (Y - 1) *ᵥ q = 0 := by rw [hD]; simp [hβ0]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
    exact this

  have hall : ∀ x, Y *ᵥ x = x := by
    intro x
    let s1 : Fin n → ℂ := ∑ a : Fin r,
      (Formalism.L2.SG.HidaSetting.hJ ε (e a) x / Z a.castSucc (π a.castSucc)) • (G *ᵥ fam e z' (π a.castSucc))
    let s2 : Fin n → ℂ := ∑ c : Fin r,
      (Formalism.L2.SG.HidaSetting.hJ ε (G *ᵥ e c) x / conj (Z (π c.castSucc) c.castSucc)) • fam e z (π c.castSucc)
    have hs1 : Y *ᵥ s1 = s1 := by
      simp only [s1, Matrix.mulVec_sum, Matrix.mulVec_smul, hYGF]
    have hs2 : Y *ᵥ s2 = s2 := by
      simp only [s2, Matrix.mulVec_sum, Matrix.mulVec_smul, hYF]
    have hq1 : ∀ d, Formalism.L2.SG.HidaSetting.hJ ε (e d) (x - s1 - s2) = 0 := by
      intro d
      rw [hJ_sub_r', hJ_sub_r', hJ_sum_r', hJ_sum_r']
      have hz2 : ∀ c : Fin r, Formalism.L2.SG.HidaSetting.hJ ε (e d) (fam e z (π c.castSucc)) = 0 :=
        fun c => hef z hez d _
      simp only [hz2, mul_zero, Finset.sum_const_zero, sub_zero]
      have hd : ∀ a : Fin r, Formalism.L2.SG.HidaSetting.hJ ε (e d) (G *ᵥ fam e z' (π a.castSucc)) =
          Z d.castSucc (π a.castSucc) := by
        intro a; rw [← hZf, fam_castSucc]
      simp only [hd]
      rw [Finset.sum_eq_single d, div_mul_cancel₀ _ ((hP1 _ _).2 (hπ _).symm), sub_self]
      · intro a _ had
        rw [hZ0 d.castSucc (π a.castSucc) (fun h' => had (Fin.castSucc_injective _ (by rw [hπ] at h'; exact h'.symm))), mul_zero]
      · intro h'; exact absurd (Finset.mem_univ d) h'
    have hq2 : ∀ d, Formalism.L2.SG.HidaSetting.hJ ε (G *ᵥ e d) (x - s1 - s2) = 0 := by
      intro d
      rw [hJ_sub_r', hJ_sub_r', hJ_sum_r', hJ_sum_r']
      have hz1 : ∀ a : Fin r, Formalism.L2.SG.HidaSetting.hJ ε (G *ᵥ e d) (G *ᵥ fam e z' (π a.castSucc)) = 0 :=
        fun a => by rw [hG]; exact hef z' hez' d _
      have hd2 : ∀ c : Fin r, Formalism.L2.SG.HidaSetting.hJ ε (G *ᵥ e d) (fam e z (π c.castSucc)) =
          conj (Z (π c.castSucc) d.castSucc) := fun c => by rw [hJ_cj', hZe]
      simp only [hz1, mul_zero, Finset.sum_const_zero, sub_zero, hd2]
      rw [Finset.sum_eq_single d, div_mul_cancel₀ _ ((map_ne_zero (starRingEnd ℂ)).2 (hZne _)), sub_self]
      · intro c _ hcd
        rw [hZ0 (π c.castSucc) d.castSucc (fun h' => hcd (Fin.castSucc_injective _ (hπi h'))), map_zero, mul_zero]
      · intro h'; exact absurd (Finset.mem_univ d) h'
    have hq := hQ _ hq1 hq2
    calc Y *ᵥ x = Y *ᵥ ((x - s1 - s2) + s1 + s2) := by congr 1; abel
      _ = (x - s1 - s2) + s1 + s2 := by rw [Matrix.mulVec_add, Matrix.mulVec_add, hq, hs1, hs2]
      _ = x := by abel
  exact Matrix.toLin'.injective (LinearMap.ext fun x => by rw [Matrix.toLin'_apply, hall x, Matrix.toLin'_one]; rfl)

end FixLoc

section FixGlob

variable {D : D7}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stVFix_holds (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : StVFix X u u' := by
  classical
  intro w hw v y hy hF hGF
  set γ := gamW X u u' w with hγdef
  have hγ : IsPtRep X u u' w γ := by
    rw [hγdef, gamW, dite_eq_left hw.1]; exact hw.1.choose_spec
  set e : Fin D.R.rS → Fin X.B.I.n → ℂ := fun a => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR a)
  set z := Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u)
  set z' := Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u')
  have hee : ∀ a b, Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (e a) (e b) = 0 := by
    intro a b; rw [Formalism.L2.SG.Pf.Level.hJ_rv]
    convert congrArg (X.B.I.φ v) (Formalism.L2.SG.Pf.UnipB.hE_ee X a b) using 1; simp
  have hez : ∀ (u : D.what₂.Word) a,
      Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (e a) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u)) = 0 := by
    intro u a; rw [Formalism.L2.SG.Pf.Level.hJ_rv]
    convert congrArg (X.B.I.φ v) (Formalism.L2.SG.Pf.UnipB.hE_ez X u a) using 1; simp
  have hGGi : uMat (γ v) * uMat (γ v)⁻¹ = 1 := by simp [uMat]
  have hG : ∀ x x', Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (uMat (γ v) *ᵥ x) (uMat (γ v) *ᵥ x') =
      Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) x x' := by
    intro x x'
    rw [Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.hJ_adj (γ v), Matrix.mulVec_mulVec,
      Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul', Matrix.one_mulVec]
  have hYG : uMat y * uMat (γ v) = uMat (γ v) * uMat ((γ v)⁻¹ * y * γ v) := by
    have e1 : y * γ v = γ v * ((γ v)⁻¹ * y * γ v) := by group
    have e2 : uMat (y * γ v) = uMat (γ v * ((γ v)⁻¹ * y * γ v)) := by rw [e1]
    simpa [uMat] using e2
  have hZ : ZX X u u' 1 γ v = RealObj.Zhat (X.B.I.ε v) (fam e z) (fam e z') (uMat (γ v)) := by
    simp only [ZX, frm, famSc_one]; rfl
  have hO := hγ v
  have hsum : (w.1.map Prod.snd).sum = D.R.rS + 1 := w.2.2
  have hZe : ∀ c b : Fin (D.R.rS + 1), RealObj.Zhat (X.B.I.ε v) (fam e z) (fam e z') (uMat (γ v)) c b =
      (-1 : ℂ) ^ (D.R.rS - b.1) * X.B.I.φ v (X.ιE.symm (if c.val = ptPar w.1 b.val then ptSc w.1 b.val else 0)) := by
    intro c b
    have h1 := congrFun (congrFun hO c) b
    simp only [RealObj.ZhatO, ptC, Matrix.map_apply, ptMat, hZ] at h1
    rw [← ptEntry_eq w.1 c.val b.val (by rw [hsum]; exact b.2), ← h1, ← mul_assoc, ← mul_pow]
    norm_num
  have hne : ∀ b : ℕ, b < D.R.rS + 1 → X.B.I.φ v (X.ιE.symm (ptSc w.1 b)) ≠ 0 := by
    intro b hb
    rw [map_ne_zero, map_ne_zero]
    exact ptSc_ne w.1 w.2.1 b (by rw [hsum]; exact hb)
  let π : Fin (D.R.rS + 1) → Fin (D.R.rS + 1) := fun b =>
    ⟨ptPar w.1 b.val, lt_of_lt_of_eq (ptPar_lt w.1 b.val (by rw [hsum]; exact b.2)) hsum⟩
  have hπ : ∀ a, π (π a) = a := fun a => Fin.ext (ptPar_invol w.1 a.val (by rw [hsum]; exact a.2))
  have hP1 : ∀ c b, RealObj.Zhat (X.B.I.ε v) (fam e z) (fam e z') (uMat (γ v)) c b ≠ 0 ↔ c = π b := by
    intro c b
    rw [hZe]
    by_cases h : c.val = ptPar w.1 b.val
    · rw [if_pos h]
      refine ⟨fun _ => Fin.ext h, fun _ => mul_ne_zero (pow_ne_zero _ (by norm_num)) (hne b.val b.2)⟩
    · rw [if_neg h, map_zero, map_zero, mul_zero]
      exact ⟨fun h' => absurd rfl h', fun h' => absurd (congrArg Fin.val h') h⟩
  have hY1 := fix_loc (X.B.I.ε v) e z z' (uMat (γ v)) (uMat (γ v)⁻¹) (uMat y) (uMat ((γ v)⁻¹ * y * γ v))
    hGGi hG hee (hez u) (hez u') π hπ hP1 hy.1.2 hy.2.2 hYG hF hGF
  apply Subtype.ext
  apply Units.ext
  simpa [uMat] using hY1

theorem stVGeo_of_sec (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (hS : StVSec X u u') :
    StVGeo X u u' := by
  exact stVGeo_of_fix_sec X u u' (stVFix_holds X u u') hS

end FixGlob

end Formalism.L2.SG.Pf.Carrier.JointQuot
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LastDiagMulVec
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ZeroOfBlk
noncomputable section

open Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

variable {m : ℕ}

def IsUB (blk : Fin m → ℕ) (C : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  (∀ i, C i i = 1) ∧ ∀ i j, C i j ≠ 0 → i ≤ j ∧ blk i = blk j

theorem IsUB.zero_of_lt {blk : Fin m → ℕ} {C : Matrix (Fin m) (Fin m) ℂ} (h : IsUB blk C) {i j : Fin m} (hij : j < i) :
    C i j = 0 := by
  by_contra hne
  exact absurd hij (not_lt.mpr (h.2 i j hne).1)

theorem IsUB.zero_of_blk {blk : Fin m → ℕ} {C : Matrix (Fin m) (Fin m) ℂ} (h : IsUB blk C) {i j : Fin m}
    (hij : blk i ≠ blk j) : C i j = 0 := by
  by_contra hne
  exact hij (h.2 i j hne).2

theorem IsUB.det_eq_one {blk : Fin m → ℕ} {C : Matrix (Fin m) (Fin m) ℂ} (h : IsUB blk C) : C.det = 1 := by
  have hup : C.BlockTriangular id := by
    intro i j hij
    exact h.zero_of_lt hij
  rw [Matrix.det_of_upperTriangular hup]
  exact Finset.prod_eq_one fun i _ => h.1 i

theorem IsUB.inv {blk : Fin m → ℕ} {C : Matrix (Fin m) (Fin m) ℂ} (h : IsUB blk C) : IsUB blk C⁻¹ := by
  have hup : C.BlockTriangular id := by
    intro i j hij
    exact h.zero_of_lt hij
  have hb1 : C.BlockTriangular blk := by
    intro i j hij
    exact h.zero_of_blk hij.ne'
  have hb2 : C.BlockTriangular (fun i => OrderDual.toDual (blk i)) := by
    intro i j hij
    exact h.zero_of_blk (OrderDual.toDual_lt_toDual.mp hij).ne
  have hdet : IsUnit C.det := by
    rw [h.det_eq_one]
    exact isUnit_one
  letI : Invertible C := C.invertibleOfIsUnitDet hdet
  have iup := Matrix.blockTriangular_inv_of_blockTriangular hup
  have ib1 := Matrix.blockTriangular_inv_of_blockTriangular hb1
  have ib2 := Matrix.blockTriangular_inv_of_blockTriangular hb2
  refine ⟨fun i => ?_, fun i j hij => ⟨?_, ?_⟩⟩
  · have h1 : (C * C⁻¹) i i = 1 := by
      rw [Matrix.mul_nonsing_inv _ hdet, one_apply_eq]
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
    · rwa [h.1, one_mul] at h1
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hlt | hlt
      · rw [h.zero_of_lt hlt, zero_mul]
      · rw [iup hlt, mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  · by_contra hlt
    exact hij (iup (not_le.mp hlt))
  · by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hij (ib2 (OrderDual.toDual_lt_toDual.mpr hlt))
    · exact hij (ib1 hlt)

section Mono

variable (π : Fin m → Fin m) (hπ : ∀ a, π (π a) = a) (Z : Matrix (Fin m) (Fin m) ℂ)
  (hZ : ∀ c b, Z c b ≠ 0 ↔ c = π b)
include hπ hZ

theorem Z_ne' (i : Fin m) : Z i (π i) ≠ 0 := (hZ i (π i)).mpr (hπ i).symm

def Zi : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun b c => if b = π c then (Z c b)⁻¹ else 0

theorem Z_mul_Zi : Z * Zi π Z = 1 := by
  refine Matrix.ext fun i k => ?_
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Zi, of_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hik : i = k
  · subst hik
    rw [if_pos rfl]
    exact mul_inv_cancel₀ (Z_ne' π hπ Z hZ i)
  · rw [if_neg hik]
    have h0 : Z i (π k) = 0 := by
      by_contra hne
      have h1 := (hZ i (π k)).mp hne
      rw [hπ] at h1
      exact hik h1
    rw [h0, zero_mul]

theorem Z_inv_eq : Z⁻¹ = Zi π Z := Matrix.inv_eq_right_inv (Z_mul_Zi π hπ Z hZ)

theorem isUnit_Z : IsUnit Z.det := Matrix.isUnit_det_of_right_inverse (Z_mul_Zi π hπ Z hZ)

theorem conj_apply (X : Matrix (Fin m) (Fin m) ℂ) (j i : Fin m) :
    (Z * X * Z⁻¹) j i = Z j (π j) * X (π j) (π i) * (Z i (π i))⁻¹ := by
  rw [Z_inv_eq π hπ Z hZ]
  simp only [Matrix.mul_apply, Zi, of_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  congr 1
  rw [Finset.sum_eq_single (π j)]
  · intro l _ hl
    have h0 : Z j l = 0 := by
      by_contra hne
      apply hl
      rw [(hZ j l).mp hne, hπ]
    rw [h0, zero_mul]
  · intro hj
    exact absurd (Finset.mem_univ _) hj

end Mono

section Pair

variable {blk : Fin m → ℕ} (π : Fin m → Fin m) (hπ : ∀ a, π (π a) = a) (hblk : ∀ a, blk (π a) = blk a)
  (hanti : ∀ a b, blk a = blk b → a < b → π b < π a) (Z : Matrix (Fin m) (Fin m) ℂ)
  (hZ : ∀ c b, Z c b ≠ 0 ↔ c = π b)
include hπ hblk hanti hZ

theorem isUB_A {C : Matrix (Fin m) (Fin m) ℂ} (hC : IsUB blk C) : IsUB blk (Z * C⁻¹ * Z⁻¹)ᴴ := by
  have hD := hC.inv
  have hM : ∀ j i, (Z * C⁻¹ * Z⁻¹) j i = Z j (π j) * C⁻¹ (π j) (π i) * (Z i (π i))⁻¹ :=
    fun j i => conj_apply π hπ Z hZ _ j i
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [conjTranspose_apply, hM, hD.1, mul_one, mul_inv_cancel₀ (Z_ne' π hπ Z hZ i),
      star_one]
  · rw [conjTranspose_apply, hM] at hij
    have h1 : C⁻¹ (π j) (π i) ≠ 0 := by
      intro h0
      apply hij
      rw [h0]
      simp
    obtain ⟨hle, hb⟩ := hD.2 _ _ h1
    refine ⟨?_, by simpa [hblk] using hb.symm⟩
    rcases hle.lt_or_eq with hlt | heq
    · have h2 := hanti _ _ hb hlt
      rw [hπ, hπ] at h2
      exact h2.le
    · have h2 := congrArg π heq
      rw [hπ, hπ] at h2
      exact h2.symm.le

theorem A_Z_C {C : Matrix (Fin m) (Fin m) ℂ} (hC : IsUB blk C) : (Z * C⁻¹ * Z⁻¹)ᴴᴴ * Z * C = Z := by
  rw [conjTranspose_conjTranspose]
  have hZu := isUnit_Z π hπ Z hZ
  have hCu : IsUnit C.det := by
    rw [hC.det_eq_one]
    exact isUnit_one
  rw [mul_assoc (Z * C⁻¹) Z⁻¹ Z, Matrix.nonsing_inv_mul _ hZu, mul_one, mul_assoc,
    Matrix.nonsing_inv_mul _ hCu, mul_one]

end Pair

theorem gram_last {blk : Fin (m + 1) → ℕ} {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} (hA : IsUB blk A)
    (Γ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hΓ : ∀ i j, (i ≠ Fin.last m ∨ j ≠ Fin.last m) → Γ i j = 0) :
    Aᴴ * Γ * A = Γ := by
  have hrow : ∀ j, A (Fin.last m) j = if j = Fin.last m then 1 else 0 := by
    intro j
    by_cases hj : j = Fin.last m
    · rw [if_pos hj, hj]
      exact hA.1 _
    · rw [if_neg hj]
      exact hA.zero_of_lt (lt_of_le_of_ne (Fin.le_last j) hj)
  ext i j
  simp only [Matrix.mul_apply, conjTranspose_apply]
  rw [Finset.sum_eq_single (Fin.last m)]
  · rw [Finset.sum_eq_single (Fin.last m)]
    · rw [hrow i, hrow j]
      by_cases hi : i = Fin.last m
      · by_cases hj : j = Fin.last m
        · subst hi
          subst hj
          simp
        · rw [if_neg hj, hΓ i j (Or.inr hj)]
          simp
      · rw [if_neg hi, hΓ i j (Or.inl hi)]
        simp
    · intro k _ hk
      rw [hΓ k (Fin.last m) (Or.inl hk), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro l _ hl
    rw [Finset.sum_eq_zero (fun k _ => by rw [hΓ k l (Or.inr hl), mul_zero]), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end

noncomputable section

open Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

variable {r : ℕ}

def lastDiag (t : ℂ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  Matrix.of fun i j => if i = Fin.last r ∧ j = Fin.last r then t else 0

theorem lastDiag_mulVec (t : ℂ) (α : Fin (r + 1) → ℂ) :
    lastDiag t *ᵥ α = Pi.single (Fin.last r) (t * α (Fin.last r)) := by
  ext i
  by_cases hi : i = Fin.last r
  · subst hi
    simp [lastDiag, Matrix.mulVec, dotProduct]
  · simp [lastDiag, Matrix.mulVec, dotProduct, hi]

theorem gram_isUnit (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hZ : IsUnit Z.det) (T T' : ℝ)
    (hG : 1 - (T : ℂ) * T' * (Z⁻¹ (Fin.last r) (Fin.last r) * starRingEnd ℂ (Z⁻¹ (Fin.last r) (Fin.last r))) ≠ 0) :
    IsUnit (Matrix.fromBlocks (lastDiag (-(T : ℂ))) Z Zᴴ (lastDiag (-(T' : ℂ)))).det := by
  rw [isUnit_iff_ne_zero, Ne, ← Matrix.exists_mulVec_eq_zero_iff]
  rintro ⟨v, hv0, hv⟩
  apply hv0
  have hZi : Z⁻¹ * Z = 1 := Matrix.nonsing_inv_mul Z hZ
  have hZhi : (Zᴴ)⁻¹ * Zᴴ = 1 :=
    Matrix.nonsing_inv_mul _ (by rw [Matrix.det_conjTranspose]; exact hZ.star)
  rw [Matrix.fromBlocks_mulVec] at hv
  have h1 : lastDiag (-(T : ℂ)) *ᵥ (v ∘ Sum.inl) + Z *ᵥ (v ∘ Sum.inr) = 0 :=
    funext fun i => by simpa only [Sum.elim_inl, Pi.zero_apply] using congrFun hv (Sum.inl i)
  have h2 : Zᴴ *ᵥ (v ∘ Sum.inl) + lastDiag (-(T' : ℂ)) *ᵥ (v ∘ Sum.inr) = 0 :=
    funext fun i => by simpa only [Sum.elim_inr, Pi.zero_apply] using congrFun hv (Sum.inr i)
  rw [lastDiag_mulVec] at h1 h2
  have h1' : Z *ᵥ (v ∘ Sum.inr) = Pi.single (Fin.last r) ((T : ℂ) * (v ∘ Sum.inl) (Fin.last r)) := by
    rw [eq_neg_of_add_eq_zero_right h1, ← Pi.single_neg]
    congr 1
    ring
  have h2' : Zᴴ *ᵥ (v ∘ Sum.inl) = Pi.single (Fin.last r) ((T' : ℂ) * (v ∘ Sum.inr) (Fin.last r)) := by
    rw [eq_neg_of_add_eq_zero_left h2, ← Pi.single_neg]
    congr 1
    ring
  have hy : v ∘ Sum.inr = Z⁻¹ *ᵥ Pi.single (Fin.last r) ((T : ℂ) * (v ∘ Sum.inl) (Fin.last r)) := by
    rw [← h1', Matrix.mulVec_mulVec, hZi, Matrix.one_mulVec]
  have hx : v ∘ Sum.inl = (Zᴴ)⁻¹ *ᵥ Pi.single (Fin.last r) ((T' : ℂ) * (v ∘ Sum.inr) (Fin.last r)) := by
    rw [← h2', Matrix.mulVec_mulVec, hZhi, Matrix.one_mulVec]
  have hsingle : ∀ (N : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (c : ℂ) (i : Fin (r + 1)),
      (N *ᵥ Pi.single (Fin.last r) c) i = N i (Fin.last r) * c := by
    intro N c i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hinv : (Zᴴ)⁻¹ (Fin.last r) (Fin.last r) = starRingEnd ℂ (Z⁻¹ (Fin.last r) (Fin.last r)) := by
    rw [← Matrix.conjTranspose_nonsing_inv]
    rfl
  have hyl := congrFun hy (Fin.last r)
  have hxl := congrFun hx (Fin.last r)
  rw [hsingle] at hyl hxl
  rw [hinv] at hxl
  have hprod : (v ∘ Sum.inl) (Fin.last r) *
      (1 - (T : ℂ) * T' * (Z⁻¹ (Fin.last r) (Fin.last r) * starRingEnd ℂ (Z⁻¹ (Fin.last r) (Fin.last r))))
        = 0 := by
    linear_combination hxl + (starRingEnd ℂ (Z⁻¹ (Fin.last r) (Fin.last r)) * (T' : ℂ)) * hyl
  have hx0 : (v ∘ Sum.inl) (Fin.last r) = 0 := (mul_eq_zero.mp hprod).resolve_right hG
  have hy0 : (v ∘ Sum.inr) (Fin.last r) = 0 := by rw [hyl, hx0]; ring
  rw [hx0, mul_zero, Pi.single_zero, Matrix.mulVec_zero] at hy
  rw [hy0, mul_zero, Pi.single_zero, Matrix.mulVec_zero] at hx
  funext s
  cases s with
  | inl i => exact congrFun hx i
  | inr i => exact congrFun hy i

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RankUpdateMul
noncomputable section

open Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

variable {n : Type} [Fintype n] [DecidableEq n] {ι : Type} [Fintype ι] [DecidableEq ι]

def Ymat (J : Matrix n n ℂ) (W : Matrix n ι ℂ) (M : Matrix ι ι ℂ) : Matrix n n ℂ :=
  1 + W * M * (Wᴴ * J * W)⁻¹ * Wᴴ * J

theorem rankUpdate_mul (J : Matrix n n ℂ) (W : Matrix n ι ℂ) (M : Matrix ι ι ℂ) (hΓ : IsUnit (Wᴴ * J * W).det) :
    Ymat J W M * W = W * (1 + M) := by
  have hinv : (Wᴴ * J * W)⁻¹ * (Wᴴ * J * W) = 1 := Matrix.nonsing_inv_mul _ hΓ
  unfold Ymat
  calc (1 + W * M * (Wᴴ * J * W)⁻¹ * Wᴴ * J) * W
        = W + W * M * ((Wᴴ * J * W)⁻¹ * (Wᴴ * J * W)) := by
          simp only [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc]
    _ = W * (1 + M) := by rw [hinv, Matrix.mul_one, Matrix.mul_add, Matrix.mul_one]

theorem Ymat_sub (J : Matrix n n ℂ) (W : Matrix n ι ℂ) (M : Matrix ι ι ℂ) (x : n → ℂ) :
    Ymat J W M *ᵥ x - x = W *ᵥ (M *ᵥ ((Wᴴ * J * W)⁻¹ *ᵥ ((Wᴴ * J) *ᵥ x))) := by
  unfold Ymat
  rw [Matrix.add_mulVec, Matrix.one_mulVec, add_sub_cancel_left]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem Ymat_unitary (J : Matrix n n ℂ) (hJ : Jᴴ = J) (W : Matrix n ι ℂ) (M : Matrix ι ι ℂ)
    (hΓ : IsUnit (Wᴴ * J * W).det) (hM : (1 + M)ᴴ * (Wᴴ * J * W) * (1 + M) = Wᴴ * J * W) :
    (Ymat J W M)ᴴ * J * Ymat J W M = J := by
  have hGh : (Wᴴ * J * W)ᴴ = Wᴴ * J * W := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJ,
      Matrix.mul_assoc]
  have hGi1 : (Wᴴ * J * W)⁻¹ * (Wᴴ * J * W) = 1 := Matrix.nonsing_inv_mul _ hΓ
  have hGi2 : (Wᴴ * J * W) * (Wᴴ * J * W)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hΓ
  have hGih : ((Wᴴ * J * W)⁻¹)ᴴ = (Wᴴ * J * W)⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hGh]
  unfold Ymat
  set G := Wᴴ * J * W with hG
  set Gi := G⁻¹ with hGi

  have hK : G * M + Mᴴ * G + Mᴴ * G * M = 0 := by
    have h' := hM
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one] at h'
    have e : (1 + Mᴴ) * G * (1 + M) = G + (G * M + Mᴴ * G + Mᴴ * G * M) := by noncomm_ring
    rw [e] at h'
    exact add_eq_left.1 h'
  have hbr : M * Gi + Gi * Mᴴ + Gi * Mᴴ * G * M * Gi = 0 := by
    calc M * Gi + Gi * Mᴴ + Gi * Mᴴ * G * M * Gi
        = Gi * G * M * Gi + Gi * Mᴴ * (G * Gi) + Gi * Mᴴ * G * M * Gi := by
          rw [hGi1, hGi2]
          noncomm_ring
      _ = Gi * (G * M + Mᴴ * G + Mᴴ * G * M) * Gi := by noncomm_ring
      _ = 0 := by rw [hK]; noncomm_ring
  have key : J * W * (M * Gi + Gi * Mᴴ + Gi * Mᴴ * G * M * Gi) * Wᴴ * J = 0 := by
    rw [hbr]
    simp
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hJ, hGih]
  refine Eq.trans ?_ (add_zero J)
  rw [← key]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, hG]
  abel

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end

noncomputable section

open Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting

variable {N r : ℕ} (ε : Fin N → Bool) (F G : Fin (r + 1) → Fin N → ℂ)

def Wfg : Matrix (Fin N) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ := Matrix.of fun p k => Sum.elim F G k p

theorem gram_Wfg : (Wfg F G)ᴴ * Formalism.REAL.Jm ε * Wfg F G =
    Matrix.fromBlocks (Matrix.of fun a b => hJ ε (F a) (F b)) (Matrix.of fun a b => hJ ε (F a) (G b))
      (Matrix.of fun a b => hJ ε (G a) (F b)) (Matrix.of fun a b => hJ ε (G a) (G b)) := by
  ext k l
  rw [Matrix.mul_assoc]
  rcases k with a | a <;> rcases l with b | b <;>
    simp [hJ, Matrix.mul_apply, mulVec, dotProduct, Wfg, conjTranspose_apply]

theorem wjx (x : Fin N → ℂ) : ((Wfg F G)ᴴ * Formalism.REAL.Jm ε) *ᵥ x = Sum.elim (fun a => hJ ε (F a) x) (fun b => hJ ε (G b) x) := by
  funext k
  rw [← mulVec_mulVec]
  rcases k with a | b <;> simp [hJ, mulVec, dotProduct, Wfg, conjTranspose_apply]

theorem Wfg_mulVec (v : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :
    Wfg F G *ᵥ v = ∑ a, v (Sum.inl a) • F a + ∑ b, v (Sum.inr b) • G b := by
  funext p
  simp [mulVec, dotProduct, Fintype.sum_sum_type, Wfg, Finset.sum_apply, mul_comm]

section Main

variable (T T' : ℝ) (π : Fin (r + 1) → Fin (r + 1)) (blk : Fin (r + 1) → ℕ)

def Zm : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.of fun a b => hJ ε (F a) (G b)

def Am (C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  (Zm ε F G * C⁻¹ * (Zm ε F G)⁻¹)ᴴ

def Mm (C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ :=
  Matrix.fromBlocks (Am ε F G C - 1) 0 0 (C - 1)

def Yc (C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Ymat (Formalism.REAL.Jm ε) (Wfg F G) (Mm ε F G C)

variable (hFF : ∀ a b, hJ ε (F a) (F b) = lastDiag (-(T : ℂ)) a b)
  (hGG : ∀ a b, hJ ε (G a) (G b) = lastDiag (-(T' : ℂ)) a b)
  (hπ : ∀ a, π (π a) = a) (hblk : ∀ a, blk (π a) = blk a) (hanti : ∀ a b, blk a = blk b → a < b → π b < π a)
  (hZ : ∀ c b, Zm ε F G c b ≠ 0 ↔ c = π b)
  (hgap : 1 - (T : ℂ) * T' * ((Zm ε F G)⁻¹ (Fin.last r) (Fin.last r) *
    starRingEnd ℂ ((Zm ε F G)⁻¹ (Fin.last r) (Fin.last r))) ≠ 0)

theorem Jm_herm : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a = true <;> simp [h]

include hFF hGG hπ hZ in
theorem gram_eq : (Wfg F G)ᴴ * Formalism.REAL.Jm ε * Wfg F G =
    Matrix.fromBlocks (lastDiag (-(T : ℂ))) (Zm ε F G) (Zm ε F G)ᴴ (lastDiag (-(T' : ℂ))) := by
  rw [gram_Wfg]
  refine fromBlocks_inj.2 ⟨?_, rfl, ?_, ?_⟩
  · ext a b
    simp [hFF]
  · ext a b
    simp only [of_apply, conjTranspose_apply, Zm]
    unfold hJ Formalism.REAL.Jm
    simp only [mulVec_diagonal, dotProduct, star_sum, star_mul', star_star, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp <;> ring
  · ext a b
    simp [hGG]

include hFF hGG hπ hZ hgap in
theorem gram_unit : IsUnit ((Wfg F G)ᴴ * Formalism.REAL.Jm ε * Wfg F G).det := by
  rw [gram_eq ε F G T T' π hFF hGG hπ hZ]
  exact gram_isUnit _ (isUnit_Z π hπ _ hZ) T T' hgap

include hFF hGG hπ hblk hanti hZ hgap in
theorem Yc_unitary {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hC : IsUB blk C) :
    (Yc ε F G C)ᴴ * Formalism.REAL.Jm ε * Yc ε F G C = Formalism.REAL.Jm ε := by
  have hA := isUB_A π hπ hblk hanti (Zm ε F G) hZ hC
  have hAZC : (Am ε F G C)ᴴ * Zm ε F G * C = Zm ε F G := A_Z_C π hπ hblk hanti _ hZ hC
  have hL : ∀ t : ℂ, ∀ i j : Fin (r + 1), i ≠ Fin.last r ∨ j ≠ Fin.last r → lastDiag t i j = 0 := by
    intro t i j h
    simp only [lastDiag, of_apply]
    rw [if_neg]
    tauto
  unfold Yc
  refine Ymat_unitary _ (Jm_herm ε) _ _ (gram_unit ε F G T T' π hFF hGG hπ hZ hgap) ?_
  rw [gram_eq ε F G T T' π hFF hGG hπ hZ]
  have h1 : (1 : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) + Mm ε F G C =
      fromBlocks (Am ε F G C) 0 0 C := by
    rw [Mm, ← fromBlocks_one, fromBlocks_add]
    simp
  rw [h1, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [conjTranspose_zero, zero_mul, mul_zero, add_zero, zero_add]
  refine fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩
  · exact gram_last hA _ (hL _)
  · exact hAZC
  · have h2 := congrArg conjTranspose hAZC
    simpa [conjTranspose_mul, Matrix.mul_assoc] using h2
  · exact gram_last hC _ (hL _)

end Main

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end

noncomputable section

open Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting

variable {N r : ℕ} (ε : Fin N → Bool) (F G : Fin (r + 1) → Fin N → ℂ) (T T' : ℝ) (π : Fin (r + 1) → Fin (r + 1))
  (blk : Fin (r + 1) → ℕ)
  (hFF : ∀ a b, hJ ε (F a) (F b) = lastDiag (-(T : ℂ)) a b)
  (hGG : ∀ a b, hJ ε (G a) (G b) = lastDiag (-(T' : ℂ)) a b)
  (hπ : ∀ a, π (π a) = a) (hblk : ∀ a, blk (π a) = blk a) (hanti : ∀ a b, blk a = blk b → a < b → π b < π a)
  (hZ : ∀ c b, Zm ε F G c b ≠ 0 ↔ c = π b)
  (hgap : 1 - (T : ℂ) * T' * ((Zm ε F G)⁻¹ (Fin.last r) (Fin.last r) *
    starRingEnd ℂ ((Zm ε F G)⁻¹ (Fin.last r) (Fin.last r))) ≠ 0)

include hFF hGG hπ hZ hgap in
theorem Yc_G {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (b : Fin (r + 1)) :
    Yc ε F G C *ᵥ G b = ∑ b', C b' b • G b' := by
  have hΓ := gram_unit (ε := ε) (F := F) (G := G) (T := T) (T' := T') (π := π) (hFF := hFF)
    (hGG := hGG) (hπ := hπ) (hZ := hZ) (hgap := hgap)
  have hW : Yc ε F G C * Wfg F G = Wfg F G * (1 + Mm ε F G C) := rankUpdate_mul _ _ _ hΓ
  have hGcol : G b = Wfg F G *ᵥ Pi.single (Sum.inr b) 1 := by
    funext p
    rw [Matrix.mulVec_single]
    simp [Wfg, Function.swap]
  rw [hGcol, Matrix.mulVec_mulVec, hW, ← Matrix.mulVec_mulVec, Matrix.mulVec_single]
  funext p
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Wfg, Mm, Matrix.one_apply, Finset.sum_apply, mul_comm]

include hFF hGG hπ hZ hgap in
theorem Yc_F {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (a : Fin (r + 1)) :
    Yc ε F G C *ᵥ F a = ∑ a', Am ε F G C a' a • F a' := by
  have hΓ := gram_unit (ε := ε) (F := F) (G := G) (T := T) (T' := T') (π := π) (hFF := hFF)
    (hGG := hGG) (hπ := hπ) (hZ := hZ) (hgap := hgap)
  have hW : Yc ε F G C * Wfg F G = Wfg F G * (1 + Mm ε F G C) := rankUpdate_mul _ _ _ hΓ
  have hFcol : F a = Wfg F G *ᵥ Pi.single (Sum.inl a) 1 := by
    funext p
    rw [Matrix.mulVec_single]
    simp [Wfg, Function.swap]
  rw [hFcol, Matrix.mulVec_mulVec, hW, ← Matrix.mulVec_mulVec, Matrix.mulVec_single]
  funext p
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Wfg, Mm, Matrix.one_apply, Finset.sum_apply, mul_comm]

theorem rowLast {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hC : IsUB blk C) (k : Fin (r + 1)) :
    C (Fin.last r) k = if k = Fin.last r then 1 else 0 := by
  obtain ⟨hdiag, hup⟩ := hC
  split_ifs with hk
  · rw [hk]
    exact hdiag _
  · by_contra h
    have h1 := (hup _ _ h).1
    exact hk (le_antisymm (Fin.le_last k) h1)

include hπ hblk hanti in
theorem colMin {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hC : IsUB blk C) (b : Fin (r + 1)) :
    C b (π (Fin.last r)) = if b = π (Fin.last r) then 1 else 0 := by
  obtain ⟨hdiag, hup⟩ := hC
  split_ifs with hb
  · rw [hb]
    exact hdiag _
  · by_contra h
    obtain ⟨hle, hbl⟩ := hup _ _ h
    have hlt : b < π (Fin.last r) := lt_of_le_of_ne hle hb
    have h2 := hanti b (π (Fin.last r)) hbl hlt
    rw [hπ] at h2
    exact absurd (Fin.le_last (π b)) (not_le.mpr h2)

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end

noncomputable section

open Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting

variable {N r : ℕ} (ε : Fin N → Bool) (F G : Fin (r + 1) → Fin N → ℂ) (T T' : ℝ) (π : Fin (r + 1) → Fin (r + 1))
  (blk : Fin (r + 1) → ℕ)
  (hFF : ∀ a b, hJ ε (F a) (F b) = lastDiag (-(T : ℂ)) a b)
  (hGG : ∀ a b, hJ ε (G a) (G b) = lastDiag (-(T' : ℂ)) a b)
  (hπ : ∀ a, π (π a) = a) (hblk : ∀ a, blk (π a) = blk a) (hanti : ∀ a b, blk a = blk b → a < b → π b < π a)
  (hZ : ∀ c b, Zm ε F G c b ≠ 0 ↔ c = π b)
  (hgap : 1 - (T : ℂ) * T' * ((Zm ε F G)⁻¹ (Fin.last r) (Fin.last r) *
    starRingEnd ℂ ((Zm ε F G)⁻¹ (Fin.last r) (Fin.last r))) ≠ 0)

def kap (x : Fin N → ℂ) : Fin (r + 1) ⊕ Fin (r + 1) → ℂ :=
  ((Wfg F G)ᴴ * Formalism.REAL.Jm ε * Wfg F G)⁻¹ *ᵥ (((Wfg F G)ᴴ * Formalism.REAL.Jm ε) *ᵥ x)

include hFF hGG hπ hZ hgap in
theorem kap_eq (x : Fin N → ℂ) :
    Matrix.fromBlocks (lastDiag (-(T : ℂ))) (Zm ε F G) (Zm ε F G)ᴴ (lastDiag (-(T' : ℂ))) *ᵥ kap ε F G x =
      Sum.elim (fun a => hJ ε (F a) x) (fun b => hJ ε (G b) x) := by
  rw [← gram_eq ε F G T T' π hFF hGG hπ hZ, kap, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (gram_unit ε F G T T' π hFF hGG hπ hZ hgap), Matrix.one_mulVec, wjx]

theorem Yc_sub (C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (x : Fin N → ℂ) :
    Yc ε F G C *ᵥ x - x = ∑ a, ((Am ε F G C - 1) *ᵥ (kap ε F G x ∘ Sum.inl)) a • F a +
      ∑ b, ((C - 1) *ᵥ (kap ε F G x ∘ Sum.inr)) b • G b := by
  unfold Yc
  rw [Ymat_sub, Wfg_mulVec]
  unfold Mm
  rw [Matrix.fromBlocks_mulVec]
  simp [kap]

include hπ hZ in
theorem monoZ_mulVec (v : Fin (r + 1) → ℂ) (a : Fin (r + 1)) : (Zm ε F G *ᵥ v) a = Zm ε F G a (π a) * v (π a) := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (π a)]
  · intro j _ hj
    have : Zm ε F G a j = 0 := by by_contra h; exact hj (by rw [(hZ a j).1 h, hπ])
    rw [this, zero_mul]
  · simp

include hπ hZ in
theorem monoZh_mulVec (v : Fin (r + 1) → ℂ) (b : Fin (r + 1)) :
    ((Zm ε F G)ᴴ *ᵥ v) b = starRingEnd ℂ (Zm ε F G (π b) b) * v (π b) := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (π b)]
  · simp [Matrix.conjTranspose_apply]
  · intro j _ hj
    have : Zm ε F G j b = 0 := by by_contra h; exact hj ((hZ j b).1 h)
    simp [Matrix.conjTranspose_apply, this]
  · simp

include hFF hGG hπ hblk hanti hZ hgap in
theorem Yc_perpF {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hC : IsUB blk C) (x : Fin N → ℂ)
    (hx : ∀ a, a ≠ Fin.last r → hJ ε (F a) x = 0) :
    Yc ε F G C *ᵥ x - x ∈ Submodule.span ℂ (F '' {a | a ≠ Fin.last r}) := by
  have hk := kap_eq ε F G T T' π hFF hGG hπ hZ hgap x
  rw [Matrix.fromBlocks_mulVec] at hk
  set κ := kap ε F G x
  have hG0 : ∀ j, j ≠ π (Fin.last r) → κ (Sum.inr j) = 0 := by
    intro j hj
    have ha : π j ≠ Fin.last r := fun h => hj (by rw [← h, hπ])
    have h1 := congrFun hk (Sum.inl (π j))
    simp only [Sum.elim_inl, Pi.add_apply] at h1
    rw [hx _ ha, lastDiag_mulVec, Pi.single_apply, if_neg ha, zero_add, monoZ_mulVec ε F G π hπ hZ, hπ] at h1
    have hz : Zm ε F G (π j) j ≠ 0 := (hZ _ _).2 rfl
    exact (mul_eq_zero.1 h1).resolve_left hz
  rw [Yc_sub]
  have h2 : ∑ b, ((C - 1) *ᵥ (κ ∘ Sum.inr)) b • G b = 0 := by
    refine Finset.sum_eq_zero fun b _ => ?_
    have : ((C - 1) *ᵥ (κ ∘ Sum.inr)) b = 0 := by
      rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (π (Fin.last r))]
      · rw [Matrix.sub_apply, colMin π blk hπ hblk hanti hC, Matrix.one_apply]
        split_ifs <;> simp
      · intro j _ hj; simp [hG0 j hj]
      · simp
    rw [this, zero_smul]
  rw [h2, add_zero]
  refine Submodule.sum_mem _ fun a _ => ?_
  by_cases ha : a = Fin.last r
  · subst ha
    have : ((Am ε F G C - 1) *ᵥ (κ ∘ Sum.inl)) (Fin.last r) = 0 := by
      rw [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun k _ => ?_
      have hA : IsUB blk (Am ε F G C) := isUB_A π hπ hblk hanti _ hZ hC
      rw [Matrix.sub_apply, rowLast blk hA, Matrix.one_apply]
      by_cases hk : k = Fin.last r
      · subst hk; simp
      · simp [hk, Ne.symm hk]
    rw [this, zero_smul]; exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)

include hFF hGG hπ hblk hanti hZ hgap in
theorem Yc_perpG {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hC : IsUB blk C) (x : Fin N → ℂ)
    (hx : ∀ b, b ≠ Fin.last r → hJ ε (G b) x = 0) :
    Yc ε F G C *ᵥ x - x ∈ Submodule.span ℂ (G '' {b | b ≠ Fin.last r}) := by
  have hk := kap_eq ε F G T T' π hFF hGG hπ hZ hgap x
  rw [Matrix.fromBlocks_mulVec] at hk
  set κ := kap ε F G x
  have hF0 : ∀ i, i ≠ π (Fin.last r) → κ (Sum.inl i) = 0 := by
    intro i hi
    have hb : π i ≠ Fin.last r := fun h => hi (by rw [← h, hπ])
    have h1 := congrFun hk (Sum.inr (π i))
    simp only [Sum.elim_inr, Pi.add_apply] at h1
    rw [hx _ hb, lastDiag_mulVec, Pi.single_apply, if_neg hb, add_zero, monoZh_mulVec ε F G π hπ hZ, hπ] at h1
    have hz : starRingEnd ℂ (Zm ε F G i (π i)) ≠ 0 := by
      rw [map_ne_zero]; exact (hZ _ _).2 (hπ i).symm
    exact (mul_eq_zero.1 h1).resolve_left hz
  rw [Yc_sub]
  have hA : IsUB blk (Am ε F G C) := isUB_A π hπ hblk hanti _ hZ hC
  have h2 : ∑ a, ((Am ε F G C - 1) *ᵥ (κ ∘ Sum.inl)) a • F a = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    have : ((Am ε F G C - 1) *ᵥ (κ ∘ Sum.inl)) a = 0 := by
      rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (π (Fin.last r))]
      · rw [Matrix.sub_apply, colMin π blk hπ hblk hanti hA, Matrix.one_apply]
        split_ifs <;> simp
      · intro j _ hj; simp [hF0 j hj]
      · simp
    rw [this, zero_smul]
  rw [h2, zero_add]
  refine Submodule.sum_mem _ fun b _ => ?_
  by_cases hb : b = Fin.last r
  · subst hb
    have : ((C - 1) *ᵥ (κ ∘ Sum.inr)) (Fin.last r) = 0 := by
      rw [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [Matrix.sub_apply, rowLast blk hC, Matrix.one_apply]
      by_cases hk : k = Fin.last r
      · subst hk; simp
      · simp [hk, Ne.symm hk]
    rw [this, zero_smul]; exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)

end Formalism.L2.S.L6.UnitaryStandardVectors
