module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.MuBridgeB
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DKForm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.RowsZP
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BlockGrp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensEx
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PlaceJacAllHolds

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DetTHolds
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def gramH {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) D.host.E :=
  Matrix.of fun i j => (VS D).hT (wF X u' i) (wF X u' j)

theorem gram_sq {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) :
    gramH X u' * gramH X u' =
    Matrix.diagonal (Fin.append (Fin.snoc (fun _ : Fin D.R.rS => (1 : D.host.E))
      ((((D.mem u').A.T : ℕ) : D.host.E) * (((D.mem u').A.T : ℕ) : D.host.E))) (fun _ : Fin D.R.rS => 1)) := by
  have h1 : ∀ b : Fin D.R.rS, Fin.last D.R.rS ≠ b.castSucc := fun b h => (Fin.castSucc_lt_last b).ne' h
  have h1' : ∀ b : Fin D.R.rS, b.castSucc ≠ Fin.last D.R.rS := fun b h => (Fin.castSucc_lt_last b).ne h
  have h2 : ∀ (x : Fin (D.R.rS + 1)) (y : Fin D.R.rS), Fin.castAdd D.R.rS x ≠ Fin.natAdd (D.R.rS + 1) y := by
    intro x y h
    have := congrArg Fin.val h
    simp only [Fin.coe_castAdd, Fin.coe_natAdd] at this
    omega
  have h2' : ∀ (x : Fin (D.R.rS + 1)) (y : Fin D.R.rS), Fin.natAdd (D.R.rS + 1) y ≠ Fin.castAdd D.R.rS x :=
    fun x y h => h2 x y h.symm
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_add, Fin.sum_univ_castSucc]
  refine Fin.addCases (fun i1 => ?_) (fun i2 => ?_) i <;> refine Fin.addCases (fun j1 => ?_) (fun j2 => ?_) j
  · refine Fin.lastCases ?_ (fun a => ?_) i1 <;> refine Fin.lastCases ?_ (fun b => ?_) j1 <;>
      simp [gramH, wF, Fin.append_left, Fin.append_right, Fin.snoc_castSucc, Fin.snoc_last, X.ee, X.ff, X.ef,
        hT_fe, hT_ze, hT_zf, (X.zu_orth u' _).1, (X.zu_orth u' _).2, X.zu_norm, Matrix.diagonal_apply, h1, h1', h2, h2', eq_comm]
  · refine Fin.lastCases ?_ (fun a => ?_) i1 <;>
      simp [gramH, wF, Fin.append_left, Fin.append_right, Fin.snoc_castSucc, Fin.snoc_last, X.ee, X.ff, X.ef,
        hT_fe, hT_ze, hT_zf, (X.zu_orth u' _).1, (X.zu_orth u' _).2, X.zu_norm, Matrix.diagonal_apply, h1, h1', h2, h2', eq_comm]
  · refine Fin.lastCases ?_ (fun b => ?_) j1 <;>
      simp [gramH, wF, Fin.append_left, Fin.append_right, Fin.snoc_castSucc, Fin.snoc_last, X.ee, X.ff, X.ef,
        hT_fe, hT_ze, hT_zf, (X.zu_orth u' _).1, (X.zu_orth u' _).2, X.zu_norm, Matrix.diagonal_apply, h1, h1', h2, h2', eq_comm]
  · simp [gramH, wF, Fin.append_left, Fin.append_right, Fin.snoc_castSucc, Fin.snoc_last, X.ee, X.ff, X.ef,
      hT_fe, hT_ze, hT_zf, (X.zu_orth u' _).1, (X.zu_orth u' _).2, X.zu_norm, Matrix.diagonal_apply, h1, h1', h2, h2', eq_comm]

theorem detT_holds : DetT := by
  intro D X u' ψ hT μinf νinf fibInf hP v
  have hGH : gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) = (gramH X u').map X.ιE.symm := by
    ext i j
    rw [gram_eq]
    rfl
  have hdet : (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det = X.ιE.symm (gramH X u').det := by
    rw [hGH]
    exact (RingHom.map_det (X.ιE.symm : D.host.E →+* X.B.I.E) _).symm
  have hsq : (gramH X u').det ^ 2 = (((D.mem u').A.T : ℕ) : D.host.E) ^ 2 := by
    have h := congrArg Matrix.det (gram_sq X u')
    rw [Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_add, Fin.prod_univ_castSucc] at h
    simp only [Fin.append_left, Fin.append_right, Fin.snoc_castSucc, Fin.snoc_last, Finset.prod_const_one,
      one_mul, mul_one] at h
    rw [sq, sq]
    exact h
  have hz : (X.B.I.φ v (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det) ^ 2 =
      ((((D.mem u').A.T : ℕ) : ℂ)) ^ 2 := by
    rw [hdet, ← map_pow, ← map_pow, hsq, map_pow, map_pow, map_natCast, map_natCast]
  have hn : ‖X.B.I.φ v (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det‖ ^ 2 = (Tw u') ^ 2 := by
    rw [← norm_pow, hz, norm_pow, Complex.norm_natCast]
    rfl
  exact (sq_eq_sq₀ (norm_nonneg _) (by unfold Tw; positivity)).1 hn

end PI.AprimeInfW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ExistsOrthonormalPerp
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PerpPosV
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.PoincareInHH.Cut
open scoped InnerProductSpace ComplexConjugate
open Matrix Finset

namespace PI.AprimeInfW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem wV_idx {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (v : InfinitePlace X.B.I.F)
    (b : Fin (D.R.rS + 1 + D.R.rS)) : wV X u' v b = rv X.B.I v (X.crd (wF X u' b)) := by
  unfold wV rv
  rw [tupH_eq]

theorem perpPosV : PerpPosV := by
  intro D X u' ψ hT μinf νinf fibInf hP v z hz hzo
  by_contra hle
  push_neg at hle
  have hzo' : ∀ b, hJ (X.B.I.ε v) (wV X u' v b) z = 0 := hzo
  have he : ∀ a : Fin D.R.rS, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) z = 0 := by
    intro a
    have := hzo' (Fin.castAdd D.R.rS (Fin.castSucc a))
    rwa [wV_idx, wF, Fin.append_left, Fin.snoc_castSucc] at this
  have hf : ∀ a : Fin D.R.rS, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) z = 0 := by
    intro a
    have := hzo' (Fin.natAdd (D.R.rS + 1) a)
    rwa [wV_idx, wF, Fin.append_right] at this
  have hzz : hJ (X.B.I.ε v) (rv X.B.I v (X.zR u')) z = 0 := by
    have := hzo' (Fin.castAdd D.R.rS (Fin.last D.R.rS))
    rwa [wV_idx, wF, Fin.append_left, Fin.snoc_last] at this
  let nv : Fin (D.R.rS + 1) → Fin X.B.I.n → ℂ := fun j =>
    if h : j.1 < D.R.rS then rv X.B.I v (X.eR ⟨j.1, h⟩) - rv X.B.I v (X.fR ⟨j.1, h⟩) else rv X.B.I v (X.zR u')
  have hb := card_le_of_orth' (X.B.I.ε v) (D.R.rS + 1) nv z ?_ ?_ ?_ hle hz
  · rw [card_eps_false X v] at hb
    omega
  · intro j k hjk
    simp only [nv]
    split_ifs with hj hk hk
    · rw [hJ_sub_left, hJ_sub_right, hJ_sub_right]
      simp only [HidaSetting.eR, HidaSetting.fR, hJ_crd, X.ee, X.ff, X.ef, hT_f_e]
      have hne : (⟨k.1, hk⟩ : Fin D.R.rS) ≠ ⟨j.1, hj⟩ := fun h => hjk (Fin.ext (by simpa using (congrArg Fin.val h).symm))
      have hne' : (⟨j.1, hj⟩ : Fin D.R.rS) ≠ ⟨k.1, hk⟩ := fun h => hne h.symm
      simp [hne, hne']
    · rw [hJ_sub_left]
      simp only [HidaSetting.eR, HidaSetting.fR, HidaSetting.zR, hJ_crd, (X.zu_orth u' _).1, (X.zu_orth u' _).2]
      simp
    · rw [hJ_sub_right]
      have h1 := hJ_crd X v (X.zu u') (X.eX ⟨k.1, hk⟩)
      have h2 := hJ_crd X v (X.zu u') (X.fY ⟨k.1, hk⟩)
      have e1 : (VS D).hT (X.zu u') (X.eX ⟨k.1, hk⟩) = 0 := by
        rw [← (VS D).herm.eq, (X.zu_orth u' _).1]; simp
      have e2 : (VS D).hT (X.zu u') (X.fY ⟨k.1, hk⟩) = 0 := by
        rw [← (VS D).herm.eq, (X.zu_orth u' _).2]; simp
      simp only [HidaSetting.eR, HidaSetting.fR, HidaSetting.zR, h1, h2, e1, e2, map_zero, sub_zero]
    · exfalso; apply hjk; ext; omega
  · intro j
    simp only [nv]
    split_ifs with hj
    · rw [hJ_sub_left, hJ_sub_right, hJ_sub_right]
      simp only [HidaSetting.eR, HidaSetting.fR, hJ_crd, X.ee, X.ff, X.ef, hT_f_e, if_true, map_zero, map_one]
      norm_num
    · simp only [HidaSetting.zR, hJ_crd, X.zu_norm, map_neg, map_natCast]
      simp only [Complex.neg_re, Complex.natCast_re, Left.neg_neg_iff]
      exact_mod_cast (D.mem u').A.T_prime.pos
  · intro j
    simp only [nv]
    split_ifs with hj
    · rw [hJ_sub_left, he, hf, sub_zero]
    · exact hzz

end PI.AprimeInfW
end
end

noncomputable section

namespace PI.AprimeInfW

open Matrix Finset

section Lin

variable {n : ℕ} (ε : Fin n → Bool)

def BJ : (Fin n → ℂ) →ₗ⋆[ℂ] (Fin n → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y))
    (fun x x' y => by rw [star_add, add_dotProduct])
    (fun c x y => by rw [star_smul, smul_dotProduct]; rfl)
    (fun x y y' => by rw [mulVec_add, dotProduct_add])
    (fun c x y => by rw [mulVec_smul, dotProduct_smul]; rfl)

theorem BJ_apply (x y : Fin n → ℂ) : BJ ε x y = star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := rfl

def dJ (i : Fin n) : ℂ := if ε i then 1 else -1

theorem BJ_sum (x y : Fin n → ℂ) : BJ ε x y = ∑ i, star (x i) * (dJ ε i * y i) := by
  rw [BJ_apply]
  simp only [dotProduct, Formalism.REAL.Jm, mulVec_diagonal, Pi.star_apply]
  rfl

theorem dJ_star (i : Fin n) : star (dJ ε i) = dJ ε i := by
  unfold dJ; split_ifs <;> simp

theorem dJ_ne (i : Fin n) : dJ ε i ≠ 0 := by
  unfold dJ
  split_ifs <;> simp

theorem BJ_herm (x y : Fin n → ℂ) : star (BJ ε x y) = BJ ε y x := by
  rw [BJ_sum, BJ_sum, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_mul', star_mul', star_star, dJ_star]
  ring

theorem BJ_nondeg (x : Fin n → ℂ) (h : ∀ y, BJ ε x y = 0) : x = 0 := by
  funext j
  have h1 := h (Pi.single j 1)
  rw [BJ_sum, Finset.sum_eq_single j] at h1
  · rw [Pi.single_eq_same, mul_one] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · simpa using h2
    · exact absurd h2 (dJ_ne ε j)
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, mul_zero, mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem BJ_single (i j : Fin n) : BJ ε (Pi.single i 1) (Pi.single j 1) = Formalism.REAL.Jm ε i j := by
  rw [BJ_sum]
  by_cases hij : i = j
  · subst hij
    rw [Finset.sum_eq_single i]
    · simp [Formalism.REAL.Jm, dJ]
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  · rw [show Formalism.REAL.Jm ε i j = 0 by simp [Formalism.REAL.Jm, hij]]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hli : l = i
    · subst hli
      simp [Pi.single_eq_of_ne hij]
    · simp [Pi.single_eq_of_ne hli]

theorem BJ_self_real (x : Fin n → ℂ) : ((BJ ε x x).re : ℂ) = BJ ε x x := by
  exact Complex.conj_eq_iff_re.mp (BJ_herm ε x x)

theorem exists_orthonormal_perp {m k : ℕ} (hn : n = m + k) (w : Fin m → Fin n → ℂ)
    (hpos : ∀ z : Fin n → ℂ, z ≠ 0 → (∀ b, BJ ε (w b) z = 0) → 0 < (BJ ε z z).re) :
    ∃ u : Fin k → Fin n → ℂ, (∀ j b, BJ ε (w b) (u j) = 0) ∧ ∀ i j, BJ ε (u i) (u j) = if i = j then 1 else 0 := by
  classical
  let L : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ) := LinearMap.pi fun b => BJ ε (w b)
  have hW : k ≤ Module.finrank ℂ (LinearMap.ker L) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker L
    have h2 : Module.finrank ℂ (LinearMap.range L) ≤ m := by
      simpa using Submodule.finrank_le (LinearMap.range L)
    simp only [Module.finrank_fin_fun] at h1
    omega
  have hker : ∀ (x : LinearMap.ker L) b, BJ ε (w b) (x : Fin n → ℂ) = 0 := by
    intro x b
    have hx := x.2
    rw [LinearMap.mem_ker] at hx
    exact congrFun hx b
  obtain ⟨v, hvli, hvo⟩ := PI.UnitaryGroupMassFormula.HermConj.exists_orthogonal_family (starRingEnd ℂ)
    (Module.finrank ℂ (LinearMap.ker L)) (LinearMap.ker L) rfl
    (fun x y => BJ ε (x : Fin n → ℂ) (y : Fin n → ℂ))
    ⟨fun x y z => by simp, fun x a y => by simp, fun x y => by rw [starRingEnd_apply, BJ_herm]⟩
  refine ⟨fun j => ((Real.sqrt (BJ ε (v (Fin.castLE hW j)) (v (Fin.castLE hW j))).re)⁻¹ : ℂ) •
    ((v (Fin.castLE hW j) : LinearMap.ker L) : Fin n → ℂ), ?_, ?_⟩
  · intro j b
    rw [map_smul, hker, smul_zero]
  · intro i j
    dsimp only
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply]
    split_ifs with hij
    · subst hij
      set z := ((v (Fin.castLE hW i) : LinearMap.ker L) : Fin n → ℂ) with hzdef
      have hz : z ≠ 0 := fun h => hvli.ne_zero _ (Submodule.coe_eq_zero.mp h)
      have hp : 0 < (BJ ε z z).re := hpos z hz (fun b => hker _ b)
      have hb : BJ ε z z = ((BJ ε z z).re : ℂ) := (BJ_self_real ε z).symm
      set r := (BJ ε z z).re with hr
      rw [hb]
      have key : (Real.sqrt r)⁻¹ * ((Real.sqrt r)⁻¹ * r) = 1 := by
        rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt hp.le, inv_mul_cancel₀ hp.ne']
      rw [map_inv₀, Complex.conj_ofReal]
      exact_mod_cast key
    · have hne : Fin.castLE hW i ≠ Fin.castLE hW j := fun h => hij (Fin.castLE_injective hW h)
      have h0 := hvo _ _ hne
      rw [h0]
      simp

private theorem card_true_ge_lemma {k : ℕ} (u : Fin k → Fin n → ℂ)
    (huo : ∀ i j, BJ ε (u i) (u j) = if i = j then 1 else 0) (c : Fin k → ℂ) (j : Fin k) :
    BJ ε (u j) (∑ l, c l • u l) = c j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, huo]

private theorem card_true_ge_lemma_2 {k : ℕ} (u : Fin k → Fin n → ℂ)
    (huo : ∀ i j, BJ ε (u i) (u j) = if i = j then 1 else 0) (c : Fin k → ℂ) :
    BJ ε (∑ l, c l • u l) (∑ l, c l • u l) = ∑ l, star (c l) * c l := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum (BJ ε), LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, card_true_ge_lemma ε u huo c l, smul_eq_mul,
    starRingEnd_apply]


open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.Cut in
theorem card_true_ge {k : ℕ} (u : Fin k → Fin n → ℂ) (huo : ∀ i j, BJ ε (u i) (u j) = if i = j then 1 else 0) :
    k ≤ (univ.filter fun i => ε i = true).card := by
  classical
  let A : (Fin k → ℂ) →ₗ[ℂ] (Fin n → ℂ) := ∑ l, (LinearMap.proj l).smulRight (u l)
  have hA : ∀ c, A c = ∑ l, c l • u l := by
    intro c
    simp [A, LinearMap.sum_apply]
  let φ : (Fin k → ℂ) →ₗ[ℂ] ({i // ε i = true} → ℂ) :=
    LinearMap.pi fun t => (LinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) t.1).comp A
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    set x := ∑ l, c l • u l with hxdef
    have hx : ∀ i, ε i = true → x i = 0 := fun i hi => by
      have h1 := congrFun hc ⟨i, hi⟩
      simp only [hxdef, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      simpa [φ, hA] using h1
    have e1 := card_true_ge_lemma_2 ε u huo c
    rw [← hxdef, BJ_sum] at e1
    have e2 := congrArg Complex.re e1
    rw [Complex.re_sum, Complex.re_sum] at e2
    have h1 : ∀ l, (star (c l) * c l).re = Complex.normSq (c l) := fun l => by
      simp [Complex.mul_re, Complex.normSq_apply]
    have h2 : ∀ i, (star (x i) * (dJ ε i * x i)).re ≤ 0 := by
      intro i
      unfold dJ
      split_ifs with hi
      · rw [hx i hi]
        simp
      · simp [Complex.mul_re]
        nlinarith [sq_nonneg (x i).re, sq_nonneg (x i).im]
    have hle : ∑ l, Complex.normSq (c l) ≤ 0 := by
      rw [← Finset.sum_congr rfl fun l _ => h1 l, ← e2]
      exact Finset.sum_nonpos fun i _ => h2 i
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun l _ => Complex.normSq_nonneg (c l)).mp
      (le_antisymm hle (Finset.sum_nonneg fun l _ => Complex.normSq_nonneg (c l)))
    funext l
    exact Complex.normSq_eq_zero.mp (hz l (Finset.mem_univ l))
  have h3 := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_fin_fun, Fintype.card_subtype] using h3

theorem BJ_orth_sum {k : ℕ} (u : Fin k → Fin n → ℂ) (huo : ∀ i j, BJ ε (u i) (u j) = if i = j then 1 else 0)
    (c : Fin k → ℂ) (j : Fin k) : BJ ε (u j) (∑ l, c l • u l) = c j := by
  exact card_true_ge_lemma ε u huo c j

private theorem wittLin_holds_lemma {k : ℕ} (a b : Fin k → Fin n → ℂ)
    (h : ∀ i j, BJ ε (a i) (a j) = BJ ε (b i) (b j)) (c d : Fin k → ℂ) :
    BJ ε (∑ i, c i • a i) (∑ j, d j • a j) = BJ ε (∑ i, c i • b i) (∑ j, d j • b j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, h]

private theorem wittLin_holds_lemma_2 (c : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (cᴴ * Formalism.REAL.Jm ε * c) i j = BJ ε (c *ᵥ Pi.single i 1) (c *ᵥ Pi.single j 1) := by
  rw [BJ_apply]
  unfold Formalism.REAL.Jm
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  simp [mulVec_diagonal, mulVec_single_one, dotProduct, conjTranspose_apply, mul_assoc]

theorem wittLin_holds : WittLin := by
  intro n m k hn ε w hli hpos
  classical
  have hpos' : ∀ z : Fin n → ℂ, z ≠ 0 → (∀ b, BJ ε (w b) z = 0) → 0 < (BJ ε z z).re := by
    intro z hz h
    rw [BJ_apply]
    exact hpos z hz (fun b => by rw [← BJ_apply]; exact h b)
  obtain ⟨u, hperp, huo⟩ := exists_orthonormal_perp ε hn w hpos'
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq (card_true_ge ε u huo)
  have hST : ∀ i ∈ S, ε i = true := fun i hi => (Finset.mem_filter.mp (hSsub hi)).2
  let s : Fin k → Fin n := fun j => (S.equivFin.symm (Fin.cast hScard.symm j)).1
  have hs_mem : ∀ j, s j ∈ S := fun j => (S.equivFin.symm (Fin.cast hScard.symm j)).2
  have hs_inj : Function.Injective s := by
    intro a b hab
    have h1 := S.equivFin.symm.injective (Subtype.ext hab)
    exact Fin.cast_injective _ h1
  have hs_surj : ∀ i ∈ S, ∃ j, s j = i := by
    intro i hi
    refine ⟨Fin.cast hScard (S.equivFin ⟨i, hi⟩), ?_⟩
    simp [s]
  have hliu : LinearIndependent ℂ u := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h1 := BJ_orth_sum ε u huo c j
    rw [hc, map_zero] at h1
    exact h1.symm
  let bU := Module.Basis.span hliu
  let f : Submodule.span ℂ (Set.range u) →ₗ[ℂ] (Fin n → ℂ) := bU.constr ℂ fun j => Pi.single (s j) 1
  have hfb : ∀ j, f (bU j) = Pi.single (s j) 1 := fun j => bU.constr_basis ℂ _ j
  have hx : ∀ x : Submodule.span ℂ (Set.range u), (x : Fin n → ℂ) = ∑ i, bU.repr x i • u i := by
    intro x
    conv_lhs => rw [← bU.sum_repr x]
    simp [bU, Module.Basis.span_apply]
  have hfx : ∀ x : Submodule.span ℂ (Set.range u), f x = ∑ i, bU.repr x i • Pi.single (s i) 1 := by
    intro x
    conv_lhs => rw [← bU.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul, hfb]
  have hgram : ∀ i j, BJ ε (u i) (u j) = BJ ε (Pi.single (s i) 1) (Pi.single (s j) 1) := by
    intro i j
    rw [BJ_single, huo]
    by_cases hij : i = j
    · subst hij
      simp [Formalism.REAL.Jm, hST _ (hs_mem i)]
    · simp [Formalism.REAL.Jm, hij, hs_inj.ne hij]
  have hiso : ∀ x y : Submodule.span ℂ (Set.range u), BJ ε (f x) (f y) = BJ ε x y := by
    intro x y
    rw [hfx, hfx, hx, hx]
    exact (wittLin_holds_lemma ε u (fun j => Pi.single (s j) 1) hgram _ _).symm
  have hfinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx0
    have hr : ∀ j, bU.repr x j = 0 := by
      intro j
      have h1 := congrFun ((hfx x).symm.trans hx0) (s j)
      simpa [Finset.sum_apply, Pi.single_apply, hs_inj.eq_iff] using h1
    have h2 : bU.repr x = 0 := Finsupp.ext hr
    simpa using h2
  obtain ⟨g, hg, hgU⟩ := witt_extension_theorem ℂ (Fin n → ℂ) (BJ ε) (BJ_herm ε) (BJ_nondeg ε) _ f hfinj hiso
  have hgu : ∀ j, g (u j) = Pi.single (s j) 1 := by
    intro j
    have h1 := hgU (bU j)
    rw [hfb, Module.Basis.span_apply] at h1
    exact h1
  let cM : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix' (g.symm : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))
  let dM : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix' (g : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))
  have hcd : cM * dM = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    ext x
    simp
  have hdc : dM * cM = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    ext x
    simp
  let cU : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨cM, dM, hcd, hdc⟩
  have hmem : cU ∈ Formalism.REAL.UJ ε := by
    show Formalism.REAL.inUJ ε cM
    unfold Formalism.REAL.inUJ
    ext i j
    rw [wittLin_holds_lemma_2 ε cM i j, ← BJ_single ε i j]
    simp only [cM, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe]
    have h1 := hg (g.symm (Pi.single i 1)) (g.symm (Pi.single j 1))
    simp only [LinearEquiv.apply_symm_apply] at h1
    exact h1.symm
  refine ⟨S, ⟨cU, hmem⟩, ⟨hScard, hST⟩, ?_⟩
  have hgw : ∀ b, Formalism.MainNotions.S.uMat (⟨cU, hmem⟩ : Formalism.REAL.UJ ε)⁻¹ *ᵥ w b = g (w b) := by
    intro b
    show dM *ᵥ w b = g (w b)
    exact LinearMap.toMatrix'_mulVec _ _
  simp only [hgw]
  apply Submodule.eq_of_le_of_finrank_le
  · rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    set x := g (w b) with hxb
    have hx0 : ∀ i ∈ S, x i = 0 := by
      intro i hi
      obtain ⟨j, rfl⟩ := hs_surj i hi
      have h1 : BJ ε (Pi.single (s j) 1) x = 0 := by
        rw [← hgu j, hxb, hg, ← BJ_herm, hperp j b, star_zero]
      rw [BJ_sum, Finset.sum_eq_single (s j)] at h1
      · simp only [Pi.single_eq_same, star_one, one_mul] at h1
        rcases mul_eq_zero.mp h1 with h2 | h2
        · exact absurd h2 (dJ_ne ε _)
        · exact h2
      · intro l _ hl
        simp [Pi.single_eq_of_ne hl]
      · intro h
        exact absurd (Finset.mem_univ _) h
    show x ∈ Submodule.span ℂ _
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : i ∈ S
    · rw [hx0 i hi, Pi.single_zero]
      exact Submodule.zero_mem _
    · have h1 : Pi.single i (x i) = x i • (Pi.single i 1 : Fin n → ℂ) := by
        ext l
        by_cases hl : l = i
        · subst hl
          simp
        · simp [Pi.single_eq_of_ne hl]
      rw [h1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, by simpa using hi, rfl⟩)
  · have hl1 : LinearIndependent ℂ (fun b => g (w b)) := hli.map' g.toLinearMap g.ker
    rw [finrank_span_eq_card hl1, Fintype.card_fin]
    have hset : (fun i : Fin n => (Pi.single i 1 : Fin n → ℂ)) '' (↑S)ᶜ =
        ↑(Sᶜ.image fun i : Fin n => (Pi.single i 1 : Fin n → ℂ)) := by
      simp [Finset.coe_image, Finset.coe_compl]
    rw [hset]
    refine (finrank_span_finset_le_card _).trans ?_
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_compl, Fintype.card_fin, hScard]
    omega

end Lin

end PI.AprimeInfW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FibNear
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FibOrbP
noncomputable section

namespace PI.AprimeInfW

theorem fibOrbAt_of (hU : UnitsOpenTens) (hF : FibAllT) (hC : MassDataMassesW.HinfCompact) : FibOrbAt := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hCh
  obtain ⟨Ω₁, hΩ₁, hn, hu⟩ := nearFacts_of hU X u' ψ hT μinf νinf fibInf hP Ω a hCh
  exact ⟨Ω₁, hΩ₁, hn, fun T hT1 => fib_near rmulFacts_holds hF hC X u' ψ hT μinf νinf fibInf hP T (a T)
    (hu T hT1).1 (hCh.2.2.2 T (hΩ₁ hT1)) (hu T hT1).2⟩

end PI.AprimeInfW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FibAllP
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem lfFib_at {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf
    (hP : PushHyp X u' ψ hT μinf νinf fibInf) (T : HmI X) : LFI X (fibInf T) := by
  intro K hK hKU
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  obtain ⟨k, -, hkcl, hKk, hkU⟩ := exists_compact_closed_between hK (isOpen_IndI X) hKU
  obtain ⟨f, hf1, hf0, hfc, -⟩ := exists_continuous_one_zero_of_isCompact hK isOpen_interior.isClosed_compl
    (Set.disjoint_compl_right_iff_subset.mpr hKk)
  have hts : tsupport f ⊆ IndI X := by
    refine (closure_minimal ?_ hkcl).trans hkU
    intro y hy
    by_contra h
    exact hy (hf0 (fun h' => h (interior_subset h')))
  have hI := ((hP.2.2.2.2.2.2).2.2 f f.continuous hfc hts).1 T (Set.mem_univ _)
  calc fibInf T K ≤ fibInf T {y | 1 ≤ ENNReal.ofReal (f y)} :=
        measure_mono fun y hy => by
          simp only [Set.mem_ofPred_eq]
          rw [hf1 hy]
          simp
    _ = 1 * fibInf T {y | 1 ≤ ENNReal.ofReal (f y)} := (one_mul _).symm
    _ ≤ ∫⁻ y, ENNReal.ofReal (f y) ∂(fibInf T) :=
        mul_meas_ge_le_lintegral₀ f.continuous.measurable.ennreal_ofReal.aemeasurable 1
    _ < ⊤ := hI.lintegral_lt_top

theorem fibAllT_holds : FibAllT := by
  intro D X u' ψ hT μinf νinf fibInf hP T
  refine ⟨fun g => ?_, lfFib_at X u' ψ hT μinf νinf fibInf hP T⟩
  have hfib := hP.2.2.2.2.2.2
  have h := fibEqI X ψ μinf νinf _ _ hP.2.2.2.2.1 hP.2.2.2.2.2.1
    (fibTrans X μinf νinf fibInf hfib g (sdInvG_of sdTestI_holds X u' ψ hT μinf νinf fibInf hP g)) hfib
  exact congrFun h T

end PI.AprimeInfW
end
end

namespace PI.AprimeInfW

theorem unitsOpenTens : UnitsOpenTens := fun X => isOpen_units_tens X

theorem fibOrbAt_of_compact (hC : MassDataMassesW.HinfCompact) : FibOrbAt :=
  fibOrbAt_of unitsOpenTens fibAllT_holds hC

end PI.AprimeInfW
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushTop
noncomputable section

namespace PI.AprimeInfW

theorem pushInf_of_pushLFin_of_orbUniq_of_constTest (hL : PushLFin) (hU : OrbUniq) (hC : ConstTest) : PushInf :=
  pushInf_of invPush_holds invFib_holds (lfPush_of detNZ_holds hL) lfFib_holds hU hC

end PI.AprimeInfW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.WittNearP
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem wittNear_holds : WittNear := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a Ω' a₂ hC hC₂ T hTm hU
  obtain ⟨-, hmul, hsm, hgr, hcT, hc1, -, -⟩ := rmulFacts_holds X
  obtain ⟨u, hu⟩ := hU
  set w : TupI X := rmulT X (↑u⁻¹ : MfI X) (rmulT X (a T) (Y0 X u')) with hw
  have hgT : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (rmulT X (a T) (Y0 X u')) = (T : Matrix _ _ _) :=
    hC.2.2.2 T hTm.1
  have hgT₂ : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (rmulT X (a₂ T) (Y0 X u')) = (T : Matrix _ _ _) :=
    hC₂.2.2.2 T hTm.2
  have hY0 : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (Y0 X u') =
      (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F)) :=
    gramR_ratTup (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))
  have hinv1 : cTI X (↑u⁻¹ : MfI X) * cTI X (↑u : MfI X) = 1 := by
    rw [← hcT, Units.mul_inv, hc1]
  have hgw : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J w =
      (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F)) := by
    rw [hw, hgr, hgT, ← hgT₂, ← hu, hgr, hY0]
    rw [show cTI X (↑u⁻¹ : MfI X) * (cTI X (↑u : MfI X) *
        (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F)) * (↑u : MfI X)) *
        (↑u⁻¹ : MfI X) = (cTI X (↑u⁻¹ : MfI X) * cTI X (↑u : MfI X)) *
        (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F)) *
        ((↑u : MfI X) * (↑u⁻¹ : MfI X)) by simp only [Matrix.mul_assoc],
      hinv1, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
  have h2 : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  have hfix : ∀ b : X.B.I.E, X.B.I.cm.sig b = b ↔ b ∈ (algebraMap X.B.I.F X.B.I.E).range :=
    fun b => X.B.I.cm.fixed b
  have hinv : ∀ x, X.B.I.cm.sig (X.B.I.cm.sig x) = x := fun x => star_star x
  have hJ : IsHermND X.B.I.cm.sig X.B.I.J := by
    refine ⟨fun i j => ?_, X.B.I.J_det⟩
    have := congrFun (congrFun X.B.I.J_herm i) j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this
    exact this
  have hdet := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  have hUC : PIW.AdelicOrbitU.UnitChoice (Ainf X.B.I.F) :=
    PIW.AdelicOrbitU.uc_pi (fun v : NumberField.InfinitePlace X.B.I.F => v.Completion)
  obtain ⟨g, hg⟩ := PI.AprimeInfWitt.witt_R X.B.I.cm.sig h2 hfix hinv X.B.I.J hJ (tupH (frameOf X u')) hT hdet
    (Ainf X.B.I.F) hUC w hgw
  refine ⟨g, ?_⟩
  have hback : rmulT X (↑u : MfI X) w = rmulT X (a T) (Y0 X u') := by
    rw [hw, hmul, Units.inv_mul, rmulT_one]
  rw [← hback, ← hu, hsm]
  congr 1
  exact hg.symm

end PI.AprimeInfW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ConstFin
noncomputable section

namespace PI.AprimeInfW

theorem properOrb_of_compact (hH : MassDataMassesW.HinfCompact) : ProperOrb :=
  properOrb_of_one (properOne_of wittInf_holds hH) invNbhd_holds

theorem pushCont_of_compact (hH : MassDataMassesW.HinfCompact) : PushCont :=
  pushCont_of frame_independent_at_infinity (properOrb_of_compact hH)

theorem pushLFin_of_compact (hH : MassDataMassesW.HinfCompact) : PushLFin :=
  pushLFin_of_proper (properOrb_of_compact hH)

theorem constTest_of_polar_compact (hP : PolarLoc) (hH : MassDataMassesW.HinfCompact) : ConstTest :=
  constTest_of_polar hP (pushCont_of_compact hH)

end PI.AprimeInfW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.JacOneCOfCharts
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def JacOneCFor (Pr : ChartPred) : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a → Pr X u' hT μinf νinf a →
    ∀ Ω₂ ⊆ Ω, Ω₂ ∈ 𝓝 (TI X u' hT) → ∀ c : HmI X → ENNReal, ContinuousAt c (TI X u' hT) →
      PolId X u' μinf νinf a Ω₂ c → c (TI X u' hT) = (ENNReal.ofReal (KVal X u'))⁻¹

theorem jacOneCFor_of {Pr : ChartPred} (hK : KPos) (hR : LocRatioFor Pr) : JacOneCFor Pr := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hC hPr Ω₂ hΩ₂ hΩ₂n c hcc hid
  obtain ⟨V, W, hVW, hsh, hlim⟩ := hR X u' ψ hT μinf νinf fibInf hP Ω a hC hPr Ω₂ hΩ₂ hΩ₂n
  have hK0 : 0 < KVal X u' := hK X u' ψ hT μinf νinf fibInf hP
  set L : ℕ → ENNReal := fun n => μinf (BoxT X u' a (V n) (W n)) with hL
  set B : ℕ → ENNReal := fun n => νinf (W n) with hB
  set M : ℕ → ENNReal := fun n => X.measG.μGinf (TubeG X u' (V n)) with hM
  set A : ℕ → ENNReal := fun n => ∫⁻ T in W n, c T ∂νinf with hA

  have key : ∀ n, L n = A n * M n := by
    intro n
    obtain ⟨hWm, hWs, -, -, hU, hBm, hBI, -, hTm, -, hMt⟩ := hVW n
    have h := hid ((BoxT X u' a (V n) (W n)).indicator 1) (measurable_one.indicator hBm) (W n)
      hWs hWm
    have hsub : BoxT X u' a (V n) (W n) ⊆
        gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' (Subtype.val '' (W n)) ∩ IndI X := by
      intro y hy
      refine ⟨?_, hBI hy⟩
      obtain ⟨T, hTW, g, -, rfl⟩ := hy
      refine ⟨T, hTW, ?_⟩
      rw [gramR_smul, hC.2.2.2 T (hΩ₂ (hWs hTW))]
    rw [lintegral_indicator_one hBm, Measure.restrict_apply hBm, Set.inter_eq_left.2 hsub] at h
    have hin : ∀ T ∈ W n, ∫⁻ g, (BoxT X u' a (V n) (W n)).indicator 1 (g • rmulT X (a T) (Y0 X u'))
        ∂X.measG.μGinf = M n := by
      intro T hTW
      have hs := pre_box X u' hT hC (V n) (hWs.trans hΩ₂) hU T hTW
      have e : (fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J =>
          (BoxT X u' a (V n) (W n)).indicator (1 : TupI X → ENNReal) (g • rmulT X (a T) (Y0 X u'))) =
          (TubeG X u' (V n)).indicator 1 := by
        funext g
        by_cases hg : g ∈ TubeG X u' (V n)
        · have h4 : g • rmulT X (a T) (Y0 X u') ∈ BoxT X u' a (V n) (W n) := by rw [← hs] at hg; exact hg
          rw [Set.indicator_of_mem hg, Set.indicator_of_mem h4]; rfl
        · have h4 : g • rmulT X (a T) (Y0 X u') ∉ BoxT X u' a (V n) (W n) := by rw [← hs] at hg; exact hg
          rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem h4]
      rw [e, lintegral_indicator_one hTm]
    rw [setLIntegral_congr_fun hWm (fun T hT' => by rw [hin T hT'])] at h
    rw [lintegral_mul_const' _ _ hMt.ne] at h
    exact h
  have hAt : ∀ n, A n ≠ ⊤ := by
    intro n hA'
    obtain ⟨-, -, -, -, -, -, -, hLt, -, hM0, -⟩ := hVW n
    have : L n = ⊤ := by rw [key n, hA', ENNReal.top_mul hM0.ne']
    exact absurd this hLt.ne
  have e1 : ∀ n, (L n).toReal / ((B n).toReal * (M n).toReal) = (A n).toReal / (B n).toReal := by
    intro n
    obtain ⟨-, -, hB0, hBt, -, -, -, -, -, hM0, hMt⟩ := hVW n
    have hMr : 0 < (M n).toReal := ENNReal.toReal_pos hM0.ne' hMt.ne
    rw [key n, ENNReal.toReal_mul]
    field_simp
  have hlim' : Tendsto (fun n => (L n).toReal / ((B n).toReal * (M n).toReal)) atTop (𝓝 (KVal X u')⁻¹) := hlim

  have hge : ∀ b : ENNReal, b < c (TI X u' hT) → b.toReal ≤ (KVal X u')⁻¹ := by
    intro b hb
    have hU : c ⁻¹' Set.Ioi b ∈ 𝓝 (TI X u' hT) := hcc (Ioi_mem_nhds hb)
    refine ge_of_tendsto hlim' ?_
    filter_upwards [hsh _ hU] with n hn
    obtain ⟨hWm, -, hB0, hBt, -⟩ := hVW n
    have hBr : 0 < (B n).toReal := ENNReal.toReal_pos hB0.ne' hBt.ne
    have hlow : b * B n ≤ A n :=
      calc b * B n = ∫⁻ _ in W n, b ∂νinf := (setLIntegral_const _ _).symm
        _ ≤ A n := lintegral_mono_ae ((ae_restrict_iff' hWm).2 (Eventually.of_forall fun T hT' =>
            (hn hT').le))
    rw [e1 n, le_div_iff₀ hBr, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (hAt n) hlow

  have hle : ∀ b : ENNReal, c (TI X u' hT) < b → b ≠ ⊤ → (KVal X u')⁻¹ ≤ b.toReal := by
    intro b hb hbt
    have hU : c ⁻¹' Set.Iio b ∈ 𝓝 (TI X u' hT) := hcc (Iio_mem_nhds hb)
    refine le_of_tendsto hlim' ?_
    filter_upwards [hsh _ hU] with n hn
    obtain ⟨hWm, -, hB0, hBt, -⟩ := hVW n
    have hBr : 0 < (B n).toReal := ENNReal.toReal_pos hB0.ne' hBt.ne
    have hup : A n ≤ b * B n :=
      calc A n ≤ ∫⁻ _ in W n, b ∂νinf := lintegral_mono_ae ((ae_restrict_iff' hWm).2
            (Eventually.of_forall fun T hT' => (hn hT').le))
        _ = b * B n := setLIntegral_const _ _
    rw [e1 n, div_le_iff₀ hBr, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top hbt hBt.ne) hup

  have hfin : c (TI X u' hT) ≠ ⊤ := by
    intro htop
    have h1 := hge (ENNReal.ofReal ((KVal X u')⁻¹ + 1)) (by rw [htop]; exact ENNReal.ofReal_lt_top)
    rw [ENNReal.toReal_ofReal (by positivity)] at h1
    linarith
  set c₀ : ℝ := (c (TI X u' hT)).toReal with hc₀
  have hle' : c₀ ≤ (KVal X u')⁻¹ := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    by_cases hcε : c₀ - ε ≤ 0
    · have : 0 < (KVal X u')⁻¹ := inv_pos.2 hK0
      linarith
    · push_neg at hcε
      have hb : ENNReal.ofReal (c₀ - ε) < c (TI X u' hT) := by
        rw [← ENNReal.ofReal_toReal hfin, ← hc₀]
        exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
      have := hge _ hb
      rw [ENNReal.toReal_ofReal hcε.le] at this
      linarith
  have hge' : (KVal X u')⁻¹ ≤ c₀ := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hc0 : 0 ≤ c₀ := ENNReal.toReal_nonneg
    have hb : c (TI X u' hT) < ENNReal.ofReal (c₀ + ε) := by
      rw [← ENNReal.ofReal_toReal hfin, ← hc₀]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    have := hle _ hb ENNReal.ofReal_ne_top
    rwa [ENNReal.toReal_ofReal (by linarith)] at this
  have hceq : c₀ = (KVal X u')⁻¹ := le_antisymm hle' hge'
  rw [← ENNReal.ofReal_toReal hfin, ← hc₀, hceq, ENNReal.ofReal_inv_of_pos hK0]

theorem jacOneC_of_charts (hK : KPos) (hU : UnimodInf) (hW : WittNear) (hG : GoodChartEx) : JacOneC := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hC Ω₂ hΩ₂ hΩ₂n c hcc hid
  obtain ⟨Ω', a₂, hC₂, hgood⟩ := hG X u' ψ hT μinf νinf fibInf hP
  have hev : ∀ᶠ T in 𝓝 (TI X u' hT), ∃ h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J,
      rmulT X (a T) (Y0 X u') = h • rmulT X (a₂ T) (Y0 X u') := by
    obtain ⟨ι, _, κ, -, η, _, eT, eH, cμ, cν, Ψ', U, -, -, -, -, -, -, -, -, hev0, -⟩ := hgood
    filter_upwards [hev0, hC.1, hC₂.1] with T h1 h2 h3
    exact hW X u' ψ hT μinf νinf fibInf hP Ω a Ω' a₂ hC hC₂ T ⟨h2, h3⟩ h1.1
  set Ω₃ := Ω₂ ∩ Ω' ∩ {T | ∃ h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J,
      rmulT X (a T) (Y0 X u') = h • rmulT X (a₂ T) (Y0 X u')} with hΩ₃
  have hΩ₃n : Ω₃ ∈ 𝓝 (TI X u' hT) := inter_mem (inter_mem hΩ₂n hC₂.1) hev
  have hid₂ : PolId X u' μinf νinf a₂ Ω₃ c := by
    intro φ hφ S hS hSm
    rw [hid φ hφ S (hS.trans (Set.inter_subset_left.trans Set.inter_subset_left)) hSm]
    refine setLIntegral_congr_fun hSm (fun T hT' => ?_)
    obtain ⟨h, eh⟩ := (hS hT').2
    rw [eh]
    congr 1
    have e : ∀ g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J,
        φ (g • h • rmulT X (a₂ T) (Y0 X u')) = (fun g' => φ (g' • rmulT X (a₂ T) (Y0 X u'))) (g * h) := by
      intro g; simp only [mul_smul]
    simp_rw [e]
    exact hU X u' ψ hT μinf νinf fibInf hP (fun g' => φ (g' • rmulT X (a₂ T) (Y0 X u'))) h
  exact jacOneCFor_of hK (locRatioFor_of hK splitAsym_good) X u' ψ hT μinf νinf fibInf hP Ω' a₂ hC₂ hgood Ω₃
    (Set.inter_subset_left.trans Set.inter_subset_right) hΩ₃n c hcc hid₂

end PI.AprimeInfW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ExInfHolds
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem exInf_holds : ExInf := by
  intro D X hb FdN FdN' u u' ψ _hX hM _hS
  obtain ⟨⟨_hT1, _νH, hOm, _⟩, _⟩ := hM.1 u'
  obtain ⟨_, h1⟩ := hOm
  refine ⟨h1.1, fun μ hμ => ⟨(h1.2 μ hμ).1, fun ν hν => ?_⟩⟩
  have h2 := (h1.2 μ hμ).2 ν hν
  obtain ⟨μv, hμv⟩ := h2.1
  have h3 := h2.2 μv hμv
  obtain ⟨νv, hνv⟩ := h3.1
  exact ((h3.2 νv hνv).1)

end PI.AprimeInfW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.WeilInfOf
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem weilInf_of (hH : HtotInf) : WeilInf := by
  intro D X hb FdN FdN' u u' hX f hf s hs
  obtain ⟨e1, e2, e3⟩ := hH X hb FdN FdN' u u' hX
  haveI : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  haveI : SecondCountableTopology (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    PI.AprimeInfT.secondCountable_HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  haveI : BorelSpace (Fin (D.R.rS + 1 + D.R.rS) → Fin X.B.I.n → Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :=
    PI.AprimeInfT.borelSpace_tup (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F) (D.R.rS + 1 + D.R.rS)
  haveI : X.measG.μGinf.IsHaarMeasure := X.measG_norm.2.1
  have hL : Measure.IsMulLeftInvariant ((X.measW u').μHinf : Measure (MulAction.stabilizer
      (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (ratTup (F := X.B.I.F) (Ainf X.B.I.F) (tupH (frameOf X u'))))) :=
    (X.measW_norm u').2.1.toIsMulLeftInvariant
  have h0 : (X.measW u').μHinf Set.univ ≠ 0 := by rw [e1]; exact e2.ne'
  have hfin : (X.measW u').μHinf Set.univ ≠ ⊤ := by rw [e1]; exact e3.ne
  exact PI.AprimeInfA.unfold_stab (G := HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)
    (ratTup (F := X.B.I.F) (Ainf X.B.I.F) (tupH (frameOf X u')))
    (PI.AprimeInfT.continuous_orbit (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J _)
    X.measG.μGinf (X.measW u').μHinf hL h0 hfin f hf s hs

end PI.AprimeInfW
end
end

namespace PI.AprimeInfAsm

open PI.AprimeInfW

theorem aprimeInf_of_good (hC : MassDataMassesW.HinfCompact) (hG : GoodChartEx) :
    Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  have hJ : JacOneC := jacOneC_of_charts kPos_holds unimodInf_holds wittNear_holds hG
  aprimeInf_of_leaves exInf_holds
    (pushInf_of_pushLFin_of_orbUniq_of_constTest (pushLFin_of_compact hC) (orbUniq_of_compact hC)
      (constTest_of_polar_compact
        (polar_local_of_fibres kPos_holds gramMeas_holds (fibOrbAt_of_compact hC) (pushCont_of_compact hC) hJ) hC))
    (weilInf_of (htotInf_of (hinfFin_of hC))) hC

theorem aprimeInf_of_std (hC : MassDataMassesW.HinfCompact) (hG : GrpStd) (hT : TupStd) :
    Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  aprimeInf_of_good hC (goodChartEx_of_witt linIndW_holds perpPosV wittLin_holds hG hT)

theorem lamDet_of_open (hN : NuBridge) (hP : PlaceJacAll) : LamDet :=
  lamDet_of betaIso_holds muBridge_holds hN dKForm_holds rowsZ_holds detT_holds hP

theorem aprimeInf_of_grp (hC : MassDataMassesW.HinfCompact) (hG : GrpStd) (hN : NuBridge) (hP : PlaceJacAll) :
    Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  aprimeInf_of_std hC hG (tupStd_of_sm kapSm_holds (lamDet_of_open hN hP))

end PI.AprimeInfAsm
