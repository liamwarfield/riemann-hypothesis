module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeIntegralUnipotentRadicalRealPoints
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductMeasureBasicProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeviFactorInverseModulusProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentEqLatticeUnipotentCoords

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WordFrameDualTupleGramIntegrality
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WordFrameDualTupleGramIntegrality
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDom.FrameCrd

variable {D : D7} (X : HidaSetting D)

theorem sig_apply (x : D.host.E) : (D.sp.cm.sig : D.host.E →+* D.host.E) x = starRingEnd D.host.E x := rfl

theorem vecOf_sum (x : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :
    vecOf X x = ∑ i, x i • X.bas (ci X i) := by
  simp only [vecOf, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Module.Basis.equivFun_symm_apply, LinearEquiv.funCongrLeft_apply]
  rw [← Equiv.sum_comp (ci X).symm]
  simp

theorem vecOf_crdH (y : (VS D).V) : vecOf X (crdH X y) = y := by
  rw [vecOf_sum]
  simp only [crdH]
  rw [Equiv.sum_comp (ci X) (fun j => X.bas.repr y j • X.bas j)]
  exact X.bas.sum_repr y

theorem pairM_apply {α β : Type} [Fintype α] [Fintype β]
    (P : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) α D.host.E) (Q : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) β D.host.E)
    (a : α) (b : β) :
    GlobalTheory.SgAlg.pairM (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) Q P a b =
      (VS D).hT (vecOf X fun i => P i a) (vecOf X fun i => Q i b) := by
  rw [vecOf_sum, vecOf_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [GlobalTheory.SgAlg.pairM, GlobalTheory.SgAlg.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Jc,
    map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum, sig_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [RingHom.id_apply]
  ring

theorem col_last (u : D.what₂.Word) : (fun i => Pc X u i (Fin.last D.R.rS)) = crdH X (X.zu u) := by
  funext i; simp [Pc]

theorem col_cs (u : D.what₂.Word) (a : Fin D.R.rS) : (fun i => Pc X u i a.castSucc) = crdH X (X.eX a) := by
  funext i; simp [Pc]

theorem col_f (a : Fin D.R.rS) : (fun i => fc X i a) = crdH X (X.fY a) := by
  funext i; simp [fc]

theorem hT_swap_zero {x y : (VS D).V} (h : (VS D).hT x y = 0) : (VS D).hT y x = 0 := by
  rw [← (VS D).herm.eq x y, h, map_zero]

theorem T_ne_zero (u : D.what₂.Word) : ((((D.mem u).A.T : ℕ) : D.host.E)) ≠ 0 :=
  Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero

theorem gram_frame (u : D.what₂.Word) :
    GlobalTheory.SgAlg.pairM (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) (Pc X u) =
      GlobalTheory.SgAlg.TF D.R.rS (algebraMap D.host.F D.host.E (Tc u)) := by
  ext a b
  rw [pairM_apply]
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => rw [col_last, vecOf_crdH, X.zu_norm]; simp [GlobalTheory.SgAlg.TF, Tc]
    | cast b =>
      rw [col_last, col_cs, vecOf_crdH, vecOf_crdH, hT_swap_zero (X.zu_orth u b).1]
      simp [GlobalTheory.SgAlg.TF, (Fin.castSucc_ne_last b).symm]
  | cast a =>
    induction b using Fin.lastCases with
    | last =>
      rw [col_last, col_cs, vecOf_crdH, vecOf_crdH, (X.zu_orth u a).1]
      simp [GlobalTheory.SgAlg.TF, Fin.castSucc_ne_last a]
    | cast b =>
      rw [col_cs, col_cs, vecOf_crdH, vecOf_crdH, X.ee]
      simp [GlobalTheory.SgAlg.TF, Matrix.diagonal_apply, Fin.castSucc_ne_last a]

theorem free_frame (u : D.what₂.Word) : GlobalTheory.SgAlg.Free (Pc X u) := by
  have hT0 := T_ne_zero u
  let Y : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (D.R.rS + 1)) D.host.E :=
    Matrix.of fun i c => Fin.lastCases (crdH X (X.zu u) i) (fun a => crdH X (X.fY a) i) c
  let Dg : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E :=
    Matrix.diagonal fun c => Fin.lastCases (-(((D.mem u).A.T : ℕ) : D.host.E))⁻¹ (fun _ => 1) c
  refine ⟨Dg * (GlobalTheory.SgAlg.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * Jc X), ?_⟩
  have h : Dg * (GlobalTheory.SgAlg.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * Jc X) * Pc X u =
      Dg * GlobalTheory.SgAlg.pairM (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) Y := by
    simp only [GlobalTheory.SgAlg.pairM, Matrix.mul_assoc]
  rw [h]
  ext c d
  rw [Matrix.diagonal_mul, pairM_apply]
  induction c using Fin.lastCases with
  | last =>
    have hy : (fun i => Y i (Fin.last D.R.rS)) = crdH X (X.zu u) := by funext i; simp [Y]
    induction d using Fin.lastCases with
    | last => rw [hy, col_last, vecOf_crdH, X.zu_norm]; simp [hT0]
    | cast b =>
      rw [hy, col_cs, vecOf_crdH, vecOf_crdH, hT_swap_zero (X.zu_orth u b).1]
      simp [(Fin.castSucc_ne_last b).symm]
  | cast a =>
    have hy : (fun i => Y i a.castSucc) = crdH X (X.fY a) := by funext i; simp [Y]
    induction d using Fin.lastCases with
    | last =>
      rw [hy, col_last, vecOf_crdH, vecOf_crdH, (X.zu_orth u a).2]
      simp [Fin.castSucc_ne_last a]
    | cast b =>
      rw [hy, col_cs, vecOf_crdH, vecOf_crdH, ← (VS D).herm.eq (X.eX b) (X.fY a), X.ef]
      by_cases hab : a = b
      · subst hab; simp
      · simp [hab, Ne.symm hab]

theorem dual_frame (u : D.what₂.Word) :
    GlobalTheory.SgAlg.IsDual (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) (fc X) := by
  refine ⟨?_, ?_⟩
  · ext a b
    rw [pairM_apply, col_f, vecOf_crdH]
    induction a using Fin.lastCases with
    | last =>
      rw [col_last, vecOf_crdH, hT_swap_zero (X.zu_orth u b).2]
      simp [(Fin.castSucc_ne_last b).symm]
    | cast a =>
      rw [col_cs, vecOf_crdH, X.ef]
      simp
  · ext a b
    rw [pairM_apply, col_f, col_f, vecOf_crdH, vecOf_crdH, X.ff]
    simp

theorem aaD_eq (a : Fin D.R.rS) : aaD D a = GlobalTheory.SgGlob.dInv D.host.E (D.R.rS - a) := by
  rw [aaD, GlobalTheory.IntTerm.Conv.ddS_eq, GlobalTheory.SgGlob.dInv, ← Nat.cast_sub a.2.le, _root_.zpow_neg, _root_.zpow_natCast,
    inv_pow]

theorem tupLat_le (u : D.what₂.Word) :
    GlobalTheory.SnMass.tupLat (GlobalTheory.SnMass.id1 D.host.E D.R.rS) (GlobalTheory.SnMass.sideM (Pc X u) (fc X)) ≤ Lc X := by
  rw [GlobalTheory.SnMass.tupLat, Submodule.span_le]
  rintro _ ⟨b, x, hx, rfl⟩
  show vecOf X (x • fun i => GlobalTheory.SnMass.sideM (Pc X u) (fc X) i b) ∈ (VS D).L0
  rw [LinearMap.map_smul, X.Lam_split]
  induction b using Fin.addCases with
  | left c =>
    simp only [GlobalTheory.SnMass.sideM, Fin.append_left]
    simp only [GlobalTheory.SnMass.id1, Fin.append_left] at hx
    induction c using Fin.lastCases with
    | last =>
      simp only [Fin.val_last, Nat.sub_self, GlobalTheory.SgGlob.dInv, pow_zero] at hx
      obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
      rw [col_last, vecOf_crdH, algebraMap_smul]
      exact Submodule.mem_sup_left (Submodule.mem_sup_right (X.Lb.smul_mem o (X.zu_Lb u)))
    | cast a =>
      simp only [Fin.val_castSucc] at hx
      rw [← aaD_eq] at hx
      rw [col_cs, vecOf_crdH]
      exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨a, x, hx, rfl⟩))
  | right a =>
    simp only [GlobalTheory.SnMass.sideM, Fin.append_right]
    simp only [GlobalTheory.SnMass.id1, Fin.append_right] at hx
    rw [← aaD_eq] at hx
    rw [col_f, vecOf_crdH]
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨a, x, hx, rfl⟩)

end GlobalTheory.CovDom.FrameCrd

namespace GlobalTheory.CovDom


open GlobalTheory.CovDom.FrameCrd in
theorem frame_dual_lat : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word),
    GlobalTheory.SgAlg.IsFrame (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (algebraMap D.host.F D.host.E (Tc u)) (Pc X u) ∧
    GlobalTheory.SgAlg.IsDual (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) (fc X) ∧
    GlobalTheory.SnMass.tupLat (GlobalTheory.SnMass.id1 D.host.E D.R.rS) (GlobalTheory.SnMass.sideM (Pc X u) (fc X)) ≤ Lc X :=
  fun _ X u => ⟨⟨free_frame X u, gram_frame X u⟩, dual_frame X u, tupLat_le X u⟩

end GlobalTheory.CovDom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WordFrameDualTupleGramIntegralityStatement
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wordFrame_dualTuple_gram_integrality : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), GlobalTheory.SgAlg.IsFrame (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (algebraMap D.host.F D.host.E (Tc u)) (Pc X u) ∧ GlobalTheory.SgAlg.IsDual (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) (fc X) ∧ GlobalTheory.SnMass.tupLat (GlobalTheory.SnMass.id1 D.host.E D.R.rS) (GlobalTheory.SnMass.sideM (Pc X u) (fc X)) ≤ Lc X := by
  first | exact @GlobalTheory.CovDom.frame_dual_lat | exact GlobalTheory.CovDom.frame_dual_lat | (intros; apply GlobalTheory.CovDom.frame_dual_lat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConcreteGramHermitianNondegenerateLatticeSelfDua
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConcreteGramHermitianNondegenerateLatticeSelfDua
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovDom

variable {D : D7} (X : HidaSetting D)

theorem vecOf_apply (x : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :
    vecOf X x = ∑ i, x i • X.bas (ci X i) := by
  simp only [vecOf, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Module.Basis.equivFun_symm_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
  exact Fintype.sum_equiv (ci X).symm _ _ fun j => by simp

theorem vecOf_bijective : Function.Bijective (vecOf X) := by
  unfold vecOf
  rw [LinearMap.coe_comp]
  exact X.bas.equivFun.symm.bijective.comp (LinearEquiv.funCongrLeft _ _ _).bijective

private theorem sig_eq_star' (a : D.host.E) : D.sp.cm.sig a = star a := by rfl

theorem form_Jc (x y : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :
    GlobalTheory.SgAlg.form (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) x y = (VS D).hT (vecOf X y) (vecOf X x) := by
  rw [vecOf_apply, vecOf_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [GlobalTheory.SgAlg.form, dotProduct, Matrix.mulVec, Jc, map_sum, map_smulₛₗ,
    LinearMap.sum_apply, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [AlgHom.coe_toRingHom, sig_eq_star', starRingEnd_apply]
  ring

end GlobalTheory.CovDom

theorem GlobalTheory.CovDom.herm_selfDual : ∀ (D : D7) (X : HidaSetting D), Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND D.sp.cm.sig (Jc X) ∧ GlobalTheory.SgGlob.SelfDual (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Lc X) := by
  intro D X
  have hform := form_Jc X
  have hinj := (vecOf_bijective X).1
  have hsurj := (vecOf_bijective X).2
  unfold Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND GlobalTheory.SgGlob.SelfDual
  refine ⟨⟨fun i j => ?_, ?_⟩, ?_, fun v => ?_⟩
  · simp only [Jc]
    rw [sig_eq_star']
    exact (VS D).herm.eq _ _
  · intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    apply hv0
    apply hinj
    rw [map_zero]
    apply (VS D).nondeg.2
    intro w
    obtain ⟨y, rfl⟩ := hsurj w
    rw [← hform v y]
    simp [GlobalTheory.SgAlg.form, hv]
  · let e : (Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) ≃ₗ[𝓞 D.host.E] (VS D).V :=
      (LinearEquiv.ofBijective (vecOf X) (vecOf_bijective X)).restrictScalars (𝓞 D.host.E)
    have hc : Lc X = (VS D).L0.comap (e : _ →ₗ[𝓞 D.host.E] (VS D).V) := rfl
    rw [hc, Submodule.comap_equiv_eq_map_symm]
    exact (VS D).standardTuple_isLattice.fg.map _
  · show vecOf X v ∈ (VS D).L0 ↔ _
    conv_lhs => rw [← (VS D).baseLattice_isUnimodular]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply]
    constructor
    · intro h w hw
      rw [hform v w]
      obtain ⟨a, ha⟩ := Submodule.mem_one.mp (h _ hw)
      exact ⟨a, ha⟩
    · intro h y hy
      obtain ⟨w, rfl⟩ := hsurj y
      have hw := h w hy
      rw [hform v w] at hw
      obtain ⟨a, ha⟩ := hw
      exact Submodule.mem_one.mpr ⟨a, ha⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConcreteGramHermitianNondegenerateLatticeSelfDuaStatement
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.concrete_gram_hermitian_nondegenerate_lattice_selfDual : ∀ (D : D7) (X : HidaSetting D), Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND D.sp.cm.sig (Jc X) ∧ GlobalTheory.SgGlob.SelfDual (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Lc X) := by
  first | exact @GlobalTheory.CovDom.herm_selfDual | exact GlobalTheory.CovDom.herm_selfDual | (intros; apply GlobalTheory.CovDom.herm_selfDual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportRealPointsBijectiveMultiplicative
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportRealPointsBijectiveMultiplicative
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDom.RealPts

theorem jm_mul_self {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

def mkUJc {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ)
    (h : Aᴴ * Formalism.REAL.Jm ε * A = Formalism.REAL.Jm ε) : Formalism.REAL.UJ ε :=
  ⟨⟨A, Formalism.REAL.Jm ε * Aᴴ * Formalism.REAL.Jm ε,
    by
      rw [mul_eq_one_comm]
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, h, jm_mul_self],
    by rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, h, jm_mul_self]⟩, h⟩

theorem uMat_mkUJc {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ)
    (h : Aᴴ * Formalism.REAL.Jm ε * A = Formalism.REAL.Jm ε) : Formalism.MainNotions.S.uMat (mkUJc ε A h) = A := rfl

theorem hpk_star (k r : ℕ) : (Formalism.QuantumDeterminants.Hpk k r).map star = Formalism.QuantumDeterminants.Hpk k r := by
  ext i j
  simp only [Matrix.map_apply]
  unfold Formalism.QuantumDeterminants.Hpk
  split_ifs <;> simp

theorem tauOf_spec (D : D7) (w : InfinitePlace D.host.E) : InfinitePlace.mk (embS D (tauOf D w)) = w := by
  unfold tauOf
  exact (GlobalTheory.RealPlaces.existsUnique_place D w).exists.choose_spec

theorem tauOf_mk (D : D7) (τ : D.what₂.Tau) : tauOf D (InfinitePlace.mk (embS D τ)) = τ :=
  (GlobalTheory.RealPlaces.existsUnique_place D _).unique (tauOf_spec D _) rfl

theorem cjw_cjw (D : D7) (w : InfinitePlace D.host.E) (M : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :
    cjw D w (cjw D w M) = M := by
  unfold cjw
  split_ifs with h
  · rfl
  · funext i j
    simp

theorem cjw_injective (D : D7) (w : InfinitePlace D.host.E) : Function.Injective (cjw D w) := by
  intro M N hMN
  rw [← cjw_cjw D w M, hMN, cjw_cjw]

theorem of_cjw_mul (D : D7) (w : InfinitePlace D.host.E) (A B : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :
    Matrix.of (cjw D w (Matrix.of.symm (Matrix.of A * Matrix.of B))) =
      Matrix.of (cjw D w A) * Matrix.of (cjw D w B) := by
  unfold cjw
  split_ifs with h
  · ext i j
    rfl
  · ext i j
    simp [Matrix.mul_apply, star_sum]

private theorem hpk_apply_of_outer_index (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    star (Formalism.QuantumDeterminants.Hpk k r i j) = Formalism.QuantumDeterminants.Hpk k r i j := by
  have e := congrFun (congrFun (hpk_star k r) i) j
  simpa only [Matrix.map_apply] using e

theorem cjw_mem (D : D7) (w : InfinitePlace D.host.E) (M : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)
    (hM : Matrix.of M ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    Matrix.of (cjw D w M) ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
  unfold cjw
  split_ifs with h
  · exact hM
  · simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq] at hM ⊢
    have e : (Matrix.of fun i j => star (M i j))ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (Matrix.of fun i j => star (M i j))
        = ((Matrix.of M)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * Matrix.of M).map star := by
      ext i j
      simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, star_sum,
        star_mul', star_star, hpk_apply_of_outer_index]
    rw [e, hM, hpk_star]

end GlobalTheory.CovDom.RealPts

namespace GlobalTheory.CovDom.RealPts

theorem trX_of {D : D7} (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) (g : X.B.I.Ginf) (τ : D.what₂.Tau) :
    Matrix.of (trX X C g τ) = C.Qi τ * Formalism.MainNotions.S.uMat (g (vOf X τ)) * C.Q τ := rfl

private theorem of_trX_mul_eq_mul {D : D7} (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) (s g : X.B.I.Ginf)
    (τ : D.what₂.Tau) :
    Matrix.of (trX X C (s * g) τ) = Matrix.of (trX X C s τ) * Matrix.of (trX X C g τ) := by
  have hQ : C.Q τ * C.Qi τ = 1 := (C.isT τ).2.1
  rw [trX_of, trX_of, trX_of]
  simp only [Pi.mul_apply, Formalism.MainNotions.S.uMat, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (C.Q τ) (C.Qi τ), hQ, Matrix.one_mul]

private theorem eq_of_mul_mul_eq_of_det_ne_zero {n m : ℕ} (Q : Matrix (Fin n) (Fin m) ℂ) (Qi : Matrix (Fin m) (Fin n) ℂ)
    (hQ : Q * Qi = 1) (A : Matrix (Fin n) (Fin n) ℂ) : Q * (Qi * A * Q) * Qi = A := by
  simp only [← Matrix.mul_assoc, hQ, Matrix.one_mul]
  rw [Matrix.mul_assoc, hQ, Matrix.mul_one]

private theorem hcompl_unit_property_of_isPrime {n m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (H N : Matrix (Fin m) (Fin m) ℂ)
    (Q : Matrix (Fin n) (Fin m) ℂ) (Qi : Matrix (Fin m) (Fin n) ℂ)
    (hQ : Q * Qi = 1) (hJ : Qᴴ * J * Q = H) (hN : Nᴴ * H * N = H) :
    (Q * N * Qi)ᴴ * J * (Q * N * Qi) = J := by
  have e : (Q * N * Qi)ᴴ * J * (Q * N * Qi) = Qiᴴ * (Nᴴ * (Qᴴ * J * Q) * N) * Qi := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have e' : (Q * Qi)ᴴ * J * (Q * Qi) = Qiᴴ * (Qᴴ * J * Q) * Qi := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e, hJ, hN, ← hJ, ← e', hQ]
  simp

end GlobalTheory.CovDom.RealPts

namespace GlobalTheory.CovDom

open GlobalTheory.CovDom.RealPts

theorem transport_real_points : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ),
    (∀ x : InfinitePlace D.host.E → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS, (∀ w, Matrix.of (x w) ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) →
      ∃ g : X.B.I.Ginf, Gm D (trX X C g) = x) ∧
    Function.Injective (fun g : X.B.I.Ginf => Gm D (trX X C g)) ∧
    ∀ (s g : X.B.I.Ginf) (w : InfinitePlace D.host.E),
      Matrix.of (Gm D (trX X C (s * g)) w) = Matrix.of (Gm D (trX X C s) w) * Matrix.of (Gm D (trX X C g) w) := by
  intro D X θ C
  refine ⟨?_, ?_, ?_⟩
  ·
    intro x hx
    have hM : ∀ τ, Matrix.of (cjw D (InfinitePlace.mk (embS D τ)) (x (InfinitePlace.mk (embS D τ)))) ∈
        Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) :=
      fun τ => cjw_mem D _ _ (hx _).1
    have hU : ∀ v, (C.Q (X.pl v) * Matrix.of (cjw D (InfinitePlace.mk (embS D (X.pl v)))
          (x (InfinitePlace.mk (embS D (X.pl v))))) * C.Qi (X.pl v))ᴴ * Formalism.REAL.Jm (X.B.I.ε v) *
        (C.Q (X.pl v) * Matrix.of (cjw D (InfinitePlace.mk (embS D (X.pl v)))
          (x (InfinitePlace.mk (embS D (X.pl v))))) * C.Qi (X.pl v)) = Formalism.REAL.Jm (X.B.I.ε v) := by
      intro v
      have hT := C.isT (X.pl v)
      simp only [IsTranspC, vOf, Equiv.symm_apply_apply] at hT
      exact hcompl_unit_property_of_isPrime _ _ _ _ _ hT.2.1 hT.2.2.1 (hM _)
    refine ⟨fun v => mkUJc (X.B.I.ε v) _ (hU v), ?_⟩
    have key : ∀ τ, trX X C (fun v => mkUJc (X.B.I.ε v) _ (hU v)) τ =
        cjw D (InfinitePlace.mk (embS D τ)) (x (InfinitePlace.mk (embS D τ))) := by
      intro τ
      apply Matrix.of.injective
      have hQi : C.Qi τ * C.Q τ = 1 := (C.isT τ).1
      simp only [trX_of, uMat_mkUJc, vOf, Equiv.apply_symm_apply]
      exact eq_of_mul_mul_eq_of_det_ne_zero (C.Qi τ) (C.Q τ) hQi _
    funext w
    simp only [Gm, key, tauOf_spec, cjw_cjw]
  ·
    intro s g hsg
    funext v
    obtain ⟨τ, rfl⟩ : ∃ τ, vOf X τ = v := ⟨X.pl v, X.pl.symm_apply_apply v⟩
    have hw := congrFun hsg (InfinitePlace.mk (embS D τ))
    simp only [Gm, tauOf_mk] at hw
    have h2 := congrArg Matrix.of (cjw_injective D _ hw)
    rw [trX_of, trX_of] at h2
    have h3 := congrArg (fun N => C.Q τ * N * C.Qi τ) h2
    simp only [eq_of_mul_mul_eq_of_det_ne_zero (C.Q τ) (C.Qi τ) (C.isT τ).2.1] at h3
    exact Subtype.ext (Units.ext h3)
  ·
    intro s g w
    simp only [Gm]
    rw [← of_cjw_mul, ← of_trX_mul_eq_mul, Equiv.symm_apply_apply]

end GlobalTheory.CovDom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportRealPointsBijectiveMultiplicativeStatement
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transport_real_points_bijective_multiplicative : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ), (∀ x : InfinitePlace D.host.E → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS, (∀ w, Matrix.of (x w) ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) → ∃ g : X.B.I.Ginf, Gm D (trX X C g) = x) ∧ Function.Injective (fun g : X.B.I.Ginf => Gm D (trX X C g)) ∧ ∀ (s g : X.B.I.Ginf) (w : InfinitePlace D.host.E), Matrix.of (Gm D (trX X C (s * g)) w) = Matrix.of (Gm D (trX X C s) w) * Matrix.of (Gm D (trX X C g) w) := by
  first | exact @GlobalTheory.CovDom.transport_real_points | exact GlobalTheory.CovDom.transport_real_points | (intros; apply GlobalTheory.CovDom.transport_real_points <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetTransportedRealPointsImage
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetTransportedRealPointsImage
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDom

theorem measPolish_UJ (n : ℕ) (ε : Fin n → Bool) : PolishSpace (Formalism.REAL.UJ ε) := by
  haveI : PolishSpace (Matrix (Fin n) (Fin n) ℂ) := inferInstanceAs (PolishSpace (Fin n → Fin n → ℂ))
  exact (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.polishSpace

variable {D : D7}

theorem measCont_trX (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) : Continuous (trX X C) := by
  refine continuous_pi fun τ => ?_
  show Continuous fun x : X.B.I.Ginf => C.Qi τ * Formalism.MainNotions.S.uMat (x (vOf X τ)) * C.Q τ
  refine (continuous_const.matrix_mul ?_).matrix_mul continuous_const
  exact (Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply _)

theorem measInj_trX (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) : Function.Injective (trX X C) := by
  intro x y h
  funext v
  obtain ⟨τ, rfl⟩ : ∃ τ, vOf X τ = v := ⟨X.pl v, by simp [vOf]⟩
  have h2 : C.Qi τ * Formalism.MainNotions.S.uMat (x (vOf X τ)) * C.Q τ =
      C.Qi τ * Formalism.MainNotions.S.uMat (y (vOf X τ)) * C.Q τ := congrFun h τ
  obtain ⟨-, h1, -⟩ := C.isT τ
  have h3 := congrArg (fun M => C.Q τ * M * C.Qi τ) h2
  simp only [Matrix.mul_assoc, h1, Matrix.mul_one] at h3
  simp only [← Matrix.mul_assoc, h1, Matrix.one_mul] at h3
  exact Subtype.ext (Units.ext h3)

theorem measTauOf_mk (D : D7) (τ : D.what₂.Tau) : tauOf D (InfinitePlace.mk (embS D τ)) = τ :=
  (GlobalTheory.RealPlaces.existsUnique_place D _).unique
    (GlobalTheory.RealPlaces.existsUnique_place D _).exists.choose_spec rfl

theorem measInj_cjw (D : D7) (w : InfinitePlace D.host.E) : Function.Injective (cjw D w) := by
  intro M N h
  by_cases hw : Direct D w
  · simpa [cjw, hw] using h
  · simp only [cjw, hw, if_false] at h
    funext i j
    simpa using congrArg star (congrFun (congrFun h i) j)

theorem measCont_Gm (D : D7) : Continuous (Gm D) := by
  refine continuous_pi fun w => ?_
  by_cases hw : Direct D w
  · simp only [Gm, cjw, hw, if_true]
    exact continuous_apply _
  · simp only [Gm, cjw, hw, if_false]
    exact continuous_pi fun i => continuous_pi fun j =>
      continuous_star.comp ((continuous_apply j).comp ((continuous_apply i).comp (continuous_apply _)))

theorem measInj_Gm (D : D7) : Function.Injective (Gm D) := by
  intro y z h
  funext τ
  have := congrFun h (InfinitePlace.mk (embS D τ))
  simp only [Gm, measTauOf_mk] at this
  exact measInj_cjw D _ this

theorem measurableSet_Gm_trX_image : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (S : Set X.B.I.Ginf),
    MeasurableSet S → MeasurableSet (Gm D '' (trX X C '' S)) := by
  intro D X θ C S hS
  haveI : ∀ v, PolishSpace (Formalism.REAL.UJ (X.B.I.ε v)) := fun v => measPolish_UJ _ _
  rw [Set.image_image]
  exact hS.image_of_continuousOn_injOn ((measCont_Gm D).comp (measCont_trX X C)).continuousOn
    ((measInj_Gm D).comp (measInj_trX X C)).injOn

end GlobalTheory.CovDom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetTransportedRealPointsImageStatement
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurableSet_transported_real_points_image : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (S : Set X.B.I.Ginf), MeasurableSet S → MeasurableSet (Gm D '' (trX X C '' S)) := by
  first | exact @GlobalTheory.CovDom.measurableSet_Gm_trX_image | exact GlobalTheory.CovDom.measurableSet_Gm_trX_image | (intros; apply GlobalTheory.CovDom.measurableSet_Gm_trX_image <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePiPointsAtInfinitePlacesCMTypeImage
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePiPointsAtInfinitePlacesCMTypeImage
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDom

section Conj

variable {k r : ℕ}

def cjm (M : Formalism.QuantumDeterminants.Mt k r) : Formalism.QuantumDeterminants.Mt k r := fun i j => star (M i j)

theorem cjm_cjm (M : Formalism.QuantumDeterminants.Mt k r) : cjm (cjm M) = M := by
  funext i j; simp [cjm]

theorem measurable_cjm : Measurable (cjm : Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r) := by
  unfold cjm; fun_prop

def cjmE : Formalism.QuantumDeterminants.Mt k r ≃ᵐ Formalism.QuantumDeterminants.Mt k r where
  toFun := cjm
  invFun := cjm
  left_inv := cjm_cjm
  right_inv := cjm_cjm
  measurable_toFun := measurable_cjm
  measurable_invFun := measurable_cjm

theorem map_star_eq (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : X.map star = Xᴴᵀ := by
  ext i j; simp

theorem exp_map_star (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    NormedSpace.exp (X.map star) = (NormedSpace.exp X).map star := by
  rw [map_star_eq, map_star_eq, Matrix.exp_transpose, Matrix.exp_conjTranspose]

theorem Hpk_map_star : (Formalism.QuantumDeterminants.Hpk k r).map star = Formalism.QuantumDeterminants.Hpk k r := by
  ext i j
  simp only [Matrix.map_apply]
  unfold Formalism.QuantumDeterminants.Hpk
  split_ifs <;> simp

theorem map_star_mem_N {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.Nset k r) : g.map star ∈ Formalism.QuantumDeterminants.Nset k r := by
  obtain ⟨h1, h2, h3⟩ := hg
  refine ⟨?_, fun a i hi => ?_, fun i j a b c => ?_⟩
  · have h1' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := h1
    show (g.map star)ᴴ * Formalism.QuantumDeterminants.Hpk k r * g.map star = Formalism.QuantumDeterminants.Hpk k r
    have e : ∀ M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, M.map star = M.map (starRingEnd ℂ) := by
      intro M; rfl
    have hc : (g.map star)ᴴ = gᴴ.map star := by ext i j; simp
    rw [hc, ← Hpk_map_star, e, e, e, ← Matrix.map_mul, ← Matrix.map_mul, h1']
  · simp only [Matrix.map_apply, h2 a i hi]; split_ifs <;> simp
  · simp only [Matrix.map_apply, h3 i j a b c]; split_ifs <;> simp

end Conj

section Conj2
variable {k r : ℕ}

def cjR (m : ℕ) :
    EuclideanSpace ℝ (Fin m × Fin m × Bool) →ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin m × Bool) where
  toFun x := (WithLp.equiv 2 _).symm (realifyFun ((unrealify x).map star))
  map_add' x y := by
    ext ⟨i, j, b⟩
    cases b <;> simp [realifyFun, unrealify] <;> ring
  map_smul' c x := by
    ext ⟨i, j, b⟩
    cases b <;> simp [realifyFun, unrealify]

theorem unrealify_realify' {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) :
    unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) = X := by
  ext i j
  simp [unrealify, realifyFun]

theorem unrealify_cjR {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (cjR m x) = (unrealify x).map star := unrealify_realify' _

theorem norm_sq_unrealify' {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    ‖x‖ ^ 2 = ∑ i, ∑ j, ‖unrealify x i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [unrealify, Real.norm_eq_abs, sq_abs]
  ring

theorem norm_cjR {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) : ‖cjR m x‖ = ‖x‖ := by
  have : ‖cjR m x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [norm_sq_unrealify', norm_sq_unrealify', unrealify_cjR]
    simp only [Matrix.map_apply, norm_star]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

theorem cjR_mem {S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)}
    (hS : ∀ g ∈ S, g.map star ∈ S) : ∀ x ∈ lieE S, cjR (2 * r + k + 1) x ∈ lieE S := by
  intro x hx
  have : lieE S ≤ (lieE S).comap (cjR (2 * r + k + 1)) := by
    unfold lieE
    rw [Submodule.span_le]
    rintro _ ⟨X, hX, rfl⟩
    refine Submodule.subset_span ⟨X.map star, fun t => ?_, ?_⟩
    · have e : ((t : ℂ) • X.map star) = ((t : ℂ) • X).map star := by
        ext i j; simp
      rw [e, exp_map_star]; exact hS _ (hX t)
    · show _ = (WithLp.equiv 2 _).symm (realifyFun ((unrealify _).map star))
      rw [unrealify_realify']
  exact this hx

theorem norm_cjR_restrict {S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)}
    (hS : ∀ g ∈ S, g.map star ∈ S) (x : lieE S) :
    ‖(cjR (2 * r + k + 1)).restrict (cjR_mem hS) x‖ = ‖x‖ := by
  show ‖cjR (2 * r + k + 1) (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖ =
    ‖(x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖
  exact norm_cjR _

theorem haarLie_map_cjm {S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)}
    (hS : ∀ g ∈ S, g.map star ∈ S) (κ : ENNReal) : (haarLie S κ).map (cjmE (k := k) (r := r)) = haarLie S κ := by
  unfold haarLie
  rw [Measure.map_smul κ (cjmE (k := k) (r := r)).measurable.aemeasurable]
  congr 1
  set E : lieE S → Formalism.QuantumDeterminants.Mt k r := fun x => fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j with hE
  by_cases hm : AEMeasurable E volume
  · let Φ₀ : lieE S →ₗᵢ[ℝ] lieE S := ⟨(cjR (2 * r + k + 1)).restrict (cjR_mem hS), norm_cjR_restrict hS⟩
    let Φ : lieE S ≃ₗᵢ[ℝ] lieE S := Φ₀.toLinearIsometryEquiv rfl
    have hΦ := Φ.measurePreserving
    have e : (cjmE (k := k) (r := r)) ∘ E = E ∘ Φ := by
      funext x
      show cjm (fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j) =
        fun i j => NormedSpace.exp (unrealify (cjR (2 * r + k + 1) x)) i j
      rw [unrealify_cjR, exp_map_star]
      rfl
    rw [AEMeasurable.map_map_of_aemeasurable (cjmE (k := k) (r := r)).measurable.aemeasurable hm, e,
      ← AEMeasurable.map_map_of_aemeasurable (by rwa [hΦ.map_eq]) hΦ.measurable.aemeasurable, hΦ.map_eq]
  · exfalso
    apply hm
    have hu : Continuous (unrealify : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool) → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      have he : (fun x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool) => unrealify x i j) =
          fun x => ((x (i, j, false) : ℝ) : ℂ) + ((x (i, j, true) : ℝ) : ℂ) * Complex.I := by
        funext x
        apply Complex.ext <;> simp [unrealify]
      rw [he]
      fun_prop
    have hexp : Continuous (NormedSpace.exp : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := by
      open scoped Norms.Operator in exact NormedSpace.exp_continuous
    apply Measurable.aemeasurable
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    exact ((continuous_apply j).comp ((continuous_apply i).comp
      (hexp.comp (hu.comp continuous_subtype_val)))).measurable

end Conj2

section Places

variable (D : D7)

def plE : D.what₂.Tau ≃ InfinitePlace D.host.E :=
  Equiv.ofBijective (fun τ => InfinitePlace.mk (embS D τ))
    ((Function.bijective_iff_existsUnique _).2 (GlobalTheory.RealPlaces.existsUnique_place D))

theorem plE_tauOf (w : InfinitePlace D.host.E) : plE D (tauOf D w) = w :=
  (GlobalTheory.RealPlaces.existsUnique_place D w).exists.choose_spec

theorem tauOf_eq (w : InfinitePlace D.host.E) : tauOf D w = (plE D).symm w := by
  rw [Equiv.eq_symm_apply, plE_tauOf]

def cjwE (w : InfinitePlace D.host.E) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS ≃ᵐ Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  if Direct D w then MeasurableEquiv.refl _ else cjmE

theorem cjwE_apply (w : InfinitePlace D.host.E) (M : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) : cjwE D w M = cjw D w M := by
  unfold cjwE cjw
  split_ifs <;> rfl

def GmE : (D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) ≃ᵐ (InfinitePlace D.host.E → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :=
  (MeasurableEquiv.piCongrLeft (fun _ => Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) (plE D)).trans
    (MeasurableEquiv.piCongrRight (fun w => cjwE D w))

theorem coe_GmE : ⇑(GmE D) = Gm D := by
  funext y w
  show cjwE D w ((MeasurableEquiv.piCongrLeft (fun _ => Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) (plE D)) y w) = _
  simp only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply, cjwE_apply, Gm, tauOf_eq, eq_rec_constant]

theorem cjwE_mp (w : InfinitePlace D.host.E) :
    MeasurePreserving (cjwE D w) (haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) (haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) := by
  unfold cjwE
  split_ifs
  · exact MeasurePreserving.id _
  · exact ⟨(cjmE).measurable, haarLie_map_cjm (fun g hg => map_star_mem_N hg) 1⟩

theorem GmE_mp : MeasurePreserving (GmE D)
    (Measure.pi fun _ : D.what₂.Tau => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1)
    (Measure.pi fun _ : InfinitePlace D.host.E => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) := by
  haveI : SigmaFinite (haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) :=
    (GlobalTheory.haarLie_isHaarOn_Nset D.R.k D.R.rS 1 one_pos ENNReal.one_lt_top).1
  have h1 := measurePreserving_piCongrLeft (fun _ : InfinitePlace D.host.E => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) (plE D)
  have h2 := measurePreserving_pi (fun _ : InfinitePlace D.host.E => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1)
    (fun _ : InfinitePlace D.host.E => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) (cjwE_mp D)
  exact h2.comp h1

end Places

theorem measure_Gm_image : ∀ (D : D7) (S : Set (D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)),
    Measure.pi (fun _ : InfinitePlace D.host.E => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) (Gm D '' S) =
      Measure.pi (fun _ : D.what₂.Tau => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) S := by
  intro D S
  rw [← coe_GmE, MeasurableEquiv.image_eq_preimage_symm, ← MeasurableEquiv.map_apply, (GmE_mp D).symm.map_eq]

end GlobalTheory.CovDom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePiPointsAtInfinitePlacesCMTypeImageStatement
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurePi_pointsAtInfinitePlacesCMType_image : ∀ (D : D7) (S : Set (D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)), Measure.pi (fun _ : InfinitePlace D.host.E => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) (Gm D '' S) = Measure.pi (fun _ : D.what₂.Tau => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) S := by
  first | exact @GlobalTheory.CovDom.measure_Gm_image | exact GlobalTheory.CovDom.measure_Gm_image | (intros; apply GlobalTheory.CovDom.measure_Gm_image <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedFundDomainVolumeClassical
noncomputable section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace GlobalTheory.CovDom
open Formalism.L2.SG.PoincareInHH.PoincareSetting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem formallyUnramified_host (D : D7) : Algebra.FormallyUnramified (𝓞 D.host.F) (𝓞 D.host.E) := by
  haveI := D.host.isCMField_hostE
  have : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E) :=
    Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by
      obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
      refine ⟨θ, ?_⟩
      have : RingOfIntegers.mapRingEquiv
          (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t :=
        RingOfIntegers.ext ht.symm
      rwa [this]
  infer_instance

theorem cancel_conj {m : ℕ} (A M N : Matrix (Fin m) (Fin m) ℂ) (hA : IsUnit A.det)
    (h : A * M * A⁻¹ = A * N * A⁻¹) : M = N := by
  have key : ∀ Z : Matrix (Fin m) (Fin m) ℂ, A⁻¹ * (A * Z * A⁻¹) * A = Z := by
    intro Z
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hA, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA,
      Matrix.one_mul]
  rw [← key M, h, key N]

theorem isDomN (D : D7) (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word) :
    GlobalTheory.SnMass.IsDomN (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Lc X) (Pc X u) (Ac X C)
      (Gm D '' (trX X C '' Y.FN u)) := by
  obtain ⟨hmeas, hex, huniq⟩ := Y.FN_fund u
  obtain ⟨hsurj, hinj, hmul⟩ := GlobalTheory.T.transport_real_points_bijective_multiplicative D X θ C
  obtain ⟨h8a, h8b⟩ := GlobalTheory.T.integralUnipotent_eq_latticeUnipotent_coords D X θ C u
  have hgrp := Formalism.L2.SG.Pf.IdMeet.noinfEqC_holds D X u Y.hK
  have hA : ∀ w, IsUnit (Ac X C w).det := by
    intro w
    have h1 := (GlobalTheory.T.bessel_transport_isometry_frame_adapted D X θ C u).1 w
    have h2 := (GlobalTheory.T.concrete_gram_hermitian_nondegenerate_lattice_selfDual D X).1.2
    have e : ((Jc X).map w.embedding).det = w.embedding (Jc X).det := by rw [RingHom.map_det]; rfl
    have h3 : ((Jc X).map w.embedding).det ≠ 0 := by rw [e]; exact (map_ne_zero _).2 h2
    rw [← h1, Matrix.det_mul, Matrix.det_mul] at h3
    exact isUnit_iff_ne_zero.2 (right_ne_zero_of_mul h3)
  refine ⟨GlobalTheory.T.measurableSet_transported_real_points_image D X θ C _ hmeas, fun x hx => ?_⟩
  obtain ⟨g, rfl⟩ := hsurj x hx
  obtain ⟨s, hs, hsg⟩ := hex g
  obtain ⟨γ, hγ, hc⟩ := h8b s hs
  refine ⟨γ, ⟨hγ, trX X C (s * g), ⟨s * g, hsg, rfl⟩, ?_⟩, ?_⟩
  · funext w
    rw [hc w, ← hmul]
    simp
  · rintro γ' ⟨hγ', y, ⟨f, hf, rfl⟩, hy⟩
    obtain ⟨s', hs', hc'⟩ := h8a γ' hγ'
    have hfe : f = s' * g := by
      apply hinj
      funext w
      have := congrFun hy w
      simp only at this ⊢
      rw [this, hc' w, ← hmul]
      simp
    have hmem : s' * s⁻¹ ∈ NOinf X u := by
      rw [hgrp] at hs hs' ⊢
      exact Subgroup.mul_mem _ hs' (Subgroup.inv_mem _ hs)
    have hss : s' * s⁻¹ = 1 := huniq (s * g) hsg _ hmem (by rw [show s' * s⁻¹ * (s * g) = s' * g by group, ← hfe]; exact hf)
    have hs'e : s' = s := by rw [mul_inv_eq_one] at hss; exact hss
    subst hs'e
    obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.E) := inferInstance
    have hm := cancel_conj _ _ _ (hA w) ((hc' w).trans (hc w).symm)
    refine Matrix.ext fun i j => w.embedding.injective ?_
    have := congrFun (congrFun hm i) j
    simpa only [Matrix.map_apply] using this

theorem main : ∀ (D : D7) (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word), (Measure.pi (fun _ : D.what₂.Tau => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u)).toReal = (2 * D.host.v) ^ (((D.R.rS : ℝ) ^ 2 + (D.R.rS : ℝ) * D.R.k + (D.R.rS : ℝ) / 2) * Fintype.card D.what₂.Tau) := by
  intro D X Y θ C u
  obtain ⟨hs, hnum⟩ := GlobalTheory.T.fundamental_domain_normalising_constants D
  obtain ⟨hH, hSD⟩ := GlobalTheory.T.concrete_gram_hermitian_nondegenerate_lattice_selfDual D X
  obtain ⟨hF, hDu, hT⟩ := GlobalTheory.T.wordFrame_dualTuple_gram_integrality D X u
  obtain ⟨hM, hAd⟩ := GlobalTheory.T.bessel_transport_isometry_frame_adapted D X θ C u
  have hI := GlobalTheory.T.covolume_integral_unipotentRadical_real_points D.host.F D.host.E D.sp.cm.sig D.R.k D.R.rS (Jc X) (Lc X) (Pc X u) (fc X) (Tc u)
    (Ac X C) (sc D) (GlobalTheory.AdelicU.isCMExt_host D) (formallyUnramified_host D) hH hSD hF hDu hT hM hs hAd
  have h1 := hI.2 _ (isDomN D X Y θ C u)
  have hv : 0 ≤ 2 * D.host.v := by unfold Host.v Host.rdE; positivity
  change (Measure.pi _ (trX X C '' Y.FN u)).toReal = _
  rw [← GlobalTheory.T.measurePi_pointsAtInfinitePlacesCMType_image D, h1, hnum, ENNReal.toReal_ofReal (Real.rpow_nonneg hv _)]

end GlobalTheory.CovDom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedFundDomainVolumeClassicalStatement
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transportedFundDomain_volume_classical : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word), (Measure.pi (fun _ : D.what₂.Tau => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u)).toReal = (2 * D.host.v) ^ (((D.R.rS : ℝ) ^ 2 + (D.R.rS : ℝ) * D.R.k + (D.R.rS : ℝ) / 2) * Fintype.card D.what₂.Tau) := by
  first | exact @GlobalTheory.CovDom.main | exact GlobalTheory.CovDom.main | (intros; apply GlobalTheory.CovDom.main <;> assumption)
end
