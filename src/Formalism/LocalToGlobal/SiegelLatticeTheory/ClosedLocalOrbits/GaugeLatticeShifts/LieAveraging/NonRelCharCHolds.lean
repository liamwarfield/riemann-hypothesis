module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LieAveraging.LiePowRPerp
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.NonRelPf

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

@[reducible] def qMod (S : HSpace E) : Module ℚ (Module.End E S.V) :=
  Module.compHom (Module.End E S.V) (algebraMap ℚ E)

attribute [local instance] qMod

theorem qsmul_apply (q : ℚ) (A : Module.End E S.V) (x : S.V) : (q • A) x = (algebraMap ℚ E q) • A x := rfl

section Xa

variable (F : FlagG S r T)

theorem Xa_zero : F.Xa 0 = ⊥ := by
  unfold FlagG.Xa
  simp

theorem Xa_mono {a b : ℕ} (h : a ≤ b) : F.Xa a ≤ F.Xa b := Submodule.span_mono (Set.image_mono fun (i : Fin r) (hi : i.1 < a) => lt_of_lt_of_le hi h)

theorem Xa_ge {a : ℕ} (h : r ≤ a) : F.Xa a = F.X := by
  unfold FlagG.Xa FlagG.X
  have hu : {i : Fin r | i.1 < a} = Set.univ := Set.eq_univ_of_forall fun i => lt_of_lt_of_le i.2 h
  rw [hu, Set.image_univ]

theorem Xa_min (a : ℕ) : F.Xa a = F.Xa (min a r) := by
  rcases le_total a r with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, Xa_ge F h, Xa_ge F le_rfl]

theorem e_mem_Xa (a : Fin r) : F.e a ∈ F.Xa (a.1 + 1) := Submodule.subset_span ⟨a, Nat.lt_succ_self _, rfl⟩

theorem hT_Xa_zero (f : S.V) (a : ℕ) (hf : ∀ b : Fin r, b.1 < a → S.hT f (F.e b) = 0) {x : S.V}
    (hx : x ∈ F.Xa a) : S.hT f x = 0 := by
  have hle : F.Xa a ≤ LinearMap.ker (S.hT f) := by
    unfold FlagG.Xa
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    exact LinearMap.mem_ker.mpr (hf b hb)
  exact LinearMap.mem_ker.mp (hle hx)

theorem hT_eq_coefX (f : S.V) (a : Fin r) (hf : ∀ b, S.hT f (F.e b) = if b = a then 1 else 0) {x : S.V}
    (hx : x ∈ F.X) : S.hT f x = F.coefX x a := by
  classical
  have hx' : x ∈ Submodule.span E (Set.range F.e) := hx
  have hc : F.coefX x a = F.e_indep.repr ⟨x, hx'⟩ a := by
    simp [FlagG.coefX, hx']
  rw [hc]
  have hsum : x = ∑ b, F.e_indep.repr ⟨x, hx'⟩ b • F.e b := by
    have h1 := F.e_indep.linearCombination_repr ⟨x, hx'⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at h1
    exact h1.symm
  conv_lhs => rw [hsum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_smul, hf]

end Xa

section Lie

variable {F : FlagG S r T} {Y : Module.End E S.V}

theorem lie_skew_pow (hY : Y ∈ F.LieN) (k : ℕ) (x y : S.V) :
    S.hT x ((Y ^ k) y) = (-1) ^ k * S.hT ((Y ^ k) x) y := by
  induction k generalizing x y with
  | zero => simp
  | succ k ih =>
    have h1 : (Y ^ (k + 1)) y = (Y ^ k) (Y y) := by rw [pow_succ, Module.End.mul_apply]
    have h2 : (Y ^ (k + 1)) x = Y ((Y ^ k) x) := by rw [pow_succ', Module.End.mul_apply]
    have h3 := hY.1 ((Y ^ k) x) y
    rw [h1, h2, ih, pow_succ]
    linear_combination ((-1 : E) ^ k) * h3

theorem lie_Xa (hY : Y ∈ F.LieN) {j : ℕ} (hj : j ≤ r) {x : S.V} (hx : x ∈ F.Xa j) : Y x ∈ F.Xa (j - 1) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [Xa_zero F] at hx
    rw [(Submodule.mem_bot E).1 hx, map_zero]
    exact Submodule.zero_mem _
  · exact hY.2.1 j hj0 hj x hx

theorem lie_pow_Xa (hY : Y ∈ F.LieN) (k : ℕ) {j : ℕ} (hj : j ≤ r) {x : S.V} (hx : x ∈ F.Xa j) :
    (Y ^ k) x ∈ F.Xa (j - k) := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ← Nat.sub_sub]
    exact lie_Xa hY (le_trans (Nat.sub_le j k) hj) ih

theorem lie_X (hY : Y ∈ F.LieN) {x : S.V} (hx : x ∈ F.X) : Y x ∈ F.X := by
  rw [← Xa_ge F (le_refl r)] at hx ⊢
  exact Xa_mono F (Nat.sub_le r 1) (lie_Xa hY le_rfl hx)

theorem lie_pow_X (hY : Y ∈ F.LieN) (k : ℕ) {x : S.V} (hx : x ∈ F.X) : (Y ^ k) x ∈ F.X := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact lie_X hY ih

theorem lie_pow_r_X (hY : Y ∈ F.LieN) {x : S.V} (hx : x ∈ F.X) : (Y ^ r) x = 0 := by
  rw [← Xa_ge F (le_refl r)] at hx
  have h := lie_pow_Xa hY r le_rfl hx
  rw [Nat.sub_self, Xa_zero F] at h
  exact (Submodule.mem_bot E).1 h

theorem lie_pow_r_perp (hY : Y ∈ F.LieN) (y : S.V) : (Y ^ r) y ∈ perpS S F.X := by
  show ∀ x ∈ F.X, S.hT x ((Y ^ r) y) = 0
  intro x hx
  rw [lie_skew_pow hY, lie_pow_r_X hY hx, map_zero, LinearMap.zero_apply, mul_zero]

theorem lie_nilp (hY : Y ∈ F.LieN) : Y ^ (2 * r + 1) = 0 := by
  have hp : Y ^ (2 * r + 1) = Y ^ r * Y * Y ^ r := by
    rw [← pow_succ, ← pow_add]
    congr 1
    omega
  apply LinearMap.ext
  intro v
  have h3 := lie_pow_r_X hY (hY.2.2 _ (lie_pow_r_perp hY v))
  rw [hp, Module.End.mul_apply, Module.End.mul_apply, LinearMap.zero_apply]
  exact h3

end Lie

section Exp

variable {F : FlagG S r T} {Y : Module.End E S.V} (s : E)

def nexp (Y : Module.End E S.V) (s : E) : Module.End E S.V := IsNilpotent.exp (s • Y)

theorem sY_nilp (hY : Y ∈ F.LieN) : (s • Y) ^ (2 * r + 1) = 0 := by
  rw [smul_pow, lie_nilp hY, smul_zero]

theorem sY_isNilp (hY : Y ∈ F.LieN) : IsNilpotent (s • Y) := ⟨2 * r + 1, sY_nilp s hY⟩

theorem nexp_apply (hY : Y ∈ F.LieN) (x : S.V) :
    nexp Y s x = ∑ i ∈ Finset.range (2 * r + 1), (algebraMap ℚ E (i.factorial : ℚ)⁻¹ * s ^ i) • (Y ^ i) x := by
  unfold nexp
  rw [IsNilpotent.exp_eq_sum (sY_nilp s hY), LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [qsmul_apply, smul_pow, LinearMap.smul_apply, mul_smul]

variable {s}

theorem star_alg_rat (q : ℚ) : star (algebraMap ℚ E q) = algebraMap ℚ E q := by
  rw [eq_ratCast (algebraMap ℚ E) q]
  exact star_ratCast q

theorem nexp_adj (hY : Y ∈ F.LieN) (hs : star s = s) (x y : S.V) :
    S.hT (nexp Y s x) y = S.hT x (nexp Y (-s) y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [nexp_apply s hY, nexp_apply (-s) hY, map_sum, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsk := lie_skew_pow hY i x y
  have hsk' : S.hT ((Y ^ i) x) y = (-1) ^ i * S.hT x ((Y ^ i) y) := by
    rw [hsk, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, starRingEnd_apply,
    star_mul', star_pow, hs, star_alg_rat]
  rw [hsk', neg_pow s i]
  ring

theorem nexp_mul_neg (hY : Y ∈ F.LieN) : nexp Y s * nexp Y (-s) = 1 := by
  letI : Algebra ℚ (Module.End E S.V) := Algebra.compHom (Module.End E S.V) (algebraMap ℚ E)
  have hc : Commute (s • Y) ((-s) • Y) := ((Commute.refl Y).smul_left s).smul_right (-s)
  have key := IsNilpotent.exp_add_of_commute hc (sY_isNilp s hY) (sY_isNilp (-s) hY)
  have h0 : s • Y + (-s) • Y = 0 := by rw [neg_smul, add_neg_cancel]
  rw [h0, IsNilpotent.exp_zero] at key
  exact key.symm

theorem nexp_neg_mul (hY : Y ∈ F.LieN) : nexp Y (-s) * nexp Y s = 1 := by
  have h := nexp_mul_neg (s := -s) hY
  rwa [neg_neg] at h

def nexpE (hY : Y ∈ F.LieN) (s : E) : S.V ≃ₗ[E] S.V :=
  LinearEquiv.ofLinear (nexp Y s) (nexp Y (-s)) (nexp_mul_neg hY) (nexp_neg_mul hY)

theorem nexpE_apply (hY : Y ∈ F.LieN) (x : S.V) : nexpE hY s x = nexp Y s x := rfl

theorem nexpE_isom (hY : Y ∈ F.LieN) (hs : star s = s) : nexpE hY s ∈ Formalism.HermitianLatticesTheory.isom S.hT := by
  show ∀ x y, S.hT (nexpE hY s x) (nexpE hY s y) = S.hT x y
  intro x y
  rw [nexpE_apply, nexpE_apply, nexp_adj hY hs, ← Module.End.mul_apply, nexp_neg_mul hY,
    Module.End.one_apply]

theorem nexp_sub (hY : Y ∈ F.LieN) (x : S.V) :
    nexp Y s x - x = ∑ i ∈ Finset.Ico 1 (2 * r + 1), (algebraMap ℚ E (i.factorial : ℚ)⁻¹ * s ^ i) • (Y ^ i) x := by
  rw [nexp_apply s hY, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  simp

theorem nexp_Xa (hY : Y ∈ F.LieN) (j : ℕ) {x : S.V} (hx : x ∈ F.Xa (j + 1)) : nexp Y s x - x ∈ F.Xa j := by
  rw [nexp_sub hY]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
  have hi1 : 1 ≤ i := (Finset.mem_Ico.1 hi).1
  rw [Xa_min F (j + 1)] at hx
  exact Xa_mono F (by omega) (lie_pow_Xa hY i (min_le_right _ _) hx)

theorem nexp_perp (hY : Y ∈ F.LieN) {x : S.V} (hx : x ∈ perpS S F.X) : nexp Y s x - x ∈ F.X := by
  rw [nexp_sub hY]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by have := (Finset.mem_Ico.1 hi).1; omega⟩
  rw [pow_succ, Module.End.mul_apply]
  exact lie_pow_X hY k (hY.2.2 x hx)

theorem nexp_root (hY : Y ∈ F.LieN) (f : S.V) (a : Fin r)
    (hf : ∀ b, S.hT f (F.e b) = if b = a then 1 else 0) (hfz : S.hT f F.z = 0) :
    S.hT f (nexp Y s (F.fvec a.succ)) = s * F.coefX (Y (F.fvec a.succ)) a := by
  have ha := a.isLt
  have hXa1 : F.Xa (a.1 + 1) ≤ F.X := by
    rw [← Xa_ge F (le_refl r)]
    exact Xa_mono F ha
  have hzperp : F.z ∈ perpS S F.X := by
    show ∀ x ∈ F.X, S.hT x F.z = 0
    intro x hx
    change x ∈ Submodule.span E (Set.range F.e) at hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨b, rfl⟩ := hx; exact F.z_orth b
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]
  obtain ⟨hw, hfv⟩ : Y (F.fvec a.succ) ∈ F.Xa (a.1 + 1) ∧ S.hT f (F.fvec a.succ) = 0 := by
    by_cases h : a.1 + 1 < r
    · have hs : a.succ = (⟨a.1 + 1, h⟩ : Fin r).castSucc := Fin.ext (by simp)
      have he : F.fvec a.succ = F.e ⟨a.1 + 1, h⟩ := by
        rw [FlagG.fvec, hs, Fin.snoc_castSucc]
      rw [he]
      refine ⟨?_, ?_⟩
      · have h1 := lie_Xa hY (j := a.1 + 1 + 1) h (e_mem_Xa F ⟨a.1 + 1, h⟩)
        simpa using h1
      · rw [hf, if_neg]
        intro hb
        have := congrArg Fin.val hb
        simp at this
    · have hs : a.succ = Fin.last r := Fin.ext (by simp; omega)
      have he : F.fvec a.succ = F.z := by simp [FlagG.fvec, hs]
      have hr : a.1 + 1 = r := by omega
      rw [he, hr, Xa_ge F le_rfl]
      exact ⟨hY.2.2 _ hzperp, hfz⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [nexp_apply s hY, map_sum, Finset.sum_eq_single 1]
  · simp only [pow_one, map_smul, smul_eq_mul, Nat.factorial_one, Nat.cast_one, inv_one, map_one,
      one_mul]
    rw [hT_eq_coefX F f a hf (hXa1 hw)]
  · intro i _ hi1
    rw [map_smul, smul_eq_mul]
    refine mul_eq_zero_of_right _ ?_
    rcases i with _ | i
    · simpa using hfv
    · rw [pow_succ, Module.End.mul_apply]
      have hi : 1 ≤ i := by omega
      exact hT_Xa_zero F f a.1
        (fun b hb => by rw [hf b, if_neg (fun h => by subst h; exact lt_irrefl _ hb)])
        (Xa_mono F (by omega) (lie_pow_Xa hY i ha hw))
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

end Exp

end Formalism.L2.SG.NonRelPf
end
end

noncomputable section

open scoped Classical ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Vanish2 Formalism.L2.SG.Pf.Level

namespace Formalism.L2.SG.NonRelPf

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem fvec_succ (F : FlagG S r T) (a : Fin r) : F.fvec a.succ = nxt F.e F.z a := by
  rfl

theorem nxt_map {V W : Type} (g : V → W) (e : Fin r → V) (z : V) (a : Fin r) :
    g (nxt e z a) = nxt (fun b => g (e b)) (g z) a := by
  simp only [nxt]
  split_ifs <;> rfl

theorem mapFlag_Xa (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : FlagG S r T) (b : ℕ) :
    (mapFlag γ hγ F).Xa b = (F.Xa b).map (γ : S.V →ₗ[E] S.V) := by
  rw [FlagG.Xa, FlagG.Xa, Submodule.map_span, Set.image_image]
  rfl

theorem mapFlag_X (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : FlagG S r T) :
    (mapFlag γ hγ F).X = F.X.map (γ : S.V →ₗ[E] S.V) := by
  rw [FlagG.X, FlagG.X, Submodule.map_span, ← Set.range_comp]
  rfl

theorem mem_map_iff (γ : S.V ≃ₗ[E] S.V) (p : Submodule E S.V) (y : S.V) :
    y ∈ p.map (γ : S.V →ₗ[E] S.V) ↔ γ.symm y ∈ p := by
  exact Submodule.mem_map_equiv p

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

def Φ (v : InfinitePlace X.B.I.F) (y : D.host.E) : ℂ := X.B.I.φ v (X.ιE.symm y)

theorem Φ_add (v) (a b : D.host.E) : Φ X v (a + b) = Φ X v a + Φ X v b := by
  simp [Φ]
theorem Φ_sum (v) {ι : Type} (s : Finset ι) (f : ι → D.host.E) : Φ X v (∑ i ∈ s, f i) = ∑ i ∈ s, Φ X v (f i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Φ, map_sum]
theorem Φ_star (v) (a : D.host.E) : Φ X v (star a) = star (Φ X v a) := by
  have hb : star a = D.host.conj a := Formalism.BasicNotions.bridge_star_holds _ _ a
  have h1 : X.ιE.symm (star a) = star (X.ιE.symm a) := by
    apply X.ιE.injective
    rw [RingEquiv.apply_symm_apply, X.ιE_conj, RingEquiv.apply_symm_apply, hb]
  simp only [Φ]
  rw [h1, Formalism.L2.SG.Pf.Level.phi_star]
theorem Φ_rat (v) (q : ℚ) : Φ X v (q : D.host.E) = (q : ℂ) := by
  simp [Φ]

theorem hE_crd (p q : (VS D).V) : hE X (X.crd p) (X.crd q) = X.ιE.symm ((VS D).hT p q) := by
  apply X.ιE.injective
  rw [Formalism.L2.SG.Pf.Level.iota_hE, Formalism.L2.SG.Pf.Level.toV_crd, Formalism.L2.SG.Pf.Level.toV_crd,
    RingEquiv.apply_symm_apply]

theorem hTfe (a b : Fin D.R.rS) : (VS D).hT (X.fY a) (X.eX b) = if b = a then 1 else 0 := by
  have h : starRingEnd D.host.E ((VS D).hT (X.eX b) (X.fY a)) = (VS D).hT (X.fY a) (X.eX b) := by
    first
      | exact (VS D).herm.eq _ _
      | exact (VS D).herm _ _
  rw [← h, X.ef b a]
  split_ifs <;> simp

theorem psi_rat (w : D.what₂.Word) {x : X.B.I.GA} {m : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x m) :
    X.psiInfU w x.1 = ∏ v, Complex.exp (2 * Real.pi * Complex.I *
      ((∑ a : Fin D.R.rS, (Φ X v ((VS D).hT (X.fY a) (m (nxt X.eX (X.zu w) a))) +
        star (Φ X v ((VS D).hT (X.fY a) (m (nxt X.eX (X.zu w) a)))))) / (X.B.g : ℂ))) := by
  obtain ⟨M, -, h1, -, h3⟩ := hx
  have hrc : ∀ v a, rootCoord (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
      (rv X.B.I v (X.zR w)) (uMat (x.1 v)) a = Φ X v ((VS D).hT (X.fY a) (m (nxt X.eX (X.zu w) a))) := by
    intro v a
    unfold rootCoord
    have e1 : nxt (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR w)) a =
        rv X.B.I v (X.crd (nxt X.eX (X.zu w) a)) := by
      rw [nxt_map (fun y => rv X.B.I v (X.crd y))]; rfl
    rw [e1, h1 v, rv_mulVec X v, ← h3, hJ_rv, HidaSetting.fR, hE_crd]
    rfl
  unfold HidaSetting.psiInfU psiInf psiR
  simp only [hrc]

theorem Φ_sub (X : HidaSetting D) (v) (a b : D.host.E) : Φ X v (a - b) = Φ X v a - Φ X v b := by
  simp [Φ]

theorem star_F (X : HidaSetting D) (y : D.host.E) (hy : y ∈ D.host.F) : star y = y := by
  rw [Formalism.BasicNotions.bridge_star_holds _ _ y]
  exact (D.host.der.mem_F y).mp hy

def sigF (X : HidaSetting D) : D.host.E ≃ₐ[D.host.F] D.host.E :=
  AlgEquiv.ofRingEquiv (f := starRingAut) fun c => by
    show star (c : D.host.E) = c
    exact star_F X c c.2

theorem trace_zero (X : HidaSetting D) {y : D.host.E} (hy : y + star y = 0) : Algebra.trace D.host.F D.host.E y = 0 := by
  have h1 : Algebra.trace D.host.F D.host.E (sigF X y) = Algebra.trace D.host.F D.host.E y :=
    Algebra.trace_eq_of_algEquiv (sigF X) y
  have h2 : sigF X y = star y := rfl
  have h3 : star y = -y := eq_neg_of_add_eq_zero_right hy
  rw [h2, h3, map_neg] at h1
  have h4 : (2 : D.host.F) * Algebra.trace D.host.F D.host.E y = 0 := by
    linear_combination -h1
  rcases mul_eq_zero.mp h4 with h5 | h5
  · exact absurd h5 two_ne_zero
  · exact h5


open Formalism.L2.SG.TermOp.Vanish in
theorem nonRelCharC_holds : NonRelCharC := by
  intro D X Yf u u' t ht
  have hiso : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hisoF : ∀ a b, (VS D).hT (t.lin a) (t.lin b) = (VS D).hT a b := hiso
  set F' := mapFlag t.lin hiso (X.Fu u') with hF'
  have hfr : t.frame = ⟨F', t.lin (X.Fu u').z⟩ := by
    unfold GTerm.frame mapLF; rw [dite_eq_left hiso]
  have hnr : ¬ Relevant D.host.F (X.Fu u) F' := by
    intro h; apply ht
    unfold GTerm.relevant TermDef.Term.relevant TermDef.IsRel
    refine ⟨t.frame, ⟨t.rep.2.2.2.2, rfl⟩, ?_⟩
    rw [hfr]; exact h
  unfold Relevant at hnr
  push Not at hnr
  obtain ⟨Y, ⟨hY1, hY2⟩, hne⟩ := hnr
  set ℓ := (X.Fu u).ell Y with hℓ
  set ℓ' := F'.ell Y with hℓ'
  set δ : D.host.E := (ℓ - ℓ') + star (ℓ - ℓ') with hδ
  have hδ0 : δ ≠ 0 := by
    intro h0
    apply hne
    have := trace_zero X h0
    unfold FlagG.dpsi
    rw [map_sub, sub_eq_zero] at this
    exact this
  have hδs : star δ = δ := by rw [hδ, star_add, star_star, add_comm]
  set N := Fintype.card (InfinitePlace X.B.I.F) with hN
  have hNpos : 0 < N := Fintype.card_pos
  have hg0 : (X.B.g : ℚ) ≠ 0 := by
    rw [X.g_eq]; push_cast
    exact mul_ne_zero (by exact_mod_cast (D.host.g_prime 0).ne_zero) (by exact_mod_cast (D.host.g_prime 1).ne_zero)
  set c : ℚ := (X.B.g : ℚ) / (2 * N) with hc
  set s : D.host.E := (c : D.host.E) * δ⁻¹ with hsdef
  have hs : star s = s := by rw [hsdef, star_mul', star_inv₀, hδs, star_ratCast]
  have hsδ : s * δ = c := by rw [hsdef, mul_assoc, inv_mul_cancel₀ hδ0, mul_one]

  set n := nexpE hY1 s with hn
  have hnI : n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := nexpE_isom hY1 hs
  have hgtop : ∀ m : (VS D).V ≃ₗ[D.host.E] (VS D).V,
      Formalism.HermitianLatticesTheory.gmap m (⊤ : Submodule (𝓞 D.host.E) (VS D).V) = ⊤ := by
    intro m; unfold Formalism.HermitianLatticesTheory.gmap; rw [Submodule.map_top]; exact LinearMap.range_eq_top.2 m.surjective
  have horth : ∀ (G : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (y : (VS D).V),
      y ∈ orth (VS D) G.X → ∀ w ∈ G.X, (VS D).hT w y = 0 := by
    intro G y hy w hw
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hy
    exact hy w hw
  have hnN : n ∈ NLam ⊤ (lf D (X.Fu u)) := by
    refine ⟨⟨hnI, hgtop n⟩, fun j x hx => nexp_Xa (s := s) hY1 j hx, fun x hx => nexp_perp (s := s) hY1 ?_⟩
    show ∀ w ∈ (X.Fu u).X, (VS D).hT w x = 0
    intro w hw
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx
    exact hx w hw
  obtain ⟨x, hx⟩ := ratPt_holds D X n hnI
  have hr1 : x.1 ∈ X.NinfU u := nLamNinf_holds D X u ⊤ x n hx hnN
  have hx' : RatLink X (t.pt⁻¹ * x * t.pt) (t.lin⁻¹ * n * t.lin) :=
    Vanish.ratLink_mul X (Vanish.ratLink_mul X (Vanish.ratLink_inv X t.rep.2.1) hx) t.rep.2.1
  set n' := t.lin⁻¹ * n * t.lin with hn'
  have hn'app : ∀ y, n' y = t.lin.symm (n (t.lin y)) := fun y => rfl
  have hsub : ∀ y, n' y - y = t.lin.symm (nexp Y s (t.lin y) - t.lin y) := by
    intro y; rw [hn'app, map_sub, LinearEquiv.symm_apply_apply]; rfl
  have hn'N : n' ∈ NLam ⊤ (lf D (X.Fu u')) := by
    refine ⟨⟨?_, hgtop n'⟩, fun j y hy => ?_, fun y hy => ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hiso) hnI) hiso
    · have h1 : t.lin y ∈ F'.Xa (j + 1) := by
        rw [hF', mapFlag_Xa]; exact Submodule.mem_map_of_mem hy
      have h2 := nexp_Xa (s := s) hY2 j h1
      rw [hF', mapFlag_Xa, mem_map_iff] at h2
      rw [hsub]; exact h2
    · have h1 : t.lin y ∈ perpS (VS D) F'.X := by
        show ∀ w ∈ F'.X, (VS D).hT w (t.lin y) = 0
        intro w hw
        rw [hF', mapFlag_X, mem_map_iff] at hw
        have := horth (X.Fu u') y hy _ hw
        rw [← hisoF (t.lin.symm w) y, LinearEquiv.apply_symm_apply] at this
        exact this
      have h2 := nexp_perp (s := s) hY2 h1
      rw [hF', mapFlag_X, mem_map_iff] at h2
      rw [hsub]; exact h2
  have hr2 : (t.pt⁻¹ * x * t.pt).1 ∈ X.NinfU u' := nLamNinf_holds D X u' ⊤ _ n' hx' hn'N
  refine ⟨x.1, ⟨hr1, hr2⟩, ?_⟩
  show X.psiInfU u x.1 ≠ X.psiInfU u' (t.pt⁻¹ * x * t.pt).1
  rw [psi_rat X u hx, psi_rat X u' hx']

  have key : ∀ a, (VS D).hT (X.fY a) (n (nxt X.eX (X.zu u) a)) = s * (X.Fu u).coefX (Y ((X.Fu u).fvec a.succ)) a := by
    intro a
    have e : nxt X.eX (X.zu u) a = (X.Fu u).fvec a.succ := by rw [fvec_succ, X.Fu_e, X.flagZVector]
    rw [e]
    exact nexp_root hY1 (X.fY a) a (fun b => by rw [X.Fu_e]; exact hTfe X a b)
      (by rw [X.flagZVector]; exact (X.zu_orth u a).2)
  have key' : ∀ a, (VS D).hT (X.fY a) (n' (nxt X.eX (X.zu u') a)) = s * F'.coefX (Y (F'.fvec a.succ)) a := by
    intro a
    have e : t.lin (nxt X.eX (X.zu u') a) = F'.fvec a.succ := by
      rw [fvec_succ, nxt_map t.lin, hF']
      simp only [mapFlag, X.Fu_e, X.flagZVector]
    rw [hn'app, ← hisoF (X.fY a), LinearEquiv.apply_symm_apply, e]
    exact nexp_root hY2 (t.lin (X.fY a)) a
      (fun b => by
        show (VS D).hT (t.lin (X.fY a)) (t.lin ((X.Fu u').e b)) = _
        rw [hisoF, X.Fu_e]; exact hTfe X a b)
      (by
        show (VS D).hT (t.lin (X.fY a)) (t.lin (X.Fu u').z) = 0
        rw [hisoF, X.flagZVector]; exact (X.zu_orth u' a).2)
  have hsum : ∀ (cf : Fin D.R.rS → D.host.E) (v : InfinitePlace X.B.I.F),
      (∑ a, (Φ X v (s * cf a) + star (Φ X v (s * cf a)))) = Φ X v (s * ((∑ a, cf a) + star (∑ a, cf a))) := by
    intro cf v
    simp_rw [← Φ_star, ← Φ_add]
    rw [← Φ_sum]
    congr 1
    rw [star_sum, Finset.sum_add_distrib, mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [star_mul', hs]
  have hA : ∀ v, (∑ a, (Φ X v (s * (X.Fu u).coefX (Y ((X.Fu u).fvec a.succ)) a) +
      star (Φ X v (s * (X.Fu u).coefX (Y ((X.Fu u).fvec a.succ)) a)))) = Φ X v (s * (ℓ + star ℓ)) :=
    fun v => hsum (fun a => (X.Fu u).coefX (Y ((X.Fu u).fvec a.succ)) a) v
  have hA' : ∀ v, (∑ a, (Φ X v (s * F'.coefX (Y (F'.fvec a.succ)) a) +
      star (Φ X v (s * F'.coefX (Y (F'.fvec a.succ)) a)))) = Φ X v (s * (ℓ' + star ℓ')) :=
    fun v => hsum (fun a => F'.coefX (Y (F'.fvec a.succ)) a) v
  simp_rw [key, key']
  simp only [hA, hA']
  rw [← Complex.exp_sum, ← Complex.exp_sum]
  intro heq
  have hd : (∑ v, 2 * (Real.pi : ℂ) * Complex.I * (Φ X v (s * (ℓ + star ℓ)) / (X.B.g : ℂ))) -
      (∑ v, 2 * (Real.pi : ℂ) * Complex.I * (Φ X v (s * (ℓ' + star ℓ')) / (X.B.g : ℂ))) =
      (Real.pi : ℂ) * Complex.I := by
    rw [← Finset.sum_sub_distrib]
    have hv : ∀ v, 2 * (Real.pi : ℂ) * Complex.I * (Φ X v (s * (ℓ + star ℓ)) / (X.B.g : ℂ)) -
        2 * (Real.pi : ℂ) * Complex.I * (Φ X v (s * (ℓ' + star ℓ')) / (X.B.g : ℂ)) =
        2 * (Real.pi : ℂ) * Complex.I * ((c : ℂ) / (X.B.g : ℂ)) := by
      intro v
      have hΦ : Φ X v (s * (ℓ + star ℓ)) - Φ X v (s * (ℓ' + star ℓ')) = (c : ℂ) := by
        rw [← Φ_sub X, ← mul_sub]
        have : (ℓ + star ℓ) - (ℓ' + star ℓ') = δ := by rw [hδ, star_sub]; ring
        rw [this, hsδ, Φ_rat]
      rw [← mul_sub, ← sub_div, hΦ]
    rw [Finset.sum_congr rfl fun v _ => hv v, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN, hc]
    have hg0' : (X.B.g : ℂ) ≠ 0 := by exact_mod_cast hg0
    have hN0' : (N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
    push_cast
    field_simp
  have h1 : Complex.exp ((Real.pi : ℂ) * Complex.I) = 1 := by
    rw [← hd, Complex.exp_sub, heq, div_self (Complex.exp_ne_zero _)]
  rw [Complex.exp_pi_mul_I] at h1
  norm_num at h1

end Formalism.L2.SG.NonRelPf
