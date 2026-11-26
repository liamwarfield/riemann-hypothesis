module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.LocalGramMatrixFrame
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OmAtComplZero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.UnifExHolds

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.HostStarConj
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)

theorem sigR_inclR (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem sigR_tmul_one (x : R) : sigR R σ (x ⊗ₜ[F] (1 : E)) = x ⊗ₜ[F] (1 : E) := by
  simp [sigR]

theorem hform_smul {A : Type} [CommRing A] {M : ℕ} (τ : A →+* A) (J : Matrix (Fin M) (Fin M) A) (c d : A)
    (x y : Fin M → A) : Formalism.UG.hform τ J (c • x) (d • y) = τ c * d * Formalism.UG.hform τ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hR_ratTup {M k : ℕ} (J : Matrix (Fin M) (Fin M) E) (Y : Fin k → Fin M → E) (a b : Fin k) :
    hR R σ J (ratTup R Y a) (ratTup R Y b) = inclR R (hE σ J (Y a) (Y b)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, hE, Formalism.UG.hform, JR, ratTup, Matrix.map_apply, map_sum, map_mul, sigR_inclR]
  rfl

end Gen

theorem dV_ne_zero {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : dV v ≠ 0 := by
  unfold dV
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_ne_zero

theorem alp_ne_zero {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (r : ℕ) (a : Fin (r + 1)) :
    alp v r a ≠ 0 := by
  unfold alp
  split_ifs
  · exact pow_ne_zero _ (inv_ne_zero (dV_ne_zero v))
  · exact one_ne_zero

theorem alp_last {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (r : ℕ) :
    alp v r (Fin.last r) = 1 := by
  simp [alp]

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

theorem host_star_conj : Formalism.BasicNotions.bridge_star := by
  intro R H x
  have := H.isCMField_hostE
  apply H.φ₀.injective
  change H.φ₀ (NumberField.IsCMField.complexConj H.E x) = H.φ₀ (H.conj x)
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem sig_apply (a : X.B.I.E) : X.B.I.cm.sig a = star a := rfl

theorem hE_crdOf (x y : (VS D).V) :
    hE X.B.I.cm.sig X.B.I.J (crdOf X.B.I X.ιE X.bas x) (crdOf X.B.I X.ιE X.bas y) =
      X.ιE.symm ((VS D).hT x y) := by
  have key : (VS D).hT x y = ∑ i, ∑ j, star (X.bas.repr x i) * (VS D).hT (X.bas i) (X.bas j) *
      X.bas.repr y j := by
    conv_lhs => rw [← X.bas.sum_repr x, ← X.bas.sum_repr y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
      smul_eq_mul, starRingEnd_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  apply X.ιE.injective
  rw [RingEquiv.apply_symm_apply, key]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hE, Formalism.UG.hform, crdOf, map_sum, map_mul, RingHom.coe_coe, sig_apply, X.ιE_conj,
    RingEquiv.apply_symm_apply, X.J_eq]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← host_star_conj D.R D.host]

def hv : Fin (D.R.rS + 1 + D.R.rS) → (VS D).V := Fin.append (Fin.snoc X.eX (X.zu u')) X.fY

theorem tupH_eq (a : Fin (D.R.rS + 1 + D.R.rS)) :
    tupH (frameOf X u') a = crdOf X.B.I X.ιE X.bas (hv X u' a) := by
  refine Fin.addCases (fun a => ?_) (fun b => ?_) a
  · rw [hv, Fin.append_left, tupH, Fin.append_left]
    refine Fin.lastCases ?_ (fun i => ?_) a
    · rw [F0, Fin.snoc_last, Fin.snoc_last]; rfl
    · rw [F0, Fin.snoc_castSucc, Fin.snoc_castSucc]; rfl
  · rw [hv, Fin.append_right, tupH, Fin.append_right]; rfl

theorem hT_zero_or (v : PlX X) (a b : Fin (D.R.rS + 1 + D.R.rS)) :
    (VS D).hT (hv X u' a) (hv X u' b) = 0 ∨ scl X v a * scl X v b = 1 := by
  have hs := (VS D).herm
  refine Fin.addCases (fun a => ?_) (fun a => ?_) a <;> refine Fin.addCases (fun b => ?_) (fun b => ?_) b <;>
    simp only [hv, scl, Fin.append_left, Fin.append_right]
  · refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b <;>
      simp only [Fin.snoc_last, Fin.snoc_castSucc]
    · right; rw [alp_last, one_mul]
    · left; exact (hs.eq_iff).1 (X.zu_orth u' j).1
    · left; exact (X.zu_orth u' i).1
    · left; exact X.ee i j
  · refine Fin.lastCases ?_ (fun i => ?_) a <;> simp only [Fin.snoc_last, Fin.snoc_castSucc]
    · left; exact (hs.eq_iff).1 (X.zu_orth u' b).2
    · by_cases h : i = b
      · right; subst h; exact mul_inv_cancel₀ (alp_ne_zero v _ _)
      · left; rw [X.ef, if_neg h]
  · refine Fin.lastCases ?_ (fun j => ?_) b <;> simp only [Fin.snoc_last, Fin.snoc_castSucc]
    · left; exact (X.zu_orth u' a).2
    · by_cases h : j = a
      · right; subst h; exact inv_mul_cancel₀ (alp_ne_zero v _ _)
      · left; refine (hs.eq_iff).1 ?_; rw [X.ef, if_neg h]
  · left; exact X.ff a b

theorem omVGram_holds : OmVGram X u' := by
  intro v
  funext a b
  have hY : ∀ i, yTup X u' v i = sc (E := X.B.I.E) v (scl X v i) • ratTup (Fv X.B.I.F v) (tupH (frameOf X u')) i :=
    fun i => rfl
  show hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (yTup X u' v a) (yTup X u' v b) =
    inclR (Fv X.B.I.F v) (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) a b)
  rw [hY, hY]
  unfold hR
  rw [hform_smul]
  change sigR (Fv X.B.I.F v) X.B.I.cm.sig (sc v (scl X v a)) * sc v (scl X v b) *
      hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J _ _ = _
  rw [hR_ratTup]
  simp only [sc, sigR_tmul_one, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  change _ = inclR (Fv X.B.I.F v) (hE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u') a) (tupH (frameOf X u') b))
  rcases hT_zero_or X u' v a b with h | h
  · have h0 : hE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u') a) (tupH (frameOf X u') b) = 0 := by
      rw [tupH_eq, tupH_eq, hE_crdOf, h, map_zero]
    rw [h0, map_zero, mul_zero]
  · rw [h, ← Algebra.TensorProduct.one_def, one_mul]

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVLatHolds
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory NumberField IsDedekindDomain

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem isCMExt_sig : IsCMExt X.B.I.F X.B.I.E X.B.I.cm.sig :=
  ⟨X.B.I.cm.totReal, X.B.I.cm.cmUnram.1, X.B.I.cm.deg2, fun τ x => X.B.I.cm.cmUnram.2.1 τ x⟩

theorem isHermND_J : IsHermND X.B.I.cm.sig X.B.I.J := by
  refine ⟨fun i j => ?_, X.B.I.J_det⟩
  have h := congrFun (congrFun X.B.I.J_herm i) j
  exact h

theorem omVStd_holds : OmVStd X ψ := fun h1 h2 => ⟨isCMExt_sig X, isHermND_J X, h1, h2⟩

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOf
noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def PrimT (a : ℕ) : Set (TupV (E := E) v n a) := {X | IsPrim v Λ X}

def prodEtaB (n a : ℕ) : ℝ :=
  ∏ j ∈ Finset.Icc (n - a) n, (1 - (etaV (E := E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)))

def GoodP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  StdHyp σ J ψ ∧ (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) ∧
  IsSDLoc σ J v Λ ∧ UnramAt (E := E) v ∧ a ≤ n ∧ IsPrim v Λ Y

def OrbP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∀ X ∈ PrimT v Λ a, gramR (Fv F v) σ J X = gramR (Fv F v) σ J Y →
    ∃ k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v, X = k • Y

def FibP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) →
    (∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν) → (∃ fib, IsOm σ J ψ v a fib) →
    ∀ ϖ : Fv F v, IsUnif v ϖ →
    omAt σ J ψ v (gramR (Fv F v) σ J Y) (PrimT v Λ a) =
      dX σ J ψ v a (PrimT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y)) / dT σ ψ v a (HermP v σ a ϖ)

def CountP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) → ∀ ϖ : Fv F v, IsUnif v ϖ →
    dX σ J ψ v a (PrimT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y)) =
      ENNReal.ofReal (qv v ^ (-((a : ℤ) ^ 2)) * prodEtaB (E := E) v n a) * dX σ J ψ v a (LamT v Λ a)

def PrimCos (a : ℕ) : Prop :=
  StdHyp σ J ψ → (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    IsSDLoc σ J v Λ → UnramAt (E := E) v → ∀ ϖ : Fv F v, IsUnif v ϖ →
    ∀ X ∈ PrimT v Λ a, ∀ Z ∈ lamN v Λ ϖ a 0, X + Z ∈ PrimT v Λ a

theorem smul_prim {a : ℕ} (k : HA (Fv F v) σ J) (hk : k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v)
    (Y : TupV (E := E) v n a) (hY : IsPrim v Λ Y) : IsPrim v Λ (k • Y) := by
  have hki : ∀ i, (k • Y) i =
      Matrix.mulVec ((HA.mat (Fv F v) σ J k : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) _) (Y i) :=
    fun i => rfl
  refine ⟨fun i => ?_, fun c hc => hY.2 c ?_⟩
  · rw [hki]; exact (hk (Y i)).1 (hY.1 i)
  · have e : (∑ i, c i • (k • Y) i) =
        Matrix.mulVec ((HA.mat (Fv F v) σ J k : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) _)
          (∑ i, c i • Y i) := by
      rw [Matrix.mulVec_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Matrix.mulVec_smul, hki]
    rw [e] at hc
    exact (hk _).2 hc

end Gen

section Loc

open Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

def OmVdEx : Prop := ∀ v : PlX X, StdHyp X.B.I.cm.sig X.B.I.J ψ →
  (∃ μ, SdW X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J (Fv X.B.I.F v) (psiV X.B.I.F ψ v) (D.R.rS + 1 + D.R.rS) μ) ∧
    ∃ ν, SdHerm X.B.I.F X.B.I.E X.B.I.cm.sig (Fv X.B.I.F v) (psiV X.B.I.F ψ v) (D.R.rS + 1 + D.R.rS) ν

def OmVdUniq : Prop := ∀ v : PlX X, OmUnique X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS)

def OmVdOrb : Prop := ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
  OrbP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v)

def OmVdFib : Prop := ∀ v : PlX X, FibP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v)

def OmVdCnt : Prop := ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
  CountP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v)

def OmVdSdW : Prop := ∀ v : PlX X, SdVolW X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS)

def OmVdSdH : Prop := ∀ v : PlX X, SdVolH X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS)

theorem a_le_n' : D.R.rS + 1 + D.R.rS ≤ X.B.I.n := by
  have h1 := X.n_eq
  have h2 := D.R.rS_two
  unfold Ranks.r at h1
  omega

theorem omVBadT_of (hStd : OmVStd X ψ) (hLat : OmVLat X) (hGram : OmVGram X u')
    (hEx : OmVdEx X ψ) (hUq : OmVdUniq X ψ) (hOrb : OmVdOrb X u' ψ) (hFib : OmVdFib X u' ψ)
    (hCnt : OmVdCnt X u' ψ) (hW : OmVdSdW X ψ) (hH : OmVdSdH X ψ) : OmVBadT X u' ψ := by
  intro hC hS v hv hSD hUn hP
  have hS' := hStd hC hS
  have hG : GoodP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v) :=
    ⟨hS', hLat, hSD, hUn, a_le_n' X, hP⟩
  obtain ⟨ϖ, hϖ⟩ := unifEx_holds v
  obtain ⟨hWe, hHe⟩ := hEx v hS'
  rw [← hGram v]
  set T := gramR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (yTup X u' v) with hTdef
  set ω := omAt X.B.I.cm.sig X.B.I.J ψ v T with hω
  set O := {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • yTup X u' v} with hO
  have hsub : O ⊆ PrimT v (abelian₂ X) (D.R.rS + 1 + D.R.rS) := by
    rintro Z ⟨k, hk, rfl⟩
    exact smul_prim X.B.I.cm.sig X.B.I.J v (abelian₂ X) k hk _ hP
  have hsup : PrimT v (abelian₂ X) (D.R.rS + 1 + D.R.rS) ⊆
      O ∪ {Z | gramR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J Z = T}ᶜ := by
    intro Z hZ
    by_cases hg : gramR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J Z = T
    · exact Or.inl (hOrb v hv hG Z hZ hg)
    · exact Or.inr hg
  have hEq : ω O = ω (PrimT v (abelian₂ X) (D.R.rS + 1 + D.R.rS)) := by
    apply le_antisymm (measure_mono hsub)
    calc ω (PrimT v (abelian₂ X) (D.R.rS + 1 + D.R.rS))
        ≤ ω (O ∪ {Z | gramR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J Z = T}ᶜ) := measure_mono hsup
      _ ≤ ω O + ω {Z | gramR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J Z = T}ᶜ := measure_union_le _ _
      _ = ω O := by rw [omAt_compl_zero X.B.I.cm.sig X.B.I.J ψ v T, add_zero]
  show ω O = _
  rw [hEq, hω, hFib v hG hWe hHe (hUq v hS').1 ϖ hϖ, hCnt v hv hG hWe ϖ hϖ, hW v hS' hLat hSD hUn hWe,
    hH v hS' hUn hHe ϖ hϖ]
  have hq := qv_pos v
  have hd := absV_dV_pos v
  rw [← ENNReal.ofReal_mul' (Real.rpow_nonneg hd.le _), ← ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  have e : absV v (dV v) ^ ((X.B.I.n : ℝ) * ((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) -
      ((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) ^ 2 / 2) =
      absV v (dV v) ^ ((X.B.I.n : ℝ) * ((D.R.rS + 1 + D.R.rS : ℕ) : ℝ)) /
        absV v (dV v) ^ (((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) ^ 2 / 2) := Real.rpow_sub hd _ _
  rw [e]
  unfold prodEtaB
  have : (0 : ℝ) < qv v ^ (-(((D.R.rS + 1 + D.R.rS : ℕ) : ℤ) ^ 2)) := zpow_pos hq _
  have : (0 : ℝ) < absV v (dV v) ^ (((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) ^ 2 / 2) := Real.rpow_pos_of_pos hd _
  field_simp

end Loc

end PI.OmVd
end
end
