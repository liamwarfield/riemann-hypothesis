module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSRecursion
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.LocalMassTypeOfParts
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LatBasisAllHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.StepSize
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LinearIndependentOrth

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocMassTyp
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.KUnip1Of
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.WittGen
noncomputable section

namespace PI.LocMassTypW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def cA {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} (D : SD σ v) {n m : ℕ}
    (Z : Fin m → Fin n → Fv F v ⊗[F] E) (hZ : ∀ a, IntV v (Z a)) :
    Matrix (Fin n) (Fin m) (v.adicCompletionIntegers F) :=
  Matrix.of fun i a => ⟨D.π₁ (Z a i), ((D.hO _).1 (hZ a i)).1⟩

def cB {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} (D : SD σ v) {n m : ℕ}
    (Z : Fin m → Fin n → Fv F v ⊗[F] E) (hZ : ∀ a, IntV v (Z a)) :
    Matrix (Fin n) (Fin m) (v.adicCompletionIntegers F) :=
  Matrix.of fun i a => ⟨D.π₂ (Z a i), ((D.hO _).1 (hZ a i)).2⟩

theorem witt_gen {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}
    {Λ : Set (Fin n → E)} (D : SD σ v) (Q : GL (Fin n) (Fv F v ⊗[F] E))
    (hQΛ : ∀ y, y ∈ latLoc (E := E) v Λ ↔
      ∃ x : Fin n → Fv F v ⊗[F] E, (∀ i, x i ∈ OEv (E := E) v) ∧
        y = (Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ x)
    (hQh : ∀ x y : Fin n → Fv F v ⊗[F] E,
      hR (Fv F v) σ J ((Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ x)
        ((Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ y) = ∑ i, sigR (Fv F v) σ (x i) * y i)
    (hC : WCore) {m : ℕ} (Z0 Z : Fin m → Fin n → Fv F v ⊗[F] E)
    (hZ0 : ∀ a, IntV v (Z0 a)) (hZ : ∀ a, IntV v (Z a))
    (hA0 : ∃ L : Matrix (Fin m) (Fin n) (v.adicCompletionIntegers F), L * cA D Z0 hZ0 = 1)
    (hB0 : ∃ L : Matrix (Fin m) (Fin n) (v.adicCompletionIntegers F), L * cB D Z0 hZ0 = 1)
    (hA1 : ∃ L : Matrix (Fin m) (Fin n) (v.adicCompletionIntegers F), L * cA D Z hZ = 1)
    (hB1 : ∃ L : Matrix (Fin m) (Fin n) (v.adicCompletionIntegers F), L * cB D Z hZ = 1)
    (hstd : ∀ a b, stdH σ (Z a) (Z b) = stdH σ (Z0 a) (Z0 b)) :
    ∃ k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v, ∀ a,
      (HA.mat (Fv F v) σ J k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ
          ((Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ Z0 a) =
        (Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ Z a := by
  classical
  set Qm : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := (Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) with hQm
  set Qi : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) :=
    ((Q⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) with hQi
  have hQQi : Qm * Qi = 1 := Q.mul_inv
  have hQiQ : Qi * Qm = 1 := Q.inv_mul
  have memΛ : ∀ y, y ∈ latLoc (E := E) v Λ ↔ IntV v (Qi *ᵥ y) := by
    intro y
    rw [hQΛ]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rwa [mulVec_mulVec, hQiQ, one_mulVec]
    · intro hy
      exact ⟨Qi *ᵥ y, hy, by rw [mulVec_mulVec, hQQi, one_mulVec]⟩
  set A0 := cA D Z0 hZ0 with hA0def
  set B0 := cB D Z0 hZ0 with hB0def
  set A1 := cA D Z hZ with hA1def
  set B1 := cB D Z hZ with hB1def
  have hgram : A0ᵀ * B0 = A1ᵀ * B1 := by
    refine Matrix.ext fun a b => Subtype.ext ?_
    have := congrArg D.π₂ (hstd a b)
    rw [D.snd_proj_standard_hermitian_form, D.snd_proj_standard_hermitian_form] at this
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    push_cast
    simp only [dotProduct] at this
    exact this.symm
  obtain ⟨k1, hk1u, hk1A, hk1B⟩ := hC (v.adicCompletionIntegers F) n m A0 A1 B0 B1 hA0 hA1 hB0 hB1 hgram
  have hdet : IsUnit k1.det := (Matrix.isUnit_iff_isUnit_det k1).1 hk1u
  have hki : k1 * k1⁻¹ = 1 := Matrix.mul_nonsing_inv k1 hdet
  have hik : k1⁻¹ * k1 = 1 := Matrix.nonsing_inv_mul k1 hdet
  set f := (v.adicCompletionIntegers F).subtype with hf
  have mo : ∀ {M N : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F)}, M * N = 1 →
      M.map f * N.map f = 1 := by
    intro M N hMN
    rw [← Matrix.map_mul, hMN, Matrix.map_one f (map_zero f) (map_one f)]
  have e1 : (k1⁻¹)ᵀᵀ * k1 = 1 := by rw [transpose_transpose, hik]
  have e2 : k1ᵀ * (k1⁻¹)ᵀ = 1 := by rw [← transpose_mul, hik, transpose_one]
  have e3 : (k1⁻¹)ᵀ * k1ᵀ = 1 := by rw [← transpose_mul, hki, transpose_one]
  have tm : ∀ M : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F), (M.map f)ᵀ = Mᵀ.map f :=
    fun M => (Matrix.transpose_map).symm
  set kstd := D.kS (k1.map f) ((k1⁻¹)ᵀ.map f) with hkstd
  set kstd' := D.kS (k1⁻¹.map f) (k1ᵀ.map f) with hkstd'
  have hkk : kstd * kstd' = 1 := by
    rw [hkstd, hkstd', SD.kS_mul, mo hki, mo e3, SD.kS_one]
  have hk'k : kstd' * kstd = 1 := mul_eq_one_comm.mp hkk

  have hkU : ∀ x y, stdH σ (kstd *ᵥ x) (kstd *ᵥ y) = stdH σ x y := by
    intro x y
    refine D.stdH_kS _ _ ?_ ?_ x y
    · rw [tm, mo e1]
    · rw [tm, mo e2]

  have hkI : ∀ x, IntV v (kstd *ᵥ x) ↔ IntV v x := by
    intro x
    constructor
    · intro hx
      have := D.intV_kS (k1⁻¹) k1ᵀ hx
      rwa [← hkstd', mulVec_mulVec, hk'k, one_mulVec] at this
    · intro hx
      exact D.intV_kS k1 (k1⁻¹)ᵀ hx

  have hkZ : ∀ a, kstd *ᵥ Z0 a = Z a := by
    intro a
    apply D.extV
    · intro i
      rw [hkstd, SD.fst_proj_split_matrix_mulVec]
      have := congrArg (fun M => f (M i a)) hk1A
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mul_apply, map_sum, map_mul] at this
      simp only [mulVec, dotProduct, Matrix.map_apply]
      exact this
    · intro i
      have hB : (k1⁻¹)ᵀ * B0 = B1 := by
        rw [← hk1B, ← Matrix.mul_assoc, e3, Matrix.one_mul]
      rw [hkstd, SD.snd_proj_split_matrix_mulVec]
      have := congrArg (fun M => f (M i a)) hB
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mul_apply, map_sum, map_mul] at this
      simp only [mulVec, dotProduct, Matrix.map_apply]
      exact this

  set kM := Qm * kstd * Qi with hkM
  set kMi := Qm * kstd' * Qi with hkMi
  have hkMM : kM * kMi = 1 := by
    rw [hkM, hkMi]
    calc Qm * kstd * Qi * (Qm * kstd' * Qi) = Qm * (kstd * (Qi * Qm) * kstd') * Qi := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQiQ, Matrix.mul_one, hkk, Matrix.mul_one, hQQi]
  have hkMM' : kMi * kM = 1 := mul_eq_one_comm.mp hkMM
  let kG : GL (Fin n) (Fv F v ⊗[F] E) := ⟨kM, kMi, hkMM, hkMM'⟩
  have hkx : ∀ x, kM *ᵥ x = Qm *ᵥ (kstd *ᵥ (Qi *ᵥ x)) := by
    intro x; rw [hkM, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have hmem : kG ∈ HR (Fv F v) σ J := by
    show Formalism.UG.cT (sigR (Fv F v) σ) kM * JR (Fv F v) J * kM = JR (Fv F v) J
    apply hform_ext (sigR (Fv F v) σ)
    intro x y
    rw [← hform_mulVec]
    show hR (Fv F v) σ J (kM *ᵥ x) (kM *ᵥ y) = hR (Fv F v) σ J x y
    rw [hkx, hkx, hQh, ← stdH, hkU, stdH, ← hQh, mulVec_mulVec, mulVec_mulVec, hQQi, one_mulVec,
      one_mulVec]
  let kH : HA (Fv F v) σ J := (⟨kG, hmem⟩ : HR (Fv F v) σ J)
  refine ⟨kH, ?_, ?_⟩
  · intro y
    show y ∈ latLoc (E := E) v Λ ↔ kM *ᵥ y ∈ latLoc (E := E) v Λ
    rw [memΛ, memΛ, hkx, mulVec_mulVec, hQiQ, one_mulVec, hkI]
  · intro a
    show kM *ᵥ (Qm *ᵥ Z0 a) = Qm *ᵥ Z a
    rw [hkx, show Qi *ᵥ (Qm *ᵥ Z0 a) = Z0 a by rw [mulVec_mulVec, hQiQ, one_mulVec], hkZ a]

end Gen

end PI.LocMassTypW
end
end

noncomputable section

namespace PI.LocMassTypW.WKUP

open Matrix

theorem hform_smul {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A)
    (α β : A) (x y : Fin n → A) :
    Formalism.UG.hform σ J (α • x) (β • y) = σ α * β * Formalism.UG.hform σ J x y := by
  unfold Formalism.UG.hform
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem hform_fin_sum_smul_left {A : Type} [CommRing A] {n m : ℕ} (σ : A →+* A)
    (J : Matrix (Fin n) (Fin n) A) (a : Fin m → A) (Y : Fin m → Fin n → A) (z : Fin n → A) :
    Formalism.UG.hform σ J (∑ c, a c • Y c) z = ∑ c, σ (a c) * Formalism.UG.hform σ J (Y c) z := by
  unfold Formalism.UG.hform
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul,
    Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => ?_
  ring

private theorem hform_fin_sum_smul_right {A : Type} [CommRing A] {n m : ℕ} (σ : A →+* A)
    (J : Matrix (Fin n) (Fin n) A) (x : Fin n → A) (b : Fin m → A) (Y : Fin m → Fin n → A) :
    Formalism.UG.hform σ J x (∑ d, b d • Y d) = ∑ d, b d * Formalism.UG.hform σ J x (Y d) := by
  unfold Formalism.UG.hform
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun d _ => ?_
  ring

theorem gram_gen {A : Type} [CommRing A] {n r : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A)
    (U : Matrix (Fin (r + 1)) (Fin (r + 1)) A) (Y : Fin (r + 1) → Fin n → A)
    (hU : ∀ c, U (Fin.last r) c = if c = Fin.last r then 1 else 0)
    (hY : ∀ c d, ¬ (c = Fin.last r ∧ d = Fin.last r) → Formalism.UG.hform σ J (Y c) (Y d) = 0)
    (a b : Fin (r + 1)) :
    Formalism.UG.hform σ J (∑ c, U c a • Y c) (∑ c, U c b • Y c) = Formalism.UG.hform σ J (Y a) (Y b) := by
  rw [hform_fin_sum_smul_left]
  simp_rw [hform_fin_sum_smul_right]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [Finset.sum_eq_single (Fin.last r)]
    · by_cases h : a = Fin.last r ∧ b = Fin.last r
      · obtain ⟨rfl, rfl⟩ := h
        simp [hU]
      · rw [hY a b h]
        rcases not_and_or.mp h with ha | hb
        · simp [hU, ha]
        · simp [hU, hb]
    · intro d _ hd
      rw [hY _ d (fun h => hd h.2), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro c _ hc
    rw [Finset.sum_eq_zero (fun d _ => by rw [hY c d (fun h => hc h.1), mul_zero]), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

end PI.LocMassTypW.WKUP

namespace PI.LocMassTypW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix
open scoped TensorProduct

theorem kUnip1_of (hS : SplitR) : KUnip1 := by
  classical
  intro F E _ _ _ _ _ σ n J ψ v r g P Λ T μS0 hyp u hu
  obtain ⟨hStd, hP, hSD, hUn, _hg, _hgv, _hN, hEta, hPr, hL, _, _⟩ := hyp
  obtain ⟨e, π₁, π₂, _he, _hσe, h1, h2, hπe1, hπe2, hπsc, hσ2, hσ1, hO⟩ := hS σ J ψ v hStd hUn hEta
  let D : SD σ v := ⟨e, π₁, π₂, h1, h2, hπe1, hπe2, hπsc, hσ1, hσ2, hO⟩
  obtain ⟨Q, hQΛ, hQh⟩ := PI.LocMassTypL.latStd_of hS σ J ψ v Λ hStd hSD hUn hEta hL
  set Qm : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := (Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) with hQm
  set Qi : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) :=
    ((Q⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) with hQi
  have hQQi : Qm * Qi = 1 := Q.mul_inv
  have hQiQ : Qi * Qm = 1 := Q.inv_mul
  have memΛ : ∀ y, y ∈ latLoc (E := E) v Λ ↔ IntV v (Qi *ᵥ y) := by
    intro y
    rw [hQΛ]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rwa [mulVec_mulVec, hQiQ, one_mulVec]
    · intro hy
      exact ⟨Qi *ᵥ y, hy, by rw [mulVec_mulVec, hQQi, one_mulVec]⟩
  have linQ : ∀ {m : ℕ} (c : Fin m → Fv F v ⊗[F] E) (W : Fin m → Fin n → Fv F v ⊗[F] E),
      Qi *ᵥ (∑ a, c a • W a) = ∑ a, c a • (Qi *ᵥ W a) := by
    intro m c W
    show Matrix.mulVecLin Qi (∑ a, c a • W a) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul, Matrix.mulVecLin_apply]
  have primT : ∀ W : Fin (r + 1) → Fin n → Fv F v ⊗[F] E, IsPrim v Λ W →
      ∀ c : Fin (r + 1) → Fv F v ⊗[F] E, IntV v (∑ a, c a • (Qi *ᵥ W a)) →
        ∀ a, c a ∈ OEv (E := E) v := by
    intro W hW c hc
    apply hW.2 c
    rw [memΛ, linQ]
    exact hc
  have hsc1 : ∀ a : Fin (r + 1), sc (E := E) v ((alp v r a)⁻¹ * alp v r a) = 1 := fun a => by
    rw [inv_mul_cancel₀ (alp_ne_zero v r a), sc_one]
  set Y0 := locF v (ratTup (F := F) (Fv F v) (F0 P)) with hY0
  set U : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E) :=
    Matrix.of fun a b => sc (E := E) v ((alp v r a)⁻¹ * alp v r b) * uMat v u a b with hU
  set Yu : Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun b => ∑ a, U a b • Y0 a with hYu
  set Z0 : Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun a => Qi *ᵥ Y0 a with hZ0
  set Z : Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun b => Qi *ᵥ Yu b with hZ
  have hZe : ∀ b i, Z b i = ∑ a, U a b * Z0 a i := by
    intro b i
    simp only [hZ, hYu, linQ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hZ0]
  have hUdiag : ∀ a, U a a = 1 := fun a => by
    simp [hU, uMat, hsc1]
  have hUlow : ∀ a b, b < a → U a b = 0 := fun a b hba => by
    simp only [hU, Matrix.of_apply, uMat, if_neg (ne_of_gt hba), dif_neg (not_lt_of_gt hba),
      mul_zero]
  have hUI : ∀ a b, U a b ∈ OEv (E := E) v := by
    intro a b
    rcases lt_trichotomy a b with hab | rfl | hba
    · have := hu ⟨(a, b), hab⟩
      simpa [hU, uMat, ne_of_lt hab, hab] using this
    · rw [hUdiag, D.hO]
      simp only [map_one]
      exact ⟨Subring.one_mem _, Subring.one_mem _⟩
    · rw [hUlow a b hba, D.hO]
      simp only [map_zero]
      exact ⟨Subring.zero_mem _, Subring.zero_mem _⟩
  have hZ0I : ∀ a, IntV v (Z0 a) := fun a => (memΛ _).1 (hPr.1 a)
  have hZI : ∀ b, IntV v (Z b) := by
    intro b i
    rw [hZe, D.hO]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul]
    exact ⟨Subring.sum_mem _ fun a _ => Subring.mul_mem _ ((D.hO _).1 (hUI a b)).1
        ((D.hO _).1 (hZ0I a i)).1,
      Subring.sum_mem _ fun a _ => Subring.mul_mem _ ((D.hO _).1 (hUI a b)).2
        ((D.hO _).1 (hZ0I a i)).2⟩
  have pZ0 := primT Y0 hPr
  have hA0 := saturated_split_lattice v n (r + 1) (cA D Z0 hZ0I) (fun t ht => D.sat₁ Z0 pZ0 t ht)
  have hB0 := saturated_split_lattice v n (r + 1) (cB D Z0 hZ0I) (fun t ht => D.sat₂ Z0 pZ0 t ht)

  let U1 : Matrix (Fin (r + 1)) (Fin (r + 1)) (v.adicCompletionIntegers F) :=
    Matrix.of fun a b => ⟨D.π₁ (U a b), ((D.hO _).1 (hUI a b)).1⟩
  let U2 : Matrix (Fin (r + 1)) (Fin (r + 1)) (v.adicCompletionIntegers F) :=
    Matrix.of fun a b => ⟨D.π₂ (U a b), ((D.hO _).1 (hUI a b)).2⟩
  have hdet : ∀ W : Matrix (Fin (r + 1)) (Fin (r + 1)) (v.adicCompletionIntegers F),
      (∀ a, W a a = 1) → (∀ a b, b < a → W a b = 0) → IsUnit W.det := by
    intro W hd hl
    rw [Matrix.det_of_isUpperTriangular (fun i j hij => hl i j hij)]
    rw [Finset.prod_eq_one fun i _ => hd i]
    exact isUnit_one
  have hU1 : IsUnit U1.det := hdet U1
    (fun a => Subtype.ext (by simp [U1, hUdiag a]))
    (fun a b hba => Subtype.ext (by simp [U1, hUlow a b hba]))
  have hU2 : IsUnit U2.det := hdet U2
    (fun a => Subtype.ext (by simp [U2, hUdiag a]))
    (fun a b hba => Subtype.ext (by simp [U2, hUlow a b hba]))
  have hAZ : cA D Z hZI = cA D Z0 hZ0I * U1 := by
    refine Matrix.ext fun i b => Subtype.ext ?_
    simp only [cA, U1, Matrix.of_apply, Matrix.mul_apply]
    push_cast
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hZe, map_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [map_mul, mul_comm]
  have hBZ : cB D Z hZI = cB D Z0 hZ0I * U2 := by
    refine Matrix.ext fun i b => Subtype.ext ?_
    simp only [cB, U2, Matrix.of_apply, Matrix.mul_apply]
    push_cast
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hZe, map_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [map_mul, mul_comm]
  have transfer : ∀ (M : Matrix (Fin n) (Fin (r + 1)) (v.adicCompletionIntegers F))
      (W : Matrix (Fin (r + 1)) (Fin (r + 1)) (v.adicCompletionIntegers F)), IsUnit W.det →
      (∃ L : Matrix (Fin (r + 1)) (Fin n) (v.adicCompletionIntegers F), L * M = 1) →
      ∃ L : Matrix (Fin (r + 1)) (Fin n) (v.adicCompletionIntegers F), L * (M * W) = 1 := by
    rintro M W hW ⟨L, hL⟩
    refine ⟨W⁻¹ * L, ?_⟩
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc L, hL, Matrix.one_mul, Matrix.nonsing_inv_mul _ hW]
  have hA1 : ∃ L : Matrix (Fin (r + 1)) (Fin n) (v.adicCompletionIntegers F), L * cA D Z hZI = 1 := by
    rw [hAZ]; exact transfer _ _ hU1 hA0
  have hB1 : ∃ L : Matrix (Fin (r + 1)) (Fin n) (v.adicCompletionIntegers F), L * cB D Z hZI = 1 := by
    rw [hBZ]; exact transfer _ _ hU2 hB0

  have hstdR : ∀ y y' : Fin n → Fv F v ⊗[F] E,
      stdH σ (Qi *ᵥ y) (Qi *ᵥ y') = hR (Fv F v) σ J y y' := by
    intro y y'
    rw [stdH, ← hQh, mulVec_mulVec, mulVec_mulVec, hQQi, one_mulVec, one_mulVec]
  have hlast : ∀ c, U (Fin.last r) c = if c = Fin.last r then 1 else 0 := by
    intro c
    by_cases hc : c = Fin.last r
    · rw [if_pos hc, hc, hUdiag]
    · rw [if_neg hc]
      exact hUlow _ _ (lt_of_le_of_ne (Fin.le_last c) hc)
  have hYoff : ∀ c d, ¬ (c = Fin.last r ∧ d = Fin.last r) →
      Formalism.UG.hform (sigR (Fv F v) σ) (JR (Fv F v) J) (Y0 c) (Y0 d) = 0 := by
    intro c d hcd
    show Formalism.UG.hform (sigR (Fv F v) σ) (JR (Fv F v) J)
      (sc (E := E) v (alp v r c) • ratV (F := F) (Fv F v) (F0 P c))
      (sc (E := E) v (alp v r d) • ratV (F := F) (Fv F v) (F0 P d)) = 0
    rw [WKUP.hform_smul]
    have := WGramP.hR_ratV σ J v (F0 P c) (F0 P d)
    rw [WGramP.hermitian_form_standard_frame_vanishes σ J hStd.1 hStd.2.1 P T hP c d hcd, map_zero] at this
    show _ * _ * hR (Fv F v) σ J _ _ = 0
    rw [this, mul_zero]
  have hstd : ∀ a b, stdH σ (Z a) (Z b) = stdH σ (Z0 a) (Z0 b) := by
    intro a b
    rw [hZ, hZ0]
    simp only
    rw [hstdR, hstdR]
    exact WKUP.gram_gen (sigR (Fv F v) σ) (JR (Fv F v) J) U Y0 hlast hYoff a b
  obtain ⟨k, hkK, hk⟩ := witt_gen D Q hQΛ hQh transitiveOverLocalRings Z0 Z hZ0I hZI hA0 hB0 hA1 hB1 hstd
  refine ⟨k, hkK, fun b => ?_⟩
  have hkb := hk b
  change (HA.mat (Fv F v) σ J k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ (Qm *ᵥ (Qi *ᵥ Y0 b)) =
    Qm *ᵥ (Qi *ᵥ Yu b) at hkb
  rw [mulVec_mulVec (Y0 b) Qm Qi, mulVec_mulVec (Yu b) Qm Qi, hQQi, one_mulVec, one_mulVec] at hkb
  have hY0b : Y0 b = sc (E := E) v (alp v r b) • ratV (F := F) (Fv F v) (F0 P b) := rfl
  have hYub : Yu b = sc (E := E) v (alp v r b) • ∑ a, uMat v u a b • ratV (F := F) (Fv F v) (F0 P a) := by
    simp only [hYu, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    show U a b • (sc (E := E) v (alp v r a) • ratV (F := F) (Fv F v) (F0 P a)) = _
    rw [smul_smul]
    congr 1
    simp only [hU, Matrix.of_apply]
    calc sc (E := E) v ((alp v r a)⁻¹ * alp v r b) * uMat v u a b * sc (E := E) v (alp v r a)
        = sc (E := E) v ((alp v r a)⁻¹ * alp v r a) * (sc (E := E) v (alp v r b) * uMat v u a b) := by
          rw [sc_mul, sc_mul]; ring
      _ = sc (E := E) v (alp v r b) * uMat v u a b := by rw [hsc1, one_mul]
  rw [hY0b, Matrix.mulVec_smul, hYub] at hkb
  have hinv : sc (E := E) v (alp v r b)⁻¹ * sc (E := E) v (alp v r b) = 1 := by
    rw [← sc_mul, inv_mul_cancel₀ (alp_ne_zero v r b), sc_one]
  show (HA.mat (Fv F v) σ J k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ
      ratV (F := F) (Fv F v) (F0 P b) = _
  calc (HA.mat (Fv F v) σ J k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ
        ratV (F := F) (Fv F v) (F0 P b)
      = (sc (E := E) v (alp v r b)⁻¹ * sc (E := E) v (alp v r b)) •
        ((HA.mat (Fv F v) σ J k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ
          ratV (F := F) (Fv F v) (F0 P b)) := by rw [hinv, one_smul]
    _ = _ := by rw [mul_smul, hkb, ← mul_smul, hinv, one_smul]

end PI.LocMassTypW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.RightInvariantCompact
noncomputable section

namespace PI.LocMassTypR

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol MeasureTheory NumberField IsDedekindDomain
open PI.LocMassTypW

theorem kv_mul_right_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E)) {κ c : HA (Fv F v) σ J}
    (hκ : κ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v) :
    c * κ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v ↔ c ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v :=
  by
  unfold Formalism.L2.SG.TypedSets.Kv at hκ ⊢
  simp only [Set.mem_setOf_eq, map_mul] at hκ ⊢
  exact Subgroup.mul_mem_cancel_right _ hκ

theorem right_invariant_compact : RightK := by
  intro F E _ _ _ _ _ σ n J ψ v Λ μG _ hSD _ _ hLat hH κ hκ A _
  haveI := hH
  haveI : LocallyCompactSpace (HA (Fv F v) σ J) := PI.LocMassTypM.lc_HA σ J v
  haveI : SecondCountableTopology (HA (Fv F v) σ J) := PI.LocMassTypM.sc_HA σ J v
  have hKc : IsCompact (Formalism.L2.SG.TypedSets.Kv σ J Λ v) := LocMassOrdND.isCompact_Kv σ J v Λ hSD hLat.1
  have hKo : IsOpen (Formalism.L2.SG.TypedSets.Kv σ J Λ v) := LocMassOrdND.isOpen_Kv σ J v Λ hSD hLat.1
  set e : HA (Fv F v) σ J ≃ᵐ HA (Fv F v) σ J := MeasurableEquiv.mulRight κ with he
  have hcoe : ∀ x, e x = x * κ := fun x => rfl
  set μ' : Measure (HA (Fv F v) σ J) := μG.map e with hμ'
  have hμ'app : ∀ s, μ' s = μG ((fun c => c * κ) ⁻¹' s) := fun s => by
    rw [hμ', MeasurableEquiv.map_apply]
    rfl
  haveI : μ'.IsMulLeftInvariant := by
    refine ⟨fun g => ?_⟩
    ext s hs
    rw [Measure.map_apply (measurable_const_mul g) hs, hμ'app, hμ'app]
    have hpre : (fun c => c * κ) ⁻¹' ((fun x => g * x) ⁻¹' s) =
        (fun x => g * x) ⁻¹' ((fun c => c * κ) ⁻¹' s) := by
      ext x
      simp only [Set.mem_preimage, mul_assoc]
    rw [hpre, ← Measure.map_apply (measurable_const_mul g) ((measurable_mul_const κ) hs),
      MeasureTheory.map_mul_left_eq_self μG g]
  haveI : IsFiniteMeasureOnCompacts μ' := by
    refine ⟨fun C hC => ?_⟩
    rw [hμ'app]
    have hC' : IsCompact ((fun c => c * κ) ⁻¹' C) :=
      (Homeomorph.mulRight κ).isCompact_preimage.mpr hC
    exact hC'.measure_lt_top
  have hsmul := Measure.isMulLeftInvariant_eq_smul μ' μG
  have hKpre : (fun c => c * κ) ⁻¹' (Formalism.L2.SG.TypedSets.Kv σ J Λ v) = Formalism.L2.SG.TypedSets.Kv σ J Λ v := by
    ext c
    exact kv_mul_right_iff σ J v Λ hκ
  have hm0 : μG (Formalism.L2.SG.TypedSets.Kv σ J Λ v) ≠ 0 := hKo.measure_ne_zero μG ⟨κ, hκ⟩
  have hmt : μG (Formalism.L2.SG.TypedSets.Kv σ J Λ v) ≠ ⊤ := hKc.measure_lt_top.ne
  have hc1 : ((Measure.haarScalarFactor μ' μG : NNReal) : ENNReal) = 1 := by
    have h := congrArg (fun m : Measure (HA (Fv F v) σ J) => m (Formalism.L2.SG.TypedSets.Kv σ J Λ v)) hsmul
    simp only [Measure.smul_apply, hμ'app, hKpre, ENNReal.smul_def, smul_eq_mul] at h
    have h2 : ((Measure.haarScalarFactor μ' μG : NNReal) : ENNReal) * μG (Formalism.L2.SG.TypedSets.Kv σ J Λ v) =
        1 * μG (Formalism.L2.SG.TypedSets.Kv σ J Λ v) := by rw [one_mul]; exact h.symm
    first
      | exact (ENNReal.mul_left_inj hm0 hmt).mp h2
      | exact ENNReal.mul_right_cancel hm0 hmt h2
      | exact (ENNReal.mul_eq_mul_right hm0 hmt).mp h2
  rw [← hμ'app, hsmul, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hc1, one_mul]

end PI.LocMassTypR
end
end

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain

theorem locMassTyp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (g : ℕ) (P P' : Frame E n r) (Λ : Set (Fin n → E)) : Formalism.L2.SG.LocVol.TypLocAt σ J ψ v g P P' Λ :=
  PI.LocMassTypW.local_mass_type_of_parts PI.LocMassTypR.right_invariant_compact
    (PI.LocMassTypW.kUnip1_of PI.LocMassTypS.split_reduction) σ J ψ v g P P' Λ
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ExpProductSquareInv
noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacTyp
open scoped Classical

section Count

end Count

section Real

open Real

variable (r : ℕ)

end Real

section Final

open Real

end Final

section AbsProd

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

def absVHom : Fv F v →* ℝ where
  toFun := absV v
  map_one' := absV_one v
  map_mul' := absV_mul v

theorem absV_prod {ι : Type} (s : Finset ι) (f : ι → Fv F v) :
    absV v (∏ i ∈ s, f i) = ∏ i ∈ s, absV v (f i) :=
  map_prod (absVHom v) f s

end AbsProd

end PI.UnitaryGroupMassFormula.LocJacTyp
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXSDLoc
noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol

namespace Formalism.L2.SG.Pf.MassDataX.SDL

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

def swp : E ⊗[F] Fv F v ≃ₐ[F] Fv F v ⊗[F] E := Algebra.TensorProduct.comm F E (Fv F v)

theorem swp_tmul (a : E) (c : Fv F v) : swp v (a ⊗ₜ[F] c) = c ⊗ₜ[F] a := rfl

def swVv (w : Fin n → E ⊗[F] Fv F v) : Fin n → Fv F v ⊗[F] E := fun i => swp v (w i)

theorem swVv_injective : Function.Injective (swVv (E := E) v (n := n)) := fun _ _ h =>
  funext fun i => (swp v).injective (congrFun h i)

theorem swVv_surjective : Function.Surjective (swVv (E := E) v (n := n)) := fun w =>
  ⟨fun i => (swp v).symm (w i), funext fun i => (swp v).apply_symm_apply (w i)⟩

theorem swVv_incl (x : Fin n → E) :
    swVv v (fun i => PI.SelfDualLoc.inclE (F := F) (Fv F v) (x i)) = ratV (F := F) (Fv F v) x := by
  funext i
  simp [swVv, swp, PI.SelfDualLoc.inclE, ratV, inclR, Algebra.TensorProduct.comm_tmul]

theorem sig_swap (σ : E →ₐ[F] E) (t : E ⊗[F] Fv F v) :
    sigR (Fv F v) σ (swp v t) = swp v (PI.SelfDualLoc.sigR σ (Fv F v) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x a => simp [sigR, PI.SelfDualLoc.sigR, swp, Algebra.TensorProduct.comm_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem incl_swap (e : E) : swp v (PI.SelfDualLoc.inclE (F := F) (Fv F v) e) = inclR (F := F) (Fv F v) e := by
  simp [swp, PI.SelfDualLoc.inclE, inclR, Algebra.TensorProduct.comm_tmul]

theorem hR_swap (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (z y : Fin n → E ⊗[F] Fv F v) :
    hR (Fv F v) σ J (swVv v z) (swVv v y) =
      swp v (PI.SelfDualLoc.hform (PI.SelfDualLoc.sigR σ (Fv F v)) (J.map (PI.SelfDualLoc.inclE (F := F) (Fv F v))) z y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, Formalism.UG.hform, PI.SelfDualLoc.hform, map_sum, map_mul, JR, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [swVv, sig_swap, incl_swap]

section Rings

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

abbrev Sv : Subring (E ⊗[F] Fv F v) :=
  PI.SelfDualLoc.tensInt (F := F) (Fv F v) (PI.SelfDualLoc.intOE E) (v.adicCompletionIntegers F).toSubring

theorem oev_gen (a : 𝓞 E) : inclR (F := F) (Fv F v) (a : E) ∈ OEv (E := E) v :=
  Submodule.subset_span ⟨a, trivial, rfl⟩

theorem oev_mul {s t : Fv F v ⊗[F] E} (hs : s ∈ OEv (E := E) v) (ht : t ∈ OEv (E := E) v) :
    s * t ∈ OEv (E := E) v := by
  unfold OEv at hs ht ⊢
  rw [SetLike.mem_coe] at hs ht ⊢
  induction hs using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨a, -, rfl⟩ := ha
    induction ht using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨b, -, rfl⟩ := hb
      exact Submodule.subset_span ⟨a * b, trivial, by simp [map_mul]⟩
    | zero => simp
    | add y z _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
    | smul c y _ h =>
      show _ * ((c : Fv F v) • y) ∈ _
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ c h
  | zero => simp
  | add x z _ _ h1 h2 => rw [add_mul]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h =>
    show ((c : Fv F v) • x) * t ∈ _
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ c h

theorem oev_alg (c : v.adicCompletionIntegers F) : ((c : Fv F v) ⊗ₜ[F] (1 : E)) ∈ OEv (E := E) v := by
  have h : ((c : Fv F v) ⊗ₜ[F] (1 : E)) = c • inclR (F := F) (Fv F v) ((1 : 𝓞 E) : E) := by
    simp [inclR, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
  rw [h]
  exact Submodule.smul_mem _ c (oev_gen v 1)

theorem swp_mem_oev {s : E ⊗[F] Fv F v} (hs : s ∈ Sv (E := E) v) : swp v s ∈ OEv (E := E) v := by
  induction hs using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨a, ⟨b, rfl⟩⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩
    · exact oev_gen v b
    · exact oev_alg v ⟨c, hc⟩
  | zero => rw [map_zero]; exact zero_mem (Submodule.span _ _)
  | one => rw [map_one]; simpa using oev_gen v (E := E) 1
  | add x y _ _ hx hy => rw [map_add]; exact add_mem (S := Submodule _ _) hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem (S := Submodule _ _) hx
  | mul x y _ _ hx hy => rw [map_mul]; exact oev_mul v hx hy

theorem oev_swp {t : Fv F v ⊗[F] E} (ht : t ∈ OEv (E := E) v) : ∃ s ∈ Sv (E := E) v, swp v s = t := by
  unfold OEv at ht
  rw [SetLike.mem_coe] at ht
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, -, rfl⟩ := hx
    refine ⟨(a : E) ⊗ₜ[F] (1 : Fv F v), Subring.subset_closure (Or.inl ⟨⟨(a : E), ⟨a, rfl⟩⟩, rfl⟩), ?_⟩
    rfl
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨s', hs', rfl⟩ := hy
    exact ⟨s + s', add_mem hs hs', map_add _ _ _⟩
  | smul c x _ hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    refine ⟨((1 : E) ⊗ₜ[F] (c : Fv F v)) * s,
      mul_mem (Subring.subset_closure (Or.inr ⟨c, rfl⟩)) hs, ?_⟩
    rw [map_mul, swp_tmul, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
    rfl

end Rings

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (Lb : Submodule (𝓞 E) (Fin n → E))

theorem oev_smul_lat {t : Fv F v ⊗[F] E} (ht : t ∈ OEv (E := E) v) {w : Fin n → Fv F v ⊗[F] E}
    (hw : w ∈ latLoc v (Lb : Set (Fin n → E))) : (fun i => t * w i) ∈ latLoc v (Lb : Set (Fin n → E)) := by
  unfold OEv at ht
  rw [SetLike.mem_coe] at ht
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, -, rfl⟩ := hx
    induction hw using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      refine Submodule.subset_span ⟨a • x, Lb.smul_mem a hx, ?_⟩
      funext i
      simp [ratV, map_mul, Pi.smul_apply, Algebra.smul_def]
    | zero =>
      convert zero_mem (latLoc v (Lb : Set (Fin n → E))) using 1
      funext i; simp
    | add y z _ _ hy hz =>
      have e : (fun i => inclR (F := F) (Fv F v) (a : E) * (y + z) i) =
          (fun i => inclR (F := F) (Fv F v) (a : E) * y i) + (fun i => inclR (F := F) (Fv F v) (a : E) * z i) := by
        funext i; simp [mul_add]
      rw [e]; exact add_mem hy hz
    | smul c y _ hy =>
      have e : (fun i => inclR (F := F) (Fv F v) (a : E) * (c • y) i) =
          c • (fun i => inclR (F := F) (Fv F v) (a : E) * y i) := by
        funext i; simp [mul_smul_comm]
      rw [e]; exact Submodule.smul_mem _ c hy
  | zero =>
    convert zero_mem (latLoc v (Lb : Set (Fin n → E))) using 1
    funext i; simp
  | add x y _ _ hx hy =>
    have e : (fun i => (x + y) * w i) = (fun i => x * w i) + (fun i => y * w i) := by funext i; simp [add_mul]
    rw [e]; exact add_mem hx hy
  | smul c x _ hx =>
    have e : (fun i => (c • x) * w i) = c • (fun i => x * w i) := by funext i; simp [smul_mul_assoc]
    rw [e]; exact Submodule.smul_mem _ c hx

theorem swVv_mem_latLoc {z : Fin n → E ⊗[F] Fv F v}
    (hz : z ∈ PI.SelfDualLoc.latS (F := F) (Fv F v) (Sv (E := E) v) Lb) :
    swVv v z ∈ latLoc v (Lb : Set (Fin n → E)) := by
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    rw [swVv_incl]
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero =>
    have : swVv v (0 : Fin n → E ⊗[F] Fv F v) = 0 := by funext i; simp [swVv]
    rw [this]; exact zero_mem _
  | add x y _ _ hx hy =>
    have : swVv v (x + y) = swVv v x + swVv v y := by funext i; simp [swVv]
    rw [this]; exact add_mem hx hy
  | smul s x _ hx =>
    have : swVv v (s • x) = fun i => swp v (s : E ⊗[F] Fv F v) * swVv v x i := by
      funext i; simp [swVv, Submodule.coe_smul_of_tower, Subring.smul_def, smul_eq_mul, map_mul]
    rw [this]
    exact oev_smul_lat v Lb (swp_mem_oev v s.2) hx

theorem latLoc_swVv {w : Fin n → Fv F v ⊗[F] E} (hw : w ∈ latLoc v (Lb : Set (Fin n → E))) :
    ∃ z ∈ PI.SelfDualLoc.latS (F := F) (Fv F v) (Sv (E := E) v) Lb, swVv v z = w := by
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨_, Submodule.subset_span ⟨x, hx, rfl⟩, swVv_incl v x⟩
  | zero => exact ⟨0, zero_mem _, by funext i; simp [swVv]⟩
  | add x y _ _ hx hy =>
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨z', hz', rfl⟩ := hy
    exact ⟨z + z', add_mem hz hz', by funext i; simp [swVv]⟩
  | smul c x _ hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    have hc : ((1 : E) ⊗ₜ[F] (c : Fv F v)) ∈ Sv (E := E) v := Subring.subset_closure (Or.inr ⟨c, rfl⟩)
    refine ⟨(⟨_, hc⟩ : Sv (E := E) v) • z, Submodule.smul_mem _ _ hz, ?_⟩
    funext i
    simp only [swVv, Pi.smul_apply]
    rw [Subring.smul_def, smul_eq_mul, map_mul, swp_tmul, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
    rfl

theorem isSDLoc_of (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (hfg : Lb.FG)
    (hint : ∀ x ∈ Lb, ∀ y ∈ Lb, PI.SelfDualLoc.hform (σ : E →+* E) J x y ∈ PI.SelfDualLoc.intOE E)
    (hdual : ∀ y : Fin n → E, (∀ x ∈ Lb, PI.SelfDualLoc.hform (σ : E →+* E) J x y ∈ PI.SelfDualLoc.intOE E) → y ∈ Lb) :
    IsSDLoc σ J v (Lb : Set (Fin n → E)) := by
  have hT : ((1 : ℕ) : 𝓞 F) ∉ v.asIdeal := by
    rw [Nat.cast_one]; exact fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have key := self_dual_local F E n σ J v Lb 1 (Module.Finite.iff_fg.2 hfg) hint
    (fun y hy => by simpa using hdual y hy) hT
  intro y'
  obtain ⟨y, rfl⟩ := swVv_surjective (E := E) v y'
  have hlat : swVv v y ∈ latLoc v (Lb : Set (Fin n → E)) ↔
      y ∈ PI.SelfDualLoc.latS (F := F) (Fv F v) (Sv (E := E) v) Lb := by
    constructor
    · intro h
      obtain ⟨z, hz, e⟩ := latLoc_swVv v Lb h
      rwa [← swVv_injective v e]
    · exact swVv_mem_latLoc v Lb
  rw [hlat, key]
  constructor
  · intro h x' hx'
    obtain ⟨z, hz, rfl⟩ := latLoc_swVv v Lb hx'
    rw [hR_swap]
    exact swp_mem_oev v (h z hz)
  · intro h z hz
    have h1 := h (swVv v z) (swVv_mem_latLoc v Lb hz)
    rw [hR_swap] at h1
    obtain ⟨s, hs, e⟩ := oev_swp v h1
    rwa [← (swp v).injective e]

end Lat

theorem sdLocX_holds {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (v : PlX X) :
    IsSDLoc X.B.I.cm.sig X.B.I.J v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
  isSDLoc_of v X.B.I.L X.B.I.cm.sig X.B.I.J X.B.I.L_fg
    (fun x hx y hy => (X.B.I.L_dual y).1 hy x hx) (fun y h => (X.B.I.L_dual y).2 h)

end Formalism.L2.SG.Pf.MassDataX.SDL
end
end

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Classical
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets Formalism.L2.SG.LocVol

namespace Formalism.L2.SG.Pf.MassDataX

def SDLocX : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (v : PlX X), IsSDLoc X.B.I.cm.sig X.B.I.J v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))

def UnramTypX : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (v : PlX X), TypAt X v → UnramAt (E := X.B.I.E) v

def STypIdx : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X), X.MeasTie hb →
    ((X.measW u).μSv p.1).IsHaarMeasure →
    ((X.measW u).μSv p.1 (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1)).toReal =
      ((glkC D.R.k (gOf p) : ℕ) : ℝ) / ((ukC D.R.k (gOf p) : ℕ) : ℝ) *
        ((X.measW u).μSv p.1 (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1)).toReal

theorem gAt_mem {D : D7} (X : HidaSetting D) (p : TypX X) : ((gAt X p.1 : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
  obtain ⟨p, hp⟩ := p
  have hT : IsTyped X.B.I.F (D.host.g 0) (D.host.g 1) p := by
    unfold typSet at hp
    split_ifs at hp with hfin
    · simpa using hp
    · simp at hp
  unfold gAt
  split_ifs with h0
  · exact h0
  · unfold IsTyped at hT
    exact hT.resolve_left h0

section Main

open Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.MassDataConc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem inTypedC_loc (hSD : SDLocX) (hUn : UnramTypX) (hI : STypIdx) (hψ : IsCharAF X.B.I.F ψ) (hψs : IsStdChar ψ) :
    InTypedC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by
  intro hX _hP hL hL' hTF p
  have : Submodule.IsFullLattice X.B.I.E X.B.I.L :=
    { toIsLattice := Submodule.IsLattice.of_fg X.B.I.E X.B.I.L_fg
      span_eq_top := X.B.I.L_span }
  have hTyp : TypAt X p.1 := p.2
  refine ⟨?_, hI X hb u p hX.1 (hL p.1).2.1, hI X hb u' p hX.1 (hL' p.1).2.1⟩
  have h := locMassTyp X.B.I.cm.sig X.B.I.J ψ p.1 (gAt X p.1) (frameOf X u) (frameOf X u')
    (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))
    ⟨MassDataVolumesW.stepCM X, MassDataVolumesW.stepHerm X, hψ, hψs⟩ _ _
    (MassDataLevelSSteps.FrameW.frameOf_isStd X u) (MassDataLevelSSteps.FrameW.frameOf_isStd X u')
    (hSD X p.1) (hUn X p.1 hTyp) ⟨X.B.I.L, inferInstance, rfl⟩
    (hTF p).1 (gAt_mem X p) (hTF p).2.1 (hTF p).2.2.1 (hTF p).2.2.2.2
    _ (hL p.1).1 _ (hL p.1).2.1 (hL p.1).2.2.1 _ (hL' p.1).2.1 (hL' p.1).2.2.1 (hL p.1).2.2.2 (hL' p.1).2.2.2
  show MX X u u' ψ p.1 / localVolumeUnit X ψ p.1 = _
  unfold MX localVolumeUnit OmX
  rw [if_pos hTyp, if_pos hTyp]
  exact h

theorem typedAll_of (hSD : SDLocX) (hUn : UnramTypX) (hI : STypIdx) : Formalism.L2.SG.PoincareAmplitudeLowerBounds.TypedAll := by
  intro D T u u' X0 sd C Th Q i0 i0' νq
  exact inTypedC_loc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hSD hUn hI T.ψ_char T.ψ_std

theorem typedAll_of_idx (hI : STypIdx) : Formalism.L2.SG.PoincareAmplitudeLowerBounds.TypedAll :=
  typedAll_of (fun X v => Formalism.L2.SG.Pf.MassDataX.SDL.sdLocX_holds X v)
    (fun X v _ => Formalism.L2.SG.Pf.NcX.OmVSt.unramAt_of_cm X.B.I.cm v) hI

end Main

end Formalism.L2.SG.Pf.MassDataX
