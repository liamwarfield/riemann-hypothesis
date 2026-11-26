module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FrameVectorMemBaseLattice

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.GramAugT
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.QuadRoot
noncomputable section

open Polynomial IsLocalRing

namespace PI.OmVf

theorem quad_root {R : Type*} [CommRing R] [HenselianLocalRing R] (A B K : R) (hA : A ∈ maximalIdeal R)
    (hB : IsUnit B) : ∃ s : R, A * s ^ 2 + B * s + K = 0 := by
  obtain ⟨u, hu⟩ := hB.exists_right_inv
  have haK : A * u * u * K ∈ maximalIdeal R := by
    have h1 : A * u * u * K = A * (u * u * K) := by ring
    rw [h1]; exact Ideal.mul_mem_right _ _ hA
  obtain ⟨w, hwr, hwm⟩ := HenselianLocalRing.is_henselian
    (X ^ 2 + X + Polynomial.C (A * u * u * K)) (by monicity!) 0
    (by simpa using haK) (by simp)
  have hw : w ^ 2 + w + A * u * u * K = 0 := by simpa using hwr
  have hwm' : w ∈ maximalIdeal R := by simpa using hwm
  have hunit : IsUnit (1 + w) := by
    by_contra hn
    have h1 : 1 + w ∈ maximalIdeal R := (mem_maximalIdeal _).mpr hn
    have h2 : (1 : R) ∈ maximalIdeal R := by
      have e : (1 : R) = (1 + w) - w := by ring
      rw [e]; exact Ideal.sub_mem _ h1 hwm'
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h2)
  obtain ⟨v, hv⟩ := hunit.exists_right_inv
  refine ⟨-(u * K * v), ?_⟩
  linear_combination K * v ^ 2 * hw - K * (2 - v + ((1 + w) * v - 1)) * hv - K * v * hu

end PI.OmVf
end
end

noncomputable section

namespace PI.OmVf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.OmVd IsLocalRing
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def bordM {a : ℕ} (G : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) (z : Fin a) :
    Matrix (Fin (a + 1)) (Fin (a + 1)) (Fv F v ⊗[F] E) :=
  Fin.snoc (α := fun _ => Fin (a + 1) → Fv F v ⊗[F] E)
    (fun i => Fin.snoc (α := fun _ => Fv F v ⊗[F] E) (G i) (if i = z then 1 else 0))
    (Fin.snoc (α := fun _ => Fv F v ⊗[F] E) (fun j => if j = z then 1 else 0) 0)

theorem hAddR (x y y' : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (y + y') = hR (Fv F v) σ J x y + hR (Fv F v) σ J x y' := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hSmulR (c : Fv F v ⊗[F] E) (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (c • y) = c * hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hAddL (x x' y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (x + x') y = hR (Fv F v) σ J x y + hR (Fv F v) σ J x' y := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hSmulL (c : Fv F v ⊗[F] E) (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (c • x) y = sigR (Fv F v) σ c * hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem gram_augT {a : ℕ} (X : TupV (E := E) v n a) (w : Fin n → Fv F v ⊗[F] E) (z : Fin a)
    (h1 : ∀ i, hR (Fv F v) σ J (X i) w = if i = z then 1 else 0)
    (h2 : ∀ i, hR (Fv F v) σ J w (X i) = if i = z then 1 else 0) (h3 : hR (Fv F v) σ J w w = 0) :
    gramR (Fv F v) σ J (augT v X w) = bordM v (gramR (Fv F v) σ J X) z := by
  funext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [gramR, augT, bordM, h3]
    | cast j => simp [gramR, augT, bordM, h2]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [gramR, augT, bordM, h1]
    | cast j => simp [gramR, augT, bordM]

end PI.OmVf
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.ExtPHolds
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.LeftInvResHolds
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.LeftInvResGen
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.LeftInvOOf
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOfIsoWX
noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVBadT_of_isoW (hStd : OmVStd X ψ) (hLat : OmVLat X) (hGram : OmVGram X u')
    (hIso : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      IsoW X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hLI : ∀ v : PlX X, LeftInvO X.B.I.cm.sig X.B.I.J ψ v (n := X.B.I.n) (D.R.rS + 1 + D.R.rS))
    (hRed : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      RedP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hFI : FFInertB) (hFS : FFSplitB) :
    OmVBadT X u' ψ :=
  omVBadT_of_iso X u' ψ hStd hLat hGram (fun v hv => isoExt_of _ _ _ _ _ _ _ (hIso v hv)) hLI hRed hFI hFS

end PI.OmVd
end
end

noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
  Topology Filter
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def LeftInvRes (a : ℕ) : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ∀ ϖ : Fv F v, IsUnif v ϖ →
  ∀ M : Matrix (Fin n) (Fin a) (Fv F v ⊗[F] E), (∀ k i, M k i ∈ OEv (E := E) v) →
    (∀ c : Fin a → Fv F v ⊗[F] E, (∀ k, Matrix.mulVec M c k ∈ OEv (E := E) v) → ∀ i, c i ∈ OEv (E := E) v) →
    ∃ N0 : Matrix (Fin a) (Fin n) (Fv F v ⊗[F] E), ∃ B : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E),
      (∀ i k, N0 i k ∈ OEv (E := E) v) ∧ (∀ i j, B i j ∈ OEv (E := E) v) ∧
      N0 * M = 1 + sc (E := E) v ϖ • B

theorem near_mulVec {a : ℕ} (ϖ : Fv F v) (B : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) (x : Fin a → Fv F v ⊗[F] E)
    (i : Fin a) :
    Matrix.mulVec (1 + sc (E := E) v ϖ • B) x i = x i + sc (E := E) v ϖ * ∑ j, B i j * x j := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rfl

theorem leftInvO_of (a : ℕ) (hR : LeftInvRes σ J ψ v (n := n) a) : LeftInvO σ J ψ v (n := n) a := by
  intro hS hUn M hM hsat
  obtain ⟨ϖ, hϖ⟩ := unifEx_holds v
  obtain ⟨h0, hπ, -⟩ := unif_spec v ϖ hϖ
  obtain ⟨N0, B, hN0, hB, hNB⟩ := hR hS hUn ϖ hϖ M hM hsat
  set C : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := 1 + sc (E := E) v ϖ • B with hCdef

  have hker : ∀ d : Fin a → Fv F v ⊗[F] E, Matrix.mulVec C d = 0 → d = 0 := by
    intro d hd
    funext i
    have hm : ∀ m : ℕ, sc (E := E) v (ϖ ^ m)⁻¹ * d i ∈ OEv (E := E) v := by
      intro m
      refine near_int v ϖ hϖ B hB (fun j => sc (E := E) v (ϖ ^ m)⁻¹ * d j) (fun j => ?_) i
      have := near_mulVec v ϖ B (sc (E := E) v (ϖ ^ m)⁻¹ • d) j
      rw [Matrix.mulVec_smul, ← hCdef, hd, smul_zero] at this
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      rw [← this]
      exact oEv_zero v
    by_contra hne
    have hN : {x : Fv F v ⊗[F] E | x ≠ d i} ∈ 𝓝 (0 : Fv F v ⊗[F] E) := isOpen_ne.mem_nhds (Ne.symm hne)
    obtain ⟨k, hk⟩ := PI.VolStabSW.eventually_smul_sub (OEv (E := E) v) (isCompact_oEv v) (fun k => ϖ ^ k) hπ _ hN
    apply hk _ (hm k)
    show ϖ ^ k • (sc (E := E) v (ϖ ^ k)⁻¹ * d i) = d i
    rw [smul_eq_sc, ← mul_assoc, sc_mul, mul_inv_cancel₀ (pow_ne_zero _ h0), sc_one, one_mul]
  have hinj : Function.Injective (Matrix.mulVecLin C) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    exact fun d hd => hker d hd
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hsurj : Function.Surjective (Matrix.mulVecLin C) := by
    have hinj' : Function.Injective ((Matrix.mulVecLin C).restrictScalars (Fv F v)) := hinj
    exact (LinearMap.injective_iff_surjective (f := (Matrix.mulVecLin C).restrictScalars (Fv F v))).1 hinj'
  have hCu : IsUnit C := Matrix.mulVec_surjective_iff_isUnit.1 hsurj
  have hCd : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).1 hCu

  have hCi : ∀ i j, C⁻¹ i j ∈ OEv (E := E) v := by
    intro i j
    have hcol : ∀ l, (fun k => C⁻¹ k j) l + sc (E := E) v ϖ * ∑ k, B l k * (fun k => C⁻¹ k j) k ∈ OEv (E := E) v := by
      intro l
      rw [← near_mulVec v ϖ B (fun k => C⁻¹ k j) l, ← hCdef]
      have e : Matrix.mulVec C (fun k => C⁻¹ k j) l = (C * C⁻¹) l j := by
        simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
      rw [e, Matrix.mul_nonsing_inv C hCd, Matrix.one_apply]
      split_ifs
      · exact one_mem_O v
      · exact oEv_zero v
    exact near_int v ϖ hϖ B hB _ hcol i
  refine ⟨C⁻¹ * N0, fun i k => ?_, ?_⟩
  · rw [Matrix.mul_apply]
    exact oEv_sum v _ _ fun l _ => oEv_mul v (hCi i l) (hN0 l k)
  · rw [Matrix.mul_assoc, hNB, Matrix.nonsing_inv_mul C hCd]

end PI.OmVd
end
end

noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

theorem leftInvRes_gen {a : ℕ} {K : Type} [CommRing K] (ϖ : Fv F v) (hϖ : IsUnif v ϖ)
    (π : Red.OR (E := E) v →+* K) (hsurj : Function.Surjective π)
    (hker : ∀ x : Red.OR (E := E) v, π x = 0 ↔ (x : Fv F v ⊗[F] E) ∈ PO (E := E) v ϖ)
    (hLK : ∀ Mb : Matrix (Fin n) (Fin a) K, Function.Injective Mb.mulVec →
      ∃ Nb : Matrix (Fin a) (Fin n) K, Nb * Mb = 1)
    (M : Matrix (Fin n) (Fin a) (Fv F v ⊗[F] E)) (hM : ∀ k i, M k i ∈ OEv (E := E) v)
    (hsat : ∀ c : Fin a → Fv F v ⊗[F] E, (∀ k, Matrix.mulVec M c k ∈ OEv (E := E) v) → ∀ i, c i ∈ OEv (E := E) v) :
    ∃ N0 : Matrix (Fin a) (Fin n) (Fv F v ⊗[F] E), ∃ B : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E),
      (∀ i k, N0 i k ∈ OEv (E := E) v) ∧ (∀ i j, B i j ∈ OEv (E := E) v) ∧
      N0 * M = 1 + sc (E := E) v ϖ • B := by
  classical
  obtain ⟨h0, -, hint⟩ := unif_spec v ϖ hϖ
  set Mo : Matrix (Fin n) (Fin a) (Red.OR (E := E) v) := fun k i => ⟨M k i, hM k i⟩ with hMo
  have hcoe : (Red.OR (E := E) v).subtype = (Red.OR (E := E) v).subtype := rfl

  have hinj : Function.Injective (Mo.map π).mulVec := by
    intro x y hxy
    have hz : (Mo.map π).mulVec (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    obtain ⟨cO, hcO⟩ : ∃ cO : Fin a → Red.OR (E := E) v, ∀ i, π (cO i) = (x - y) i :=
      ⟨fun i => (hsurj ((x - y) i)).choose, fun i => (hsurj ((x - y) i)).choose_spec⟩
    have hred : ∀ k, π ((Mo.mulVec cO) k) = 0 := by
      intro k
      rw [RingHom.map_mulVec]
      have : (π ∘ cO) = x - y := funext hcO
      rw [this, hz]
      rfl
    have hPO : ∀ k, ∃ m ∈ OEv (E := E) v, ((Mo.mulVec cO k : Red.OR (E := E) v) : Fv F v ⊗[F] E) =
        sc (E := E) v ϖ * m := fun k => (hker _).1 (hred k)
    choose m hmO hm using hPO
    have hc : ∀ i, sc (E := E) v ϖ⁻¹ * (cO i : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
      refine hsat _ fun k => ?_
      have e : Matrix.mulVec M (fun i => sc (E := E) v ϖ⁻¹ * (cO i : Fv F v ⊗[F] E)) k =
          sc (E := E) v ϖ⁻¹ * ((Mo.mulVec cO k : Red.OR (E := E) v) : Fv F v ⊗[F] E) := by
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
        rw [show ((∑ i, Mo k i * cO i : Red.OR (E := E) v) : Fv F v ⊗[F] E) =
            ∑ i, ((Mo k i : Fv F v ⊗[F] E) * (cO i : Fv F v ⊗[F] E)) by push_cast; rfl]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [e, hm k, ← mul_assoc, sc_mul, inv_mul_cancel₀ h0, sc_one, one_mul]
      exact hmO k
    funext i
    have : π (cO i) = 0 := by
      rw [hker]
      refine ⟨sc (E := E) v ϖ⁻¹ * (cO i : Fv F v ⊗[F] E), hc i, ?_⟩
      rw [← mul_assoc, sc_mul, mul_inv_cancel₀ h0, sc_one, one_mul]
    rw [← sub_eq_zero, ← Pi.sub_apply, ← hcO i, this]
  obtain ⟨Nb, hNb⟩ := hLK _ hinj
  obtain ⟨NO, hNO⟩ : ∃ NO : Matrix (Fin a) (Fin n) (Red.OR (E := E) v), ∀ i k, π (NO i k) = Nb i k :=
    ⟨fun i k => (hsurj (Nb i k)).choose, fun i k => (hsurj (Nb i k)).choose_spec⟩
  have hmap : (NO * Mo).map π = 1 := by
    rw [Matrix.map_mul]
    have : NO.map π = Nb := by ext i k; exact hNO i k
    rw [this, hNb]
  set P : Matrix (Fin a) (Fin a) (Red.OR (E := E) v) := NO * Mo with hP
  have hPO : ∀ i j, ∃ b ∈ OEv (E := E) v, (((P - 1 : Matrix (Fin a) (Fin a) (Red.OR (E := E) v)) i j :
      Red.OR (E := E) v) : Fv F v ⊗[F] E) = sc (E := E) v ϖ * b := by
    intro i j
    refine (hker _).1 ?_
    have := congrFun (congrFun hmap i) j
    simp only [Matrix.map_apply] at this
    rw [Matrix.sub_apply, map_sub, this]
    simp [Matrix.one_apply]
  choose B hBO hB using hPO
  refine ⟨NO.map (Red.OR (E := E) v).subtype, fun i j => B i j, fun i k => (NO i k).2, hBO, ?_⟩
  have hM' : M = Mo.map (Red.OR (E := E) v).subtype := by ext k i; rfl
  rw [hM', ← Matrix.map_mul, ← hP]
  ext i j
  have h1 := hB i j
  rw [Matrix.sub_apply] at h1
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have e1 : (Red.OR (E := E) v).subtype (P i j) =
      (((P i j - (1 : Matrix (Fin a) (Fin a) (Red.OR (E := E) v)) i j : Red.OR (E := E) v) : Fv F v ⊗[F] E) +
        (((1 : Matrix (Fin a) (Fin a) (Red.OR (E := E) v)) i j : Red.OR (E := E) v) : Fv F v ⊗[F] E)) := by
    show (P i j : Fv F v ⊗[F] E) = _
    push_cast; ring
  rw [e1, h1, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp [add_comm] <;> rfl

end PI.OmVd
end
end

noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open scoped TensorProduct

theorem linv_field {K : Type} [Field K] {n a : ℕ} (Mb : Matrix (Fin n) (Fin a) K)
    (h : Function.Injective Mb.mulVec) : ∃ Nb : Matrix (Fin a) (Fin n) K, Nb * Mb = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.mulVecLin Mb) (LinearMap.ker_eq_bot.2 h)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have : LinearMap.toMatrix' g * LinearMap.toMatrix' (Matrix.mulVecLin Mb) = 1 := by
    rw [← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  have hMb : LinearMap.toMatrix' (Matrix.mulVecLin Mb) = Mb := by
    rw [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
  rwa [hMb] at this

theorem linv_prod {k : Type} [Field k] {n a : ℕ} (Mb : Matrix (Fin n) (Fin a) (k × k))
    (h : Function.Injective Mb.mulVec) : ∃ Nb : Matrix (Fin a) (Fin n) (k × k), Nb * Mb = 1 := by
  have hfst : ∀ c : Fin a → k × k, ∀ r, ((Mb.mulVec c) r).1 = ((Mb.map (RingHom.fst k k)).mulVec (fun i => (c i).1)) r :=
    fun c r => RingHom.map_mulVec (RingHom.fst k k) Mb c r
  have hsnd : ∀ c : Fin a → k × k, ∀ r, ((Mb.mulVec c) r).2 = ((Mb.map (RingHom.snd k k)).mulVec (fun i => (c i).2)) r :=
    fun c r => RingHom.map_mulVec (RingHom.snd k k) Mb c r
  have h1 : Function.Injective (Mb.map (RingHom.fst k k)).mulVec := by
    intro x y hxy
    have : Mb.mulVec (fun i => (x i, 0)) = Mb.mulVec (fun i => (y i, 0)) := by
      funext r
      refine Prod.ext ?_ ?_
      · rw [hfst, hfst]; exact congrFun hxy r
      · rw [hsnd, hsnd]
    have := h this
    funext i
    exact congrArg Prod.fst (congrFun this i)
  have h2 : Function.Injective (Mb.map (RingHom.snd k k)).mulVec := by
    intro x y hxy
    have : Mb.mulVec (fun i => (0, x i)) = Mb.mulVec (fun i => (0, y i)) := by
      funext r
      refine Prod.ext ?_ ?_
      · rw [hfst, hfst]
      · rw [hsnd, hsnd]; exact congrFun hxy r
    have := h this
    funext i
    exact congrArg Prod.snd (congrFun this i)
  obtain ⟨N1, hN1⟩ := linv_field _ h1
  obtain ⟨N2, hN2⟩ := linv_field _ h2
  set Nb : Matrix (Fin a) (Fin n) (k × k) := Matrix.of fun i r => (N1 i r, N2 i r) with hNbd
  refine ⟨Nb, ?_⟩
  have e1 : (Nb * Mb).map (RingHom.fst k k) = 1 := by
    rw [Matrix.map_mul]
    have : Nb.map (RingHom.fst k k) = N1 := by ext i r; rfl
    rw [this]; exact hN1
  have e2 : (Nb * Mb).map (RingHom.snd k k) = 1 := by
    rw [Matrix.map_mul]
    have : Nb.map (RingHom.snd k k) = N2 := by ext i r; rfl
    rw [this]; exact hN2
  ext i j
  · have := congrFun (congrFun e1 i) j
    simp only [Matrix.map_apply, RingHom.coe_fst] at this
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> rfl
  · have := congrFun (congrFun e2 i) j
    simp only [Matrix.map_apply, RingHom.coe_snd] at this
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> rfl

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

theorem leftInvRes_holds (a : ℕ) : LeftInvRes σ J ψ v (n := n) a := by
  intro hS hUn ϖ hϖ M hM hsat
  have hR : Red.ResAlg σ J ψ v := Red.resAlg_of_sp σ J ψ v (Red.etaSp_holds σ J ψ v)
  obtain ⟨k, _, _, -, h⟩ := hR hS hUn ϖ hϖ
  rcases h with ⟨-, K, _, _, σ', π, -, -, -, hres⟩ | ⟨-, π, hres⟩
  · exact leftInvRes_gen v ϖ hϖ π hres.1 hres.2.1 (fun Mb h => linv_field Mb h) M hM hsat
  · exact leftInvRes_gen v ϖ hϖ π hres.1 hres.2.1 (fun Mb h => linv_prod Mb h) M hM hsat

theorem leftInvO_holds (a : ℕ) : LeftInvO σ J ψ v (n := n) a :=
  leftInvO_of σ J ψ v a (leftInvRes_holds σ J ψ v a)

end Gen

section Loc

open Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVBadT_of_last (hStd : OmVStd X ψ) (hLat : OmVLat X) (hGram : OmVGram X u')
    (hIso : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      IsoW X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hRed : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      RedP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hFI : FFInertB) (hFS : FFSplitB) :
    OmVBadT X u' ψ :=
  omVBadT_of_isoW X u' ψ hStd hLat hGram hIso (fun v => leftInvO_holds _ _ _ v _) hRed hFI hFS

theorem omVBadT_of_lastX (hStd : Formalism.L2.SG.Pf.NcX.OmVSt.OmVStd X ψ) (hLat : Formalism.L2.SG.Pf.NcX.OmVSt.OmVLat X)
    (hGram : Formalism.L2.SG.Pf.NcX.OmVSt.OmVGram X u')
    (hIso : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      IsoW X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hRed : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      RedP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hFI : FFInertB) (hFS : FFSplitB) :
    Formalism.L2.SG.Pf.NcX.OmVSt.OmVBadT X u' ψ :=
  omVBadT_of_last X u' ψ hStd hLat hGram hIso hRed hFI hFS

end Loc

end PI.OmVd
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.IsoWGen
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Root
noncomputable section

namespace PI.OmVf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.OmVd IsLocalRing
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem exists_integral_root_of_quadratic (β γ ν : Fv F v) (hβ : β ∈ v.adicCompletionIntegers F) (hγ : γ ∈ v.adicCompletionIntegers F)
    (hγm : Valued.v γ < 1) (hν : ν ∈ v.adicCompletionIntegers F) :
    ∃ s ∈ v.adicCompletionIntegers F, β + (1 - γ * β) * s - γ * (1 - γ * β) * ν * s ^ 2 = 0 := by
  set b : v.adicCompletionIntegers F := ⟨β, hβ⟩
  set g : v.adicCompletionIntegers F := ⟨γ, hγ⟩
  set m : v.adicCompletionIntegers F := ⟨ν, hν⟩
  have hg : g ∈ maximalIdeal (v.adicCompletionIntegers F) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨w, hw⟩
    have h1 : ((w⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) * g = 1 := by
      rw [← hw]; simp
    have h2 : ((((w⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : Fv F v)) * γ = 1 := by
      have := congrArg (fun x : v.adicCompletionIntegers F => (x : Fv F v)) h1
      simpa using this
    have h3 : Valued.v ((((w⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : Fv F v)) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers (K := F) (v := v)).1 (Subtype.property _)
    have h4 := congrArg Valued.v h2
    rw [map_mul, map_one] at h4
    have : Valued.v ((((w⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : Fv F v)) * Valued.v γ < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_left' h3) hγm
    rw [h4] at this
    exact lt_irrefl _ this
  have hu : IsUnit (1 - g * b) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ ((maximalIdeal _).mul_mem_right b hg)
  open scoped WithZero Topology in
  open HeightOneSpectrum Filter in
  have hcomplete : IsAdicComplete (maximalIdeal (v.adicCompletionIntegers F)) (v.adicCompletionIntegers F) := by
    let R := 𝓞 F
    let L := F
    let w := v
    let Ow := v.adicCompletionIntegers F
    let Lw := v.adicCompletion F
    have lt_one_iff_le (g : ℤᵐ⁰) : g < 1 ↔ g ≤ WithZero.exp (-1 : ℤ) := by
      induction g using WithZero.expRecOn with
      | zero => simp
      | exp a => rw [← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]; omega

    have v_algebraMap (l : L) : Valued.v (algebraMap L Lw l) = w.valuation L l :=
      valuedAdicCompletion_eq_valuation' w l

    have exists_unif : ∃ π : Ow, Valued.v (π : Lw) = WithZero.exp (-1 : ℤ) := by
      obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer L
      have h : Valued.v (algebraMap L Lw π) = WithZero.exp (-1 : ℤ) := by
        rw [v_algebraMap, hπ]
      refine ⟨⟨algebraMap L Lw π, ?_⟩, h⟩
      rw [mem_adicCompletionIntegers, h]
      exact ((lt_one_iff_le _).2 le_rfl).le

    have mem_max_iff (x : Ow) :
        x ∈ IsLocalRing.maximalIdeal Ow ↔ Valued.v (x : Lw) < 1 := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        adicCompletionIntegers.isUnit_iff_valued_eq_one]
      have : Valued.v (x : Lw) ≤ 1 := (mem_adicCompletionIntegers R L w).1 x.2
      exact ⟨fun h => lt_of_le_of_ne this h, fun h => h.ne⟩

    have max_eq_span {π : Ow} (hπ : Valued.v (π : Lw) = WithZero.exp (-1 : ℤ)) :
        IsLocalRing.maximalIdeal Ow = Ideal.span {π} := by
      ext x
      rw [mem_max_iff, Ideal.mem_span_singleton, lt_one_iff_le, ← hπ]
      exact (adicCompletionIntegers.integers L w).le_iff_dvd

    have mem_max_pow_iff {π : Ow} (hπ : Valued.v (π : Lw) = WithZero.exp (-1 : ℤ)) (x : Ow) (n : ℕ) :
        x ∈ IsLocalRing.maximalIdeal Ow ^ n ↔ Valued.v (x : Lw) ≤ Valued.v (π : Lw) ^ n := by
      rw [max_eq_span hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      have := (adicCompletionIntegers.integers L w).le_iff_dvd (x := x) (y := π ^ n)
      rw [map_pow, map_pow] at this
      exact this.symm

    obtain ⟨π, hπ⟩ := exists_unif
    have hπ1 : ‖(π : Lw)‖ < 1 := by
      rw [Valued.toNormedField.norm_lt_one_iff]
      exact (lt_one_iff_le _).2 hπ.le
    have hπ0 : (π : Lw) ≠ 0 := by
      intro h
      rw [h, map_zero] at hπ
      exact WithZero.exp_ne_zero hπ.symm
    have hr0 : 0 < ‖(π : Lw)‖ := norm_pos_iff.mpr hπ0
    have key : ∀ (n : ℕ) (x y : Ow),
        x ≡ y [SMOD ((IsLocalRing.maximalIdeal Ow) ^ n • ⊤ : Submodule Ow Ow)] ↔
          ‖(x : Lw) - y‖ ≤ ‖(π : Lw)‖ ^ n := by
      intro n x y
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_max_pow_iff hπ,
        ← map_pow, ← Valued.toNormedField.norm_le_iff]
      simp only [norm_pow]
      rfl
    refine { haus' := ?_, prec' := ?_ }
    · intro x hx
      have h : ∀ n : ℕ, ‖(x : Lw)‖ ≤ ‖(π : Lw)‖ ^ n := fun n => by
        simpa using (key n x 0).mp (hx n)
      have hx0 : ‖(x : Lw)‖ ≤ 0 :=
        ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hπ1) h
      exact Subtype.ext (norm_le_zero_iff.mp hx0)
    · intro f hf
      have hc : ∀ n : ℕ, dist (f n : Lw) (f (n + 1)) ≤ 1 * ‖(π : Lw)‖ ^ n := fun n => by
        rw [dist_eq_norm, one_mul]
        exact (key n _ _).mp (hf n.le_succ)
      obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric _ 1 hπ1 hc)
      have hl1 : ‖l‖ ≤ 1 := le_of_tendsto' hl.norm (fun n =>
        Valued.toNormedField.norm_le_one_iff.mpr (f n).2)
      refine ⟨⟨l, Valued.toNormedField.norm_le_one_iff.mp hl1⟩, fun n => ?_⟩
      rw [key]
      have ht : Tendsto (fun m => ‖(f n : Lw) - f m‖) atTop (𝓝 ‖(f n : Lw) - l‖) :=
        (tendsto_const_nhds.sub hl).norm
      exact le_of_tendsto ht (eventually_atTop.mpr ⟨n, fun m hm => (key n _ _).mp (hf hm)⟩)

  letI := hcomplete
  haveI : HenselianLocalRing (v.adicCompletionIntegers F) := ⟨fun f hf a h₁ h₂ => HenselianRing.is_henselian f hf a h₁ (h₂.map _)⟩
  obtain ⟨s, hs⟩ := PI.OmVf.quad_root (-(g * (1 - g * b) * m)) (1 - g * b) b
    (neg_mem ((maximalIdeal _).mul_mem_right m ((maximalIdeal _).mul_mem_right _ hg))) hu
  refine ⟨s, s.property, ?_⟩
  have := congrArg (fun x : v.adicCompletionIntegers F => (x : Fv F v)) hs
  simp only [b, g, m] at this
  push_cast at this
  linear_combination this
end PI.OmVf
end
end

noncomputable section

namespace PI.OmVf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.OmVd IsLocalRing
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem isoW_gen {a : ℕ} (Y : TupV (E := E) v n a) (z : Fin a) (γ : Fv F v)
    (hγ : γ ∈ v.adicCompletionIntegers F) (hγm : Valued.v γ < 1)
    (hz : ∀ i, gramR (Fv F v) σ J Y i z = if i = z then sc (E := E) v γ else 0)
    (hPD : PrimDual σ J ψ v Λ a)
    (hTS : ∃ S : Matrix (Fin (a + 1)) (Fin (a + 1)) (Fv F v ⊗[F] E), (∀ i j, S i j ∈ OEv (E := E) v) ∧
      bordM v (gramR (Fv F v) σ J Y) z * S = 1) :
    IsoW σ J ψ v Λ a Y := by
  classical
  intro hG
  obtain ⟨hS, hL, hSD, hUn, -, hYp⟩ := hG
  have hcm := hS.1
  have hJ : ∀ i j, σ (J j i) = J i j := hS.2.1.1
  have hconj : ∀ x y, sigR (Fv F v) σ (hR (Fv F v) σ J x y) = hR (Fv F v) σ J y x :=
    fun x y => PI.OmLocU.Orb.hR_conj σ J v hcm hJ x y
  have hsc : ∀ r : Fv F v, sigR (Fv F v) σ (sc (E := E) v r) = sc (E := E) v r :=
    fun r => PI.OmLocU.NormOneUnitFixedPoints.sigR_sc' σ v r
  set G := gramR (Fv F v) σ J Y with hGdef

  obtain ⟨S, hSi, hTS1⟩ := hTS
  have hGi : ∀ i j, G i j ∈ OEv (E := E) v := fun i j =>
    PI.OmLocU.hR_mem_oEv σ J v Λ hSD (hYp.1 i) (hYp.1 j)
  have hBi : ∀ i j, bordM v G z i j ∈ OEv (E := E) v := by
    intro i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp only [bordM, Fin.snoc_last]; exact oEv_zero v
      | cast j =>
        simp only [bordM, Fin.snoc_last, Fin.snoc_castSucc]
        split_ifs
        · exact oEv_one v
        · exact oEv_zero v
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [bordM, Fin.snoc_last, Fin.snoc_castSucc]
        split_ifs
        · exact oEv_one v
        · exact oEv_zero v
      | cast j => simp only [bordM, Fin.snoc_castSucc]; exact hGi i j
  refine ⟨bordM v G z, ⟨S.det, det_int v _ hSi, det_int v _ hBi, ?_⟩, ?_⟩
  · rw [← Matrix.det_mul, hTS1, Matrix.det_one]
  intro X hX hXY
  obtain ⟨W, hW, hWd⟩ := hPD hS hSD hUn hL X hX
  set g := sc (E := E) v γ with hg
  have hgO : g ∈ OEv (E := E) v := PI.OmLocU.NormOneUnitFixedPoints.sc_mem v hγ
  have hXz : ∀ i, hR (Fv F v) σ J (X i) (X z) = if i = z then g else 0 := by
    intro i
    have := congrFun (congrFun hXY i) z
    simp only [gramR] at this
    rw [this]; exact hz i
  set w0 := W z with hw0
  have hw0L : w0 ∈ latLoc (E := E) v Λ := hW z
  have hXw0 : ∀ i, hR (Fv F v) σ J (X i) w0 = if i = z then 1 else 0 := fun i => (hWd i z).1
  have hw0X : ∀ i, hR (Fv F v) σ J w0 (X i) = if i = z then 1 else 0 := fun i => (hWd i z).2
  set y := X z + (-g) • w0 with hy
  have hyL : y ∈ latLoc (E := E) v Λ :=
    Submodule.add_mem _ (hX.1 z) (PI.OmLocU.Orb.oSmul v Λ hL _ (oEv_neg v hgO) _ hw0L)
  have hXy : ∀ i, hR (Fv F v) σ J (X i) y = 0 := by
    intro i
    rw [hy, hAddR, hSmulR, hXz, hXw0]
    split_ifs <;> ring
  have hyX : ∀ i, hR (Fv F v) σ J y (X i) = 0 := by
    intro i; rw [← hconj, hXy, map_zero]
  set b := hR (Fv F v) σ J w0 w0 with hb
  have hbO : b ∈ OEv (E := E) v := PI.OmLocU.hR_mem_oEv σ J v Λ hSD hw0L hw0L
  obtain ⟨β, hβ, hbβ⟩ := PI.OmLocU.NormOneUnitFixedPoints.fix_int_sc σ v hcm hbO (hconj w0 w0)
  have h1 : hR (Fv F v) σ J w0 y = 1 + (-g) * b := by
    rw [hy, hAddR, hSmulR, hw0X, if_pos rfl]
  have h2 : hR (Fv F v) σ J y w0 = 1 + (-g) * b := by
    rw [← hconj, h1, map_add (f := _), map_one, map_mul, map_neg, hg, hsc, hconj]
  have h3 : hR (Fv F v) σ J y y = (-g) * (1 + (-g) * b) := by
    rw [hy, hAddR, hSmulR, ← hy, hyX, h2, zero_add]

  obtain ⟨θ, hθO, hθ⟩ := PI.OmLocU.Red.trOnto_holds σ J ψ v hS hUn 1 (oEv_one v) (map_one _)
  have hinv : ∀ x, sigR (Fv F v) σ (sigR (Fv F v) σ x) = x := PI.OmLocU.Orb.sigR_invol σ v hcm
  have hNO : sigR (Fv F v) σ θ * θ ∈ OEv (E := E) v := by
    refine oEv_mul v ?_ hθO
    have := hθ ▸ (oEv_one (E := E) v)
    have e : sigR (Fv F v) σ θ = (θ + sigR (Fv F v) σ θ) - θ := by ring
    rw [e]
    exact oEv_add v this (oEv_neg v hθO)
  have hNf : sigR (Fv F v) σ (sigR (Fv F v) σ θ * θ) = sigR (Fv F v) σ θ * θ := by
    rw [map_mul, hinv, mul_comm]
  obtain ⟨ν, hν, hNν⟩ := PI.OmLocU.NormOneUnitFixedPoints.fix_int_sc σ v hcm hNO hNf
  obtain ⟨s, hsO, hs⟩ := exists_integral_root_of_quadratic v β γ ν hβ hγ hγm hν
  set t := sc (E := E) v s * θ with ht
  have htO : t ∈ OEv (E := E) v := oEv_mul v (PI.OmLocU.NormOneUnitFixedPoints.sc_mem v hsO) hθO
  have hσt : sigR (Fv F v) σ t = sc (E := E) v s * sigR (Fv F v) σ θ := by
    rw [ht, map_mul, hsc]
  set w := w0 + t • y with hw
  have hwL : w ∈ latLoc (E := E) v Λ :=
    Submodule.add_mem _ hw0L (PI.OmLocU.Orb.oSmul v Λ hL _ htO _ hyL)
  have hXw : ∀ i, hR (Fv F v) σ J (X i) w = if i = z then 1 else 0 := by
    intro i; rw [hw, hAddR, hSmulR, hXy, hXw0, mul_zero, add_zero]
  have hwX : ∀ i, hR (Fv F v) σ J w (X i) = if i = z then 1 else 0 := by
    intro i; rw [hw, hAddL, hSmulL, hyX, hw0X, mul_zero, add_zero]
  have E0 : hR (Fv F v) σ J w w = b + t * hR (Fv F v) σ J w0 y +
      (sigR (Fv F v) σ t * hR (Fv F v) σ J y w0 + sigR (Fv F v) σ t * (t * hR (Fv F v) σ J y y)) := by
    rw [hw, hAddL, hAddR, hAddR, hSmulR, hSmulL, hSmulL, hSmulR]
  have key : sc (E := E) v (β + (1 - γ * β) * s - γ * (1 - γ * β) * ν * s ^ 2) = 0 := by
    rw [hs]; simp [sc]
  have keyE : sc (E := E) v β + (1 - g * sc (E := E) v β) * sc (E := E) v s -
      g * (1 - g * sc (E := E) v β) * sc (E := E) v ν * sc (E := E) v s ^ 2 = 0 := by
    rw [← key, hg]
    simp only [PI.OmLocU.NormOneUnitFixedPoints.sc_eq, map_add (f := _), map_sub, map_mul, map_one, map_pow]
  have hww : hR (Fv F v) σ J w w = 0 := by
    rw [E0, h1, h2, h3, hσt, hbβ, ht]
    linear_combination keyE + ((1 - g * sc (E := E) v β) * sc (E := E) v s) * hθ -
      (g * (1 - g * sc (E := E) v β) * sc (E := E) v s ^ 2) * hNν
  refine ⟨w, hwL, ?_⟩
  rw [gram_augT σ J v X w z hXw hwX hww, hXY]

end PI.OmVf
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.BordMulSM
noncomputable section

namespace PI.OmVf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.OmVd
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def sM {a : ℕ} (π : Fin a → Fin a) (z : Fin a) (g : Fv F v ⊗[F] E) :
    Matrix (Fin (a + 1)) (Fin (a + 1)) (Fv F v ⊗[F] E) :=
  Fin.snoc (α := fun _ => Fin (a + 1) → Fv F v ⊗[F] E)
    (fun k => Fin.snoc (α := fun _ => Fv F v ⊗[F] E)
      (fun j => if k = z ∨ j = z then 0 else if j = π k then 1 else 0) (if k = z then 1 else 0))
    (Fin.snoc (α := fun _ => Fv F v ⊗[F] E) (fun j => if j = z then 1 else 0) (-g))

theorem bord_mul_sM {a : ℕ} (G : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) (π : Fin a → Fin a)
    (hπ : Function.Involutive π) (z : Fin a) (hπz : π z = z) (g : Fv F v ⊗[F] E) (d : Fin a → Fv F v ⊗[F] E)
    (hd : ∀ i, i ≠ z → d i = 1) (hdz : d z = g) (hG : ∀ i k, G i k = if k = π i then d i else 0) :
    bordM v G z * sM v π z g = 1 := by
  have hπz' : ∀ i, π i = z ↔ i = z := fun i => ⟨fun h => by rw [← hπ i, h, hπz], fun h => h ▸ hπz⟩
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.one_apply] <;>
    simp only [bordM, sM, Fin.snoc_castSucc, Fin.snoc_last, hG]
  all_goals simp [hπz', hπ _, (Fin.castSucc_lt_last _).ne, (Fin.castSucc_lt_last _).ne', Fin.castSucc_inj]
  · refine Finset.sum_eq_zero (fun x _ => ?_)
    split_ifs <;> first | rfl | (exfalso; tauto)
  · rcases eq_or_ne i z with rfl | hi
    · simp [hπz, hdz]
    · have : z ≠ π i := fun h => hi ((hπz' i).1 h.symm)
      simp [this, hi]
  · rw [Finset.sum_eq_single (π i) (fun x _ hx => by simp [hx]) (by simp)]
    simp only [hπ i, hπz', if_true]
    rcases eq_or_ne i z with rfl | hi
    · by_cases hj : j = i
      · simp [hj]
      · simp [hj, Ne.symm hj]
    · rcases eq_or_ne j z with rfl | hj
      · simp [hi]
      · simp [hi, hj, hd i hi, eq_comm]

end PI.OmVf
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.AriEta
noncomputable section

open Polynomial IsDedekindDomain NumberField IsLocalRing
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.NcVal.AriEta

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem val_int (x : 𝓞 F) : Valued.v (((x : F) : v.adicCompletion F)) ≤ 1 := by
  have h : Valued.v (((x : F) : v.adicCompletion F)) = v.valuation F (x : F) :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : F)
  rw [h]
  exact v.valuation_le_one x

theorem val_int_lt (x : 𝓞 F) (hx : x ∈ v.asIdeal) : Valued.v (((x : F) : v.adicCompletion F)) < 1 := by
  have h : Valued.v (((x : F) : v.adicCompletion F)) = v.valuation F (x : F) :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : F)
  rw [h]
  exact (v.valuation_lt_one_iff_mem x).mpr hx

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

end Formalism.L2.SG.Pf.NcVal.AriEta
end
end

noncomputable section

namespace PI.OmVf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.OmVd
open Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.L2.SG.Pf.NcVal.OmVSt.OmW Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem zi_val' : (zi (D := D)).val = D.R.rS := by simp [zi]

theorem zi_iff (i : Fin (D.R.rS + 1 + D.R.rS)) : i.val = D.R.rS ↔ i = zi (D := D) :=
  ⟨fun h => Fin.ext (by rw [h, zi_val']), fun h => by rw [h, zi_val']⟩

theorem gram_yTup (v : PlX X) (i k : Fin (D.R.rS + 1 + D.R.rS)) :
    gramR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (yTup X u' v) i k =
      if k = piv D.R.rS i then inclR (F := X.B.I.F) (Fv X.B.I.F v) (cD X u' i) else 0 := by
  rw [omVGram_holds X u' v]
  simp only [localGramMatrixFrame, Matrix.map_apply]
  rw [gramE_entry X u' i k, apply_ite (inclR (F := X.B.I.F) (Fv X.B.I.F v)), map_zero]

theorem inclR_apply' (v : PlX X) :
    inclR (F := X.B.I.F) (Fv X.B.I.F v) (cD X u' (zi (D := D))) =
      sc (E := X.B.I.E) v (-((Tw u' : ℕ) : Fv X.B.I.F v)) := by
  have h : (zi (D := D)).val = D.R.rS := zi_val'
  simp only [cD, h, if_true, map_neg, map_natCast, PI.OmLocU.NormOneUnitFixedPoints.sc_eq]

theorem gam_int (v : PlX X) : -((Tw u' : ℕ) : Fv X.B.I.F v) ∈ v.adicCompletionIntegers X.B.I.F := by
  have h := Formalism.L2.SG.Pf.NcVal.AriEta.val_int v ((Tw u' : ℕ) : 𝓞 X.B.I.F)
  have e : (((((Tw u' : ℕ) : 𝓞 X.B.I.F) : X.B.I.F) : v.adicCompletion X.B.I.F)) = ((Tw u' : ℕ) : Fv X.B.I.F v) := by
    rw [show (((Tw u' : ℕ) : 𝓞 X.B.I.F) : X.B.I.F) = ((Tw u' : ℕ) : X.B.I.F) by simp]
    exact map_natCast (algebraMap X.B.I.F (v.adicCompletion X.B.I.F)) _
  rw [e] at h
  exact neg_mem ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 h)

theorem gam_lt (v : PlX X) (hv : ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal) :
    Valued.v (-((Tw u' : ℕ) : Fv X.B.I.F v)) < 1 := by
  have h := Formalism.L2.SG.Pf.NcVal.AriEta.val_int_lt v ((Tw u' : ℕ) : 𝓞 X.B.I.F) hv
  have e : (((((Tw u' : ℕ) : 𝓞 X.B.I.F) : X.B.I.F) : v.adicCompletion X.B.I.F)) = ((Tw u' : ℕ) : Fv X.B.I.F v) := by
    rw [show (((Tw u' : ℕ) : 𝓞 X.B.I.F) : X.B.I.F) = ((Tw u' : ℕ) : X.B.I.F) by simp]
    exact map_natCast (algebraMap X.B.I.F (v.adicCompletion X.B.I.F)) _
  rw [e] at h
  rw [Valuation.map_neg]
  exact h

theorem isoW_holds (v : PlX X) (hv : ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal) :
    IsoW X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v) := by
  classical
  set γ : Fv X.B.I.F v := -((Tw u' : ℕ) : Fv X.B.I.F v) with hγ
  have hγO := gam_int X u' v
  have hgO : sc (E := X.B.I.E) v γ ∈ OEv (E := X.B.I.E) v := PI.OmLocU.NormOneUnitFixedPoints.sc_mem v hγO
  have hpz : piv D.R.rS (zi (D := D)) = zi (D := D) := pivot_castAdd_last D.R.rS
  have hpe : ∀ i, zi (D := D) = piv D.R.rS i ↔ i = zi (D := D) := fun i =>
    ⟨fun h => by rw [← piv_invol D.R.rS i, ← h, hpz], fun h => by rw [h, hpz]⟩
  have hd : ∀ i, i ≠ zi (D := D) → inclR (F := X.B.I.F) (Fv X.B.I.F v) (cD X u' i) = 1 := by
    intro i hi
    have : ¬ i.val = D.R.rS := fun h => hi ((zi_iff i).1 h)
    simp only [cD, this, if_false, map_one]
  refine isoW_gen X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (yTup X u' v) (zi (D := D)) γ hγO (gam_lt X u' v hv)
    (fun i => ?_) (primDual_of_left _ _ _ _ _ _ (leftInvO_holds _ _ _ _ _)) ?_
  · rw [gram_yTup]
    by_cases hi : i = zi (D := D)
    · rw [if_pos ((hpe i).2 hi), if_pos hi, hi, inclR_apply']
    · rw [if_neg (fun h => hi ((hpe i).1 h)), if_neg hi]
  · refine ⟨sM v (piv D.R.rS) (zi (D := D)) (sc (E := X.B.I.E) v γ), fun i j => ?_,
      bord_mul_sM v _ (piv D.R.rS) (piv_invol D.R.rS) (zi (D := D)) hpz _
        (fun i => inclR (F := X.B.I.F) (Fv X.B.I.F v) (cD X u' i)) hd (inclR_apply' X u' v) (gram_yTup X u' v)⟩
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp only [sM, Fin.snoc_last]; exact oEv_neg v hgO
      | cast j =>
        simp only [sM, Fin.snoc_last, Fin.snoc_castSucc]
        split_ifs
        · exact oEv_one v
        · exact oEv_zero v
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [sM, Fin.snoc_last, Fin.snoc_castSucc]
        split_ifs
        · exact oEv_one v
        · exact oEv_zero v
      | cast j =>
        simp only [sM, Fin.snoc_castSucc]
        split_ifs
        · exact oEv_zero v
        · exact oEv_one v
        · exact oEv_zero v

end PI.OmVf
end
end

noncomputable section

namespace PI.OmVf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.OmVd
open Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVBadT_of_restX (hStd : Formalism.L2.SG.Pf.NcX.OmVSt.OmVStd X ψ) (hLat : Formalism.L2.SG.Pf.NcX.OmVSt.OmVLat X)
    (hGram : Formalism.L2.SG.Pf.NcX.OmVSt.OmVGram X u')
    (hRed : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      RedP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hFI : FFInertB) (hFS : FFSplitB) : Formalism.L2.SG.Pf.NcX.OmVSt.OmVBadT X u' ψ :=
  omVBadT_of_lastX X u' ψ hStd hLat hGram (fun v hv => isoW_holds X u' ψ v hv) hRed hFI hFS

end PI.OmVf
