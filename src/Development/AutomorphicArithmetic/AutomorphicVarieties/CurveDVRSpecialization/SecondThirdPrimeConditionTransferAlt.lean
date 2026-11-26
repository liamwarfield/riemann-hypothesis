module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PropagationTheoremGL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FullEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SepOfMinors

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SecondThirdPrimeConditionTransferAlt
set_option linter.overlappingInstances false

noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

namespace UpperTheory.V.Pr

structure Setup {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    [Algebra ℤ_[l] O] (F : Frame l (ResidueField O)) (n : ℕ) : Type 1 where
  n23 : n = 2 ∨ n = 3
  C₀ : ℕ
  ok : F.Ok C₀
  big : F.Big C₀
  lne : (l : O) ≠ 0
  G : W.GFrame l
  r : W.Resid G O n
  K : TwLink F r
  B : W.UniversalOrdinaryDeterminantRing r
  S : Space O F n

namespace Setup

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
  [Algebra ℤ_[l] O] {F : Frame l (ResidueField O)} {n : ℕ} (T : Setup F n)

abbrev IsPhi (Φ : T.B.B →ₐ[O] T.S.B) : Prop := T.K.IsPhi T.B T.S Φ

def phi (Φ : T.B.B →ₐ[O] T.S.B) {x : Ideal T.S.A} (L : T.S.Loc x) : T.B.B →ₐ[O] L.R := L.ι.comp (T.S.inc.comp Φ)

def back (Φ : T.B.B →ₐ[O] T.S.B) {x : Ideal T.S.A} (L : T.S.Loc x) (P : Ideal L.R) [P.IsPrime] : PrimeSpectrum T.B.B :=
  ⟨P.comap (T.phi Φ L : T.B.B →+* L.R), inferInstance⟩

def PhiEx : Prop := ∃ Φ, T.IsPhi Φ ∧ Function.Surjective Φ

def FinLamOf : Prop :=
  ∀ Φ, T.IsPhi Φ → Function.Surjective Φ → ∀ (Λ : W.LamObj T.r) (J : Ideal T.B.B),
    ((Ideal.Quotient.mk J).comp (Λ.toPair T.B.u : Λ.Λ →+* T.B.B)).Finite → T.S.FinLam (J.map Φ)

def PointEx : Prop :=
  ∀ Φ, T.IsPhi Φ → ∀ (x : Ideal T.S.A) (L : T.S.Loc x) (p : Ideal L.R), p.IsPrime → qdim p = 1 → (l : L.R) ∈ p →
    ∃ (y : W.Point T.r) (j : L.R →ₐ[O] y.A), RingHom.ker j = p ∧ IsLocalHom j ∧
      W.mat y.ρ = T.K.tw (L.ρ.map (j : L.R →+* y.A)) ∧ y.ψ = T.K.twψ (L.ρ.map (j : L.R →+* y.A)) ∧
      T.B.IsPt y (j.comp (T.phi Φ L))

def NiceOf : Prop :=
  ∀ (x : Ideal T.S.A) (L : T.S.Loc x) (y : W.Point T.r) (j : L.R →ₐ[O] y.A), IsLocalHom j → Nice L.ρ (RingHom.ker j) →
    W.mat y.ρ = T.K.tw (L.ρ.map (j : L.R →+* y.A)) → y.ψ = T.K.twψ (L.ρ.map (j : L.R →+* y.A)) →
    y.N1 ∧ y.N3 ∧ (L.ρ.TI (RingHom.ker j) → y.TypeI) ∧ (L.ρ.TE (RingHom.ker j) → y.TypeE)

def StableOf : Prop :=
  ∀ Φ, T.IsPhi Φ → ∀ (x : Ideal T.S.A) (L : T.S.Loc x) (P : Ideal L.R) [P.IsPrime], L.ρ.TI P → T.B.IsStable (T.back Φ L P)

def FirstPrimeConditionTransfer : Prop :=
  ∀ Φ, T.IsPhi Φ → (∀ y : W.Point T.r, y.N4) → ∀ J, T.B.P1core J → P1' T.S (J.map Φ)

def IdealSpecializationPoint (J : Ideal T.B.B) : Prop :=
  ∃ (K' : Type) (_ : Field K') (_ : IsAlgClosed K') (_ : Algebra O K') (φ : T.B.B →ₐ[O] K') (ρ : NRep F n K'),
    MatIrr ⊤ ρ.r ∧ J ≤ RingHom.ker φ ∧ T.B.u.D.map (φ : T.B.B →+* K') = W.GDet.ofRep (T.K.tw ρ)

def Unr0 (J : Ideal T.B.B) : Prop :=
  ∀ g ∈ T.G.I0, (T.B.u.D.map (Ideal.Quotient.mk J)).Kills (MonoidAlgebra.single (g : T.G.G₀) (1 : T.B.B ⧸ J) - 1)

def DimT (J : Ideal T.B.B) : Prop := ∀ Z ∈ J.minimalPrimes, qdim Z = ((1 + n * F.d : ℕ) : WithBot ℕ∞)

def CurveSpecializationHypothesis : Prop :=
  ∀ Φ, T.IsPhi Φ → ∀ J, T.Unr0 J → T.DimT J → T.IdealSpecializationPoint J → SeedIn T.S (J.map Φ)

def GoodPt (J : Ideal T.B.B) : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra O A] [IsCD O A] (ρ : NRep F n A), IsLiftA O ρ →
    ∀ (K' : Type) [Field K'] (j : A →+* K'), Function.Injective j → MatIrr ⊤ (ρ.map j).r →
    ∃ f : T.B.B →ₐ[O] A, J ≤ RingHom.ker f ∧ T.B.u.Maps (f : T.B.B →+* A) (W.GDet.ofRep (T.K.tw ρ)) (T.K.twψ ρ)

def GoodPtOf : Prop := ∀ Φ, T.IsPhi Φ → ∀ J, AllGood T.S (J.map Φ) → T.GoodPt J

structure ModIn (J : Ideal T.B.B) : Prop where
  fin : ∃ Λ : W.LamObj T.r, ((Ideal.Quotient.mk J).comp (Λ.toPair T.B.u : Λ.Λ →+* T.B.B)).Finite
  dim : T.DimT J
  unr : T.Unr0 J
  n4 : ∀ y : W.Point T.r, y.N4
  p1 : T.B.P1core J
  p3 : T.B.P3core J
  seed : T.IdealSpecializationPoint J

end Setup

section Three

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
  [Algebra ℤ_[l] O] {F : Frame l (ResidueField O)} (T : Setup F 3)

def Setup.ThickOf : Prop :=
  ∀ Φ, T.IsPhi Φ → ∀ (x : Ideal T.S.A) (L : T.S.Loc x) (P : Ideal L.R) [P.IsPrime], Thick L.ρ P →
    T.B.IsThick (T.back Φ L P)

def Setup.SecondThirdPrimeConditionTransfer : Prop :=
  ∀ Φ, T.IsPhi Φ → (∀ y : W.Point T.r, y.N4) → ∀ J, T.B.P3core J → P23' T.S (J.map Φ)

end Three

def AbsMain : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    [Algebra ℤ_[l] O] (F : Frame l (ResidueField O)) (T₂ : Setup F 2) (T₃ : Setup F 3) (J₂ : Ideal T₂.B.B)
    (J₃ : Ideal T₃.B.B), T₂.ModIn J₂ → T₃.ModIn J₃ →
    T₂.GoodPt J₂ ∧ T₃.GoodPt J₃ ∧ FinPt O F 3

end UpperTheory.V.Pr

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RegCosetE
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DiagonalEntries
theorem UpperTheory.Reformulated.B.DiagonalizeTwoByTwo.diagE :
    ∀ {κ : Type} [inst : Field κ]
    (M : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) κ) (α : Fin (2 : ℕ) → κ),
    Function.Injective α →
      M.charpoly = ∏ i : Fin (2 : ℕ), (Polynomial.X - (Polynomial.C : κ → Polynomial κ) (α i)) →
        ∃ (P : GL (Fin (2 : ℕ)) κ),
          M * (↑P : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) κ) =
            (↑P : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) κ) * Matrix.diagonal α := by
  intro κ _ M α hα h
  classical
  have hv : ∀ i : Fin 2, ∃ v : Fin 2 → κ, v ≠ 0 ∧ M.mulVec v = α i • v := by
    intro i
    have h0 : (Matrix.scalar (Fin 2) (α i) - M).det = 0 := by
      rw [← Matrix.eval_charpoly, h, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    refine ⟨v, hv0, ?_⟩
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext j
    simp [Matrix.mulVec_diagonal]
  choose v hv0 hv using hv
  have hli : LinearIndependent κ v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' M) α hα v fun i =>
      ⟨Module.End.mem_eigenspace_iff.2 (by simpa using hv i), hv0 i⟩
  have hu : IsUnit (Matrix.of v).transpose :=
    Matrix.linearIndependent_cols_iff_isUnit.1 hli
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec]
  ext j i
  have := congrFun (hv i) j
  rw [Matrix.mul_diagonal]
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using this
end

open Matrix Polynomial

namespace UpperTheory.V.Pr

private lemma diagE {κ : Type} [Field κ] (M : Matrix (Fin 2) (Fin 2) κ) (α : Fin 2 → κ)
    (hα : Function.Injective α) (h : M.charpoly = ∏ i, (X - C (α i))) :
    ∃ P : GL (Fin 2) κ, M * (P : Matrix (Fin 2) (Fin 2) κ) = (P : Matrix (Fin 2) (Fin 2) κ) * diagonal α :=
  _root_.UpperTheory.Reformulated.B.DiagonalizeTwoByTwo.diagE M α hα h

private lemma strongIrr_conjE {G κ : Type} [Group G] [Field κ] {n : ℕ} (r : G →* GL (Fin n) κ) (h : StrongIrr r)
    (P : GL (Fin n) κ) : StrongIrr ((MulAut.conj P⁻¹).toMonoidHom.comp r) := by
  intro W S hS hW
  set A : Matrix (Fin n) (Fin n) κ := (P : Matrix (Fin n) (Fin n) κ) with hA
  set B : Matrix (Fin n) (Fin n) κ := ((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) with hB
  have hAB : ∀ v, A *ᵥ (B *ᵥ v) = v := fun v => by rw [mulVec_mulVec, hA, hB, Units.mul_inv, one_mulVec]
  have hBA : ∀ v, B *ᵥ (A *ᵥ v) = v := fun v => by rw [mulVec_mulVec, hA, hB, Units.inv_mul, one_mulVec]
  have hg : ∀ g v, gm ((MulAut.conj P⁻¹).toMonoidHom.comp r) g *ᵥ v = B *ᵥ (gm r g *ᵥ (A *ᵥ v)) := by
    intro g v
    rw [mulVec_mulVec, mulVec_mulVec]
    rfl
  have hm : ∀ v, v ∈ W.comap (Matrix.toLin' B) ↔ B *ᵥ v ∈ W := fun v => by
    rw [Submodule.mem_comap, toLin'_apply]
  have key := h (W.comap (Matrix.toLin' B)) S hS (by
    intro g
    rw [hW g]
    constructor
    · intro h1 v hv
      have := h1 _ ((hm v).1 hv)
      rw [hg, hAB] at this
      exact (hm _).2 this
    · intro h1 v hv
      rw [hg, ← hm]
      exact h1 _ (by rw [hm, hBA]; exact hv))
  rcases key with key | key
  · left
    rw [eq_bot_iff]
    intro v hv
    have : A *ᵥ v ∈ W.comap (Matrix.toLin' B) := by rw [hm, hBA]; exact hv
    rw [key, Submodule.mem_bot] at this
    rw [Submodule.mem_bot, ← hBA v, this, mulVec_zero]
  · right
    rw [eq_top_iff]
    intro v _
    have : A *ᵥ v ∈ W.comap (Matrix.toLin' B) := by rw [key]; trivial
    rwa [hm, hBA] at this

private def blkE {κ : Type} [Field κ] (M : Matrix (Fin 2) (Fin 2) κ) (w : κ) : Matrix (Fin 3) (Fin 3) κ :=
  !![M 0 0, M 0 1, 0; M 1 0, M 1 1, 0; 0, 0, w]

private lemma charpoly_blkE {κ : Type} [Field κ] (M : Matrix (Fin 2) (Fin 2) κ) (w : κ) :
    (blkE M w).charpoly = M.charpoly * (X - C w) := by
  simp only [Matrix.charpoly, det_fin_three, det_fin_two]
  simp [blkE, charmatrix_apply]
  ring

private lemma blkE_mul {κ : Type} [Field κ] (M : Matrix (Fin 2) (Fin 2) κ) (w : κ) (a : Fin 2 → κ) (c : κ) (m : ℕ)
    (d : Fin 3 → κ) (h0 : d 0 = a 0) (h1 : d 1 = a 1) (h2 : d 2 = c) :
    blkE M w * diagonal d ^ m = blkE (M * diagonal a ^ m) (w * c ^ m) := by
  ext i j
  simp only [diagonal_pow, mul_diagonal, blkE]
  fin_cases i <;> fin_cases j <;> simp [h0, h1, h2]

private lemma minor_neE {κ : Type} [Field κ] {n : ℕ} (Y : Matrix (Fin n) (Fin n) κ) (S : Finset (Fin n))
    (h : ∀ v : Fin n → κ, (∀ i ∈ S, (Y *ᵥ v) i = 0) → (∀ i, i ∉ S → v i = 0) → v = 0) :
    (Y.submatrix (Subtype.val : S → Fin n) Subtype.val).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hv'⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have := h (fun j => if hj : j ∈ S then v ⟨j, hj⟩ else 0) (by
    intro i hi
    have h1 := congrFun hv' ⟨i, hi⟩
    simp only [mulVec, dotProduct, submatrix_apply, Pi.zero_apply] at h1 ⊢
    refine Eq.trans ?_ h1
    rw [← Finset.sum_subset (Finset.subset_univ S) (by intro x _ hx; rw [dif_neg hx, mul_zero]),
      ← Finset.sum_coe_sort S]
    exact Finset.sum_congr rfl fun x _ => by rw [dif_pos x.2]) (by intro i hi; exact dif_neg hi)
  apply hv
  ext ⟨j, hj⟩
  have h3 := congrFun this j
  simp only [dif_pos hj] at h3
  exact h3

private lemma minor_blkE {κ : Type} [Field κ] (M : Matrix (Fin 2) (Fin 2) κ) (w : κ) (h0 : M 0 0 ≠ 0) (h1 : M 1 1 ≠ 0)
    (hd : M.det ≠ 0) (hw : w ≠ 0) (S : Finset (Fin 3)) :
    ((blkE M w).submatrix (Subtype.val : S → Fin 3) Subtype.val).det ≠ 0 := by
  apply minor_neE
  intro v ha hb
  rw [det_fin_two] at hd
  have e0 : (blkE M w *ᵥ v) 0 = M 0 0 * v 0 + M 0 1 * v 1 := by simp [blkE, mulVec, dotProduct, Fin.sum_univ_three]
  have e1 : (blkE M w *ᵥ v) 1 = M 1 0 * v 0 + M 1 1 * v 1 := by simp [blkE, mulVec, dotProduct, Fin.sum_univ_three]
  have e2 : (blkE M w *ᵥ v) 2 = w * v 2 := by simp [blkE, mulVec, dotProduct, Fin.sum_univ_three]
  have v2 : v 2 = 0 := by
    by_cases h : (2 : Fin 3) ∈ S
    · have := ha _ h
      rw [e2] at this
      simpa [hw] using this
    · exact hb _ h
  have v01 : v 0 = 0 ∧ v 1 = 0 := by
    by_cases k0 : (0 : Fin 3) ∈ S <;> by_cases k1 : (1 : Fin 3) ∈ S
    · have a0 := ha _ k0
      have a1 := ha _ k1
      rw [e0] at a0
      rw [e1] at a1
      constructor
      · apply mul_left_cancel₀ hd
        linear_combination M 1 1 * a0 - M 0 1 * a1
      · apply mul_left_cancel₀ hd
        linear_combination M 0 0 * a1 - M 1 0 * a0
    · have a0 := ha _ k0
      have a1 := hb _ k1
      rw [e0, a1] at a0
      exact ⟨by simpa [h0] using a0, a1⟩
    · have a0 := hb _ k0
      have a1 := ha _ k1
      rw [e1, a0] at a1
      exact ⟨a0, by simpa [h1] using a1⟩
    · exact ⟨hb _ k0, hb _ k1⟩
  ext i
  fin_cases i
  · exact v01.1
  · exact v01.2
  · exact v2

private lemma diagCaseE (G κ : Type) [Group G] [Field κ] (σ : G →* GL (Fin 2) κ) (ψ₀ : G →* κˣ) (hσ : StrongIrr σ)
    (u : G) (α : Fin 2 → κˣ) (hα : FreeRatios ![α 0, α 1, ψ₀ u])
    (hu : gm σ u = diagonal (fun i => ((α i : κˣ) : κ))) (y : GL (Fin 2) κ) (z : κˣ) :
    ∃ h, (((y : Matrix (Fin 2) (Fin 2) κ) * gm σ h).charpoly * (X - C ((z * ψ₀ h : κˣ) : κ))).Separable := by
  have hα2 : FreeRatios α := by
    intro i j hij m hm
    have := hα i.castSucc j.castSucc (by simpa using hij) m hm
    fin_cases i <;> fin_cases j <;> simpa using this
  obtain ⟨b, hb⟩ := fullEx G κ 2 σ hσ u α hα2 hu
  obtain ⟨m, hm⟩ := expSums κ (Fin 2) (Fin 2) (fun _ => α)
    (fun s i => (y : Matrix (Fin 2) (Fin 2) κ) s i * gm σ b i s) (fun _ => hα2) (by
      intro s
      by_contra hc
      push Not at hc
      have : ∀ i, (y : Matrix (Fin 2) (Fin 2) κ) s i = 0 := fun i =>
        (mul_eq_zero.1 (hc i)).resolve_right (hb i s).1
      exact y.det_ne_zero (det_eq_zero_of_row_eq_zero s this))
  have hpow : ∀ k : ℕ, gm σ (u ^ k) = diagonal (fun i => ((α i : κˣ) : κ)) ^ k := by
    intro k
    rw [← hu]; simp [gm]
  have hmul : ∀ g g', gm σ (g * g') = gm σ g * gm σ g' := by
    intro g g'; simp [gm]
  set M : Matrix (Fin 2) (Fin 2) κ := (y : Matrix (Fin 2) (Fin 2) κ) * gm σ (u ^ m * b) with hM
  have hdiag : ∀ s, M s s ≠ 0 := by
    intro s
    have : M s s = ∑ i, (y : Matrix (Fin 2) (Fin 2) κ) s i * gm σ b i s * ((α i : κˣ) : κ) ^ m := by
      rw [hM, hmul, hpow, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [diagonal_pow, diagonal_mul]
      simp only [Pi.pow_apply]
      ring
    rw [this]; exact hm s
  have hdet : M.det ≠ 0 := by
    have := (y * σ (u ^ m * b)).det_ne_zero
    rwa [Units.val_mul] at this
  obtain ⟨k, hk⟩ := sepOfMinors κ 3 le_rfl (blkE M ((z * ψ₀ (u ^ m * b) : κˣ) : κ)) _ hα
    (minor_blkE M _ (hdiag 0) (hdiag 1) hdet (Units.ne_zero _))
  rw [blkE_mul M _ (fun i => ((α i : κˣ) : κ)) ((ψ₀ u : κˣ) : κ) k _ rfl rfl rfl, charpoly_blkE] at hk
  refine ⟨u ^ m * b * u ^ k, ?_⟩
  rw [hmul, hpow, ← Matrix.mul_assoc, ← hM]
  convert hk using 4
  simp [mul_assoc]

end UpperTheory.V.Pr

theorem UpperTheory.V.Pr.regCosetE :
    UpperTheory.V.Pr.RegCosetE := by
  intro G κ _ _ σ ψ₀ hσ u α hα hu y z
  have hinj : Function.Injective (fun i => ((α i : κˣ) : κ)) := by
    intro i j hij
    by_contra hne
    have := hα i.castSucc j.castSucc (by simpa using hne) 1 one_pos
    have h2 : α i = α j := Units.ext hij
    fin_cases i <;> fin_cases j <;> simp_all
  obtain ⟨P, hP⟩ := diagE (gm σ u) _ hinj hu
  obtain ⟨h, hh⟩ := diagCaseE G κ _ ψ₀ (strongIrr_conjE σ hσ P) u α hα (by
    simp only [gm] at hP
    simp [gm, Matrix.mul_assoc, hP]) (P⁻¹ * y * P) z
  refine ⟨h, ?_⟩
  convert hh using 2
  rw [← Matrix.charpoly_units_conj P⁻¹]
  congr 1
  simp [gm, Matrix.mul_assoc]
end
