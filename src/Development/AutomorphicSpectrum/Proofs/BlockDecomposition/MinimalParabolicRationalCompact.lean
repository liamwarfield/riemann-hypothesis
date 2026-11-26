module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentOfIsWittFrame
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneFormMapEqKaehlerDifferentialMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviMinimalIdeleHermitianBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothCutoffTranslateContDiff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutantClosedSubgroupCompactQuotient

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutantClosedSubgroupCompactQuotientStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutant_closed_subgroup_compact_quotient : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (M : Type) [Finite M] (S : M → Matrix (Fin n) (Fin n) E) (L : Subgroup (GAd σ J)), IsClosed (L : Set (GAd σ J)) → (∀ g ∈ L, ∀ k, (matHom _ σ J g).1 * (S k).map (inclR (F := F) (AF F)) = (S k).map (inclR (F := F) (AF F)) * (matHom _ σ J g).1) → (∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ L, ∀ ξ : Fin n → E, ξ ≠ 0 → ε ≤ hgt σ J g ξ) → (∀ γ ∈ ratPts σ J, (∀ k, (matHom _ σ J γ).1 * (S k).map (inclR (F := F) (AF F)) = (S k).map (inclR (F := F) (AF F)) * (matHom _ σ J γ).1) → γ ∈ L) → ∃ Ω : Set (GAd σ J), IsCompact Ω ∧ Ω ⊆ L ∧ ∀ g ∈ L, ∃ δ ∈ ratPts σ J, δ ∈ L ∧ δ⁻¹ * g ∈ Ω := by
  first | exact @GlobalTheory.CompanionTheory.ParCocompact.exists_isCompact_of_centralizer_height | exact GlobalTheory.CompanionTheory.ParCocompact.exists_isCompact_of_centralizer_height | (intros; apply GlobalTheory.CompanionTheory.ParCocompact.exists_isCompact_of_centralizer_height <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviNormalizesUnipotentTer
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviNormalizesUnipotentTer
set_option linter.unusedSectionVars false

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.ParCocompact.UnipNormal

section Ring

variable {n r : ℕ} {R : Type} [CommRing R] {s : R →+* R} {Jm : Matrix (Fin n) (Fin n) R}
  {Xm Ym : Matrix (Fin n) (Fin r) R}

theorem coef_inv (hF : PFr s Jm Xm Ym) {M : Matrix (Fin n) (Fin n) R} (hM : cT s M * Jm * M = Jm)
    {d d' : Fin r → R} (e : M * Xm = Xm * diagonal d) (e' : M * Ym = Ym * diagonal d') (i : Fin r) :
    d i * s (d' i) = 1 := by
  have h := hF.inv_coef hM e
  rw [e', ← Matrix.mul_assoc, hF.xy, Matrix.one_mul] at h
  have h2 := congrFun (congrFun h i) i
  have e3 : cT s (diagonal d') = diagonal (fun i => s (d' i)) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [cT]
    · simp [cT, Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ (Ne.symm hab)]
  rw [e3, Matrix.diagonal_mul_diagonal] at h2
  simpa [mul_comm] using h2

theorem inv_mul_frame {M Mi : Matrix (Fin n) (Fin n) R} (hMi : Mi * M = 1) {d c : Fin r → R}
    (hdc : ∀ i, d i * c i = 1) (e : M * Xm = Xm * diagonal d) : Mi * Xm = Xm * diagonal c := by
  have h1 : diagonal d * diagonal c = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg _ (funext hdc)
  calc Mi * Xm = Mi * (Xm * (diagonal d * diagonal c)) := by rw [h1, Matrix.mul_one]
    _ = Mi * M * Xm * diagonal c := by
      rw [← Matrix.mul_assoc Xm, ← e]
      simp only [Matrix.mul_assoc]
    _ = Xm * diagonal c := by rw [hMi, Matrix.one_mul]

theorem orth_mulVec {M : Matrix (Fin n) (Fin n) R} (hM : cT s M * Jm * M = Jm) {d c : Fin r → R}
    (hdc : ∀ i, d i * c i = 1) (e : M * Xm = Xm * diagonal d) {v : Fin n → R}
    (hv : (cT s Xm * Jm) *ᵥ v = 0) : (cT s Xm * Jm) *ᵥ (M *ᵥ v) = 0 := by
  have h1 : diagonal d * diagonal c = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg _ (funext hdc)
  have h := pgram_unitary hM (Xm * diagonal c) (1 : Matrix (Fin n) (Fin n) R)
  rw [← Matrix.mul_assoc M, e, Matrix.mul_assoc Xm, h1, Matrix.mul_one, Matrix.mul_one, Matrix.mul_one,
    Formalism.UG.cT_mul] at h
  rw [Matrix.mulVec_mulVec, h, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

theorem clause_extend (hF : PFr s Jm Xm Ym) {U : Matrix (Fin n) (Fin n) R} {B : Matrix (Fin r) (Fin r) R}
    (hU : U * Xm = Xm * B) {P : Matrix (Fin n) (Fin n) R}
    (hP : P = 1 - Xm * (cT s Ym * Jm) - Ym * (cT s Xm * Jm))
    (hc : ∀ k, ∃ a : Fin r → R, (U - 1) *ᵥ (fun i => P i k) = Xm *ᵥ a) {w : Fin n → R}
    (hw : (cT s Xm * Jm) *ᵥ w = 0) : ∃ a : Fin r → R, (U - 1) *ᵥ w = Xm *ᵥ a := by
  choose A hA using hc
  have hUP : (U - 1) * P = Xm * (Matrix.of fun j k => A k j) := by
    ext i k
    have := congrFun (hA k) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hUX : (U - 1) * Xm = Xm * (B - 1) := by
    rw [Matrix.sub_mul, Matrix.one_mul, hU, Matrix.mul_sub, Matrix.mul_one]
  have hwd : w = P *ᵥ w + Xm *ᵥ ((cT s Ym * Jm) *ᵥ w) := by
    rw [hP, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec w Ym, hw,
      Matrix.mulVec_zero, ← Matrix.mulVec_mulVec]
    abel
  refine ⟨(Matrix.of fun j k => A k j) *ᵥ w + (B - 1) *ᵥ ((cT s Ym * Jm) *ᵥ w), ?_⟩
  conv_lhs => rw [hwd]
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hUP, hUX, Matrix.mulVec_add]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}

def orthProj (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E) :
    Matrix (Fin n) (Fin n) E :=
  1 - X * (cT (σ : E →+* E) Y * J) - Y * (cT (σ : E →+* E) X * J)

theorem orth_orthProj (hW : IsWittFrame σ J X Y) : (cT (σ : E →+* E) X * J) * orthProj σ J X Y = 0 := by
  have e1 : cT (σ : E →+* E) X * J * (X * (cT (σ : E →+* E) Y * J)) = 0 := by
    rw [← Matrix.mul_assoc, hW.xx, Matrix.zero_mul]
  have e2 : cT (σ : E →+* E) X * J * (Y * (cT (σ : E →+* E) X * J)) = cT (σ : E →+* E) X * J := by
    rw [← Matrix.mul_assoc, hW.xy, Matrix.one_mul]
  rw [orthProj, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, e1, e2]
  abel

theorem leviMin_normalises_unipMin (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E) (hW : IsWittFrame σ J X Y) (m : GAd σ J) (hm : m ∈ leviMin σ J X Y)
    (u : GAd σ J) (hu : u ∈ unipMin σ J X) : m⁻¹ * u * m ∈ unipMin σ J X := by
  have hF := pfrA h hJ hW
  obtain ⟨d, d', e, e'⟩ := hm
  obtain ⟨B, hB, hB1, eU, hz⟩ := hu
  have hM := unitaryA_matHom m
  set M := (matHom _ σ J m).1 with hMdef
  set U := (matHom _ σ J u).1 with hUdef
  set Mi := (matHom _ σ J m⁻¹).1 with hMidef
  have hMi : Mi * M = 1 := by
    rw [hMidef, hMdef, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  obtain ⟨c, hdc⟩ : ∃ c : Fin r → AF F ⊗[F] E, ∀ i, d i * c i = 1 := ⟨_, coef_inv hF hM e e'⟩
  have eMi := inv_mul_frame hMi hdc e
  have hV : (matHom _ σ J (m⁻¹ * u * m)).1 = Mi * U * M := by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul]
  refine ⟨diagonal c * B * diagonal d, ((Matrix.blockTriangular_diagonal _).mul hB).mul
    (Matrix.blockTriangular_diagonal _), ?_, ?_, ?_⟩
  · intro i
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hB1, mul_one, mul_comm]
    exact hdc i
  · rw [hV, Matrix.mul_assoc, e, ← Matrix.mul_assoc, Matrix.mul_assoc Mi, eU, ← Matrix.mul_assoc Mi, eMi]
    simp only [Matrix.mul_assoc]
  · intro z hzz
    have hcol : ∀ k, ∃ a, (U - 1) *ᵥ (fun i => ((orthProj σ J X Y).map (inclR (F := F) (AF F))) i k) =
        adMat F X *ᵥ a := by
      intro k
      refine hz (fun i => orthProj σ J X Y i k) ?_
      funext i
      have := congrFun (congrFun (orth_orthProj hW) i) k
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    have hv : (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F X) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J) *ᵥ
        (fun i => inclR (F := F) (AF F) (z i)) = 0 := by
      have e1 : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F X) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J =
          (cT (σ : E →+* E) X * J).map (inclR (F := F) (AF F)) := by
        unfold JR
        rw [← cT_map_inclR, Matrix.map_mul]
        rfl
      rw [e1]
      funext i
      have := congrArg (inclR (F := F) (AF F)) (congrFun hzz i)
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul] using this
    obtain ⟨a, ha⟩ := clause_extend hF eU (by
      unfold JR
      rw [← cT_map_inclR, ← cT_map_inclR, orthProj, Matrix.map_sub _ (map_sub _), Matrix.map_sub _ (map_sub _),
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]) hcol
      (orth_mulVec hM hdc e hv)
    refine ⟨diagonal c *ᵥ a, ?_⟩
    have e4 : Mi * U * M - 1 = Mi * (U - 1) * M := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hMi]
    rw [hV, e4, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_mulVec, eMi,
      Matrix.mulVec_mulVec]

end GlobalTheory.CompanionTheory.ParCocompact.UnipNormal

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviNormalizesUnipotentTerStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_normalizes_unipotent_ter : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ m ∈ leviMin σ J X Y, ∀ u ∈ unipMin σ J X, m⁻¹ * u * m ∈ unipMin σ J X := by
  first | exact @GlobalTheory.CompanionTheory.ParCocompact.UnipNormal.leviMin_normalises_unipMin | exact GlobalTheory.CompanionTheory.ParCocompact.UnipNormal.leviMin_normalises_unipMin | (intros; apply GlobalTheory.CompanionTheory.ParCocompact.UnipNormal.leviMin_normalises_unipMin <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviParabolicIntersectionClosed
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviParabolicIntersectionClosed
set_option linter.unusedSectionVars false

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
  GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.ParCocompact.LeviOne

section Frame

variable {n r : ℕ} {R : Type} [CommRing R] {s : R →+* R} {Jm : Matrix (Fin n) (Fin n) R}
  {Xm Ym : Matrix (Fin n) (Fin r) R}

theorem pfr_swap (hF : PFr s Jm Xm Ym) : PFr s Jm Ym Xm :=
  ⟨hF.ss, hF.herm, hF.yy, hF.xx, hF.yx⟩

theorem coef_mul_eq_one (hF : PFr s Jm Xm Ym) {g : Matrix (Fin n) (Fin n) R} (hg : cT s g * Jm * g = Jm)
    {d d' : Fin r → R} (e : g * Xm = Xm * diagonal d) (e' : g * Ym = Ym * diagonal d') (i : Fin r) :
    s (d' i) * d i = 1 := by
  have h := hF.inv_coef hg e
  rw [e', ← Matrix.mul_assoc, hF.xy, Matrix.one_mul] at h
  have h2 : cT s (diagonal d') = diagonal (fun i => s (d' i)) := Matrix.ext fun a b => by
    by_cases hab : a = b
    · subst hab
      simp [cT]
    · simp [cT, Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ (Ne.symm hab)]
  rw [h2, diagonal_mul_diagonal] at h
  simpa using congrFun (congrFun h i) i

theorem inv_act {g g' : Matrix (Fin n) (Fin n) R} (hg : g' * g = 1) {d e : Fin r → R}
    (he : ∀ i, e i * d i = 1) (h : g * Xm = Xm * diagonal d) : g' * Xm = Xm * diagonal e := by
  have h1 : diagonal d * diagonal e = (1 : Matrix (Fin r) (Fin r) R) := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [mul_comm, he i]
  calc g' * Xm = g' * (Xm * (diagonal d * diagonal e)) := by rw [h1, Matrix.mul_one]
    _ = g' * g * Xm * diagonal e := by
        rw [← Matrix.mul_assoc Xm, ← h]
        simp only [Matrix.mul_assoc]
    _ = Xm * diagonal e := by rw [hg, Matrix.one_mul]

end Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}

theorem one_mem_minParOne : (1 : GAd σ J) ∈ minParOne σ J X :=
  ⟨1, Matrix.blockTriangular_one, by simp, fun i => ⟨1, by simp, map_one _⟩⟩

theorem mul_mem_levi {a b : GAd σ J} (ha : a ∈ leviMin σ J X Y) (hb : b ∈ leviMin σ J X Y) :
    a * b ∈ leviMin σ J X Y := by
  obtain ⟨d₁, d₁', e₁, e₁'⟩ := ha
  obtain ⟨d₂, d₂', e₂, e₂'⟩ := hb
  refine ⟨d₁ * d₂, d₁' * d₂', ?_, ?_⟩
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, e₂, ← Matrix.mul_assoc, e₁, Matrix.mul_assoc,
      diagonal_mul_diagonal]
    rfl
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, e₂', ← Matrix.mul_assoc, e₁', Matrix.mul_assoc,
      diagonal_mul_diagonal]
    rfl

theorem inv_mem (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {m : GAd σ J}
    (hm : m ∈ leviMin σ J X Y) (hm1 : m ∈ minParOne σ J X) :
    m⁻¹ ∈ leviMin σ J X Y ∧ m⁻¹ ∈ minParOne σ J X := by
  have hF := pfrA h hJ hW
  obtain ⟨d, d', e, e'⟩ := hm
  have hu := unitaryA_matHom m
  have h1 := coef_mul_eq_one hF hu e e'
  have hss := hF.ss
  have hinv : (matHom _ σ J m⁻¹).1 * (matHom _ σ J m).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have h2 : ∀ i, d i * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ (d' i) = 1 := fun i => by rw [mul_comm, h1 i]
  have h3 : ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ (d i) * d' i = 1 := coef_mul_eq_one (pfr_swap hF) hu e' e
  have f := inv_act hinv h1 e
  have f' := inv_act hinv h3 e'
  refine ⟨⟨_, _, f, f'⟩, ?_⟩
  obtain ⟨B, -, eB, hB⟩ := hm1
  have hBd : B = diagonal d := by rw [← Bm_eq hF eB, Bm_eq hF e]
  refine ⟨_, Matrix.blockTriangular_diagonal _, f, fun i => ?_⟩
  obtain ⟨u, hu1, hu2⟩ := hB i
  refine ⟨u⁻¹, ?_, by rw [map_inv, hu2, inv_one]⟩
  have hd : d i = u := by rw [← hu1, hBd, Matrix.diagonal_apply_eq]
  rw [Matrix.diagonal_apply_eq]
  exact (Units.inv_eq_of_mul_eq_one_left (by rw [← hd]; exact h1 i)).symm ▸ rfl

theorem leviMin_eq (hF : PFr (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J) (adMat F X) (adMat F Y)) :
    leviMin σ J X Y = {m | (matHom _ σ J m).1 * adMat F X = adMat F X * diagonal (fun i => Bm σ J X Y m i i)} ∩
      {m | (matHom _ σ J m).1 * adMat F Y = adMat F Y * diagonal (fun i => Bm σ J Y X m i i)} := by
  ext m
  constructor
  · rintro ⟨d, d', e, e'⟩
    have a1 : (fun i => Bm σ J X Y m i i) = d := funext fun i => by
      rw [Bm_eq hF e, Matrix.diagonal_apply_eq]
    have a2 : (fun i => Bm σ J Y X m i i) = d' := funext fun i => by
      rw [Bm_eq (pfr_swap hF) e', Matrix.diagonal_apply_eq]
    exact ⟨by simpa only [Set.mem_setOf_eq, a1] using e, by simpa only [Set.mem_setOf_eq, a2] using e'⟩
  · rintro ⟨e, e'⟩
    exact ⟨_, _, e, e'⟩

theorem isClosed_leviMin (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    IsClosed (leviMin σ J X Y) := by
  have hF := pfrA h hJ hW
  have := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : T2Space (AF F ⊗[F] E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  have hc : ∀ {X' Y' : Matrix (Fin n) (Fin r) E}, Continuous fun m : GAd σ J =>
      adMat F X' * diagonal (fun i => Bm σ J X' Y' m i i) := fun {X' Y'} => by
    have hd : Continuous fun m : GAd σ J => diagonal (fun i => Bm σ J X' Y' m i i) :=
      continuous_matrix fun a b => by
        by_cases hab : a = b
        · subst hab
          simpa using (continuous_Bm (σ := σ) (J := J) (X := X') (Y := Y')).matrix_elem a a
        · simpa [Matrix.diagonal_apply_ne _ hab] using continuous_const
    exact continuous_const.matrix_mul hd
  rw [leviMin_eq hF]
  exact (isClosed_eq ((continuous_matHom_val (σ := σ) (J := J)).matrix_mul continuous_const) hc).inter
    (isClosed_eq ((continuous_matHom_val (σ := σ) (J := J)).matrix_mul continuous_const) hc)

end GlobalTheory.CompanionTheory.ParCocompact.LeviOne


open GlobalTheory.CompanionTheory.ParCocompact.LeviOne in
theorem GlobalTheory.CompanionTheory.ParCocompact.exists_leviOne_subgroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ L : Subgroup (GAd σ J), (L : Set (GAd σ J)) = leviMin σ J X Y ∩ minParOne σ J X ∧ IsClosed (L : Set (GAd σ J)) := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW
  refine ⟨{ carrier := leviMin σ J X Y ∩ minParOne σ J X
            mul_mem' := fun {a b} ha hb => ⟨mul_mem_levi ha.1 hb.1, (minParOne_props h hJ hW).2 a ha.2 b hb.2⟩
            one_mem' := ⟨one_mem_leviMin σ J X Y, one_mem_minParOne⟩
            inv_mem' := fun {a} ha => inv_mem h hJ hW ha.1 ha.2 }, rfl, ?_⟩
  exact (isClosed_leviMin h hJ hW).inter (minParOne_props h hJ hW).1

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviParabolicIntersectionClosedStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_parabolic_intersection_closed : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ L : Subgroup (GAd σ J), (L : Set (GAd σ J)) = leviMin σ J X Y ∩ minParOne σ J X ∧ IsClosed (L : Set (GAd σ J)) := by
  first | exact @GlobalTheory.CompanionTheory.ParCocompact.exists_leviOne_subgroup | exact GlobalTheory.CompanionTheory.ParCocompact.exists_leviOne_subgroup | (intros; apply GlobalTheory.CompanionTheory.ParCocompact.exists_leviOne_subgroup <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianFamilyAnisotropicJoint
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianFamilyAnisotropicJoint
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.ParCocompact.HermNondeg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem hE_eq_dot (σ : E →ₐ[F] E) {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hE σ A x y = (fun i => σ (x i)) ⬝ᵥ (A *ᵥ y) := by
  have : hE σ A x y = ∑ i, ∑ j, σ (x i) * A i j * y j := rfl
  rw [this]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hE_normMat (σ : E →ₐ[F] E) {n : ℕ} (l ξ : Fin n → E) :
    hE σ (normMat σ l) ξ ξ = σ (l ⬝ᵥ ξ) * (l ⬝ᵥ ξ) := by
  have : hE σ (normMat σ l) ξ ξ = ∑ i, ∑ j, σ (ξ i) * (σ (l i) * l j) * ξ j := rfl
  rw [this]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, map_sum, map_mul, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dot_eq_zero_of_hE_normMat (σ : E →ₐ[F] E) {n : ℕ} {l ξ : Fin n → E}
    (h : hE σ (normMat σ l) ξ ξ = 0) : l ⬝ᵥ ξ = 0 := by
  rw [hE_normMat] at h
  rcases mul_eq_zero.1 h with h | h
  · exact (map_eq_zero_iff σ σ.toRingHom.injective).1 h
  · exact h

theorem hE_conj (σ : E →ₐ[F] E) {n : ℕ} (J P : Matrix (Fin n) (Fin n) E) (ξ : Fin n → E) :
    hE σ (cT (σ : E →+* E) P * J * P) ξ ξ = hE σ J (P *ᵥ ξ) (P *ᵥ ξ) := by
  rw [hE_eq_dot, hE_eq_dot, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec _ (cT (σ : E →+* E) P)]
  congr 1
  ext j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, cT, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

theorem anisoProj_mulVec (σ : E →ₐ[F] E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E)
    (ξ : Fin n → E) (hX : ∀ i, rowOf σ J X i ⬝ᵥ ξ = 0) (hY : ∀ i, rowOf σ J Y i ⬝ᵥ ξ = 0) :
    anisoProj σ J X Y *ᵥ ξ = ξ := by
  have h0 : ∀ k, projFam σ J X Y k *ᵥ ξ = 0 := by
    rintro (i | i)
    · simp only [projFam, Sum.elim_inl, lineProj, Matrix.vecMulVec_mulVec, hY i]
      ext k
      simp
    · simp only [projFam, Sum.elim_inr, lineProj, Matrix.vecMulVec_mulVec, hX i]
      ext k
      simp
  rw [anisoProj, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.sum_mulVec, Finset.sum_eq_zero fun k _ => h0 k, sub_zero]

end GlobalTheory.CompanionTheory.ParCocompact.HermNondeg

namespace GlobalTheory.CompanionTheory.ParCocompact

theorem hermFam_nondeg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ ξ : Fin n → E,
    (∀ j, hE σ (hermFam σ J X Y j) ξ ξ = 0) → ξ = 0 := by
  intro F E _ _ _ _ _ σ _ n J _ r X Y hW ξ h
  have hY : ∀ i, rowOf σ J Y i ⬝ᵥ ξ = 0 := fun i =>
    HermNondeg.dot_eq_zero_of_hE_normMat σ (h (some (Sum.inl i)))
  have hX : ∀ i, rowOf σ J X i ⬝ᵥ ξ = 0 := fun i =>
    HermNondeg.dot_eq_zero_of_hE_normMat σ (h (some (Sum.inr i)))
  have hπ := HermNondeg.anisoProj_mulVec σ J X Y ξ hX hY
  have hn : hE σ J ξ ξ = 0 := by
    have := h none
    change hE σ (cT (σ : E →+* E) (anisoProj σ J X Y) * J * anisoProj σ J X Y) ξ ξ = 0 at this
    rwa [HermNondeg.hE_conj, hπ] at this
  refine hW.aniso ξ ?_ ?_ hn
  · ext i
    exact hX i
  · ext i
    exact hY i

end GlobalTheory.CompanionTheory.ParCocompact
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianFamilyAnisotropicJointStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_family_anisotropic_joint : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ ξ : Fin n → E, (∀ j, hE σ (hermFam σ J X Y j) ξ ξ = 0) → ξ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.ParCocompact.hermFam_nondeg | exact GlobalTheory.CompanionTheory.ParCocompact.hermFam_nondeg | (intros; apply GlobalTheory.CompanionTheory.ParCocompact.hermFam_nondeg <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviMinimalCommutesProjectionFamily
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviMinimalCommutesProjectionFamily
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.ParCocompact.LeviComm

section Ring

variable {n r : ℕ} {R : Type} [CommRing R] {s : R →+* R} {Jm : Matrix (Fin n) (Fin n) R}
  {Xm Ym : Matrix (Fin n) (Fin r) R}

theorem pfr_swap (hF : PFr s Jm Xm Ym) : PFr s Jm Ym Xm :=
  ⟨hF.ss, hF.herm, hF.yy, hF.xx, hF.yx⟩

theorem row_mul {g : Matrix (Fin n) (Fin n) R} (hF : PFr s Jm Xm Ym) (hg : cT s g * Jm * g = Jm) {d d' : Fin r → R}
    (hX : g * Xm = Xm * diagonal d) (hY : g * Ym = Ym * diagonal d') :
    cT s Ym * Jm * g = diagonal d * (cT s Ym * Jm) := by
  have h1 : cT s (diagonal d') * diagonal d = 1 := by
    have e := pgram_unitary hg Ym Xm
    rw [hY, hX, hF.yx, Formalism.UG.cT_mul] at e
    calc cT s (diagonal d') * diagonal d
        = cT s (diagonal d') * (cT s Ym * Jm * Xm) * diagonal d := by rw [hF.yx, Matrix.mul_one]
      _ = 1 := by rw [← e]; simp only [Matrix.mul_assoc]
  have h2 : diagonal d * cT s (diagonal d') = 1 := mul_eq_one_comm.1 h1
  have h3 : cT s (diagonal d') * (cT s Ym * Jm * g) = cT s Ym * Jm := by
    have e : cT s (g * Ym) * Jm * g = cT s Ym * Jm := by
      conv_rhs => rw [← hg]
      simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]
    rw [hY, Formalism.UG.cT_mul] at e
    calc cT s (diagonal d') * (cT s Ym * Jm * g) = cT s (diagonal d') * cT s Ym * Jm * g := by
          simp only [Matrix.mul_assoc]
      _ = cT s Ym * Jm := e
  calc cT s Ym * Jm * g = diagonal d * cT s (diagonal d') * (cT s Ym * Jm * g) := by rw [h2, Matrix.one_mul]
    _ = diagonal d * (cT s Ym * Jm) := by rw [Matrix.mul_assoc, h3]

theorem comm_vecMulVec {m : ℕ} {g : Matrix (Fin n) (Fin n) R} {C : Matrix (Fin n) (Fin m) R}
    {A : Matrix (Fin m) (Fin n) R} {d : Fin m → R} (hC : g * C = C * diagonal d) (hA : A * g = diagonal d * A)
    (i : Fin m) : g * vecMulVec (fun k => C k i) (A i) = vecMulVec (fun k => C k i) (A i) * g := by
  ext a b
  have e1 : ∑ k, g a k * C k i = C a i * d i := by
    have := congrFun (congrFun hC a) i
    rwa [Matrix.mul_apply, Matrix.mul_diagonal] at this
  have e2 : ∑ k, A i k * g k b = d i * A i b := by
    have := congrFun (congrFun hA i) b
    rwa [Matrix.mul_apply, Matrix.diagonal_mul] at this
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply]
  calc ∑ k, g a k * (C k i * A i b) = (∑ k, g a k * C k i) * A i b := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm
    _ = C a i * (d i * A i b) := by rw [e1, mul_assoc]
    _ = C a i * ∑ k, A i k * g k b := by rw [e2]
    _ = ∑ k, C a i * A i k * g k b := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n r : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem lineProj_map (C D : Matrix (Fin n) (Fin r) E) (i : Fin r) :
    (lineProj σ J C D i).map (inclR (F := F) (AF F)) =
      vecMulVec (fun k => adMat F C k i)
        (((cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F D) : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) *
          (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))) i) := by
  have e : (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F D) : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) *
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) =
      (cT (σ : E →+* E) D * J).map (inclR (F := F) (AF F)) := by
    unfold JR
    rw [← cT_map_inclR, ← Matrix.map_mul]
  rw [e]
  ext a b
  exact map_mul (inclR (F := F) (AF F)) (C a i) ((cT (σ : E →+* E) D * J) i b)

theorem leviMin_comm_projFam (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E) (hW : IsWittFrame σ J X Y) (m) (hm : m ∈ leviMin σ J X Y) (k) :
    (matHom _ σ J m).1 * (projFam σ J X Y k).map (inclR (F := F) (AF F)) =
      (projFam σ J X Y k).map (inclR (F := F) (AF F)) * (matHom _ σ J m).1 := by
  obtain ⟨d, d', hX, hY⟩ := hm
  have hF := pfrA h hJ hW
  have hg := unitaryA_matHom m
  rcases k with i | i
  · simp only [projFam, Sum.elim_inl]
    rw [lineProj_map]
    exact comm_vecMulVec hX (row_mul hF hg hX hY) i
  · simp only [projFam, Sum.elim_inr]
    rw [lineProj_map]
    exact comm_vecMulVec hY (row_mul (pfr_swap hF) hg hY hX) i

end GlobalTheory.CompanionTheory.ParCocompact.LeviComm

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviMinimalCommutesProjectionFamilyStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_minimal_commutes_projection_family : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ m ∈ leviMin σ J X Y, ∀ k, (matHom _ σ J m).1 * (projFam σ J X Y k).map (inclR (F := F) (AF F)) = (projFam σ J X Y k).map (inclR (F := F) (AF F)) * (matHom _ σ J m).1 := by
  first | exact @GlobalTheory.CompanionTheory.ParCocompact.LeviComm.leviMin_comm_projFam | exact GlobalTheory.CompanionTheory.ParCocompact.LeviComm.leviMin_comm_projFam | (intros; apply GlobalTheory.CompanionTheory.ParCocompact.LeviComm.leviMin_comm_projFam <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicLeviDecomposition
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicLeviDecomposition
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.LeviDecomp

section Block

variable {n r : ℕ} {R : Type} [CommRing R]

def piM (X Y : Matrix (Fin n) (Fin r) R) (Xs Ys : Matrix (Fin r) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  1 - X * Ys - Y * Xs

def leviM (X Y : Matrix (Fin n) (Fin r) R) (Xs Ys : Matrix (Fin r) (Fin n) R) (D D' : Matrix (Fin r) (Fin r) R)
    (g : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  X * (D * Ys) + Y * (D' * Xs) + piM X Y Xs Ys * (g * piM X Y Xs Ys)

variable {X Y : Matrix (Fin n) (Fin r) R} {Xs Ys : Matrix (Fin r) (Fin n) R}

theorem piM_mul_X (hxx : Xs * X = 0) (hyx : Ys * X = 1) : piM X Y Xs Ys * X = 0 := by
  simp only [piM, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hxx, hyx, Matrix.mul_one, Matrix.mul_zero, sub_self,
    sub_zero]

theorem piM_mul_Y (hxy : Xs * Y = 1) (hyy : Ys * Y = 0) : piM X Y Xs Ys * Y = 0 := by
  simp only [piM, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hxy, hyy, Matrix.mul_one, Matrix.mul_zero, sub_self,
    sub_zero]

theorem Xs_mul_piM (hxx : Xs * X = 0) (hxy : Xs * Y = 1) : Xs * piM X Y Xs Ys = 0 := by
  simp only [piM, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hxx, hxy, Matrix.zero_mul, Matrix.one_mul, sub_self,
    sub_zero]

theorem Ys_mul_piM (hyx : Ys * X = 1) (hyy : Ys * Y = 0) : Ys * piM X Y Xs Ys = 0 := by
  simp only [piM, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hyx, hyy, Matrix.zero_mul, Matrix.one_mul, sub_self,
    sub_zero]

theorem piM_mul (W : Matrix (Fin n) (Fin n) R) : piM X Y Xs Ys * W = W - X * (Ys * W) - Y * (Xs * W) := by
  simp only [piM, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]

theorem piM_idem (hxx : Xs * X = 0) (hxy : Xs * Y = 1) (hyx : Ys * X = 1) (hyy : Ys * Y = 0) :
    piM X Y Xs Ys * piM X Y Xs Ys = piM X Y Xs Ys := by
  rw [piM_mul, Xs_mul_piM hxx hxy, Ys_mul_piM hyx hyy, Matrix.mul_zero, Matrix.mul_zero, sub_zero, sub_zero]

theorem mul_piM_mul {g h : Matrix (Fin n) (Fin n) R} {B C : Matrix (Fin r) (Fin r) R} (hxx : Xs * X = 0)
    (hxy : Xs * Y = 1) (hgh : g * h = 1) (hgX : g * X = X * B) (hC : Xs * h = C * Xs) :
    g * (piM X Y Xs Ys * (h * piM X Y Xs Ys)) =
      piM X Y Xs Ys - X * (B * (Ys * (h * piM X Y Xs Ys))) := by
  have e2 : Xs * (h * piM X Y Xs Ys) = 0 := by
    rw [← Matrix.mul_assoc, hC, Matrix.mul_assoc, Xs_mul_piM hxx hxy, Matrix.mul_zero]
  rw [piM_mul (h * piM X Y Xs Ys), e2, Matrix.mul_zero, sub_zero, Matrix.mul_sub, ← Matrix.mul_assoc g h, hgh,
    Matrix.one_mul, ← Matrix.mul_assoc g X, hgX, Matrix.mul_assoc]

theorem piM_sandwich {g h : Matrix (Fin n) (Fin n) R} {B C : Matrix (Fin r) (Fin r) R} (hxx : Xs * X = 0)
    (hxy : Xs * Y = 1) (hyx : Ys * X = 1) (hyy : Ys * Y = 0) (hgh : g * h = 1) (hgX : g * X = X * B)
    (hC : Xs * h = C * Xs) :
    piM X Y Xs Ys * (g * (piM X Y Xs Ys * (h * piM X Y Xs Ys))) = piM X Y Xs Ys := by
  rw [mul_piM_mul hxx hxy hgh hgX hC, Matrix.mul_sub, piM_idem hxx hxy hyx hyy, ← Matrix.mul_assoc (piM X Y Xs Ys) X,
    piM_mul_X hxx hyx, Matrix.zero_mul, sub_zero]

theorem leviM_mul {g h : Matrix (Fin n) (Fin n) R} {D Di D' Di' : Matrix (Fin r) (Fin r) R} (hxx : Xs * X = 0)
    (hxy : Xs * Y = 1) (hyx : Ys * X = 1) (hyy : Ys * Y = 0) (h1 : D * Di = 1) (h2 : D' * Di' = 1)
    (hs : piM X Y Xs Ys * (g * (piM X Y Xs Ys * (h * piM X Y Xs Ys))) = piM X Y Xs Ys) :
    leviM X Y Xs Ys D D' g * leviM X Y Xs Ys Di Di' h = 1 := by
  have a1 : ∀ {k : Type} [Fintype k] (M : Matrix (Fin r) k R), Ys * (X * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hyx, Matrix.one_mul]
  have a2 : ∀ {k : Type} [Fintype k] (M : Matrix (Fin r) k R), Xs * (Y * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hxy, Matrix.one_mul]
  have a3 : ∀ {k : Type} [Fintype k] (M : Matrix (Fin r) k R), Xs * (X * M) = 0 := fun M => by
    rw [← Matrix.mul_assoc, hxx, Matrix.zero_mul]
  have a4 : ∀ {k : Type} [Fintype k] (M : Matrix (Fin r) k R), Ys * (Y * M) = 0 := fun M => by
    rw [← Matrix.mul_assoc, hyy, Matrix.zero_mul]
  have a5 : ∀ {k : Type} [Fintype k] (M : Matrix (Fin n) k R), Xs * (piM X Y Xs Ys * M) = 0 := fun M => by
    rw [← Matrix.mul_assoc, Xs_mul_piM hxx hxy, Matrix.zero_mul]
  have a6 : ∀ {k : Type} [Fintype k] (M : Matrix (Fin n) k R), Ys * (piM X Y Xs Ys * M) = 0 := fun M => by
    rw [← Matrix.mul_assoc, Ys_mul_piM hyx hyy, Matrix.zero_mul]
  have a7 : ∀ {k : Type} [Fintype k] (M : Matrix (Fin r) k R), piM X Y Xs Ys * (X * M) = 0 := fun M => by
    rw [← Matrix.mul_assoc, piM_mul_X hxx hyx, Matrix.zero_mul]
  have a8 : ∀ {k : Type} [Fintype k] (M : Matrix (Fin r) k R), piM X Y Xs Ys * (Y * M) = 0 := fun M => by
    rw [← Matrix.mul_assoc, piM_mul_Y hxy hyy, Matrix.zero_mul]
  have a9 : ∀ {k : Type} [Fintype k] (M : Matrix (Fin n) k R),
      piM X Y Xs Ys * (piM X Y Xs Ys * M) = piM X Y Xs Ys * M := fun M => by
    rw [← Matrix.mul_assoc, piM_idem hxx hxy hyx hyy]
  have b1 : ∀ {k : Type} [Fintype k] (M : Matrix (Fin r) k R), D * (Di * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have b2 : ∀ {k : Type} [Fintype k] (M : Matrix (Fin r) k R), D' * (Di' * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  simp only [leviM, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2,
    Matrix.mul_zero, add_zero, zero_add, hs]
  unfold piM
  abel

theorem leviM_mul_X {g : Matrix (Fin n) (Fin n) R} (D D' : Matrix (Fin r) (Fin r) R) (hxx : Xs * X = 0)
    (hyx : Ys * X = 1) : leviM X Y Xs Ys D D' g * X = X * D := by
  simp only [leviM, Matrix.add_mul, Matrix.mul_assoc, hxx, hyx, piM_mul_X hxx hyx, Matrix.mul_one, Matrix.mul_zero,
    add_zero]

theorem leviM_mul_Y {g : Matrix (Fin n) (Fin n) R} (D D' : Matrix (Fin r) (Fin r) R) (hxy : Xs * Y = 1)
    (hyy : Ys * Y = 0) : leviM X Y Xs Ys D D' g * Y = Y * D' := by
  simp only [leviM, Matrix.add_mul, Matrix.mul_assoc, hxy, hyy, piM_mul_Y hxy hyy, Matrix.mul_one, Matrix.mul_zero,
    add_zero, zero_add]

theorem mul_leviM_sub_one {g h : Matrix (Fin n) (Fin n) R} {B C : Matrix (Fin r) (Fin r) R}
    (Di Di' : Matrix (Fin r) (Fin r) R) (hxx : Xs * X = 0) (hxy : Xs * Y = 1) (hgh : g * h = 1)
    (hgX : g * X = X * B) (hC : Xs * h = C * Xs) :
    g * leviM X Y Xs Ys Di Di' h - 1 =
      X * (B * (Di * Ys) - B * (Ys * (h * piM X Y Xs Ys)) - Ys) + (g * (Y * Di') - Y) * Xs := by
  have e1 : (1 : Matrix (Fin n) (Fin n) R) = X * Ys + Y * Xs + piM X Y Xs Ys := by
    unfold piM
    abel
  have e2 : g * (X * (Di * Ys)) = X * (B * (Di * Ys)) := by
    rw [← Matrix.mul_assoc, hgX, Matrix.mul_assoc]
  rw [leviM, Matrix.mul_add, Matrix.mul_add, mul_piM_mul hxx hxy hgh hgX hC, e2]
  generalize Ys * (h * piM X Y Xs Ys) = Q
  rw [e1]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

theorem exists_mulVec_eq {A : Matrix (Fin n) (Fin n) R} {T : Matrix (Fin r) (Fin n) R} {V : Matrix (Fin n) (Fin r) R}
    (hA : A = X * T + V * Xs) {w : Fin n → R} (hw : Xs *ᵥ w = 0) : ∃ a, A *ᵥ w = X *ᵥ a :=
  ⟨T *ᵥ w, by
    rw [hA, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero, add_zero]⟩

end Block

section Frame

variable {n r : ℕ} {R : Type} [CommRing R] {s : R →+* R} {Jm : Matrix (Fin n) (Fin n) R}
  {X Y : Matrix (Fin n) (Fin r) R}

theorem cT_sub' {a b : Type} (P Q : Matrix a b R) : cT s (P - Q) = cT s P - cT s Q :=
  Matrix.ext fun _ _ => by simp [cT]

theorem cT_add' {a b : Type} (P Q : Matrix a b R) : cT s (P + Q) = cT s P + cT s Q :=
  Matrix.ext fun _ _ => by simp [cT]

theorem cT_diagonal' (d : Fin r → R) : cT s (diagonal d) = diagonal (fun i => s (d i)) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [cT]
  · simp [cT, Matrix.diagonal_apply, hij, Ne.symm hij]

theorem cT_piM_mul (hF : PFr s Jm X Y) :
    cT s (piM X Y (cT s X * Jm) (cT s Y * Jm)) * Jm = Jm * piM X Y (cT s X * Jm) (cT s Y * Jm) := by
  simp only [piM, cT_sub', Formalism.UG.cT_one, Formalism.UG.cT_mul, hF.cc, hF.herm, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, Matrix.mul_assoc]
  abel

theorem cT_leviM_mul (hF : PFr s Jm X Y) {g h : Matrix (Fin n) (Fin n) R} (D D' : Matrix (Fin r) (Fin r) R)
    (hgJ : cT s g * Jm = Jm * h) :
    cT s (leviM X Y (cT s X * Jm) (cT s Y * Jm) D D' g) * Jm =
      Jm * leviM X Y (cT s X * Jm) (cT s Y * Jm) (cT s D') (cT s D) h := by
  have hp := cT_piM_mul hF
  have e3 : cT s (piM X Y (cT s X * Jm) (cT s Y * Jm) * (g * piM X Y (cT s X * Jm) (cT s Y * Jm))) * Jm =
      Jm * (piM X Y (cT s X * Jm) (cT s Y * Jm) * (h * piM X Y (cT s X * Jm) (cT s Y * Jm))) := by
    generalize piM X Y (cT s X * Jm) (cT s Y * Jm) = P at hp
    calc cT s (P * (g * P)) * Jm = cT s P * (cT s g * (cT s P * Jm)) := by
          rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul]
          simp only [Matrix.mul_assoc]
      _ = cT s P * ((cT s g * Jm) * P) := by rw [hp, Matrix.mul_assoc]
      _ = (cT s P * Jm) * (h * P) := by rw [hgJ]; simp only [Matrix.mul_assoc]
      _ = Jm * (P * (h * P)) := by rw [hp, Matrix.mul_assoc]
  rw [leviM, leviM, cT_add', cT_add', Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, e3]
  congr 1
  simp only [Formalism.UG.cT_mul, hF.cc, hF.herm, Matrix.mul_assoc]
  rw [add_comm]

theorem frame_levi (hF : PFr s Jm X Y) {g h : Matrix (Fin n) (Fin n) R} {B Q D Di : Matrix (Fin r) (Fin r) R}
    (hgh : g * h = 1) (hhg : h * g = 1) (hg : cT s g * Jm * g = Jm) (hh : cT s h * Jm * h = Jm)
    (hgX : g * X = X * B) (hhX : h * X = X * Q) (hD : D * Di = 1) (hDi : Di * D = 1) :
    leviM X Y (cT s X * Jm) (cT s Y * Jm) D (cT s Di) g * leviM X Y (cT s X * Jm) (cT s Y * Jm) Di (cT s D) h = 1 ∧
    leviM X Y (cT s X * Jm) (cT s Y * Jm) Di (cT s D) h * leviM X Y (cT s X * Jm) (cT s Y * Jm) D (cT s Di) g = 1 ∧
    cT s (leviM X Y (cT s X * Jm) (cT s Y * Jm) D (cT s Di) g) * Jm *
      leviM X Y (cT s X * Jm) (cT s Y * Jm) D (cT s Di) g = Jm ∧
    cT s X * Jm * h = cT s B * (cT s X * Jm) := by
  have hgJ : cT s g * Jm = Jm * h := by
    conv_rhs => rw [← hg]
    rw [Matrix.mul_assoc _ g h, hgh, Matrix.mul_one]
  have hhJ : cT s h * Jm = Jm * g := by
    conv_rhs => rw [← hh]
    rw [Matrix.mul_assoc _ h g, hhg, Matrix.mul_one]
  have hC : cT s X * Jm * h = cT s B * (cT s X * Jm) := by
    rw [Matrix.mul_assoc, ← hgJ, ← Matrix.mul_assoc, ← Formalism.UG.cT_mul, hgX, Formalism.UG.cT_mul, Matrix.mul_assoc]
  have hC' : cT s X * Jm * g = cT s Q * (cT s X * Jm) := by
    rw [Matrix.mul_assoc, ← hhJ, ← Matrix.mul_assoc, ← Formalism.UG.cT_mul, hhX, Formalism.UG.cT_mul, Matrix.mul_assoc]
  have hxx : cT s X * Jm * X = 0 := hF.xx
  have hxy : cT s X * Jm * Y = 1 := hF.xy
  have hyx : cT s Y * Jm * X = 1 := hF.yx
  have hyy : cT s Y * Jm * Y = 0 := hF.yy
  have c1 : cT s Di * cT s D = 1 := by rw [← Formalism.UG.cT_mul, hD, Formalism.UG.cT_one]
  have c2 : cT s D * cT s Di = 1 := by rw [← Formalism.UG.cT_mul, hDi, Formalism.UG.cT_one]
  have m1 := leviM_mul hxx hxy hyx hyy hD c1 (piM_sandwich hxx hxy hyx hyy hgh hgX hC)
  have m2 := leviM_mul hxx hxy hyx hyy hDi c2 (piM_sandwich hxx hxy hyx hyy hhg hhX hC')
  refine ⟨m1, m2, ?_, hC⟩
  rw [cT_leviM_mul hF D (cT s Di) hgJ, hF.cc, Matrix.mul_assoc, m2, Matrix.mul_one]

end Frame

theorem levi_decomp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E),
    IsWittFrame σ J X Y → ∀ p ∈ minParOne σ J X, ∃ u ∈ unipMin σ J X, ∃ m ∈ leviMin σ J X Y,
      m ∈ minParOne σ J X ∧ p = u * m := by
  intro F E _ _ _ _ _ σ hcm n J hJ r X Y hW p hp
  have hF := pfrA hcm hJ hW
  obtain ⟨B, hB, e, hu⟩ := id hp
  choose v hv1 hv2 using hu
  obtain ⟨Q, -, eQ⟩ := inv_mem_minPar hcm hJ hW (minParOne_sub hp)
  have hgh : (matHom _ σ J p).1 * (matHom _ σ J p⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hhg : (matHom _ σ J p⁻¹).1 * (matHom _ σ J p).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hD : diagonal (fun i => (v i : AF F ⊗[F] E)) * diagonal (fun i => ((v i)⁻¹ : (AF F ⊗[F] E)ˣ).1) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    simp
  have hDi : diagonal (fun i => ((v i)⁻¹ : (AF F ⊗[F] E)ˣ).1) * diagonal (fun i => (v i : AF F ⊗[F] E)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    simp
  obtain ⟨m1, m2, m3, hC⟩ := frame_levi hF hgh hhg (unitaryA_matHom p) (unitaryA_matHom p⁻¹) e eQ hD hDi
  let m : GAd σ J := ⟨⟨_, _, m1, m2⟩, m3⟩
  have hm : (matHom _ σ J m).1 = leviM (adMat F X) (adMat F Y) (cT (sigR (AF F) σ) (adMat F X) * JR (AF F) J)
      (cT (sigR (AF F) σ) (adMat F Y) * JR (AF F) J) (diagonal (fun i => (v i : AF F ⊗[F] E)))
      (cT (sigR (AF F) σ) (diagonal (fun i => ((v i)⁻¹ : (AF F ⊗[F] E)ˣ).1))) (matHom _ σ J p).1 := rfl
  have hmi : (matHom _ σ J m⁻¹).1 = leviM (adMat F X) (adMat F Y) (cT (sigR (AF F) σ) (adMat F X) * JR (AF F) J)
      (cT (sigR (AF F) σ) (adMat F Y) * JR (AF F) J) (diagonal (fun i => ((v i)⁻¹ : (AF F ⊗[F] E)ˣ).1))
      (cT (sigR (AF F) σ) (diagonal (fun i => (v i : AF F ⊗[F] E)))) (matHom _ σ J p⁻¹).1 := rfl
  have hmX : (matHom _ σ J m).1 * adMat F X = adMat F X * diagonal (fun i => (v i : AF F ⊗[F] E)) := by
    rw [hm]
    exact leviM_mul_X _ _ hF.xx hF.yx
  have hmY : (matHom _ σ J m).1 * adMat F Y = adMat F Y * diagonal (fun i => sigR (AF F) σ (((v i)⁻¹ : (AF F ⊗[F] E)ˣ).1)) := by
    rw [hm]
    exact (leviM_mul_Y (X := adMat F X) _ _ hF.xy hF.yy).trans (congrArg (adMat F Y * ·) (cT_diagonal' _))
  have hmiX : (matHom _ σ J m⁻¹).1 * adMat F X = adMat F X * diagonal (fun i => ((v i)⁻¹ : (AF F ⊗[F] E)ˣ).1) := by
    rw [hmi]
    exact leviM_mul_X _ _ hF.xx hF.yx
  refine ⟨p * m⁻¹, ?_, m, ⟨_, _, hmX, hmY⟩, ⟨_, Matrix.blockTriangular_diagonal _, hmX, fun i =>
    ⟨v i, Matrix.diagonal_apply_eq _ _, hv2 i⟩⟩, (inv_mul_cancel_right p m).symm⟩
  have hval : (matHom _ σ J (p * m⁻¹)).1 = (matHom _ σ J p).1 * (matHom _ σ J m⁻¹).1 := by
    rw [map_mul, Units.val_mul]
  refine ⟨B * diagonal (fun i => ((v i)⁻¹ : (AF F ⊗[F] E)ˣ).1), hB.mul (Matrix.blockTriangular_diagonal _), fun i => ?_, ?_,
    fun z hz => ?_⟩
  · rw [Matrix.mul_diagonal, hv1]
    simp
  · rw [hval, Matrix.mul_assoc, hmiX, ← Matrix.mul_assoc, e, Matrix.mul_assoc]
  · have hs : (cT (sigR (AF F) σ) (adMat F X) * JR (AF F) J) *ᵥ (fun i => inclR (F := F) (AF F) (z i)) = 0 := by
      have e1 : cT (sigR (AF F) σ) (adMat F X) * JR (AF F) J = (cT (σ : E →+* E) X * J).map (inclR (F := F) (AF F)) := by
        unfold JR
        rw [← cT_map_inclR]
        exact (Matrix.map_mul (L := cT (σ : E →+* E) X) (M := J) (f := inclR (F := F) (AF F))).symm
      rw [e1]
      funext i
      have := RingHom.map_mulVec (inclR (F := F) (AF F)) (cT (σ : E →+* E) X * J) z i
      rw [hz, Pi.zero_apply, map_zero] at this
      exact this.symm
    rw [hval, hmi]
    exact exists_mulVec_eq (mul_leviM_sub_one (Ys := cT (sigR (AF F) σ) (adMat F Y) * JR (AF F) J) _ _ hF.xx hF.xy hgh e hC) hs

end GlobalTheory.CompanionTheory.LeviDecomp

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicLeviDecompositionStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minimal_parabolic_levi_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ p ∈ minParOne σ J X, ∃ u ∈ unipMin σ J X, ∃ m ∈ leviMin σ J X Y, m ∈ minParOne σ J X ∧ p = u * m := by
  first | exact @GlobalTheory.CompanionTheory.LeviDecomp.levi_decomp | exact GlobalTheory.CompanionTheory.LeviDecomp.levi_decomp | (intros; apply GlobalTheory.CompanionTheory.LeviDecomp.levi_decomp <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicRationalCompact
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.ParCocompact

theorem levi_cocompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ C : Set (GAd σ J), IsCompact C ∧ C ⊆ leviMin σ J X Y ∩ minParOne σ J X ∧ ∀ m ∈ leviMin σ J X Y, m ∈ minParOne σ J X → ∃ δ ∈ ratPts σ J, δ ∈ leviMin σ J X Y ∧ ∃ c ∈ C, m = δ * c := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW
  obtain ⟨L, hL, hLc⟩ := GlobalTheory.T.levi_parabolic_intersection_closed F E σ h n J hJ r X Y hW
  have hmem : ∀ g, g ∈ L ↔ g ∈ leviMin σ J X Y ∧ g ∈ minParOne σ J X := fun g => by
    rw [← SetLike.mem_coe, hL]; rfl
  obtain ⟨ε, hε, hh⟩ := GlobalTheory.T.idele_bound_of_joint_anisotropic F E σ h n J hJ _ (hermFam σ J X Y) (L : Set (GAd σ J))
    (GlobalTheory.T.hermitian_family_anisotropic_joint F E σ h n J hJ r X Y hW)
    (fun g hg j => GlobalTheory.T.levi_minimal_idele_hermitian_bound F E σ h n J hJ r X Y hW g ((hmem g).1 hg).1 ((hmem g).1 hg).2 j)
  obtain ⟨Ω, hΩ, hsub, hred⟩ := GlobalTheory.T.commutant_closed_subgroup_compact_quotient F E σ h n J hJ _ (projFam σ J X Y) L hLc
    (fun g hg k => GlobalTheory.T.levi_minimal_commutes_projection_family F E σ h n J hJ r X Y hW g ((hmem g).1 hg).1 k) ⟨ε, hε, hh⟩
    (fun γ hγ hc => (hmem γ).2 (GlobalTheory.T.mem_levi_minimal_of_commutes_projections F E σ h n J hJ r X Y hW γ hγ hc))
  refine ⟨Ω, hΩ, fun c hc => (hmem c).1 (hsub hc), fun m hm hm1 => ?_⟩
  obtain ⟨δ, hδ, hδL, hd⟩ := hred m ((hmem m).2 ⟨hm, hm1⟩)
  exact ⟨δ, hδ, ((hmem δ).1 hδL).1, _, hd, by group⟩

theorem minParOne_cocompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ Ω : Set (GAd σ J), IsCompact Ω ∧ Ω ⊆ minParOne σ J X ∧ ∀ p ∈ minParOne σ J X, ∃ δ ∈ ratPts σ J, δ ∈ minPar σ J X ∧ ∃ ω ∈ Ω, p = δ * ω := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW
  obtain ⟨hcl, hmul⟩ := minParOne_props h hJ hW
  obtain ⟨C, hC, hU⟩ := GlobalTheory.CompanionTheory.UnipCocompact.unipMin_cocompact F E σ h n J hJ r X Y hW
  obtain ⟨C', hC', hsub, hM⟩ := levi_cocompact F E σ h n J hJ r X Y hW
  refine ⟨(C ∩ minParOne σ J X) * C', (hC.inter_right hcl).mul hC', ?_, fun p hp => ?_⟩
  · rintro _ ⟨c, hc, c', hc', rfl⟩
    exact hmul _ hc.2 _ (hsub hc').2
  · obtain ⟨u, hu, m, hm, hm1, rfl⟩ := GlobalTheory.T.minimal_parabolic_levi_decomposition F E σ h n J hJ r X Y hW p hp
    obtain ⟨δ, hδ, hδL, c', hc', rfl⟩ := hM m hm hm1
    have hu' := GlobalTheory.T.levi_normalizes_unipotent_ter F E σ h n J hJ r X Y hW δ hδL u hu
    obtain ⟨δ', hδ', hδU, c, hc, hcU, e⟩ := hU _ hu'
    refine ⟨δ * δ', mul_mem hδ hδ', mul_mem_minPar (leviMin_subset X Y hδL)
      (minParOne_subset (unipMin_subset_minParOne X hδU)), c * c',
      ⟨c, ⟨hc, unipMin_subset_minParOne X hcU⟩, c', hc', rfl⟩, ?_⟩
    have e2 : u = δ * (δ' * c) * δ⁻¹ := by
      rw [← e]; group
    rw [e2]; group

end GlobalTheory.CompanionTheory.ParCocompact

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicRationalCompactStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minimal_parabolic_rational_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ Ω : Set (GAd σ J), IsCompact Ω ∧ Ω ⊆ minParOne σ J X ∧ ∀ p ∈ minParOne σ J X, ∃ δ ∈ ratPts σ J, δ ∈ minPar σ J X ∧ ∃ ω ∈ Ω, p = δ * ω := by
  first | exact @GlobalTheory.CompanionTheory.ParCocompact.minParOne_cocompact | exact GlobalTheory.CompanionTheory.ParCocompact.minParOne_cocompact | (intros; apply GlobalTheory.CompanionTheory.ParCocompact.minParOne_cocompact <;> assumption)
end
