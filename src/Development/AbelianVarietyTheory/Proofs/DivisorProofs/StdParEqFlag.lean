module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviDecompositionGradedIsotropicFlag
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagUnipotentRadicalLeStandardParabolicUnipotent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTSubmatrixMul
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct

namespace GlobalTheory.TieStd

theorem depth_lt_iff {r : ℕ} (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r) (d : Fin s → ℕ)
    (hd : ∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) (i j : Fin s) :
    d j < d i ↔ ∃ k ∈ S, Fin.castLE hs j ≤ k ∧ k < Fin.castLE hs i := by
  rw [hd, hd]
  constructor
  · intro h
    by_contra hne
    push Not at hne
    refine absurd h (not_lt.2 (Finset.card_le_card fun k hk => ?_))
    rw [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, lt_of_not_ge fun h' => absurd hk.2 (not_lt.2 (hne k hk.1 h'))⟩
  · rintro ⟨k, hk, h1, h2⟩
    refine Finset.card_lt_card ⟨fun x hx => ?_, fun h => ?_⟩
    · rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, lt_of_lt_of_le hx.2 (h1.trans h2.le)⟩
    · have := h (Finset.mem_filter.2 ⟨hk, h2⟩)
      exact absurd (Finset.mem_filter.1 this).2 (not_lt.2 h1)

theorem cT_submatrix_mul {E : Type} [Field E] (σ : E →+* E) {n r s : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (A B : Matrix (Fin n) (Fin r) E) (f g : Fin s → Fin r) :
    Formalism.UG.cT σ (A.submatrix id f) * J * B.submatrix id g = (Formalism.UG.cT σ A * J * B).submatrix f g := by
  ext i j
  simp [Formalism.UG.cT, Matrix.mul_apply]

end GlobalTheory.TieStd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalGradedIsotropicFlagLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalGradedIsotropicFlagLe
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct

namespace GlobalTheory.TieStd

theorem unipFlag_castLE_le_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r),
    (∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) → ∀ d : Fin s → ℕ, (∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) →
    GlobalTheory.UAut.unipFlag σ J (X.submatrix id (Fin.castLE hs)) d ≤ GlobalTheory.StdPar.unip σ J X S := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW S s hs hS d hd
  rcases S.eq_empty_or_nonempty with rfl | hne
  · have hs0 : s = 0 := by
      by_contra h0
      obtain ⟨k, hk, -⟩ := (hS ⟨0, by omega⟩).1 (by simp only; omega)
      simp at hk
    subst hs0
    rw [GlobalTheory.StdPar.unip_empty]
    refine (Subgroup.closure_le _).2 fun g hg => ?_
    rw [SetLike.mem_coe, Subgroup.mem_bot]
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    obtain ⟨a, ha⟩ := hg.2 (Pi.single j 1) (Subsingleton.elim _ _)
    have h0 : adMat F (X.submatrix id (Fin.castLE hs)) *ᵥ a = 0 := funext fun _ => by simp [Matrix.mulVec, dotProduct]
    have hv : (fun i => inclR (F := F) (AF F) ((Pi.single j (1 : E) : Fin n → E) i)) = Pi.single j 1 := by
      funext l
      by_cases hl : l = j
      · subst hl; simp
      · simp [Pi.single_apply, hl]
    rw [h0, hv, sub_mulVec, one_mulVec, sub_eq_zero, mulVec_single_one] at ha
    exact (congrFun ha i).trans (Pi.single_apply _ _ _)
  · obtain ⟨m, hmS, hmax⟩ : ∃ m ∈ S, ∀ k ∈ S, k ≤ m := ⟨S.max' hne, S.max'_mem hne, fun k hk => S.le_max' k hk⟩
    have hsm : s = m.val + 1 := by
      apply le_antisymm
      · by_contra hlt
        push_neg at hlt
        obtain ⟨k, hk, hle⟩ := (hS ⟨m.val + 1, by omega⟩).1 (by simp only; omega)
        have h2 := hmax k hk
        rw [Fin.le_def] at hle h2
        simp only at hle
        omega
      · have := (hS m).2 ⟨m, hmS, le_rfl⟩
        omega
    subst hsm
    have hd' : d = fun i => (S.filter fun k => k.val < i.val).card := by
      funext i
      rw [hd i]
      congr 1
    subst hd'
    exact GlobalTheory.FlagRad.unipFlag_le_unip F E σ h n J hJ r X Y hW S m hmS hmax

end GlobalTheory.TieStd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalGradedIsotropicFlagLeStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_radical_graded_isotropic_flag_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r), (∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) → ∀ d : Fin s → ℕ, (∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) → GlobalTheory.UAut.unipFlag σ J (X.submatrix id (Fin.castLE hs)) d ≤ GlobalTheory.StdPar.unip σ J X S := by
  first | exact @GlobalTheory.TieStd.unipFlag_castLE_le_unip | exact GlobalTheory.TieStd.unipFlag_castLE_le_unip | (intros; apply GlobalTheory.TieStd.unipFlag_castLE_le_unip <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianWittFrameUnipotentLeFlagUnipotent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoeffOfMemColSpan
open Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.StdPar
open scoped TensorProduct

namespace GlobalTheory.ColumnSpanCoefficients

theorem exists_coeff_of_mem_colSpan {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n r s : ℕ} (hs : s ≤ r) (X : Matrix (Fin n) (Fin r) E) (I : Set (Fin r)) (P : Fin s → Prop)
    (hI : ∀ i ∈ I, ∃ j : Fin s, Fin.castLE hs j = i ∧ P j) {y : Fin n → AF F ⊗[F] E} (hy : y ∈ colSpan F X I) :
    ∃ a : Fin s → AF F ⊗[F] E, (∀ j, ¬ P j → a j = 0) ∧ adMat F (X.submatrix id (Fin.castLE hs)) *ᵥ a = y := by
  classical
  rw [colSpan] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨j, rfl, hj⟩ := hI i hi
    refine ⟨Pi.single j 1, fun j' hj' => ?_, ?_⟩
    · rw [Pi.single_apply, if_neg]
      rintro rfl
      exact hj' hj
    · rw [Matrix.mulVec_single_one]
      ext r
      rfl
  | zero => exact ⟨0, fun _ _ => rfl, Matrix.mulVec_zero _⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hz
    exact ⟨a + b, fun j hj => by simp [ha j hj, hb j hj], Matrix.mulVec_add _ _ _⟩
  | smul c x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨c • a, fun j hj => by simp [ha j hj], Matrix.mulVec_smul _ _ _⟩

end GlobalTheory.ColumnSpanCoefficients
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianWittFrameUnipotentLeFlagUnipotent
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct

namespace GlobalTheory.TieStd

theorem exists_coeff_of_mem_colSpan {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n r s : ℕ} (hs : s ≤ r) (X : Matrix (Fin n) (Fin r) E) (I : Set (Fin r)) (P : Fin s → Prop)
    (hI : ∀ i ∈ I, ∃ j, Fin.castLE hs j = i ∧ P j) {y : Fin n → AF F ⊗[F] E}
    (hy : y ∈ GlobalTheory.StdPar.colSpan F X I) :
    ∃ a : Fin s → AF F ⊗[F] E, (∀ j, ¬ P j → a j = 0) ∧ adMat F (X.submatrix id (Fin.castLE hs)) *ᵥ a = y := by
  first
  | exact @_root_.GlobalTheory.ColumnSpanCoefficients.exists_coeff_of_mem_colSpan
  | exact _root_.GlobalTheory.ColumnSpanCoefficients.exists_coeff_of_mem_colSpan
  | (apply _root_.GlobalTheory.ColumnSpanCoefficients.exists_coeff_of_mem_colSpan <;> assumption)
  | (intros; apply _root_.GlobalTheory.ColumnSpanCoefficients.exists_coeff_of_mem_colSpan <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ColumnSpanCoefficients.exists_coeff_of_mem_colSpan <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ColumnSpanCoefficients.exists_coeff_of_mem_colSpan ..)

theorem unip_le_unipFlag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r), (∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) → ∀ d : Fin s → ℕ, (∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) → GlobalTheory.StdPar.unip σ J X S ≤ GlobalTheory.UAut.unipFlag σ J (X.submatrix id (Fin.castLE hs)) d := by
  intro F E _ _ _ _ _ σ _ n J _ r X Y _ S s hs hS d hd g hg
  refine Subgroup.subset_closure (?_ : g ∈ GlobalTheory.UAut.unipSet σ J (X.submatrix id (Fin.castLE hs)) d)
  have hlt : ∀ i : Fin r, (∃ k ∈ S, i ≤ k) → ∃ j : Fin s, Fin.castLE hs j = i :=
    fun i h => ⟨⟨i.val, (hS i).2 h⟩, rfl⟩
  refine ⟨fun i => ?_, fun x hx => ?_⟩
  · have h1 := (Subgroup.mem_iInf.1 hg.1 (Fin.castLE hs i)).2 _ (Submodule.subset_span ⟨Fin.castLE hs i, rfl, rfl⟩)
    obtain ⟨a, ha, e⟩ := exists_coeff_of_mem_colSpan hs X {i' | ∃ k ∈ S, i' ≤ k ∧ k < Fin.castLE hs i} (fun j => d j < d i) (fun i' ⟨k, hk, h1, h2⟩ => by
      obtain ⟨j, rfl⟩ := hlt i' ⟨k, hk, h1⟩
      exact ⟨j, rfl, (depth_lt_iff S s hs d hd i j).2 ⟨k, hk, h1, h2⟩⟩) h1
    refine ⟨a, fun j hj => ha j (not_lt.2 hj), ?_⟩
    rw [sub_mulVec, one_mulVec, e]
    rfl
  · have hp : (fun i => inclR (F := F) (AF F) (x i)) ∈ GlobalTheory.StdPar.colPerp σ J X {i | ∃ k ∈ S, i ≤ k} := by
      simp only [GlobalTheory.StdPar.colPerp, Submodule.mem_iInf, LinearMap.mem_ker]
      intro i hi
      obtain ⟨j, rfl⟩ := hlt i hi
      refine (RingHom.map_mulVec (inclR (F := F) (AF F)) _ x (Fin.castLE hs j)).symm.trans ?_
      rw [show ((Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ x) (Fin.castLE hs j) =
        ((Formalism.UG.cT (σ : E →+* E) (X.submatrix id (Fin.castLE hs)) * J) *ᵥ x) j from rfl, hx]
      exact map_zero _
    obtain ⟨a, -, e⟩ := exists_coeff_of_mem_colSpan hs X _ (fun _ => True)
      (fun i' h => let ⟨j, hj⟩ := hlt i' h; ⟨j, hj, trivial⟩) (hg.2.2 _ hp)
    exact ⟨a, by rw [sub_mulVec, one_mulVec, e]⟩

end GlobalTheory.TieStd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianWittFrameUnipotentLeFlagUnipotentStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianWittFrame_unipotent_le_flag_unipotent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r), (∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) → ∀ d : Fin s → ℕ, (∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) → GlobalTheory.StdPar.unip σ J X S ≤ GlobalTheory.UAut.unipFlag σ J (X.submatrix id (Fin.castLE hs)) d := by
  first | exact @GlobalTheory.TieStd.unip_le_unipFlag | exact GlobalTheory.TieStd.unip_le_unipFlag | (intros; apply GlobalTheory.TieStd.unip_le_unipFlag <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviSubgroupLeGradedIsotropicFlagLevi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviSubgroupLeGradedIsotropicFlagLevi
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct

namespace GlobalTheory.TieStd

theorem submatrix_mul_right' {R : Type} [CommRing R] {m n o p : ℕ} (P : Matrix (Fin m) (Fin n) R)
    (Q : Matrix (Fin n) (Fin o) R) (e : Fin p → Fin o) : (P * Q).submatrix id e = P * Q.submatrix id e := by
  ext i j; simp [Matrix.mul_apply]

theorem submatrix_eq_mul_one {R : Type} [CommRing R] {m n p : ℕ} (A : Matrix (Fin m) (Fin n) R)
    (e : Fin p → Fin n) : A.submatrix id e = A * (1 : Matrix (Fin n) (Fin n) R).submatrix id e := by
  ext i j; simp [Matrix.mul_apply, Matrix.one_apply]

theorem flag_mat {R : Type} [CommRing R] {n r : ℕ} (A : Matrix (Fin n) (Fin r) R)
    (A' : Matrix (Fin r) (Fin n) R) (hA : A' * A = 1) (M : Matrix (Fin n) (Fin n) R)
    (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r) (hS : ∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k)
    (d : Fin s → ℕ) (hd : ∀ i, d i = (S.filter (· < Fin.castLE hs i)).card)
    (hM : ∀ k ∈ S, ∃ Bk : Matrix (Fin (k.val + 1)) (Fin (k.val + 1)) R,
      M * A.submatrix id (Fin.castLE k.2) = A.submatrix id (Fin.castLE k.2) * Bk) :
    ∃ B : Matrix (Fin s) (Fin s) R, B.BlockTriangular d ∧
      M * A.submatrix id (Fin.castLE hs) = A.submatrix id (Fin.castLE hs) * B := by
  have key : ∀ k ∈ S, ∀ j : Fin r, j ≤ k →
      (∀ l : Fin r, k < l → (A' * M * A) l j = 0) ∧ ∀ a, (M * A) a j = (A * (A' * M * A)) a j := by
    intro k hk j hj
    obtain ⟨Bk, hB⟩ := hM k hk
    have hAk : A' * A.submatrix id (Fin.castLE k.2) = (1 : Matrix (Fin r) (Fin r) R).submatrix id (Fin.castLE k.2) := by
      rw [← submatrix_mul_right', hA]
    have hTk : (A' * M * A).submatrix id (Fin.castLE k.2) =
        (1 : Matrix (Fin r) (Fin r) R).submatrix id (Fin.castLE k.2) * Bk := by
      rw [Matrix.mul_assoc, submatrix_mul_right', submatrix_mul_right', hB, ← Matrix.mul_assoc, hAk]
    have hjk : j.val < k.val + 1 := Nat.lt_succ_of_le hj
    have hj' : Fin.castLE k.2 (⟨j.val, hjk⟩ : Fin (k.val + 1)) = j := Fin.ext rfl
    refine ⟨fun l hl => ?_, fun a => ?_⟩
    · have := congrFun (congrFun hTk l) ⟨j.val, hjk⟩
      rw [Matrix.submatrix_apply, hj'] at this
      change (A' * M * A) l j = _ at this
      rw [this, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun l' _ => ?_
      have hne : l ≠ Fin.castLE k.2 l' := by
        intro h; have := congrArg Fin.val h; simp at this; have := l'.2; have := Fin.lt_def.1 hl; omega
      simp [Matrix.one_apply, hne]
    · have e1 : M * A.submatrix id (Fin.castLE k.2) = (A * (A' * M * A)).submatrix id (Fin.castLE k.2) := by
        rw [hB, submatrix_mul_right', hTk, ← Matrix.mul_assoc, ← submatrix_eq_mul_one]
      have := congrFun (congrFun e1 a) ⟨j.val, hjk⟩
      rw [← submatrix_mul_right', Matrix.submatrix_apply, Matrix.submatrix_apply, hj'] at this
      exact this
  have hsmall : ∀ j : Fin r, j.val < s → ∀ l : Fin r, s ≤ l.val → (A' * M * A) l j = 0 := by
    intro j hj l hl
    obtain ⟨k, hk, hjk⟩ := (hS j).1 hj
    have hks : k.val < s := (hS k).2 ⟨k, hk, le_rfl⟩
    exact (key k hk j hjk).1 l (Fin.lt_def.2 (by omega))
  refine ⟨(A' * M * A).submatrix (Fin.castLE hs) (Fin.castLE hs), fun i j hij => ?_, ?_⟩
  · obtain ⟨k, hk, h1, h2⟩ := (depth_lt_iff S s hs d hd i j).1 hij
    exact (key k hk _ h1).1 _ h2
  · ext a j
    have hj : (Fin.castLE hs j).val < s := j.2
    obtain ⟨k, hk, hjk⟩ := (hS _).1 hj
    have e := (key k hk _ hjk).2 a
    rw [← submatrix_mul_right']
    change (M * A) a (Fin.castLE hs j) = _
    rw [e, Matrix.mul_apply, Matrix.mul_apply]
    symm
    rw [show (∑ x : Fin s, A.submatrix id (Fin.castLE hs) a x * (A' * M * A).submatrix (Fin.castLE hs) (Fin.castLE hs) x j) =
        ∑ l ∈ Finset.univ.map (Fin.castLEEmb hs), A a l * (A' * M * A) l (Fin.castLE hs j) from by
      rw [Finset.sum_map]; rfl]
    refine Finset.sum_subset (Finset.subset_univ _) fun l _ hl => ?_
    have : s ≤ l.val := by
      by_contra h; push_neg at h
      exact hl (Finset.mem_map.2 ⟨⟨l.val, h⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    rw [hsmall _ hj l this, mul_zero]

end GlobalTheory.TieStd

namespace GlobalTheory.TieStd


open GlobalTheory.StdPar in
theorem levi_le_leviFlag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r),
    (∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) → ∀ d : Fin s → ℕ, (∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) →
    GlobalTheory.StdPar.levi σ J X Y S ≤
      GlobalTheory.UAut.leviFlag σ J (X.submatrix id (Fin.castLE hs)) (Y.submatrix id (Fin.castLE hs)) d := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW S s hs hS d hd
  have side : ∀ Z W : Matrix (Fin n) (Fin r) E, Formalism.UG.cT (σ : E →+* E) W * J * Z = 1 →
      ∀ g : GAd σ J, (∀ k ∈ S, g ∈ frameStab σ J (initCols Z k) ⊤) →
      ∃ B : Matrix (Fin s) (Fin s) (AF F ⊗[F] E), B.BlockTriangular d ∧
        (matHom _ σ J g).1 * adMat F (Z.submatrix id (Fin.castLE hs)) =
          adMat F (Z.submatrix id (Fin.castLE hs)) * B := by
    intro Z W hWZ g hg
    have hA : adMat F (Formalism.UG.cT (σ : E →+* E) W * J) * adMat F Z = 1 := by
      rw [← Matrix.map_mul, hWZ, Matrix.map_one _ (map_zero _) (map_one _)]
    exact flag_mat (adMat F Z) _ hA _ S s hs hS d hd fun k hk => by
      obtain ⟨B, -, e⟩ := hg k hk
      exact ⟨B.1, e⟩
  have mem : ∀ g ∈ levi σ J X Y S, ∀ k ∈ S,
      g ∈ frameStab σ J (initCols X k) ⊤ ∧ g ∈ frameStab σ J (initCols Y k) ⊤ := fun g hg k hk => by
    simp only [levi, Subgroup.mem_iInf, Subgroup.mem_inf] at hg
    exact hg k hk
  have hyx : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := yx h hJ hW
  intro g hg
  have hgi := inv_mem hg
  exact Subgroup.mem_inf.2
    ⟨⟨side X Y hyx g fun k hk => (mem g hg k hk).1, side X Y hyx g⁻¹ fun k hk => (mem _ hgi k hk).1⟩,
      ⟨side Y X hW.xy g fun k hk => (mem g hg k hk).2, side Y X hW.xy g⁻¹ fun k hk => (mem _ hgi k hk).2⟩⟩

end GlobalTheory.TieStd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviSubgroupLeGradedIsotropicFlagLeviStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviSubgroup_le_gradedIsotropicFlagLevi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r), (∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) → ∀ d : Fin s → ℕ, (∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) → GlobalTheory.StdPar.levi σ J X Y S ≤ GlobalTheory.UAut.leviFlag σ J (X.submatrix id (Fin.castLE hs)) (Y.submatrix id (Fin.castLE hs)) d := by
  first | exact @GlobalTheory.TieStd.levi_le_leviFlag | exact GlobalTheory.TieStd.levi_le_leviFlag | (intros; apply GlobalTheory.TieStd.levi_le_leviFlag <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedIsotropicFlagLeviLeLeviSubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedIsotropicFlagLeviLeLeviSubgroup
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct

namespace GlobalTheory.TieStd

theorem sum_castLE_of_zero {M : Type*} [AddCommMonoid M] {m s : ℕ} (hm : m ≤ s) (g : Fin s → M)
    (hg : ∀ i : Fin s, m ≤ i.val → g i = 0) : ∑ i : Fin s, g i = ∑ i : Fin m, g (Fin.castLE hm i) := by
  symm
  refine Eq.trans (Finset.sum_map Finset.univ (Fin.castLEEmb hm) g).symm ?_
  refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => hg i (not_lt.1 fun h => hi ?_)
  exact Finset.mem_map.2 ⟨⟨i.val, h⟩, Finset.mem_univ _, Fin.ext rfl⟩

theorem mul_submatrix_castLE {R ι' κ : Type*} [CommRing R] {m s : ℕ} (hm : m ≤ s) (C : Matrix ι' (Fin s) R)
    (B : Matrix (Fin s) (Fin s) R) (hB : ∀ i j : Fin s, m ≤ i.val → j.val < m → B i j = 0) (f : κ → ι') :
    (C * B).submatrix f (Fin.castLE hm) =
      C.submatrix f (Fin.castLE hm) * B.submatrix (Fin.castLE hm) (Fin.castLE hm) := by
  ext a j
  simp only [submatrix_apply, Matrix.mul_apply]
  exact sum_castLE_of_zero hm _ fun i hi => by rw [hB i _ hi j.2, mul_zero]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem mem_frameStab_of_mem_parFlag {s m : ℕ} (hm : m ≤ s) (C : Matrix (Fin n) (Fin s) E)
    (L : Matrix (Fin s) (Fin n) E) (hL : L * C = 1) (d : Fin s → ℕ)
    (hd : ∀ i j : Fin s, m ≤ i.val → j.val < m → d j < d i) {g : GAd σ J} (hg : g ∈ GlobalTheory.UAut.parFlag σ J C d) :
    g ∈ GlobalTheory.StdPar.frameStab σ J (C.submatrix id (Fin.castLE hm)) ⊤ := by
  obtain ⟨⟨B, hB, e⟩, B', hB', e'⟩ := hg
  have hL' : adMat F L * adMat F C = 1 := by rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  have hMM : (matHom _ σ J g).1 * (matHom _ σ J g⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hBB : B * B' = 1 := by
    calc B * B' = adMat F L * (adMat F C * B) * B' := by rw [← Matrix.mul_assoc, hL', Matrix.one_mul]
      _ = adMat F L * ((matHom _ σ J g).1 * ((matHom _ σ J g⁻¹).1 * adMat F C)) := by
          simp only [← e, e', Matrix.mul_assoc]
      _ = 1 := by rw [← Matrix.mul_assoc (matHom _ σ J g).1, hMM, Matrix.one_mul, hL']
  have hz : ∀ {A : Matrix (Fin s) (Fin s) (AF F ⊗[F] E)}, A.BlockTriangular d →
      ∀ i j : Fin s, m ≤ i.val → j.val < m → A i j = 0 := fun hA i j hi hj => hA (hd i j hi hj)
  have hU : B.submatrix (Fin.castLE hm) (Fin.castLE hm) * B'.submatrix (Fin.castLE hm) (Fin.castLE hm) = 1 := by
    rw [← mul_submatrix_castLE hm B B' (hz hB') (Fin.castLE hm), hBB, Matrix.submatrix_one _ (Fin.castLE_injective hm)]
  refine ⟨⟨_, _, hU, mul_eq_one_comm.1 hU⟩, Subgroup.mem_top _, ?_⟩
  show (matHom _ σ J g).1 * (adMat F C).submatrix id (Fin.castLE hm) =
    (adMat F C).submatrix id (Fin.castLE hm) * B.submatrix (Fin.castLE hm) (Fin.castLE hm)
  rw [← mul_submatrix_castLE hm _ B (hz hB) id, ← e]
  ext a j
  simp [Matrix.mul_apply]

end GlobalTheory.TieStd

namespace GlobalTheory.TieStd

theorem leviFlag_le_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E),
    IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r), (∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) →
    ∀ d : Fin s → ℕ, (∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) →
    GlobalTheory.UAut.leviFlag σ J (X.submatrix id (Fin.castLE hs)) (Y.submatrix id (Fin.castLE hs)) d ≤
      GlobalTheory.StdPar.levi σ J X Y S := by
  intro F E _ _ _ _ _ σ hσ n J hJ r X Y hW S s hs hS d hd g hg
  obtain ⟨hgX, hgY⟩ := Subgroup.mem_inf.1 hg
  have hyx := GlobalTheory.StdPar.yx hσ hJ hW
  have hLX : Formalism.UG.cT (σ : E →+* E) (Y.submatrix id (Fin.castLE hs)) * J * X.submatrix id (Fin.castLE hs) = 1 := by
    rw [cT_submatrix_mul, hyx, Matrix.submatrix_one _ (Fin.castLE_injective hs)]
  have hLY : Formalism.UG.cT (σ : E →+* E) (X.submatrix id (Fin.castLE hs)) * J * Y.submatrix id (Fin.castLE hs) = 1 := by
    rw [cT_submatrix_mul, hW.xy, Matrix.submatrix_one _ (Fin.castLE_injective hs)]
  rw [GlobalTheory.StdPar.levi, Subgroup.mem_iInf]
  intro k
  rw [Subgroup.mem_iInf]
  intro hk
  have hm : k.val + 1 ≤ s := (hS k).2 ⟨k, hk, le_rfl⟩
  have hdk : ∀ i j : Fin s, k.val + 1 ≤ i.val → j.val < k.val + 1 → d j < d i := fun i j hi hj =>
    (depth_lt_iff S s hs d hd i j).2 ⟨k, hk, Fin.le_iff_val_le_val.2 (Nat.lt_succ_iff.1 hj), Fin.lt_iff_val_lt_val.2 hi⟩
  exact Subgroup.mem_inf.2 ⟨mem_frameStab_of_mem_parFlag σ J hm _ _ hLX d hdk hgX,
    mem_frameStab_of_mem_parFlag σ J hm _ _ hLY d hdk hgY⟩

end GlobalTheory.TieStd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedIsotropicFlagLeviLeLeviSubgroupStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gradedIsotropicFlagLevi_le_leviSubgroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r), (∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) → ∀ d : Fin s → ℕ, (∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) → GlobalTheory.UAut.leviFlag σ J (X.submatrix id (Fin.castLE hs)) (Y.submatrix id (Fin.castLE hs)) d ≤ GlobalTheory.StdPar.levi σ J X Y S := by
  first | exact @GlobalTheory.TieStd.leviFlag_le_levi | exact GlobalTheory.TieStd.leviFlag_le_levi | (intros; apply GlobalTheory.TieStd.leviFlag_le_levi <;> assumption)
end
end

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct

namespace GlobalTheory.TieStd

def leftStab {G : Type} [Group G] (φ : G → ℂ) : Subgroup G where
  carrier := {γ | ∀ g, φ (γ * g) = φ g}
  one_mem' := fun g => by simp
  mul_mem' := fun {a b} ha hb g => by rw [mul_assoc, ha, hb]
  inv_mem' := fun {a} ha g => by rw [← ha (a⁻¹ * g), mul_inv_cancel_left]

theorem stdPar_eq_flag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r), (∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) → ∀ d : Fin s → ℕ, (∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) → GlobalTheory.StdPar.unip σ J X S = GlobalTheory.UAut.unipFlag σ J (X.submatrix id (Fin.castLE hs)) d ∧ GlobalTheory.StdPar.levi σ J X Y S = GlobalTheory.UAut.leviFlag σ J (X.submatrix id (Fin.castLE hs)) (Y.submatrix id (Fin.castLE hs)) d ∧ ∀ (K : Subgroup (GAd σ J)) (φ : GAd σ J → ℂ), GlobalTheory.StdPar.IsAutOn σ J X Y S K φ ↔ GlobalTheory.UAut.IsAutOn σ J (GlobalTheory.UAut.leftGrp σ J (X.submatrix id (Fin.castLE hs)) d) K φ := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW S s hs hS d hd
  have hu := le_antisymm (GlobalTheory.T.hermitianWittFrame_unipotent_le_flag_unipotent F E σ h n J hJ r X Y hW S s hs hS d hd) (GlobalTheory.T.unipotent_radical_graded_isotropic_flag_le F E σ h n J hJ r X Y hW S s hs hS d hd)
  have hl := le_antisymm (GlobalTheory.T.leviSubgroup_le_gradedIsotropicFlagLevi F E σ h n J hJ r X Y hW S s hs hS d hd) (GlobalTheory.T.gradedIsotropicFlagLevi_le_leviSubgroup F E σ h n J hJ r X Y hW S s hs hS d hd)
  have hg := (GlobalTheory.T.leviDecomposition_gradedIsotropicFlag F E σ h n J hJ s (X.submatrix id (Fin.castLE hs)) (Y.submatrix id (Fin.castLE hs)) d
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xx]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.yy]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xy]; exact Matrix.submatrix_one _ (Fin.castLE_injective hs))).2.2.1
  refine ⟨hu, hl, fun K φ => ⟨fun hφ => ⟨?_, hφ.level, hφ.cont, hφ.smooth, hφ.growth, GlobalTheory.UAut.kfin_iff.1 hφ.kfin, hφ.zfin⟩,
    fun hφ => ⟨fun u hu' g => hφ.left u ?_ g, fun γ hγ hγ' g => hφ.left γ ?_ g, hφ.level, hφ.cont, hφ.smooth, hφ.growth,
      GlobalTheory.UAut.kfin_iff.2 hφ.kfin, hφ.zfin⟩⟩⟩
  · rw [hg]
    have : GlobalTheory.UAut.unipFlag σ J (X.submatrix id (Fin.castLE hs)) d ⊔ (ratPts σ J ⊓ GlobalTheory.UAut.leviFlag σ J (X.submatrix id (Fin.castLE hs)) (Y.submatrix id (Fin.castLE hs)) d) ≤ leftStab φ :=
      sup_le (fun u hu' => hφ.leftN u (hu ▸ hu')) (fun γ hγ => hφ.leftM γ hγ.1 (hl ▸ hγ.2))
    exact fun γ hγ => this hγ
  · rw [hg]; exact Subgroup.mem_sup_left (hu ▸ hu')
  · rw [hg]; exact Subgroup.mem_sup_right ⟨hγ, hl ▸ hγ'⟩

end GlobalTheory.TieStd
