module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitOfSumEqOne

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationClosureEqual
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationClosureEqual
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

theorem inv_mem_locSub_prod {K : Type} [Field K] {Q : Type} [Fintype Q] (D : Subring K) (s : Q → K)
    (h0 : ∀ q, s q ≠ 0) (hD : ∀ q, s q ∈ D) (q : Q) : (s q)⁻¹ ∈ locSub D (∏ q, s q) := by
  classical
  have hprod : s q * ∏ q' ∈ Finset.univ.erase q, s q' = ∏ q', s q' :=
    Finset.mul_prod_erase Finset.univ s (Finset.mem_univ q)
  have hne : (∏ q', s q') ≠ 0 := Finset.prod_ne_zero_iff.2 fun q' _ => h0 q'
  have e : (s q)⁻¹ = (∏ q', s q')⁻¹ * ∏ q' ∈ Finset.univ.erase q, s q' := by
    rw [← hprod] at hne ⊢
    have h1 : (∏ q' ∈ Finset.univ.erase q, s q') ≠ 0 := right_ne_zero_of_mul hne
    field_simp [h0 q, h1]
  rw [e]
  exact (locSub D (∏ q, s q)).mul_mem (inv_mem_locSub D _)
    (le_locSub D _ (D.prod_mem fun q' _ => hD q'))

theorem locSub_eq_of_inverse_family : ∀ {K : Type} [Field K] {Q : Type} [Fintype Q] (A B : Subring K) (t : Q → K),
    (∀ q, t q ≠ 0) → (∀ q, t q ∈ A) → (∀ q, (t q)⁻¹ ∈ B) →
    A ≤ Subring.closure ((B : Set K) ∪ Set.range t) →
    B ≤ Subring.closure ((A : Set K) ∪ Set.range fun q => (t q)⁻¹) →
    locSub A (∏ q, t q) = locSub B (∏ q, t q)⁻¹ := by
  intro K _ Q _ A B t h0 hA hB hAB hBA
  have hT : (∏ q, t q) ∈ A := A.prod_mem fun q _ => hA q
  have hTi : (∏ q, t q)⁻¹ ∈ B := by
    rw [← Finset.prod_inv_distrib]
    exact B.prod_mem fun q _ => hB q
  have hBle : B ≤ locSub A (∏ q, t q) := by
    refine hBA.trans ((Subring.closure_le).2 ?_)
    rintro x (hx | ⟨q, rfl⟩)
    · exact le_locSub A _ hx
    · exact inv_mem_locSub_prod A t h0 hA q
  have hAle : A ≤ locSub B (∏ q, t q)⁻¹ := by
    refine hAB.trans ((Subring.closure_le).2 ?_)
    rintro x (hx | ⟨q, rfl⟩)
    · exact le_locSub B _ hx
    · have h := inv_mem_locSub_prod B (fun q => (t q)⁻¹) (fun q => inv_ne_zero (h0 q)) hB q
      rw [Finset.prod_inv_distrib] at h
      simpa using h
  refine le_antisymm ((Subring.closure_le).2 ?_) ((Subring.closure_le).2 ?_)
  · rintro x (hx | hx)
    · exact hAle hx
    · rw [Set.mem_singleton_iff.1 hx]
      exact le_locSub B _ hTi
  · rintro x (hx | hx)
    · exact hBle hx
    · rw [Set.mem_singleton_iff.1 hx, inv_inv]
      exact le_locSub A _ hT

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationClosureEqualStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_closure_equal : ∀ {K : Type} [Field K] {Q : Type} [Fintype Q] (A B : Subring K) (t : Q → K), (∀ q, t q ≠ 0) → (∀ q, t q ∈ A) → (∀ q, (t q)⁻¹ ∈ B) → A ≤ Subring.closure ((B : Set K) ∪ Set.range t) → B ≤ Subring.closure ((A : Set K) ∪ Set.range fun q => (t q)⁻¹) → locSub A (∏ q, t q) = locSub B (∏ q, t q)⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.locSub_eq_of_inverse_family | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.locSub_eq_of_inverse_family | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.locSub_eq_of_inverse_family <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalizedMinorExtends
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalizedMinorExtends
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

theorem det_mem_subring {F : Type} [CommRing F] (D : Subring F) {k : ℕ} (A : Matrix (Fin k) (Fin k) F)
    (hA : ∀ a b, A a b ∈ D) : A.det ∈ D := by
  rw [Matrix.det_apply']
  exact D.sum_mem fun σ _ => D.mul_mem (intCast_mem D _) (D.prod_mem fun a _ => hA _ _)

theorem mul_adjugate_apply_eq_kMinor {F : Type} [Field F] {n r : ℕ} (Y : Matrix (Fin n) (Fin r) F) (m : ℕ)
    (hm : m ≤ r) (J : Fin m → Fin n) (i : Fin n) (j : Fin m) :
    (Y.submatrix id (Fin.castLE hm) * (Y.submatrix J (Fin.castLE hm)).adjugate) i j =
      kMinor Y m hm (Function.update J j i) := by
  classical
  have h1 : (Y.submatrix id (Fin.castLE hm) * (Y.submatrix J (Fin.castLE hm)).adjugate) i j =
      Matrix.cramer (Y.submatrix J (Fin.castLE hm)).transpose (Y.submatrix id (Fin.castLE hm) i) j := by
    rw [Matrix.cramer_eq_adjugate_mulVec, ← Matrix.adjugate_transpose]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  rw [h1, Matrix.cramer_transpose_apply]
  unfold kMinor
  congr 1
  ext a b
  by_cases hab : a = j
  · subst hab
    simp
  · simp [Matrix.updateRow_ne hab, Function.update_of_ne hab]

theorem normAt_mul_inv_mem {F : Type} [Field F] (O : Subring F) {n r : ℕ} (Y : Matrix (Fin n) (Fin r) F)
    (m : ℕ) (hm : m ≤ r) (J : Fin m → Fin n) (hJ : NormAt O Y m hm J) (i : Fin n) (j : Fin m) :
    (Y.submatrix id (Fin.castLE hm) * (Y.submatrix J (Fin.castLE hm))⁻¹) i j ∈ O := by
  classical
  have e : (Y.submatrix id (Fin.castLE hm) * (Y.submatrix J (Fin.castLE hm))⁻¹) i j =
      kMinor Y m hm (Function.update J j i) / kMinor Y m hm J := by
    rw [Matrix.inv_def, Matrix.mul_smul, Matrix.smul_apply, mul_adjugate_apply_eq_kMinor,
      Ring.inverse_eq_inv', smul_eq_mul, div_eq_inv_mul]
    rfl
  rw [e]
  exact hJ.2 _

theorem normAt_exchange {F : Type} [Field F] (O : Subring F) [IsLocalRing O] {n r : ℕ}
    (Y : Matrix (Fin n) (Fin r) F) (k : ℕ) (hk : k + 1 ≤ r) (I' : Fin (k + 1) → Fin n) (I : Fin k → Fin n)
    (h' : NormAt O Y (k + 1) hk I') (h : NormAt O Y k (Nat.le_of_succ_le hk) I) :
    ∃ f : Fin k → Fin (k + 1), Function.Injective f ∧ NormAt O Y k (Nat.le_of_succ_le hk) (I' ∘ f) := by
  classical
  have hk0 : k ≤ r := Nat.le_of_succ_le hk
  have hM' : IsUnit (Y.submatrix I' (Fin.castLE hk)).det := isUnit_iff_ne_zero.2 h'.1
  have hM : IsUnit (Y.submatrix I (Fin.castLE hk0)).det := isUnit_iff_ne_zero.2 h.1
  obtain ⟨Z, hZdef⟩ : ∃ Z, Z = Y.submatrix id (Fin.castLE hk) * (Y.submatrix I' (Fin.castLE hk))⁻¹ := ⟨_, rfl⟩
  obtain ⟨Z', hZ'def⟩ : ∃ Z', Z' = Y.submatrix id (Fin.castLE hk0) * (Y.submatrix I (Fin.castLE hk0))⁻¹ :=
    ⟨_, rfl⟩
  have hZ : ∀ a b, Z a b ∈ O := fun a b => by
    rw [hZdef]; exact normAt_mul_inv_mem O Y _ hk I' h' a b
  have hZ' : ∀ a b, Z' a b ∈ O := fun a b => by
    rw [hZ'def]; exact normAt_mul_inv_mem O Y _ hk0 I h a b
  have e1 : Y.submatrix id (Fin.castLE hk) = Z * Y.submatrix I' (Fin.castLE hk) := by
    rw [hZdef, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hM', Matrix.mul_one]
  have hY0 : Y.submatrix id (Fin.castLE hk0) = Z * (Y.submatrix I' (Fin.castLE hk0)) := by
    ext a b
    have := congrFun (congrFun e1 a) (Fin.castSucc b)
    simpa [Matrix.mul_apply] using this
  have hD : ∀ {m : ℕ} (J : Fin m → Fin n), Z'.submatrix J id =
      Y.submatrix J (Fin.castLE hk0) * (Y.submatrix I (Fin.castLE hk0))⁻¹ := by
    intro m J
    rw [hZ'def]
    ext a b
    simp [Matrix.mul_apply]
  have hZZ : Z' = Z * Z'.submatrix I' id := by
    rw [hD, ← Matrix.mul_assoc, ← hY0, hZ'def]
  have hI : Z'.submatrix I id = 1 := by
    rw [hD, Matrix.mul_nonsing_inv _ hM]
  have hone : Z.submatrix I id * Z'.submatrix I' id = 1 := by
    rw [← hI]
    conv_rhs => rw [hZZ]
    ext a b
    simp [Matrix.mul_apply]
  have hsum := det_mul_expand (Z.submatrix I id) (Z'.submatrix I' id)
  rw [hone, Matrix.det_one] at hsum
  obtain ⟨f, -, hne, hinv⟩ := exists_unit_of_sum_eq_one O Finset.univ _
    (fun f _ => O.mul_mem (O.prod_mem fun a _ => hZ _ _) (det_mem_subring O _ fun a b => hZ' _ _)) hsum.symm
  have hc : (∏ a, (Z.submatrix I id) a (f a)) ≠ 0 := left_ne_zero_of_mul hne
  have hd : ((Z'.submatrix I' id).submatrix f id).det ≠ 0 := right_ne_zero_of_mul hne
  have hdet : ((Z'.submatrix I' id).submatrix f id).det =
      kMinor Y k hk0 (I' ∘ f) / kMinor Y k hk0 I := by
    have e2 : (Z'.submatrix I' id).submatrix f id = Z'.submatrix (I' ∘ f) id := by
      ext a b; simp
    rw [e2, hD, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', div_eq_mul_inv]
    rfl
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne'
    exact hd (Matrix.det_zero_of_row_eq hne' (by ext c; simp [hab]))
  refine ⟨f, hinj, ?_, fun I'' => ?_⟩
  · intro h0
    apply hd
    rw [hdet, h0, zero_div]
  · have hP := h.1
    have hQ : kMinor Y k hk0 (I' ∘ f) ≠ 0 := by
      intro h0
      apply hd
      rw [hdet, h0, zero_div]
    have e : kMinor Y k hk0 I'' / kMinor Y k hk0 (I' ∘ f) =
        (kMinor Y k hk0 I'' / kMinor Y k hk0 I) * ((∏ a, (Z.submatrix I id) a (f a)) *
          ((∏ a, (Z.submatrix I id) a (f a)) * ((Z'.submatrix I' id).submatrix f id).det)⁻¹) := by
      rw [hdet]
      field_simp
    rw [e]
    exact O.mul_mem (h.2 I'') (O.mul_mem (O.prod_mem fun a _ => hZ _ _) hinv)

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalizedMinorExtendsStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalized_minor_extends : ∀ {F : Type} [Field F] (O : Subring F) [IsLocalRing O] {n r : ℕ} (Y : Matrix (Fin n) (Fin r) F) (k : ℕ) (hk : k + 1 ≤ r) (I' : Fin (k + 1) → Fin n) (I : Fin k → Fin n), NormAt O Y (k + 1) hk I' → NormAt O Y k (Nat.le_of_succ_le hk) I → ∃ f : Fin k → Fin (k + 1), Function.Injective f ∧ NormAt O Y k (Nat.le_of_succ_le hk) (I' ∘ f) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.normAt_exchange | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.normAt_exchange | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.normAt_exchange <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPermNormalizedMinors
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPermNormalizedMinors
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

theorem kMinor_comp_perm {F : Type} [CommRing F] {n r : ℕ} (A : Matrix (Fin n) (Fin r) F) (k : ℕ)
    (hk : k ≤ r) (I : Fin k → Fin n) (σ : Equiv.Perm (Fin k)) :
    kMinor A k hk (I ∘ σ) = ((Equiv.Perm.sign σ : ℤ) : F) * kMinor A k hk I := by
  unfold kMinor
  have e : A.submatrix (I ∘ σ) (Fin.castLE hk) = (A.submatrix I (Fin.castLE hk)).submatrix σ id := by
    ext a b
    simp
  rw [e, Matrix.det_permute]

theorem normAt_comp_perm {F : Type} [Field F] (O : Subring F) {n r : ℕ} (Y : Matrix (Fin n) (Fin r) F)
    (k : ℕ) (hk : k ≤ r) (I : Fin k → Fin n) (σ : Equiv.Perm (Fin k)) (h : NormAt O Y k hk I) :
    NormAt O Y k hk (I ∘ σ) := by
  obtain ⟨h0, h1⟩ := h
  refine ⟨?_, fun J => ?_⟩
  · rw [kMinor_comp_perm]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · simpa [hs] using h0
    · simpa [hs] using h0
  · rw [kMinor_comp_perm]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · simpa [hs] using h1 J
    · simpa [hs, div_neg] using O.neg_mem (h1 J)

theorem exists_perm_castSucc {k : ℕ} (f : Fin k → Fin (k + 1)) (hf : Function.Injective f) :
    ∃ g : Equiv.Perm (Fin (k + 1)), ∀ a : Fin k, g a.castSucc = f a := by
  classical
  let e : {x // x ∈ Set.range (Fin.castSucc : Fin k → Fin (k + 1))} ≃ {x // x ∈ Set.range f} :=
    (Equiv.ofInjective _ (Fin.castSucc_injective k)).symm.trans (Equiv.ofInjective f hf)
  refine ⟨e.extendSubtype, fun a => ?_⟩
  have h := e.extendSubtype_apply_of_mem a.castSucc ⟨a, rfl⟩
  rw [h]
  have h2 : (Equiv.ofInjective _ (Fin.castSucc_injective k)).symm
      ⟨a.castSucc, ⟨a, rfl⟩⟩ = a := Equiv.ofInjective_symm_apply _ a
  simp only [e, Equiv.trans_apply]
  erw [h2]
  rfl

def castEmb {m n : ℕ} (h : m ≤ n) : Fin m ↪ Fin n := ⟨Fin.castLE h, Fin.castLE_injective h⟩

theorem exists_perm_restrict {m j r : ℕ} (hm : m ≤ j) (hj : j ≤ r) (hmr : m ≤ r)
    (g : Equiv.Perm (Fin m)) :
    ∃ σ : Equiv.Perm (Fin j), ∀ a : Fin j,
      g.viaFintypeEmbedding (castEmb hmr) (Fin.castLE hj a) = Fin.castLE hj (σ a) := by
  classical
  refine ⟨g.viaFintypeEmbedding (castEmb hm), fun a => ?_⟩
  by_cases ha : (a : ℕ) < m
  · have e1 : Fin.castLE hj a = castEmb hmr ⟨a, ha⟩ := by ext; simp [castEmb]
    have e2 : a = castEmb hm ⟨a, ha⟩ := by ext; simp [castEmb]
    rw [e1, Equiv.Perm.viaFintypeEmbedding_apply_image]
    conv_rhs => rw [e2, Equiv.Perm.viaFintypeEmbedding_apply_image]
    ext; simp [castEmb]
  · have n1 : Fin.castLE hj a ∉ Set.range (castEmb hmr) := by
      rintro ⟨b, hb⟩
      have := congrArg Fin.val hb
      have hb2 := b.2
      simp [castEmb] at this
      omega
    have n2 : a ∉ Set.range (castEmb hm) := by
      rintro ⟨b, hb⟩
      have := congrArg Fin.val hb
      have hb2 := b.2
      simp [castEmb] at this
      omega
    rw [Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ n1,
      Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ n2]

theorem exists_perm_top {F : Type} [Field F] (O : Subring F) {r : ℕ} (Y : Matrix (Fin r) (Fin r) F)
    (I : Fin r → Fin r) (h : NormAt O Y r le_rfl I) : ∃ w : Equiv.Perm (Fin r), ⇑w = I := by
  have hinj : Function.Injective I := by
    intro a b hab
    by_contra hne
    refine h.1 ?_
    unfold kMinor
    refine Matrix.det_zero_of_row_eq hne ?_
    ext c
    simp [hab]
  exact ⟨Equiv.ofBijective I (Finite.injective_iff_bijective.1 hinj), rfl⟩

theorem perm_step {F : Type} [Field F] (O : Subring F) {r : ℕ} (Y : Matrix (Fin r) (Fin r) F) (k : ℕ)
    (hk : k + 1 ≤ r) (w : Equiv.Perm (Fin r)) (f : Fin k → Fin (k + 1)) (hf : Function.Injective f)
    (hw : ∀ (j : ℕ) (hj : j ≤ r), k + 1 ≤ j → NormAt O Y j hj (w ∘ Fin.castLE hj))
    (hn : NormAt O Y k (Nat.le_of_succ_le hk) ((w ∘ Fin.castLE hk) ∘ f)) :
    ∃ w' : Equiv.Perm (Fin r), ∀ (j : ℕ) (hj : j ≤ r), k ≤ j → NormAt O Y j hj (w' ∘ Fin.castLE hj) := by
  classical
  obtain ⟨g, hg⟩ := exists_perm_castSucc f hf
  refine ⟨w * g.viaFintypeEmbedding (castEmb hk), fun j hj hkj => ?_⟩
  rcases Nat.eq_or_lt_of_le hkj with rfl | hlt
  · have e : (⇑(w * g.viaFintypeEmbedding (castEmb hk)) ∘ Fin.castLE hj) =
        (w ∘ Fin.castLE hk) ∘ f := by
      funext a
      have e1 : Fin.castLE hj a = castEmb hk a.castSucc := by ext; simp [castEmb]
      simp only [Function.comp_apply, Equiv.Perm.mul_apply]
      rw [e1, Equiv.Perm.viaFintypeEmbedding_apply_image, hg]
      rfl
    rw [e]
    exact hn
  · obtain ⟨σ, hσ⟩ := exists_perm_restrict (m := k + 1) (j := j) hlt hj hk g
    have e : (⇑(w * g.viaFintypeEmbedding (castEmb hk)) ∘ Fin.castLE hj) =
        (w ∘ Fin.castLE hj) ∘ σ := by
      funext a
      simp only [Function.comp_apply, Equiv.Perm.mul_apply]
      rw [hσ]
    rw [e]
    exact normAt_comp_perm O Y j hj _ σ (hw j hj hlt)

theorem exists_perm_normAt {F : Type} [Field F] (O : Subring F) {r : ℕ} (Y : Matrix (Fin r) (Fin r) F)
    (hex : ∀ (k : ℕ) (hk : k + 1 ≤ r) (I' : Fin (k + 1) → Fin r) (I : Fin k → Fin r),
      NormAt O Y (k + 1) hk I' → NormAt O Y k (Nat.le_of_succ_le hk) I →
        ∃ f : Fin k → Fin (k + 1), Function.Injective f ∧
          NormAt O Y k (Nat.le_of_succ_le hk) (I' ∘ f))
    (hall : ∀ (k : ℕ) (hk : k ≤ r), ∃ I : Fin k → Fin r, NormAt O Y k hk I) :
    ∃ w : Equiv.Perm (Fin r), ∀ (k : ℕ) (hk : k ≤ r), NormAt O Y k hk (w ∘ Fin.castLE hk) := by
  have key : ∀ d : ℕ, d ≤ r → ∃ w : Equiv.Perm (Fin r), ∀ (j : ℕ) (hj : j ≤ r), r - d ≤ j →
      NormAt O Y j hj (w ∘ Fin.castLE hj) := by
    intro d
    induction d with
    | zero =>
      intro _
      obtain ⟨I, hI⟩ := hall r le_rfl
      obtain ⟨w, hw⟩ := exists_perm_top O Y I hI
      refine ⟨w, fun j hj hrj => ?_⟩
      have hjr : j = r := le_antisymm hj (by simpa using hrj)
      subst hjr
      have e : (⇑w ∘ Fin.castLE hj) = I := by
        funext a
        simp [hw]
      rw [e]
      exact hI
    | succ d ih =>
      intro hd
      obtain ⟨w, hw⟩ := ih (by omega)
      obtain ⟨k, hkd⟩ : ∃ k, k + 1 = r - d := ⟨r - d - 1, by omega⟩
      have hk : k + 1 ≤ r := by omega
      obtain ⟨I, hI⟩ := hall k (Nat.le_of_succ_le hk)
      obtain ⟨f, hf, hn⟩ := hex k hk (w ∘ Fin.castLE hk) I (hw _ hk (by omega)) hI
      obtain ⟨w', hw'⟩ := perm_step O Y k hk w f hf (fun j hj h => hw j hj (by omega)) hn
      exact ⟨w', fun j hj h => hw' j hj (by omega)⟩
  obtain ⟨w, hw⟩ := key r le_rfl
  exact ⟨w, fun k hk => hw k hk (by omega)⟩

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPermNormalizedMinorsStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_perm_normalized_minors : ∀ {F : Type} [Field F] (O : Subring F) {r : ℕ} (Y : Matrix (Fin r) (Fin r) F), (∀ (k : ℕ) (hk : k + 1 ≤ r) (I' : Fin (k + 1) → Fin r) (I : Fin k → Fin r), NormAt O Y (k + 1) hk I' → NormAt O Y k (Nat.le_of_succ_le hk) I → ∃ f : Fin k → Fin (k + 1), Function.Injective f ∧ NormAt O Y k (Nat.le_of_succ_le hk) (I' ∘ f)) → (∀ (k : ℕ) (hk : k ≤ r), ∃ I : Fin k → Fin r, NormAt O Y k hk I) → ∃ w : Equiv.Perm (Fin r), ∀ (k : ℕ) (hk : k ≤ r), NormAt O Y k hk (w ∘ Fin.castLE hk) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.exists_perm_normAt | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.exists_perm_normAt | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.exists_perm_normAt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicIndependentOfAdjoin
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicIndependentOfAdjoin
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

theorem algebraicIndependent_of_mem_adjoin_range :
    ∀ {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] {ι : Type} [Finite ι] (u v : ι → K),
      AlgebraicIndependent Ω u → (∀ a, u a ∈ IntermediateField.adjoin Ω (Set.range v)) →
      AlgebraicIndependent Ω v := by
  intro Ω K _ _ _ ι _ u v hu hmem
  set L := IntermediateField.adjoin Ω (Set.range v) with hL
  let v' : ι → L := fun a => ⟨v a, IntermediateField.subset_adjoin Ω _ ⟨a, rfl⟩⟩
  let u' : ι → L := fun a => ⟨u a, hmem a⟩
  have hu' : AlgebraicIndependent Ω u' := AlgebraicIndependent.of_comp (x := u') L.val hu
  have htop : IntermediateField.adjoin Ω (Set.range v') = ⊤ := by
    apply IntermediateField.map_injective L.val
    have hcomp : (⇑L.val ∘ v') = v := rfl
    rw [IntermediateField.adjoin_map, ← Set.range_comp, hcomp, ← AlgHom.fieldRange_eq_map,
      IntermediateField.fieldRange_val]
    try rfl
  haveI : Algebra.IsAlgebraic (Algebra.adjoin Ω (Set.range v')) L := by
    rw [← IntermediateField.isAlgebraic_adjoin_iff_top]
    refine ⟨fun x => ?_⟩
    have hx : x ∈ IntermediateField.adjoin Ω (Set.range v') := by
      rw [htop]
      exact IntermediateField.mem_top
    exact isAlgebraic_algebraMap (⟨x, hx⟩ : IntermediateField.adjoin Ω (Set.range v'))
  haveI : FaithfulSMul Ω L :=
    (faithfulSMul_iff_algebraMap_injective Ω L).mpr (algebraMap Ω L).injective
  obtain ⟨t, hts, htb⟩ := exists_isTranscendenceBasis_subset (R := Ω) (Set.range v')
  have hle : Cardinal.mk ι ≤ Cardinal.mk t :=
    hu'.cardinalMk_le_trdeg.trans htb.cardinalMk_eq_trdeg.symm.le
  haveI : Finite t := ((Set.finite_range v').subset hts).to_subtype
  have hcard : Nat.card ι ≤ Nat.card t := by
    letI := Fintype.ofFinite ι
    letI := Fintype.ofFinite t
    rw [Cardinal.mk_fintype, Cardinal.mk_fintype] at hle
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact_mod_cast hle
  have heq : t = Set.range v' :=
    Set.eq_of_subset_of_ncard_le hts
      (by
        rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
        exact (Finite.card_range_le v').trans hcard)
      (Set.finite_range v')
  subst heq
  have hinj : Function.Injective v' := by
    have hbij := (Set.rangeFactorization_surjective (f := v')).bijective_of_nat_card_le hcard
    intro a b hab
    exact hbij.1 (Subtype.ext hab)
  have hv' : AlgebraicIndependent Ω v' := (algebraicIndependent_subtype_range hinj).mp htb.1
  exact hv'.map' (f := L.val) Subtype.val_injective

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicIndependentOfAdjoinStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_independent_of_adjoin : ∀ {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] {ι : Type} [Finite ι] (u v : ι → K), AlgebraicIndependent Ω u → (∀ a, u a ∈ IntermediateField.adjoin Ω (Set.range v)) → AlgebraicIndependent Ω v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.algebraicIndependent_of_mem_adjoin_range | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.algebraicIndependent_of_mem_adjoin_range | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.algebraicIndependent_of_mem_adjoin_range <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LuDecompositionOfMinors
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LuDecompositionOfMinors
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

theorem exists_lu_of_leading_minors {F : Type} [Field F] {r : ℕ} (Y : Matrix (Fin r) (Fin r) F)
    (h : ∀ (k : ℕ) (hk : k ≤ r), kMinor Y k hk (Fin.castLE hk) ≠ 0) :
    ∃ C V : Matrix (Fin r) (Fin r) F, (∀ l k, k < l → C l k = 0) ∧ (∀ l k, l < k → V l k = 0) ∧
      (∀ l, V l l = 1) ∧ Y * C = V := by
  classical
  let B : ∀ k : Fin r, Matrix (Fin ((k : ℕ) + 1)) (Fin ((k : ℕ) + 1)) F := fun k =>
    Y.submatrix (Fin.castLE k.2) (Fin.castLE k.2)
  have hB : ∀ k, IsUnit (B k).det := fun k => isUnit_iff_ne_zero.2 (h _ k.2)
  let a : ∀ k : Fin r, Fin ((k : ℕ) + 1) → F := fun k =>
    (B k)⁻¹.mulVec (Pi.single (Fin.last _) 1)
  have ha : ∀ k, (B k).mulVec (a k) = Pi.single (Fin.last _) 1 := fun k => by
    simp only [a]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hB k), Matrix.one_mulVec]
  let C : Matrix (Fin r) (Fin r) F := fun l k =>
    if hlk : (l : ℕ) < (k : ℕ) + 1 then a k ⟨l, hlk⟩ else 0
  have hV : ∀ (k : Fin r) (l : Fin ((k : ℕ) + 1)),
      (Y * C) (Fin.castLE k.2 l) k = (Pi.single (Fin.last (k : ℕ)) (1 : F) :
        Fin ((k : ℕ) + 1) → F) l := by
    intro k l
    rw [← ha k]
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    symm
    refine Finset.sum_of_injOn (Fin.castLE k.2) (Fin.castLE_injective _).injOn
      (fun _ _ => Finset.mem_univ _) (fun j _ hj => ?_) (fun b _ => ?_)
    · have hjk : ¬ (j : ℕ) < (k : ℕ) + 1 := fun hlt =>
        hj ⟨⟨j, hlt⟩, by simp, by ext; simp⟩
      simp only [C, dif_neg hjk, mul_zero]
    · have hb : ((Fin.castLE k.2 b : Fin r) : ℕ) < (k : ℕ) + 1 := b.2
      simp only [C, dif_pos hb]
      rfl
  refine ⟨C, Y * C, fun l k hkl => ?_, fun l k hlk => ?_, fun l => ?_, rfl⟩
  · have hn : ¬ (l : ℕ) < (k : ℕ) + 1 := by
      have : (k : ℕ) < l := hkl
      omega
    simp only [C, dif_neg hn]
  · have hlt : (l : ℕ) < (k : ℕ) + 1 := by
      have : (l : ℕ) < k := hlk
      omega
    have h1 := hV k ⟨l, hlt⟩
    have e : Fin.castLE k.2 (⟨l, hlt⟩ : Fin ((k : ℕ) + 1)) = l := by ext; simp
    have hne : (⟨l, hlt⟩ : Fin ((k : ℕ) + 1)) ≠ Fin.last (k : ℕ) := by
      intro hh
      have h2 : (l : ℕ) = k := by simpa using Fin.ext_iff.1 hh
      have : (l : ℕ) < k := hlk
      omega
    rw [e, Pi.single_eq_of_ne hne] at h1
    exact h1
  · have h1 := hV l (Fin.last (l : ℕ))
    have e : Fin.castLE l.2 (Fin.last (l : ℕ)) = l := by ext; simp
    rw [e, Pi.single_eq_same] at h1
    exact h1

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LuDecompositionOfMinorsStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lu_decomposition_of_minors : ∀ {F : Type} [Field F] {r : ℕ} (Y : Matrix (Fin r) (Fin r) F), (∀ (k : ℕ) (hk : k ≤ r), kMinor Y k hk (Fin.castLE hk) ≠ 0) → ∃ C V : Matrix (Fin r) (Fin r) F, (∀ l k, k < l → C l k = 0) ∧ (∀ l k, l < k → V l k = 0) ∧ (∀ l, V l l = 1) ∧ Y * C = V := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.exists_lu_of_leading_minors | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.exists_lu_of_leading_minors | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.exists_lu_of_leading_minors <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationClosureSmooth
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationClosureSmooth
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

theorem smooth_of_away_mvPolynomial {R L ι : Type} [CommRing R] [CommRing L] [Finite ι]
    (g : R →+* L) (ψ : MvPolynomial ι R →+* L) (hg : ψ.comp MvPolynomial.C = g) (f : MvPolynomial ι R)
    (hl : @IsLocalization.Away _ _ f L _ ψ.toAlgebra) : g.Smooth := by
  letI := ψ.toAlgebra
  haveI := hl
  have h1 : ψ.Smooth := (Algebra.Smooth.of_isLocalization_Away f : Algebra.Smooth (MvPolynomial ι R) L)
  have h2 : (algebraMap R (MvPolynomial ι R)).Smooth :=
    RingHom.smooth_algebraMap.2 ⟨inferInstance, inferInstance⟩
  rw [MvPolynomial.algebraMap_eq] at h2
  rw [← hg]
  exact RingHom.Smooth.comp h2 h1

def evalSub {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] {ι : Type} (R : Subring Ω) (v : ι → K) :
    MvPolynomial ι R →+* K :=
  MvPolynomial.eval₂Hom ((algebraMap Ω K).comp R.subtype) v

theorem evalSub_injective {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] {ι : Type} (R : Subring Ω)
    (v : ι → K) (hv : AlgebraicIndependent Ω v) : Function.Injective (evalSub R v) := by
  have e : evalSub R v =
      (MvPolynomial.aeval v : MvPolynomial ι Ω →ₐ[Ω] K).toRingHom.comp (MvPolynomial.map R.subtype) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [evalSub]
    · intro i
      simp [evalSub]
  rw [e]
  exact fun p q hpq => MvPolynomial.map_injective _ R.subtype_injective
    (algebraicIndependent_iff_injective_aeval.1 hv hpq)

theorem evalSub_range {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] {ι : Type} (R : Subring Ω)
    (v : ι → K) : (evalSub R v).range =
      Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v) := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    induction a using MvPolynomial.induction_on with
    | C a =>
      refine Subring.subset_closure (Or.inl ⟨a, a.2, ?_⟩)
      simp [evalSub]
    | add p q hp hq =>
      rw [map_add (f := _)]
      exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      refine mul_mem hp (Subring.subset_closure (Or.inr ⟨i, ?_⟩))
      simp [evalSub]
  · refine Subring.closure_le.2 ?_
    rintro x (⟨a, ha, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨MvPolynomial.C ⟨a, ha⟩, by simp [evalSub]⟩
    · exact ⟨MvPolynomial.X i, by simp [evalSub]⟩

theorem smooth_locSub_closure : ∀ {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] {ι : Type} [Finite ι] (R : Subring Ω) (v : ι → K), AlgebraicIndependent Ω v → ∀ ℓ : K, ℓ ∈ Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v) → ℓ ≠ 0 → ∀ h : (∀ a ∈ R, algebraMap Ω K a ∈ locSub (Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v)) ℓ), (((algebraMap Ω K).comp R.subtype).codRestrict (locSub (Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v)) ℓ) (fun a => h a a.2)).Smooth := by
  intro Ω K _ _ _ ι _ R v hv ℓ hℓ h0 h
  have hr := evalSub_range R v
  generalize Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v) = B at *
  subst hr
  have hinj := evalSub_injective R v hv
  have hmem : ∀ a, evalSub R v a ∈ locSub (evalSub R v).range ℓ :=
    fun a => le_locSub _ _ ⟨a, rfl⟩
  obtain ⟨f, hf⟩ := hℓ
  refine smooth_of_away_mvPolynomial _ ((evalSub R v).codRestrict _ hmem) ?_ f ?_
  · ext a
    change evalSub R v (MvPolynomial.C a) = algebraMap Ω K a
    simp [evalSub]
  · letI := ((evalSub R v).codRestrict _ hmem).toAlgebra
    have hval : ∀ a : MvPolynomial ι R,
        ((algebraMap (MvPolynomial ι R) (locSub (evalSub R v).range ℓ) a : locSub (evalSub R v).range ℓ) : K)
          = evalSub R v a := fun a => rfl
    refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
    · rintro ⟨_, n, rfl⟩
      have hu : IsUnit (algebraMap (MvPolynomial ι R) (locSub (evalSub R v).range ℓ) f) := by
        refine IsUnit.of_mul_eq_one ⟨ℓ⁻¹, inv_mem_locSub _ _⟩ (Subtype.ext ?_)
        simp [hval, hf, h0]
      simpa using hu.pow n
    · rintro ⟨z, hz⟩
      obtain ⟨k, hk⟩ := (mem_locSub_iff (RingHom.mem_range.2 ⟨f, hf⟩) h0 z).1 hz
      obtain ⟨a, ha⟩ := RingHom.mem_range.1 hk
      refine ⟨⟨a, ⟨f ^ k, k, rfl⟩⟩, Subtype.ext ?_⟩
      simp [hval, hf, ha, mul_comm]
    · intro x y hxy
      exact ⟨1, by rw [hinj (congrArg Subtype.val hxy)]⟩

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationClosureSmoothStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_closure_smooth : ∀ {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] {ι : Type} [Finite ι] (R : Subring Ω) (v : ι → K), AlgebraicIndependent Ω v → ∀ ℓ : K, ℓ ∈ Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v) → ℓ ≠ 0 → ∀ h : (∀ a ∈ R, algebraMap Ω K a ∈ locSub (Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v)) ℓ), (((algebraMap Ω K).comp R.subtype).codRestrict (locSub (Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v)) ℓ) (fun a => h a a.2)).Smooth := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.smooth_locSub_closure | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.smooth_locSub_closure | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.smooth_locSub_closure <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameMatricesRegularGeneric
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

theorem exists_cell {F : Type} [Field F] (O : Subring F) [IsLocalRing O] {n r : ℕ}
    (A : Matrix (Fin n) (Fin r) F) (N : Matrix (Fin r) (Fin n) F) (hA : ∀ a b, A a b ∈ O)
    (hN : ∀ a b, N a b ∈ O) (hNA : N * A = 1) (Y : Matrix (Fin r) (Fin r) F)
    (hs : ∀ i : Fin r, ∃ J, NormAt O (A * Y) ((i : ℕ) + 1) i.2 J) :
    ∃ w : Equiv.Perm (Fin r), ∀ (k : ℕ) (hk : k ≤ r), NormAt O Y k hk (w ∘ Fin.castLE hk) := by
  refine GlobalTheory.T.exists_perm_normalized_minors O Y (fun k hk I' I => GlobalTheory.T.normalized_minor_extends O Y k hk I' I) fun k hk => ?_
  cases k with
  | zero => exact ⟨Fin.elim0, normAt_zero O Y _⟩
  | succ k =>
    obtain ⟨J, hJ⟩ := hs ⟨k, hk⟩
    exact exists_normAt O A N hA hN hNA Y _ hk J hJ

theorem big_cell_smooth : ∀ (Ω : Type) [Field Ω] (S : Type) [Fintype S] (r n : S → ℕ) (R : Subring Ω) (O : Subring (GenField Ω r)) [IsLocalRing O] (T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω) (N : ∀ s, Matrix (Fin (r s)) (Fin (n s)) Ω) (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)), (∀ a ∈ R, algebraMap Ω (GenField Ω r) a ∈ O) → (∀ s, (T s).det ≠ 0) → (∀ s j l, M s j l ∈ R) → (∀ s l j, N s l j ∈ R) → (∀ s, N s * M s = 1) → (∀ q, stepMinor (flagB M T q.1) q.2 (J q) ≠ 0) → (∀ (q : Σ s, Fin (r s)) (J' : Fin ((q.2 : ℕ) + 1) → Fin (n q.1)), stepMinor (flagB M T q.1) q.2 J' / stepMinor (flagB M T q.1) q.2 (J q) ∈ O) → ∃ t ∈ ratioRing R (flagB M T) J, t ≠ 0 ∧ t ∈ O ∧ t⁻¹ ∈ O ∧ ∃ h : ∀ a ∈ R, algebraMap Ω (GenField Ω r) a ∈ locSub (ratioRing R (flagB M T) J) t, (((algebraMap Ω (GenField Ω r)).comp R.subtype).codRestrict (locSub (ratioRing R (flagB M T) J) t) (fun a => h a a.2)).Smooth := by
  intro Ω _ S _ r n R O _ T M N J hRO hT hM hN hNM hJ0 hJr
  classical
  haveI : Finite (GenIx r) := by unfold GenIx; infer_instance
  set i := algebraMap Ω (GenField Ω r) with hi
  set A := ratioRing R (flagB M T) J with hAdef
  let Y : ∀ s, Matrix (Fin (r s)) (Fin (r s)) (GenField Ω r) := fun s => (T s).map i * genU Ω r s
  let Am : ∀ s, Matrix (Fin (n s)) (Fin (r s)) (GenField Ω r) := fun s => (M s).map i
  let Nm : ∀ s, Matrix (Fin (r s)) (Fin (n s)) (GenField Ω r) := fun s => (N s).map i
  have hB : ∀ s, flagB M T s = Am s * Y s := fun s => by
    show (M s * T s).map i * genU Ω r s = (M s).map i * ((T s).map i * genU Ω r s)
    rw [Matrix.map_mul, Matrix.mul_assoc]
  have hNA : ∀ s, Nm s * Am s = 1 := fun s => by
    show (N s).map i * (M s).map i = 1
    rw [← Matrix.map_mul, hNM, Matrix.map_one _ (map_zero _) (map_one _)]
  have hYN : ∀ s, Nm s * flagB M T s = Y s := fun s => by
    rw [hB, ← Matrix.mul_assoc, hNA, Matrix.one_mul]
  have hAmO : ∀ s a b, Am s a b ∈ O := fun s a b => hRO _ (hM _ _ _)
  have hNmO : ∀ s a b, Nm s a b ∈ O := fun s a b => hRO _ (hN _ _ _)

  have hw : ∀ s, ∃ w : Equiv.Perm (Fin (r s)), ∀ (k : ℕ) (hk : k ≤ r s),
      NormAt O (Y s) k hk (w ∘ Fin.castLE hk) := fun s =>
    exists_cell O (Am s) (Nm s) (hAmO s) (hNmO s) (hNA s) (Y s) fun i' => by
      refine ⟨J ⟨s, i'⟩, ?_⟩
      rw [← hB]
      exact ⟨hJ0 ⟨s, i'⟩, hJr ⟨s, i'⟩⟩
  choose w hw using hw
  have hlu := fun s => GlobalTheory.T.lu_decomposition_of_minors ((Y s).submatrix (w s) id) fun k hk => (hw s k hk).1
  choose C V hC hV0 hV1 hCV using hlu

  let v : GenIx r → GenField Ω r := fun q => V q.1 q.2.1.1 q.2.1.2
  set B := Subring.closure (((R.map i : Subring _) : Set (GenField Ω r)) ∪ Set.range v) with hBdef
  have hRB : ∀ a ∈ R, i a ∈ B := fun a ha =>
    Subring.subset_closure (Or.inl ⟨a, ha, rfl⟩)
  have hRA : ∀ a ∈ R, i a ∈ A := fun a ha =>
    Subring.subset_closure (Or.inl ⟨a, ha, rfl⟩)
  have hVB : ∀ s l k, V s l k ∈ B := fun s l k => by
    rcases lt_trichotomy l k with h | h | h
    · rw [hV0 s l k h]; exact B.zero_mem
    · rw [h, hV1]; exact B.one_mem
    · exact Subring.subset_closure (Or.inr ⟨⟨s, ⟨(l, k), h⟩⟩, rfl⟩)

  let y0 : (q : Σ s, Fin (r s)) → GenField Ω r := fun q =>
    kMinor (Y q.1) ((q.2 : ℕ) + 1) q.2.2 (w q.1 ∘ Fin.castLE q.2.2)
  have hy0 : ∀ q, y0 q ≠ 0 := fun q => (hw q.1 _ q.2.2).1
  have hrat : ∀ (s : S) (k : ℕ) (hk : k ≤ r s) (I : Fin k → Fin (r s)),
      kMinor (Y s) k hk (w s ∘ I) / kMinor (Y s) k hk (w s ∘ Fin.castLE hk) = kMinor (V s) k hk I :=
    fun s k hk I => ratio_eq_kMinor ((Y s).submatrix (w s) id) (C s) (V s) (hC s) (hV0 s) (hV1 s) (hCV s) k hk I
      (hw s k hk).1
  have hyB : ∀ (q : Σ s, Fin (r s)) I, kMinor (Y q.1) ((q.2 : ℕ) + 1) q.2.2 I / y0 q ∈ B := fun q I => by
    have e : I = w q.1 ∘ ((w q.1).symm ∘ I) := by
      ext a; simp
    rw [e]
    show kMinor (Y q.1) _ q.2.2 _ / kMinor (Y q.1) _ q.2.2 _ ∈ B
    rw [hrat]
    exact kMinor_mem B _ (hVB q.1) _ _ _
  have hPB : ∀ (q : Σ s, Fin (r s)) J', stepMinor (flagB M T q.1) q.2 J' / y0 q ∈ B := fun q J' => by
    rw [hB, stepMinor_eq_kMinor]
    exact kMinor_mul_div_mem B (Am q.1) (Y q.1) _ q.2.2 _ (fun a b => hRB _ (hM _ _ _)) (hyB q) J'
  have hPA : ∀ (q : Σ s, Fin (r s)) J', stepMinor (flagB M T q.1) q.2 J' / stepMinor (flagB M T q.1) q.2 (J q) ∈ A :=
    fun q J' => Subring.subset_closure (Or.inr ⟨q, J', rfl⟩)
  have hyA : ∀ (q : Σ s, Fin (r s)) I, kMinor (Y q.1) ((q.2 : ℕ) + 1) q.2.2 I /
      stepMinor (flagB M T q.1) q.2 (J q) ∈ A := fun q I => by
    rw [← hYN q.1]
    exact kMinor_mul_div_mem A (Nm q.1) (flagB M T q.1) _ q.2.2 _ (fun a b => hRA _ (hN _ _ _)) (hPA q) I
  have hAO : A ≤ O := by
    refine Subring.closure_le.2 ?_
    rintro a (⟨b, hb, rfl⟩ | ⟨q, J', rfl⟩)
    · exact hRO b hb
    · exact hJr q J'

  let tq : (Σ s, Fin (r s)) → GenField Ω r := fun q => y0 q / stepMinor (flagB M T q.1) q.2 (J q)
  have htq0 : ∀ q, tq q ≠ 0 := fun q => div_ne_zero (hy0 q) (hJ0 q)
  have htqA : ∀ q, tq q ∈ A := fun q => hyA q _
  have htqB : ∀ q, (tq q)⁻¹ ∈ B := fun q => by
    show (y0 q / _)⁻¹ ∈ B
    rw [inv_div]
    exact hPB q _
  have htqO : ∀ q, (tq q)⁻¹ ∈ O := fun q => by
    show (y0 q / _)⁻¹ ∈ O
    rw [inv_div, hB, stepMinor_eq_kMinor]
    exact kMinor_mul_div_mem O (Am q.1) (Y q.1) _ q.2.2 _ (hAmO q.1) (hw q.1 _ q.2.2).2 _
  have hAB : A ≤ Subring.closure ((B : Set (GenField Ω r)) ∪ Set.range tq) := by
    refine Subring.closure_le.2 ?_
    rintro a (⟨b, hb, rfl⟩ | ⟨q, J', rfl⟩)
    · exact Subring.subset_closure (Or.inl (hRB b hb))
    · have e : stepMinor (flagB M T q.1) q.2 J' / stepMinor (flagB M T q.1) q.2 (J q) =
          (stepMinor (flagB M T q.1) q.2 J' / y0 q) * tq q := by
        show _ = _ * (y0 q / _)
        have := hy0 q
        have := hJ0 q
        field_simp
      rw [SetLike.mem_coe, e]
      exact mul_mem (Subring.subset_closure (Or.inl (hPB q J'))) (Subring.subset_closure (Or.inr ⟨q, rfl⟩))
  have hBA : B ≤ Subring.closure ((A : Set (GenField Ω r)) ∪ Set.range fun q => (tq q)⁻¹) := by
    refine Subring.closure_le.2 ?_
    rintro a (⟨b, hb, rfl⟩ | ⟨q, rfl⟩)
    · exact Subring.subset_closure (Or.inl (hRA b hb))
    · obtain ⟨s, ⟨⟨l, k⟩, hlk⟩⟩ := q
      have hlk' : k < l := hlk
      have e1 : V s l k = kMinor (Y s) ((k : ℕ) + 1) k.2 (w s ∘ lastRow k l) / y0 ⟨s, k⟩ := by
        rw [← kMinor_lower_lastRow (V s) (hV0 s) (hV1 s) k l hlk', ← hrat]
      have e2 : V s l k = (kMinor (Y s) ((k : ℕ) + 1) k.2 (w s ∘ lastRow k l) /
          stepMinor (flagB M T s) k (J ⟨s, k⟩)) * (tq ⟨s, k⟩)⁻¹ := by
        rw [e1]
        show _ = _ * (y0 ⟨s, k⟩ / _)⁻¹
        have := hy0 ⟨s, k⟩
        have := hJ0 ⟨s, k⟩
        field_simp
      show V s l k ∈ _
      rw [e2]
      exact mul_mem (Subring.subset_closure (Or.inl (hyA ⟨s, k⟩ _))) (Subring.subset_closure (Or.inr ⟨_, rfl⟩))

  have hv : AlgebraicIndependent Ω v := by
    refine GlobalTheory.T.algebraic_independent_of_adjoin _ v (genU_indep Ω r) fun q => ?_
    rw [← genU_gen]
    have hmem : ∀ s l k, V s l k ∈ IntermediateField.adjoin Ω (Set.range v) := fun s l k => by
      rcases lt_trichotomy l k with h | h | h
      · rw [hV0 s l k h]; exact zero_mem _
      · rw [h, hV1]; exact one_mem _
      · exact IntermediateField.subset_adjoin _ _ ⟨⟨s, ⟨(l, k), h⟩⟩, rfl⟩
    refine entries_mem _ ((T q.1).submatrix (w q.1) id) ?_ (genU Ω r q.1) (C q.1) (V q.1)
      (genU_zero Ω r q.1) (genU_one Ω r q.1) (hC q.1) (hV0 q.1) (hV1 q.1) ?_ (hmem q.1) _ _ q.2.2
    · rw [Matrix.det_permute]
      exact mul_ne_zero (by rcases Int.units_eq_one_or (Equiv.Perm.sign (w q.1)) with h | h <;> simp [h]) (hT _)
    · rw [← hCV q.1]
      congr 1

  have hL := GlobalTheory.T.localization_closure_equal A B tq htq0 htqA htqB hAB hBA
  have htA : (∏ q, tq q) ∈ A := A.prod_mem fun q _ => htqA q
  have hinv : (∏ q, tq q)⁻¹ = ∏ q, (tq q)⁻¹ := (Finset.prod_inv_distrib _).symm
  refine ⟨∏ q, tq q, htA, Finset.prod_ne_zero_iff.2 fun q _ => htq0 q, hAO htA, ?_, ?_⟩
  · rw [hinv]
    exact O.prod_mem fun q _ => htqO q
  have hR : ∀ a ∈ R, i a ∈ locSub A (∏ q, tq q) := fun a ha => le_locSub _ _ (hRA a ha)
  refine ⟨hR, ?_⟩
  have gen : ∀ (L : Subring (GenField Ω r)), L = locSub B (∏ q, tq q)⁻¹ → ∀ h : ∀ a ∈ R, i a ∈ L,
      ((i.comp R.subtype).codRestrict L (fun a => h a a.2)).Smooth := by
    rintro _ rfl h
    refine GlobalTheory.T.localization_closure_smooth R v hv _ ?_ (inv_ne_zero (Finset.prod_ne_zero_iff.2 fun q _ => htq0 q)) h
    rw [hinv]
    exact B.prod_mem fun q _ => htqB q
  exact gen _ hL hR

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameMatricesRegularGenericStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_matrices_regular_generic : ∀ (Ω : Type) [Field Ω] (S : Type) [Fintype S] (r n : S → ℕ) (R : Subring Ω) (O : Subring (GenField Ω r)) [IsLocalRing O] (T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω) (N : ∀ s, Matrix (Fin (r s)) (Fin (n s)) Ω) (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)), (∀ a ∈ R, algebraMap Ω (GenField Ω r) a ∈ O) → (∀ s, (T s).det ≠ 0) → (∀ s j l, M s j l ∈ R) → (∀ s l j, N s l j ∈ R) → (∀ s, N s * M s = 1) → (∀ q, stepMinor (flagB M T q.1) q.2 (J q) ≠ 0) → (∀ (q : Σ s, Fin (r s)) (J' : Fin ((q.2 : ℕ) + 1) → Fin (n q.1)), stepMinor (flagB M T q.1) q.2 J' / stepMinor (flagB M T q.1) q.2 (J q) ∈ O) → ∃ t ∈ ratioRing R (flagB M T) J, t ≠ 0 ∧ t ∈ O ∧ t⁻¹ ∈ O ∧ ∃ h : ∀ a ∈ R, algebraMap Ω (GenField Ω r) a ∈ locSub (ratioRing R (flagB M T) J) t, (((algebraMap Ω (GenField Ω r)).comp R.subtype).codRestrict (locSub (ratioRing R (flagB M T) J) t) (fun a => h a a.2)).Smooth := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.big_cell_smooth | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.big_cell_smooth | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.big_cell_smooth <;> assumption)
end
