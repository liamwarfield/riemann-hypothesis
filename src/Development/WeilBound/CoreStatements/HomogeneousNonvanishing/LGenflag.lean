module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LGenflagFld
section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LGenflagLU
open GlobalTheory.CompanionTheory.Ar Matrix

namespace PositivityTheory.UnitarySelfGeneration.GF

variable {r : ℕ}

def trunc {R : Type} [CommRing R] (k : Fin r) (A : Matrix (Fin r) (Fin r) R) : Matrix (Fin r) (Fin r) R :=
  Matrix.of fun i j => if i ≤ k ∧ j ≤ k then A i j else if i = j then 1 else 0

def Uni {R : Type} [CommRing R] (L : Matrix (Fin r) (Fin r) R) : Prop :=
  (∀ k, L k k = 1) ∧ ∀ l k, l < k → L l k = 0

def Up {R : Type} [CommRing R] (C : Matrix (Fin r) (Fin r) R) : Prop := ∀ l k, k < l → C l k = 0

section Ring

variable {R R' : Type} [CommRing R] [CommRing R']

theorem trunc_map (φ : R →+* R') (k : Fin r) (A : Matrix (Fin r) (Fin r) R) :
    trunc k (A.map φ) = (trunc k A).map φ := by
  ext i j
  simp only [trunc, of_apply, map_apply]
  split_ifs <;> simp

theorem det_trunc_map (φ : R →+* R') (k : Fin r) (A : Matrix (Fin r) (Fin r) R) :
    (trunc k (A.map φ)).det = φ (trunc k A).det := by
  rw [trunc_map, RingHom.map_det, RingHom.mapMatrix_apply]

theorem Uni.map {L : Matrix (Fin r) (Fin r) R} (h : Uni L) (φ : R →+* R') : Uni (L.map φ) :=
  ⟨fun k => by simp [h.1], fun l k hlk => by simp [h.2 l k hlk]⟩

theorem Up.map {L : Matrix (Fin r) (Fin r) R} (h : Up L) (φ : R →+* R') : Up (L.map φ) :=
  fun l k hlk => by simp [h l k hlk]

theorem Uni.det {L : Matrix (Fin r) (Fin r) R} (h : Uni L) : L.det = 1 := by
  rw [det_of_isLowerTriangular L (fun i j hij => h.2 i j hij)]
  simp [h.1]

theorem Uni.trunc {L : Matrix (Fin r) (Fin r) R} (h : Uni L) (k : Fin r) : Uni (trunc k L) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · simp [GF.trunc, h.1]
  · simp [GF.trunc, h.2 i j hij, hij.ne]

theorem uni_one : Uni (1 : Matrix (Fin r) (Fin r) R) :=
  ⟨fun k => by simp, fun l k h => by simp [h.ne]⟩

theorem trunc_mul (k : Fin r) (A C : Matrix (Fin r) (Fin r) R) (hC : Up C) :
    trunc k (A * C) = trunc k A * trunc k C := by
  ext i j
  simp only [trunc, of_apply, Matrix.mul_apply]
  by_cases hi : i ≤ k
  · by_cases hj : j ≤ k
    · simp only [hi, hj, and_self, if_true, true_and, and_true]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases hl : l ≤ k
      · simp [hl]
      · have h1 : j < l := lt_of_le_of_lt hj (not_le.1 hl)
        simp [hl, hC l j h1, h1.ne']
    · have hij : i ≠ j := fun e => hj (e ▸ hi)
      simp only [hi, hj, and_false, if_false, true_and, hij]
      refine (Finset.sum_eq_zero fun l _ => ?_).symm
      by_cases hl : l = j
      · subst hl; simp [hj, hij]
      · simp [hl]
  · simp only [hi, false_and, if_false]
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro l _ hl; simp [Ne.symm hl]
    · simp

theorem Up.mul {A B : Matrix (Fin r) (Fin r) R} (hA : Up A) (hB : Up B) : Up (A * B) := by
  have h : BlockTriangular (A * B) id :=
    BlockTriangular.mul (fun i j h => hA i j h) (fun i j h => hB i j h)
  exact fun i j hij => h hij

end Ring

variable {F F' : Type} [Field F] [Field F']

theorem Up.inv {A : Matrix (Fin r) (Fin r) F} (hA : Up A) (h0 : A.det ≠ 0) : Up A⁻¹ := by
  let _ := A.invertibleOfIsUnitDet (IsUnit.mk0 _ h0)
  have h : BlockTriangular A⁻¹ id := blockTriangular_inv_of_blockTriangular (fun i j h => hA i j h)
  exact fun i j hij => h hij

theorem exists_lu (A : Matrix (Fin r) (Fin r) F) (h : ∀ k, (trunc k A).det ≠ 0) :
    ∃ C, Up C ∧ Uni (A * C) := by
  have hx : ∀ k, ∃ x : Fin r → F, trunc k A *ᵥ x = Pi.single k 1 := fun k =>
    ⟨(trunc k A)⁻¹ *ᵥ Pi.single k 1, by
      rw [mulVec_mulVec, mul_nonsing_inv _ (IsUnit.mk0 _ (h k)), one_mulVec]⟩
  choose x hx using hx
  have hup : ∀ l k, k < l → x k l = 0 := by
    intro l k hkl
    have := congrFun (hx k) l
    simp only [mulVec, dotProduct, trunc, of_apply, not_le.2 hkl, false_and, if_false] at this
    rw [Finset.sum_eq_single l] at this
    · simpa [hkl.ne'] using this
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  have key : ∀ l k, l ≤ k → (A * Matrix.of fun l k => x k l) l k = (Pi.single k 1 : Fin r → F) l := by
    intro l k hlk
    rw [← congrFun (hx k) l]
    simp only [Matrix.mul_apply, mulVec, dotProduct, trunc, of_apply, hlk, true_and]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : b ≤ k
    · simp [hb]
    · simp [hup b k (not_le.1 hb)]
  refine ⟨Matrix.of fun l k => x k l, hup, fun k => ?_, fun l k hlk => ?_⟩
  · rw [key k k le_rfl]; simp
  · rw [key l k hlk.le]; simp [hlk.ne]

theorem dets_of_lu {A C : Matrix (Fin r) (Fin r) F} (hC : Up C) (h : Uni (A * C)) :
    A.det ≠ 0 ∧ C.det ≠ 0 ∧ ∀ k, (trunc k A).det ≠ 0 ∧ (trunc k C).det ≠ 0 := by
  have h1 := h.det
  rw [det_mul] at h1
  refine ⟨left_ne_zero_of_mul_eq_one h1, right_ne_zero_of_mul_eq_one h1, fun k => ?_⟩
  have h2 := (h.trunc k).det
  rw [trunc_mul k A C hC, det_mul] at h2
  exact ⟨left_ne_zero_of_mul_eq_one h2, right_ne_zero_of_mul_eq_one h2⟩

theorem uni_mul_up {L W : Matrix (Fin r) (Fin r) F} (hL : Uni L) (hW : Up W) (h : Uni (L * W)) : W = 1 := by
  have hL0 : L.det ≠ 0 := by rw [hL.det]; exact one_ne_zero
  have h1 : Up (Lᵀ) := fun i j hij => hL.2 j i hij
  have h2 : Up ((L * W)ᵀ) := fun i j hij => h.2 j i hij
  have h3 : Up ((L * W)ᵀ * (Lᵀ)⁻¹) := h2.mul (h1.inv (by rwa [det_transpose]))
  rw [transpose_mul, Matrix.mul_assoc, mul_nonsing_inv _ (IsUnit.mk0 _ (by rwa [det_transpose])),
    Matrix.mul_one] at h3
  have hoff : ∀ i j, i ≠ j → W i j = 0 := fun i j hij =>
    (lt_or_gt_of_ne hij).elim (fun h => h3 j i h) (fun h => hW i j h)
  ext i j
  by_cases hij : i = j
  · subst hij
    have := h.1 i
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at this
    · simpa [hL.1] using this
    · intro b _ hb; simp [hoff b i hb]
    · simp
  · rw [hoff i j hij, one_apply_ne hij]

theorem lu_unique {A C C' : Matrix (Fin r) (Fin r) F} (hC : Up C) (h : Uni (A * C)) (hC' : Up C')
    (h' : Uni (A * C')) : A * C = A * C' := by
  have h0 := (dets_of_lu hC h).2.1
  have e : A * C' = A * C * (C⁻¹ * C') := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc C, mul_nonsing_inv _ (IsUnit.mk0 _ h0), Matrix.one_mul]
  have := uni_mul_up h ((hC.inv h0).mul hC') (e ▸ h')
  rw [e, this, Matrix.mul_one]

theorem lu_mem (K : Subfield F) {A C : Matrix (Fin r) (Fin r) F} (hC : Up C) (h : Uni (A * C))
    (hA : ∀ i j, A i j ∈ K) : ∀ i j, (A * C) i j ∈ K := by
  let A₀ : Matrix (Fin r) (Fin r) K := Matrix.of fun i j => ⟨A i j, hA i j⟩
  have e : A₀.map K.subtype = A := rfl
  obtain ⟨C₀, h1, h2⟩ := exists_lu A₀ fun k h0 => ((dets_of_lu hC h).2.2 k).1 (by
    rw [← e, det_trunc_map, h0, map_zero])
  have h3 := h2.map K.subtype
  have e2 : (A₀ * C₀).map K.subtype = A * C₀.map K.subtype := by rw [Matrix.map_mul, e]
  rw [e2] at h3
  rw [lu_unique hC h (h1.map K.subtype) h3, ← e2]
  exact fun i j => ((A₀ * C₀) i j).2

theorem exists_general (g : Matrix (Fin r) (Fin r) F) (hg : g.det ≠ 0) :
    ∃ w : Matrix (Fin r) (Fin r) (RatFunc F), Uni w ∧
      ∀ k, (trunc k (g.map (algebraMap F (RatFunc F)) * w)).det ≠ 0 := by
  let N : Matrix (Fin r) (Fin r) (Polynomial F) :=
    (Polynomial.X : Polynomial F) • 1 + (1 - Polynomial.X : Polynomial F) • (g⁻¹).map Polynomial.C
  let φ := algebraMap (Polynomial F) (RatFunc F)
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  have e1 : N.map (Polynomial.evalRingHom (1 : F)) = 1 := by
    ext i j
    by_cases h : i = j <;> simp [N, h, Matrix.one_apply]
  have e0 : (g.map Polynomial.C * N).map (Polynomial.evalRingHom (0 : F)) = 1 := by
    rw [Matrix.map_mul, ← mul_nonsing_inv g (IsUnit.mk0 _ hg)]
    congr 1
    · ext i j; simp
    · ext i j
      by_cases h : i = j <;> simp [N, h, one_apply]
  have nz : ∀ (M : Matrix (Fin r) (Fin r) (Polynomial F)) (a : F), M.map (Polynomial.evalRingHom a) = 1 →
      ∀ k, (trunc k (M.map φ)).det ≠ 0 := by
    intro M a hM k h0
    rw [det_trunc_map, map_eq_zero_iff _ hφ] at h0
    have := det_trunc_map (Polynomial.evalRingHom a) k M
    rw [hM, h0, map_zero, (uni_one.trunc k).det] at this
    exact one_ne_zero this
  obtain ⟨C, hC, hU⟩ := exists_lu (N.map φ) (nz N 1 e1)
  refine ⟨_, hU, fun k => ?_⟩
  have e : g.map (algebraMap F (RatFunc F)) * N.map φ = (g.map Polynomial.C * N).map φ := by
    rw [Matrix.map_mul, Matrix.map_map]
    rfl
  rw [← Matrix.mul_assoc, trunc_mul _ _ _ hC, det_mul, e]
  exact mul_ne_zero (nz _ 0 e0 k) ((dets_of_lu hC hU).2.2 k).2

def fl (M : Matrix (Fin r) (Fin r) F) (i : ℕ) : Submodule F (Fin r → F) := flagStep F (fun k l => M l k) i

theorem fl_mul_le (M C : Matrix (Fin r) (Fin r) F) (hC : Up C) (i : ℕ) : fl (M * C) i ≤ fl M i := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨k, hk, rfl⟩
  have : (fun l => (M * C) l k) = ∑ b, C b k • fun l => M l b := by
    funext l
    simp [Matrix.mul_apply, Finset.sum_apply, mul_comm]
  simp only [this]
  refine Submodule.sum_mem _ fun b _ => ?_
  by_cases hb : k < b
  · rw [hC b k hb, zero_smul]; exact Submodule.zero_mem _
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, ?_, rfl⟩)
    exact lt_of_le_of_lt (Fin.le_def.1 (not_lt.1 hb)) hk

theorem fl_mul (M C : Matrix (Fin r) (Fin r) F) (hC : Up C) (h0 : C.det ≠ 0) (i : ℕ) : fl (M * C) i = fl M i := by
  refine le_antisymm (fl_mul_le M C hC i) ?_
  have := fl_mul_le (M * C) C⁻¹ (hC.inv h0) i
  rwa [Matrix.mul_assoc, mul_nonsing_inv _ (IsUnit.mk0 _ h0), Matrix.mul_one] at this

theorem flagStep_map {E E' : Type} [AddCommGroup E] [Module F E] [AddCommGroup E'] [Module F E'] (f : E →ₗ[F] E')
    (b : Fin r → E) (i : ℕ) : (flagStep F b i).map f = flagStep F (fun k => f (b k)) i := by
  unfold flagStep
  rw [Submodule.map_span, Set.image_image]

theorem fl_of_indep {E : Type} [AddCommGroup E] [Module F E] {e : Fin r → E} (he : LinearIndependent F e)
    {M N : Matrix (Fin r) (Fin r) F} {i : ℕ}
    (h : flagStep F (fun k => ∑ l, M l k • e l) i = flagStep F (fun k => ∑ l, N l k • e l) i) : fl M i = fl N i := by
  apply Submodule.map_injective_of_injective (f := Fintype.linearCombination F e)
    (he.fintypeLinearCombination_injective)
  unfold fl
  rw [flagStep_map, flagStep_map]
  simpa only [Fintype.linearCombination_apply] using h

end PositivityTheory.UnitarySelfGeneration.GF
end

open GlobalTheory.CompanionTheory.Ar Matrix

namespace PositivityTheory.UnitarySelfGeneration.GF

variable {S : Type} {r : S → ℕ} {Ω : Type} [Field Ω]

abbrev Idx (r : S → ℕ) : Type := Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1}

abbrev ent {F : Type} (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F) : Idx r → F := fun q => u q.1 q.2.1.1 q.2.1.2

noncomputable def gen (Ω : Type) [Field Ω] (r : S → ℕ) (σ : S) :
    Matrix (Fin (r σ)) (Fin (r σ)) (MvPolynomial (Idx r) Ω) :=
  Matrix.of fun l k => if h : k < l then MvPolynomial.X ⟨σ, ⟨(l, k), h⟩⟩ else if l = k then 1 else 0

theorem gen_map {F : Type} [Field F] [Algebra Ω F] (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F)
    (hu : ∀ σ, Uni (u σ)) (σ : S) :
    (gen Ω r σ).map (MvPolynomial.aeval (R := Ω) (ent u)).toRingHom = u σ := by
  ext l k
  simp only [gen, map_apply, of_apply]
  split_ifs with h1 h2
  · simp [ent]
  · subst h2; simp [(hu σ).1]
  · simp [(hu σ).2 l k (lt_of_le_of_ne (not_lt.1 h1) h2)]

theorem general_of_indep {F : Type} [Field F] [Algebra Ω F] (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F)
    (hu : ∀ σ, Uni (u σ)) (hi : AlgebraicIndependent Ω (ent u)) (g : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) Ω)
    (hg : ∀ σ, (g σ).det ≠ 0) (σ : S) (k : Fin (r σ)) :
    (trunc k ((g σ).map (algebraMap Ω F) * u σ)).det ≠ 0 := by
  choose w hw hw' using fun σ => exists_general (g σ) (hg σ)
  have key : ∀ (F : Type) [Field F] [Algebra Ω F] (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F),
      (∀ σ, Uni (u σ)) → (trunc k ((g σ).map (algebraMap Ω F) * u σ)).det =
        MvPolynomial.aeval (R := Ω) (ent u) (trunc k ((g σ).map MvPolynomial.C * gen Ω r σ)).det := by
    intro F _ _ u hu
    have := det_trunc_map (MvPolynomial.aeval (R := Ω) (ent u)).toRingHom k ((g σ).map MvPolynomial.C * gen Ω r σ)
    rw [Matrix.map_mul, gen_map u hu σ, Matrix.map_map] at this
    have e : (⇑(MvPolynomial.aeval (R := Ω) (ent u)).toRingHom ∘ ⇑MvPolynomial.C) = algebraMap Ω F := by
      funext a
      simp
    rw [e] at this
    exact this
  intro h0
  rw [key F u hu, map_eq_zero_iff _ hi] at h0
  exact hw' σ k (by rw [key _ w hw, h0, map_zero])

theorem mem_adjoin_ent {F : Type} [Field F] [Algebra Ω F] (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F)
    (hu : ∀ σ, Uni (u σ)) (σ : S) (l k : Fin (r σ)) : u σ l k ∈ IntermediateField.adjoin Ω (Set.range (ent u)) := by
  rcases lt_trichotomy l k with h | h | h
  · rw [(hu σ).2 l k h]; exact zero_mem _
  · rw [h, (hu σ).1]; exact one_mem _
  · exact IntermediateField.subset_adjoin _ _ ⟨⟨σ, ⟨(l, k), h⟩⟩, rfl⟩

theorem adjoin_all {F : Type} [Field F] [Algebra Ω F] (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F)
    (hu : ∀ σ, Uni (u σ)) :
    IntermediateField.adjoin Ω (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2) =
      IntermediateField.adjoin Ω (Set.range (ent u)) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨q, rfl⟩
    exact mem_adjoin_ent u hu _ _ _
  · apply IntermediateField.adjoin.mono
    rintro _ ⟨q, rfl⟩
    exact ⟨⟨q.1, q.2.1⟩, rfl⟩

theorem adjoin_le {F : Type} [Field F] [Algebra Ω F] (u u' : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F)
    (hu : ∀ σ, Uni (u σ)) (hu' : ∀ σ, Uni (u' σ)) (g : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) Ω)
    (C : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F) (hC : ∀ σ, Up (C σ))
    (e : ∀ σ, u' σ = (g σ).map (algebraMap Ω F) * u σ * C σ) :
    IntermediateField.adjoin Ω (Set.range (ent u')) ≤ IntermediateField.adjoin Ω (Set.range (ent u)) := by
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨q, rfl⟩
  have := lu_mem (IntermediateField.adjoin Ω (Set.range (ent u))).toSubfield (hC q.1) (e q.1 ▸ hu' q.1)
    (fun i j => by
      rw [Matrix.mul_apply]
      exact sum_mem fun l _ => mul_mem (IntermediateField.algebraMap_mem _ _) (mem_adjoin_ent u hu _ _ _))
  rw [← e q.1] at this
  exact this _ _

theorem change [Finite S] {F : Type} [Field F] [Algebra Ω F] (u : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F)
    (hu : ∀ σ, Uni (u σ)) (hi : AlgebraicIndependent Ω (ent u))
    (hf : FiniteDimensional (IntermediateField.adjoin Ω (Set.range (ent u))) F)
    (g : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) Ω) (hg : ∀ σ, (g σ).det ≠ 0) :
    ∃ u' : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F, (∀ σ, Uni (u' σ)) ∧ AlgebraicIndependent Ω (ent u') ∧
      IntermediateField.adjoin Ω (Set.range (ent u')) = IntermediateField.adjoin Ω (Set.range (ent u)) ∧
      ∀ σ i, fl (u' σ) i = fl ((g σ).map (algebraMap Ω F) * u σ) i := by
  choose C hC hU using fun σ => exists_lu _ (general_of_indep u hu hi g hg σ)
  have hC0 := fun σ => (dets_of_lu (hC σ) (hU σ)).2.1
  let u' : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) F := fun σ => (g σ).map (algebraMap Ω F) * u σ * C σ
  have heq : IntermediateField.adjoin Ω (Set.range (ent u')) = IntermediateField.adjoin Ω (Set.range (ent u)) := by
    refine le_antisymm (adjoin_le u u' hu hU g C hC fun _ => rfl)
      (adjoin_le u' u hU hu (fun σ => (g σ)⁻¹) (fun σ => (C σ)⁻¹) (fun σ => (hC σ).inv (hC0 σ)) fun σ => ?_)
    simp only [u']
    rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ (IsUnit.mk0 _ (hC0 σ)), Matrix.mul_one,
      ← Matrix.mul_assoc, ← Matrix.map_mul, nonsing_inv_mul _ (IsUnit.mk0 _ (hg σ)),
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  refine ⟨u', hU, ?_, heq, fun σ i => fl_mul _ _ (hC σ) (hC0 σ) i⟩
  have a1 : Algebra.IsAlgebraic (IntermediateField.adjoin Ω (Set.range (ent u))) F := inferInstance
  have a2 : Algebra.IsAlgebraic (IntermediateField.adjoin Ω (Set.range (ent u'))) F := by rw [heq]; exact a1
  rw [IntermediateField.isAlgebraic_adjoin_iff_top] at a1 a2
  have b1 := hi.isTranscendenceBasis_iff_isAlgebraic.2 a1
  exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite Ω (ent u') b1.cardinalMk_eq_trdeg.le).1

theorem compositum (K Ω₁ Ω₂ : Type) [Field K] [Field Ω₁] [Field Ω₂] [Algebra K Ω₁] [Algebra K Ω₂]
    [FiniteDimensional K Ω₁] [FiniteDimensional K Ω₂] :
    ∃ (Ω₃ : Type) (_ : Field Ω₃) (i₁ : Ω₁ →+* Ω₃) (i₂ : Ω₂ →+* Ω₃),
      (∀ x, i₁ (algebraMap K Ω₁ x) = i₂ (algebraMap K Ω₂ x)) ∧
      ∃ n₁ n₂ : ℕ, 0 < n₁ ∧ n₁ * Module.finrank K Ω₁ = n₂ * Module.finrank K Ω₂ ∧
        Module.finrank i₁.fieldRange Ω₃ = n₁ ∧ Module.finrank i₂.fieldRange Ω₃ = n₂ := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (TensorProduct K Ω₁ Ω₂)
  let Ω₃ := TensorProduct K Ω₁ Ω₂ ⧸ M
  let _ : Field Ω₃ := Ideal.Quotient.field M
  have fin : FiniteDimensional K Ω₃ :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K M).toLinearMap (Ideal.Quotient.mkₐ_surjective K M)
  let j₁ : Ω₁ →ₐ[K] Ω₃ := (Ideal.Quotient.mkₐ K M).comp Algebra.TensorProduct.includeLeft
  let j₂ : Ω₂ →ₐ[K] Ω₃ := (Ideal.Quotient.mkₐ K M).comp Algebra.TensorProduct.includeRight
  have e₁ := (letI : Module.Free j₁.fieldRange Ω₃ := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank K j₁.fieldRange Ω₃)
  have e₂ := (letI : Module.Free j₂.fieldRange Ω₃ := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank K j₂.fieldRange Ω₃)
  have q₁ : Module.finrank K Ω₁ = Module.finrank K j₁.fieldRange :=
    (AlgEquiv.ofInjectiveField j₁).toLinearEquiv.finrank_eq
  have q₂ : Module.finrank K Ω₂ = Module.finrank K j₂.fieldRange :=
    (AlgEquiv.ofInjectiveField j₂).toLinearEquiv.finrank_eq
  rw [← q₁] at e₁
  rw [← q₂] at e₂
  refine ⟨Ω₃, inferInstance, j₁.toRingHom, j₂.toRingHom, fun x => (j₁.commutes x).trans (j₂.commutes x).symm,
    Module.finrank j₁.fieldRange Ω₃, Module.finrank j₂.fieldRange Ω₃, Module.finrank_pos, ?_, rfl, rfl⟩
  rw [mul_comm, e₁, mul_comm, e₂]

theorem compositum' {Ω₁ Ω₂ : Type} [Field Ω₁] [Field Ω₂] [Algebra Ω Ω₁] [Algebra Ω Ω₂] {I : Type}
    (x₁ : I → Ω₁) (x₂ : I → Ω₂) (h₁ : AlgebraicIndependent Ω x₁) (h₂ : AlgebraicIndependent Ω x₂)
    (f₁ : FiniteDimensional (IntermediateField.adjoin Ω (Set.range x₁)) Ω₁)
    (f₂ : FiniteDimensional (IntermediateField.adjoin Ω (Set.range x₂)) Ω₂) :
    ∃ (Ω₃ : Type) (_ : Field Ω₃) (i₁ : Ω₁ →+* Ω₃) (i₂ : Ω₂ →+* Ω₃),
      (∀ a, i₁ (algebraMap Ω Ω₁ a) = i₂ (algebraMap Ω Ω₂ a)) ∧ (∀ q, i₁ (x₁ q) = i₂ (x₂ q)) ∧
      ∃ n₁ n₂ : ℕ, 0 < n₁ ∧ n₁ * Module.finrank (IntermediateField.adjoin Ω (Set.range x₁)) Ω₁ =
          n₂ * Module.finrank (IntermediateField.adjoin Ω (Set.range x₂)) Ω₂ ∧
        Module.finrank i₁.fieldRange Ω₃ = n₁ ∧ Module.finrank i₂.fieldRange Ω₃ = n₂ := by
  let K₁ := IntermediateField.adjoin Ω (Set.range x₁)
  let K₂ := IntermediateField.adjoin Ω (Set.range x₂)
  let e : K₁ ≃ₐ[Ω] K₂ := h₁.aevalEquivField.symm.trans h₂.aevalEquivField
  let _ : Algebra K₁ Ω₂ := ((algebraMap K₂ Ω₂).comp e.toRingEquiv.toRingHom).toAlgebra
  have hr : Module.finrank K₁ Ω₂ = Module.finrank K₂ Ω₂ :=
    Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv (RingEquiv.refl _) rfl
  have : FiniteDimensional K₁ Ω₂ := Module.finite_of_finrank_pos (by rw [hr]; exact Module.finrank_pos)
  obtain ⟨Ω₃, _, i₁, i₂, h, n₁, n₂, hn, e', e₁, e₂⟩ := compositum K₁ Ω₁ Ω₂
  refine ⟨Ω₃, inferInstance, i₁, i₂, fun a => ?_, fun q => ?_, n₁, n₂, hn, hr ▸ e', e₁, e₂⟩
  · refine (h (algebraMap Ω K₁ a)).trans ?_
    congr 1
    change ((e (algebraMap Ω K₁ a) : K₂) : Ω₂) = _
    rw [e.commutes]
    rfl
  · have := h (h₁.aevalEquivField (algebraMap (MvPolynomial I Ω) _ (MvPolynomial.X q)))
    change i₁ (h₁.aevalEquivField (algebraMap (MvPolynomial I Ω) _ (MvPolynomial.X q)) : Ω₁) =
      i₂ (e (h₁.aevalEquivField (algebraMap (MvPolynomial I Ω) _ (MvPolynomial.X q))) : Ω₂) at this
    simp only [e, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply] at this
    rw [h₁.aevalEquivField_algebraMap_apply_coe, h₂.aevalEquivField_algebraMap_apply_coe] at this
    simpa using this

theorem fl_coord {Ω' : Type} [Field Ω'] [Algebra Ω Ω'] {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E']
    [Module Ω' E'] (j : E →+ E') (hj : ∀ (a : Ω) e, j (a • e) = algebraMap Ω Ω' a • j e) {n : ℕ} {c c' : Fin n → E}
    (hc' : LinearIndependent Ω' fun k => j (c' k)) {h : Matrix (Fin n) (Fin n) Ω} (hh : ∀ k, c k = ∑ l, h l k • c' l)
    {b : Fin n → E'} {m u : Matrix (Fin n) (Fin n) Ω'} (hb : ∀ k, b k = ∑ l, m l k • j (c l)) {i : ℕ}
    (hf : flagStep Ω' b i = flagStep Ω' (fun k => ∑ l, u l k • j (c' l)) i) :
    fl (h.map (algebraMap Ω Ω') * m) i = fl u i := by
  refine fl_of_indep hc' ?_
  rw [← hf]
  congr 1
  funext k
  rw [hb]
  simp only [Matrix.mul_apply, Matrix.map_apply, Finset.sum_smul, hh, map_sum, hj,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

end PositivityTheory.UnitarySelfGeneration.GF
end

open MvPolynomial AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp

namespace PositivityTheory.UnitarySelfGeneration

private theorem l_genflag_lemma_0 {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {n : ℕ}
    (c'' c' c : Fin n → E) {A B : Matrix (Fin n) (Fin n) Ω} (hA : ∀ k, c'' k = ∑ l, A l k • c' l)
    (hB : ∀ k, c' k = ∑ l, B l k • c l) : ∀ k, c'' k = ∑ p, (B * A) p k • c p := by
  intro k
  rw [hA k]
  simp_rw [hB, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

private theorem l_genflag_lemma {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {n : ℕ}
    (c c' : Fin n → E) (hc : ∀ k, c k ∈ Submodule.span Ω (Set.range c')) :
    ∃ h : Matrix (Fin n) (Fin n) Ω, ∀ k, c k = ∑ l, h l k • c' l := by
  choose f hf using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (hc k)
  exact ⟨Matrix.of fun l k => f k l, fun k => by simp only [Matrix.of_apply]; exact (hf k).symm⟩

private theorem l_genflag_lemma_2 {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {n : ℕ}
    (c c' : Fin n → E) (hc : LinearIndependent Ω c) {h P : Matrix (Fin n) (Fin n) Ω}
    (hh : ∀ k, c k = ∑ l, h l k • c' l) (hP : ∀ k, c' k = ∑ l, P l k • c l) : P * h = 1 := by
  have key := l_genflag_lemma_0 c c' c hh hP
  ext p k
  have := Fintype.linearIndependent_iff.1 hc (fun p => (P * h) p k - (1 : Matrix (Fin n) (Fin n) Ω) p k)
    (by simp [sub_smul, Finset.sum_sub_distrib, ← key k, Matrix.one_apply]) p
  exact sub_eq_zero.1 this

private theorem l_genflag_lemma_3 {F K : Type} [Field F] [Field K] (f : F →+* K) {n : ℕ} (S : Set (Fin n → F)) :
    Submodule.span K ((fun v l => f (v l)) '' (Submodule.span F S : Set (Fin n → F))) =
      Submodule.span K ((fun v l => f (v l)) '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    simp only [SetLike.mem_coe]
    induction hv using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      convert (Submodule.span K ((fun v l => f (v l)) '' S)).zero_mem using 1
      ext i; simp
    | add x y _ _ hx hy =>
      convert Submodule.add_mem _ hx hy using 1
      ext i; simp
    | smul a x _ hx =>
      convert Submodule.smul_mem _ (f a) hx using 1
      ext i; simp
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

private theorem l_genflag_lemma_4 {F K : Type} [Field F] [Field K] (f : F →+* K) {n : ℕ}
    {M M' : Matrix (Fin n) (Fin n) F} {t : ℕ} (h : GF.fl M t = GF.fl M' t) :
    GF.fl (M.map f) t = GF.fl (M'.map f) t := by
  have key : ∀ N : Matrix (Fin n) (Fin n) F, GF.fl (N.map f) t =
      Submodule.span K ((fun v l => f (v l)) '' (GF.fl N t : Set (Fin n → F))) := by
    intro N
    simp only [GF.fl, flagStep]
    rw [l_genflag_lemma_3, Set.image_image]
    rfl
  rw [key, key, h]

private theorem l_genflag_lemma_5 {F : Type} [Field F] {n : ℕ} (N : Matrix (Fin n) (Fin n) F)
    {M M' : Matrix (Fin n) (Fin n) F} {t : ℕ} (h : GF.fl M t = GF.fl M' t) :
    GF.fl (N * M) t = GF.fl (N * M') t := by
  have key : ∀ M : Matrix (Fin n) (Fin n) F, GF.fl (N * M) t = (GF.fl M t).map (Matrix.mulVecLin N) := by
    intro M
    simp only [GF.fl, flagStep, Submodule.map_span, Set.image_image]
    congr 2
  rw [key, key, h]

open GF in
theorem l_genflag : ∀ (Ω Ω₁ Ω₂ : Type) [Field Ω] [Field Ω₁] [Field Ω₂] [Algebra Ω Ω₁] [Algebra Ω Ω₂] (E E₁ E₂ : Type) [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω₁ E₁] [AddCommGroup E₂] [Module Ω₂ E₂] (j₁ : E →+ E₁) (j₂ : E →+ E₂) (S : Type) [Fintype S] (r : S → ℕ) (V : S → Submodule Ω E) (b₁ : ∀ s, Fin (r s) → E₁) (b₂ : ∀ s, Fin (r s) → E₂) (d₁ d₂ : ℕ), IsGenericFlag (Ω' := Ω₁) j₁ V b₁ d₁ → IsGenericFlag (Ω' := Ω₂) j₂ V b₂ d₂ → ∃ (Ω₃ : Type) (_ : Field Ω₃) (i₁ : Ω₁ →+* Ω₃) (i₂ : Ω₂ →+* Ω₃), i₁.comp (algebraMap Ω Ω₁) = i₂.comp (algebraMap Ω Ω₂) ∧ (∃ n₁ n₂ : ℕ, 0 < n₁ ∧ n₁ * d₁ = n₂ * d₂ ∧ Module.finrank i₁.fieldRange Ω₃ = n₁ ∧ Module.finrank i₂.fieldRange Ω₃ = n₂) ∧ ∀ s (c : Fin (r s) → E) (m₁ : Matrix (Fin (r s)) (Fin (r s)) Ω₁) (m₂ : Matrix (Fin (r s)) (Fin (r s)) Ω₂), LinearIndependent Ω c → Submodule.span Ω (Set.range c) = V s → (∀ k, b₁ s k = ∑ l, m₁ l k • j₁ (c l)) → (∀ k, b₂ s k = ∑ l, m₂ l k • j₂ (c l)) → ∀ i, flagStep Ω₃ (fun k l => i₁ (m₁ l k) : Fin (r s) → Fin (r s) → Ω₃) i = flagStep Ω₃ (fun k l => i₂ (m₂ l k) : Fin (r s) → Fin (r s) → Ω₃) i := by
  intro Ω Ω₁ Ω₂ _ _ _ _ _ E E₁ E₂ _ _ _ _ _ _ j₁ j₂ S _ r V b₁ b₂ d₁ d₂ hG1 hG2
  unfold IsGenericFlag at hG1 hG2
  obtain ⟨c1, u1, hc1, hj1, hjc1, -, hd1, hup1, hfl1, hai1, hdpos1, hrk1⟩ := hG1
  obtain ⟨c2, u2, hc2, hj2, hjc2, -, hd2, hup2, hfl2, hai2, hdpos2, hrk2⟩ := hG2
  have hU1 : ∀ σ, GF.Uni (u1 σ) := fun σ => ⟨hd1 σ, hup1 σ⟩
  have hU2 : ∀ σ, GF.Uni (u2 σ) := fun σ => ⟨hd2 σ, hup2 σ⟩
  rw [GF.adjoin_all u1 hU1] at hrk1
  rw [GF.adjoin_all u2 hU2] at hrk2
  have hfd1 : FiniteDimensional (IntermediateField.adjoin Ω (Set.range (GF.ent u1))) Ω₁ :=
    Module.finite_of_finrank_pos (by rw [hrk1]; exact hdpos1)
  have hfd2 : FiniteDimensional (IntermediateField.adjoin Ω (Set.range (GF.ent u2))) Ω₂ :=
    Module.finite_of_finrank_pos (by rw [hrk2]; exact hdpos2)
  have hA : ∀ σ, ∃ A : Matrix (Fin (r σ)) (Fin (r σ)) Ω,
      (∀ k, c2 σ k = ∑ l, A l k • c1 σ l) ∧ A.det ≠ 0 := by
    intro σ
    obtain ⟨A, hA⟩ := l_genflag_lemma (c2 σ) (c1 σ)
      (fun k => by rw [(hc1 σ).2, ← (hc2 σ).2]; exact Submodule.subset_span ⟨k, rfl⟩)
    obtain ⟨B, hB⟩ := l_genflag_lemma (c1 σ) (c2 σ)
      (fun k => by rw [(hc2 σ).2, ← (hc1 σ).2]; exact Submodule.subset_span ⟨k, rfl⟩)
    refine ⟨A, hA, fun h0 => ?_⟩
    have hBA := congrArg Matrix.det (l_genflag_lemma_2 (c2 σ) (c1 σ) (hc2 σ).1 hA hB)
    rw [Matrix.det_mul, Matrix.det_one, h0, mul_zero] at hBA
    exact zero_ne_one hBA
  choose A hAc hAdet using hA
  obtain ⟨u2', hU2', hai2', hadj, hfl2'⟩ := GF.change u2 hU2 hai2 hfd2 A hAdet
  have hfd2' : FiniteDimensional (IntermediateField.adjoin Ω (Set.range (GF.ent u2'))) Ω₂ := by
    rw [hadj]; exact hfd2
  have hrk2' : Module.finrank (IntermediateField.adjoin Ω (Set.range (GF.ent u2'))) Ω₂ = d₂ := by
    rw [hadj]; exact hrk2
  obtain ⟨Ω₃, hF3, i₁, i₂, hα, hq, n₁, n₂, hn, hdeg, hr1, hr2⟩ :=
    GF.compositum' (GF.ent u1) (GF.ent u2') hai1 hai2' hfd1 hfd2'
  have hU : ∀ σ, (u1 σ).map i₁ = (u2' σ).map i₂ := by
    intro σ
    ext l k
    simp only [Matrix.map_apply]
    rcases lt_trichotomy k l with hkl | rfl | hlk
    · exact hq ⟨σ, ⟨(l, k), hkl⟩⟩
    · rw [(hU1 σ).1 k, (hU2' σ).1 k, map_one, map_one]
    · rw [(hU1 σ).2 l k hlk, (hU2' σ).2 l k hlk, map_zero, map_zero]
  refine ⟨Ω₃, hF3, i₁, i₂, RingHom.ext hα, ⟨n₁, n₂, hn, ?_, hr1, hr2⟩, ?_⟩
  · rw [← hrk1, ← hrk2', hdeg]
  intro s c m₁ m₂ hc hspan hb1 hb2 i
  obtain ⟨h1, hh1⟩ := l_genflag_lemma c (c1 s)
    (fun k => by rw [(hc1 s).2, ← hspan]; exact Submodule.subset_span ⟨k, rfl⟩)
  obtain ⟨P1, hP1⟩ := l_genflag_lemma (c1 s) c
    (fun k => by rw [hspan, ← (hc1 s).2]; exact Submodule.subset_span ⟨k, rfl⟩)
  have hP2 : ∀ k, c2 s k = ∑ p, (P1 * A s) p k • c p := l_genflag_lemma_0 (c2 s) (c1 s) c (hAc s) hP1
  obtain ⟨h2, hh2⟩ := l_genflag_lemma c (c2 s)
    (fun k => by rw [(hc2 s).2, ← hspan]; exact Submodule.subset_span ⟨k, rfl⟩)
  have e1 : P1 * h1 = 1 := l_genflag_lemma_2 c (c1 s) hc hh1 hP1
  have e2 : (P1 * A s) * h2 = 1 := l_genflag_lemma_2 c (c2 s) hc hh2 hP2
  have f1 := GF.fl_coord j₁ hj1 (hjc1 s) hh1 hb1 (hfl1 s i)
  have f2 := GF.fl_coord j₂ hj2 (hjc2 s) hh2 hb2 (hfl2 s i)
  have g1 : GF.fl m₁ i = GF.fl (P1.map (algebraMap Ω Ω₁) * u1 s) i := by
    have := l_genflag_lemma_5 (P1.map (algebraMap Ω Ω₁)) f1
    rwa [← mul_assoc, ← Matrix.map_mul, e1, Matrix.map_one _ (map_zero _) (map_one _), one_mul] at this
  have g2 : GF.fl m₂ i = GF.fl ((P1 * A s).map (algebraMap Ω Ω₂) * u2 s) i := by
    have := l_genflag_lemma_5 ((P1 * A s).map (algebraMap Ω Ω₂)) f2
    rwa [← mul_assoc, ← Matrix.map_mul, e2, Matrix.map_one _ (map_zero _) (map_one _), one_mul] at this
  change GF.fl (m₁.map i₁) i = GF.fl (m₂.map i₂) i
  rw [l_genflag_lemma_4 i₁ g1, l_genflag_lemma_4 i₂ g2]
  have hPβ : (P1.map (algebraMap Ω Ω₁)).map i₁ = (P1.map (algebraMap Ω Ω₂)).map i₂ := by
    ext l k
    exact hα (P1 l k)
  have L : (P1.map (algebraMap Ω Ω₁) * u1 s).map i₁ =
      (P1.map (algebraMap Ω Ω₂)).map i₂ * (u2' s).map i₂ := by
    rw [Matrix.map_mul, hPβ, hU s]
  have R : ((P1 * A s).map (algebraMap Ω Ω₂) * u2 s).map i₂ =
      (P1.map (algebraMap Ω Ω₂)).map i₂ * (((A s).map (algebraMap Ω Ω₂) * u2 s).map i₂) := by
    simp only [Matrix.map_mul, mul_assoc]
  rw [L, R]
  exact l_genflag_lemma_5 _ (l_genflag_lemma_4 i₂ (hfl2' s i))

end PositivityTheory.UnitarySelfGeneration
