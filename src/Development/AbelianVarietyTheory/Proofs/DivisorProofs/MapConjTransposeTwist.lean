module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHeisenbergOperatorISignatureConjApplyOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsConjOfMinpolyEqOfSeparable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalRowPartsOfDistinctTypes
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapConjTransposeTwist
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix ComplexOrder

namespace GlobalTheory.QuotRational

theorem gram_of_quotMet {n d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) (G : Matrix (Fin d) (Fin d) ℂ)
    (hG : IsUnit G.det) (P : Matrix (Fin d) (Fin n) ℂ) (D : Matrix (Fin n) (Fin d) ℂ) (h1 : G * P = Dᴴ * A)
    (h2 : (P * A⁻¹ * Pᴴ)⁻¹ = G) : Dᴴ * A * D = G := by
  have hAu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
  have hM : IsUnit (P * A⁻¹ * Pᴴ).det := by
    by_contra h
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h] at h2
    subst h2
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · exact h (by simp)
    · have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
      simp at hG
  have h3 : G * (P * A⁻¹ * Pᴴ) = 1 := by rw [← h2]; exact Matrix.nonsing_inv_mul _ hM
  have h4 : Dᴴ * Pᴴ = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.mul_assoc Dᴴ, Matrix.mul_nonsing_inv _ hAu,
      Matrix.mul_one] at h3
    exact h3
  have h5 : P * D = 1 := by
    have := congrArg Matrix.conjTranspose h4
    simpa [Matrix.conjTranspose_mul] using this
  rw [← h1, Matrix.mul_assoc, h5, Matrix.mul_one]

theorem eq_of_gram {n d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) (G : Matrix (Fin d) (Fin d) ℂ)
    (C D : Matrix (Fin n) (Fin d) ℂ) (h1 : Dᴴ * A * D = G) (h2 : Cᴴ * A * C = G) (h3 : Dᴴ * A * C = G) : C = D := by
  have hG : Gᴴ = G := by
    rw [← h1]; simp [Matrix.conjTranspose_mul, hA.isHermitian.eq, Matrix.mul_assoc]
  have h4 : Cᴴ * A * D = G := by
    have := congrArg Matrix.conjTranspose h3
    rw [hG] at this
    simpa [Matrix.conjTranspose_mul, hA.isHermitian.eq, Matrix.mul_assoc] using this
  have h5 : (C - D)ᴴ * A * (C - D) = 0 := by
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, h1, h2, h3, h4]
    simp
  have h6 : ∀ x, (C - D) *ᵥ x = 0 := by
    intro x
    by_contra hx
    have := hA.dotProduct_mulVec_pos hx
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h5] at this
    simp at this
  rw [← sub_eq_zero]
  ext i j
  simpa using congrFun (h6 (Pi.single j 1)) i

variable {K : Type} [Field K] [StarRing K]

theorem map_conjTranspose_twist (σ : K →+* ℂ) {n d : ℕ} (E : Matrix (Fin n) (Fin d) K) :
    (Eᴴ).map σ = (E.map (Formalism.DivisionValues.twist σ))ᴴ := by
  ext a i
  simp only [Matrix.map_apply, Matrix.conjTranspose_apply, Formalism.DivisionValues.twist, RingHom.comp_apply, starRingEnd_apply, star_star]

theorem twist_twist (σ : K →+* ℂ) : Formalism.DivisionValues.twist (Formalism.DivisionValues.twist σ) = σ := by
  ext a
  simp [Formalism.DivisionValues.twist]

theorem map_twist_of_mem (σ : K →+* ℂ) {n d : ℕ} (H : Matrix (Fin n) (Fin d) K) (hH : ∀ i j, H i j ∈ cmMax K) :
    H.map (Formalism.DivisionValues.twist σ) = H.map σ := by
  ext i j
  have : σ (star (H i j)) = starRingEnd ℂ (σ (H i j)) := hH i j σ
  simp only [Matrix.map_apply, Formalism.DivisionValues.twist, RingHom.comp_apply, starRingEnd_apply (R := K), this, Complex.conj_conj]

theorem entries_mem_cmMax [NumberField K] {n d : ℕ} (H : Matrix (Fin n) (Fin n) K) (hH : ∀ i j, H i j ∈ cmMax K)
    (hpos : ∀ v : InfinitePlace K, (H.map v.embedding).PosDef) (E : Matrix (Fin n) (Fin d) K)
    (Pr : Matrix (Fin d) (Fin n) K) (hP : IsOrthProj H E Pr)
    (hR : IsRatHerm (cmMax K) (Eᴴ * H * E) (quotFrame Pr H)) : ∀ i a, E i a ∈ cmMax K := by
  have hsurj : Function.Surjective Pr.mulVec :=
    Matrix.mulVec_surjective_iff_exists_right_inverse.mpr ⟨E, hP.1⟩
  have hGP : Eᴴ * H * E * Pr = Eᴴ * H := by
    have h2 := hP.2
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h2
    rw [Matrix.mul_assoc (Eᴴ * H), ← h2]
  have hv : ∀ v : InfinitePlace K, (Eᴴ).map v.embedding * H.map v.embedding * E.map (Formalism.DivisionValues.twist v.embedding) =
      (Eᴴ * H * E).map v.embedding := by
    intro v
    have hq := (quotFrameIsQuot K n d H hpos Pr hsurj v).2
    have hr := (hR.2 v).2
    rw [map_conjTranspose_twist]
    refine gram_of_quotMet _ (hpos v) _ ?_ (Pr.map v.embedding) _ ?_ (hq.symm.trans hr)
    · rw [← hr]
      exact (Matrix.isUnit_iff_isUnit_det _).mp (metOfSpec d _ (hR.2 v).1).1.isUnit
    · rw [← Matrix.map_mul, hGP, Matrix.map_mul, map_conjTranspose_twist]
  have hall : ∀ σ : K →+* ℂ, (Eᴴ).map σ * H.map σ * E.map (Formalism.DivisionValues.twist σ) = (Eᴴ * H * E).map σ := by
    intro σ
    rcases InfinitePlace.mk_eq_iff.mp (InfinitePlace.mk_embedding (InfinitePlace.mk σ)) with h | h
    · rw [← h]; exact hv _
    · have h1 := congrArg (fun M => M.map (starRingEnd ℂ)) (hv (InfinitePlace.mk σ))
      simp only [Matrix.map_mul (f := starRingEnd ℂ), Matrix.map_map] at h1
      rw [← h]
      exact h1
  have hE : ∀ v : InfinitePlace K, E.map v.embedding = E.map (Formalism.DivisionValues.twist v.embedding) := by
    intro v
    refine eq_of_gram _ (hpos v) ((Eᴴ * H * E).map v.embedding) _ _ ?_ ?_ ?_
    · rw [← map_conjTranspose_twist]; exact hall _
    · have h1 := hall (Formalism.DivisionValues.twist v.embedding)
      rwa [map_conjTranspose_twist, twist_twist, map_twist_of_mem _ H hH, map_twist_of_mem _ _ hR.1] at h1
    · rw [Matrix.map_mul, Matrix.map_mul, map_conjTranspose_twist]
  intro i a σ
  have h1 := congrFun (congrFun (hE (InfinitePlace.mk σ)) i) a
  simp only [Matrix.map_apply, Formalism.DivisionValues.twist, RingHom.comp_apply, starRingEnd_apply] at h1
  rcases InfinitePlace.mk_eq_iff.mp (InfinitePlace.mk_embedding (InfinitePlace.mk σ)) with h | h
  · rw [h] at h1
    rw [h1, starRingEnd_apply, star_star]
  · rw [← h, ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, h1]
    simp

theorem fE_mem_cmMax : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (v0 : InfinitePlace K) (s : ℕ), BlockHyp B ℓ v0 s → IsRatHerm (cmMax K) (B.HZ ℓ Z) (B.XQ ℓ Z) → ∀ a k, B.fE ℓ Z a k ∈ cmMax K := by
  intro K _ _ _ G _ _ Pl0 B ℓ Z v0 s h hR a k
  have hE := entries_mem_cmMax (B.HV ℓ) (BlockDat.HV_rat h.conj h.ok h.irr) (BlockDat.HV_pos h.conj h.ok h.irr)
    (B.zE ℓ Z) (B.Pq ℓ Z) (BlockDat.Pq_orth h.conj h.ok h.irr) hR
  rw [BlockDat.fE, Matrix.mul_apply]
  exact Subfield.sum_mem _ fun j _ => Subfield.mul_mem _ (BlockDat.vE_rat h.conj h.ok h.irr a j) (hE j k)

end GlobalTheory.QuotRational
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemChartFormsIff
open GlobalTheory GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogDR.ChartMem

variable {K : Type} [Field K]

def wt {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (i : Fin n) : K :=
  if i ∈ J then 1 else (x i : K)

theorem frame_eq {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (i : Fin n) :
    frame x J i = wt x J i • dlog (x i) := by
  unfold frame wt
  split_ifs with h
  · simp
  · simp [dlog, smul_smul]

theorem prod_wt {n : ℕ} (x : Fin n → Kˣ) (J I : Finset (Fin n)) :
    ∏ i ∈ I, wt x J i = ∏ i ∈ I \ J, (x i : K) := by
  simp only [wt]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.sdiff_eq_filter]

theorem wt_mul_prod {n : ℕ} (x : Fin n → Kˣ) (J I : Finset (Fin n)) (i : Fin n) (hi : i ∉ I) :
    wt x J i * ∏ j ∈ I \ J, (x j : K) = ∏ j ∈ insert i I \ J, (x j : K) := by
  rw [← prod_wt, ← prod_wt, Finset.prod_insert hi]

theorem prod_sdiff_ne_zero {n : ℕ} (x : Fin n → Kˣ) (J I : Finset (Fin n)) :
    ∏ j ∈ I \ J, (x j : K) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => Units.ne_zero _

theorem ιMulti_frame {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) :
    ∀ (a : ℕ) (v : Fin a → Ω[K⁄ℤ]), (∀ i, v i ∈ Set.range (frame x J)) →
      ∃ (I : Finset (Fin n)) (m : ℤ), (m ≠ 0 → I.card = a) ∧
        ExteriorAlgebra.ιMulti K a v = ((m : K) * ∏ j ∈ I \ J, (x j : K)) • logWedge x I := by
  intro a
  induction a with
  | zero =>
    intro v _
    exact ⟨∅, 1, fun _ => rfl, by simp [logWedge]⟩
  | succ a ih =>
    intro v hv
    obtain ⟨I, m, hc, he⟩ := ih (Matrix.vecTail v) (fun i => hv i.succ)
    obtain ⟨i0, hi0⟩ := hv 0
    rw [ExteriorAlgebra.ιMulti_succ_apply, he, ← hi0, frame_eq, map_smul, smul_mul_smul_comm]
    by_cases hi : i0 ∈ I
    · refine ⟨∅, 0, fun h => absurd rfl h, ?_⟩
      rw [(GlobalTheory.T.logDifferential_mul_logCoordinateWedge K n x i0 I).1 hi]
      simp
    · obtain ⟨ε, hε, hw⟩ := (GlobalTheory.T.logDifferential_mul_logCoordinateWedge K n x i0 I).2 hi
      refine ⟨insert i0 I, m * ε, fun h => ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hi, hc (left_ne_zero_of_mul h)]
      · rw [hw, ← Int.cast_smul_eq_zsmul K, smul_smul, ← wt_mul_prod x J I i0 hi]
        push_cast
        ring_nf

theorem list_frame {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) : ∀ l : List (Fin n),
    (l.map fun i => ExteriorAlgebra.ι K (frame x J i)).prod =
      (l.map (wt x J)).prod • (l.map fun i => ExteriorAlgebra.ι K (dlog (x i))).prod
  | [] => by simp
  | i :: l => by
    simp only [List.map_cons, List.prod_cons]
    rw [list_frame x J l, frame_eq, map_smul, smul_mul_smul_comm]

theorem ofFn_orderEmbOfFin {n a : ℕ} (I : Finset (Fin n)) (h : I.card = a) {β : Type} (f : Fin n → β) :
    List.ofFn (fun i => f (I.orderEmbOfFin h i)) = (I.sort (· ≤ ·)).map f := by
  apply List.ext_getElem
  · simp [h]
  · intro k h1 h2
    simp [Finset.orderEmbOfFin_apply]

theorem ιMulti_orderEmbOfFin {n a : ℕ} (x : Fin n → Kˣ) (J I : Finset (Fin n)) (h : I.card = a) :
    ExteriorAlgebra.ιMulti K a (fun i => frame x J (I.orderEmbOfFin h i)) =
      (∏ j ∈ I \ J, (x j : K)) • logWedge x I := by
  rw [ExteriorAlgebra.ιMulti_apply,
    show (List.ofFn fun i => ExteriorAlgebra.ι K (frame x J (I.orderEmbOfFin h i))) = _ from
      ofFn_orderEmbOfFin I h (fun j => ExteriorAlgebra.ι K (frame x J j)),
    list_frame, logWedge, ← prod_wt]
  congr 1
  rw [← Multiset.prod_coe, ← Multiset.map_coe, Finset.sort_eq, Finset.prod_eq_multiset_prod]

def coeffForms (A : Subring K) {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ) (a : ℕ) :
    AddSubgroup (abelian₂ K) where
  carrier := {η | ∃ c : Finset (Fin n) → K, (∀ I, I.card ≠ a → c I = 0) ∧
    (∀ I, c I * t / ∏ j ∈ I \ J, (x j : K) ∈ A) ∧ η = ∑ I, c I • logWedge x I}
  add_mem' := by
    rintro _ _ ⟨c, h1, h2, rfl⟩ ⟨d, g1, g2, rfl⟩
    refine ⟨c + d, fun I h => by simp [h1 I h, g1 I h], fun I => ?_, by
      simp [add_smul, Finset.sum_add_distrib]⟩
    simpa [add_mul, add_div] using A.add_mem (h2 I) (g2 I)
  zero_mem' := ⟨0, by simp, by simp, by simp⟩
  neg_mem' := by
    rintro _ ⟨c, h1, h2, rfl⟩
    refine ⟨-c, fun I h => by simp [h1 I h], fun I => ?_, by simp [neg_smul, Finset.sum_neg_distrib]⟩
    simpa [neg_mul, neg_div] using A.neg_mem (h2 I)

end GlobalTheory.LogDR.ChartMem

namespace GlobalTheory.LogDR


open ChartMem in
theorem mem_chartForms_iff : ∀ (K : Type) [Field K] (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ) (a : ℕ) (η : abelian₂ K), η ∈ chartForms A x J t a ↔ ∃ c : Finset (Fin n) → K, (∀ I, I.card ≠ a → c I = 0) ∧ (∀ I, c I * t / ∏ j ∈ I \ J, (x j : K) ∈ A) ∧ η = ∑ I, c I • logWedge x I := by
  intro K _ A n x J t a η
  constructor
  · intro hη
    have hle : chartForms A x J t a ≤ coeffForms A x J t a := by
      unfold chartForms spanForms
      rw [AddSubgroup.closure_le]
      rintro _ ⟨c, hc, v, hv, rfl⟩
      obtain ⟨I, m, hm, he⟩ := ιMulti_frame x J a v hv
      refine ⟨fun I' => if I' = I then c * ((m : K) * ∏ j ∈ I \ J, (x j : K)) else 0, ?_, ?_, ?_⟩
      · intro I' h'
        dsimp only
        split_ifs with e
        · subst e
          by_cases h0 : m = 0
          · simp [h0]
          · exact absurd (hm h0) h'
        · rfl
      · intro I'
        dsimp only
        split_ifs with e
        · subst e
          have hp := prod_sdiff_ne_zero x J I'
          have hq : c * ((m : K) * ∏ j ∈ I' \ J, (x j : K)) * t / ∏ j ∈ I' \ J, (x j : K) =
              (m : K) * (c * t) := by
            field_simp
          rw [hq]
          exact A.mul_mem (intCast_mem A m) hc
        · simp
      · rw [he, smul_smul]
        simp [ite_smul]
    exact hle hη
  · rintro ⟨c, h1, h2, rfl⟩
    refine AddSubgroup.sum_mem _ fun I _ => ?_
    by_cases h : I.card = a
    · have hp := prod_sdiff_ne_zero x J I
      have e : c I • logWedge x I = (c I / ∏ j ∈ I \ J, (x j : K)) •
          ExteriorAlgebra.ιMulti K a (fun i => frame x J (I.orderEmbOfFin h i)) := by
        rw [ιMulti_orderEmbOfFin, smul_smul, div_mul_cancel₀ _ hp]
      rw [e]
      apply AddSubgroup.subset_closure
      refine ⟨_, ?_, _, fun i => ⟨_, rfl⟩, rfl⟩
      show c I / _ * (t : K) ∈ A
      rw [div_mul_eq_mul_div]
      exact h2 I
    · rw [h1 I h, zero_smul]
      exact zero_mem _

end GlobalTheory.LogDR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairWeightInvariantFormGroupConj
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionDivisorSupport
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CxUnfold

theorem minpoly_units_conj {F A : Type*} [Field F] [Ring A] [Algebra F A] (u : Aˣ) (x : A) :
    minpoly F ((u : A) * x * ((u⁻¹ : Aˣ) : A)) = minpoly F x := by
  let e : A ≃ₐ[F] A :=
    { toFun := fun z => (u : A) * z * ((u⁻¹ : Aˣ) : A)
      invFun := fun z => ((u⁻¹ : Aˣ) : A) * z * u
      left_inv := fun z => by simp [mul_assoc]
      right_inv := fun z => by simp [mul_assoc]
      map_mul' := fun z w => by simp [mul_assoc]
      map_add' := fun z w => by simp [mul_add, add_mul]
      commutes' := fun r => by
        show (u : A) * algebraMap F A r * ((u⁻¹ : Aˣ) : A) = algebraMap F A r
        rw [← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one] }
  exact minpoly.algEquiv_eq e x

theorem fixL_smul_iff {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (y : grp G β)
    (z : Fin G.n → ℂ) (c : ℂ) (hc : c ≠ 0) : FixL G v β y (c • z) ↔ FixL G v β y z := by
  unfold FixL
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨d, ?_⟩
    rw [Matrix.mulVec_smul, smul_comm d c z] at hd
    exact smul_right_injective _ hc hd
  · rintro ⟨d, hd⟩
    exact ⟨d, by rw [Matrix.mulVec_smul, hd, smul_comm]⟩

end GlobalTheory.CxUnfold

namespace GlobalTheory.CxUnfold

theorem rep_smul {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (η : grp G β)
    (l : PLv G v β) : ∃ c : ℂ, c ≠ 0 ∧
      Projectivization.rep ((η • l : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ)) =
        c • ((toV G v β η : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ
          Projectivization.rep (l : Projectivization ℂ (Fin G.n → ℂ))) := by
  set w := Projectivization.rep (l : Projectivization ℂ (Fin G.n → ℂ))
  have hw : w ≠ 0 := Projectivization.rep_nonzero _
  have hMw : (toV G v β η : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ w ≠ 0 := by
    intro h0
    apply hw
    apply toV_injective G v β η
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h0, Matrix.mulVec_zero]
  have hl : ((η • l : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ)) =
      Projectivization.mk ℂ ((toV G v β η : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ w) hMw := by
    show Projectivization.map _ _ (l : Projectivization ℂ (Fin G.n → ℂ)) = _
    conv_lhs => rw [← Projectivization.mk_rep (l : Projectivization ℂ (Fin G.n → ℂ))]
    rw [Projectivization.map_mk]
    simp only [Matrix.toLin'_apply]
    rfl
  rw [hl]
  have h2 := Projectivization.mk_rep (Projectivization.mk ℂ ((toV G v β η : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ w) hMw)
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ (Projectivization.rep_nonzero _) hMw).1 h2
  exact ⟨c, c.ne_zero, by rw [← hc, Units.smul_def]⟩

end GlobalTheory.CxUnfold

namespace GlobalTheory.CxUnfold

end GlobalTheory.CxUnfold
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairWeightInvariantFormGroupConj
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CxUnfold

theorem cxF_smul_conj_gen : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F)
    (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ),
    (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ),
    (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t), ∀ (η : grp G β) (a : GlobalTheory.CxUnfold.Ys G v β x t hx Kf K') (y : grp G β),
    GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' (η • a) (η * y * η⁻¹) =
      GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' a y := by
  intro p _ G v wt Kf f hf K' f' hf' β x t hx η a y

  have ha1 : (η • a).1 = LeftCosets.mk ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K')
      (((toAfF G β x t hx).prod (toP1 G β)) η *
        LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1) := by
    show η • a.1 = _
    conv_lhs => rw [← LeftCosets.mk_rep a.1]
    rfl
  obtain ⟨k, hk, hrep⟩ := LeftCosets.rep_mk (ι := (toAfF G β x t hx).prod (toP1 G β))
    (K := Kf.prod K') (((toAfF G β x t hx).prod (toP1 G β)) η *
        LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1)
  rw [← ha1] at hrep
  rw [Subgroup.mem_prod] at hk
  have hF : f ((LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') (η • a).1).1⁻¹ *
        toAfF G β x t hx (η * y * η⁻¹) *
        (LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') (η • a).1).1) =
      f ((LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).1⁻¹ *
        toAfF G β x t hx y *
        (LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).1) := by
    rw [hrep, ← hf k.1 hk.1 ((LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).1⁻¹ *
        toAfF G β x t hx y *
        (LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).1)]
    congr 1
    simp only [Prod.fst_mul, MonoidHom.prod_apply, map_mul, map_inv]
    group
  have hF' : f' ((LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') (η • a).1).2⁻¹ *
        toP1 G β (η * y * η⁻¹) *
        (LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') (η • a).1).2) =
      f' ((LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).2⁻¹ *
        toP1 G β y *
        (LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).2) := by
    rw [hrep, ← hf' k.2 hk.2 ((LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).2⁻¹ *
        toP1 G β y *
        (LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).2)]
    congr 1
    simp only [Prod.snd_mul, MonoidHom.prod_apply, map_mul, map_inv]
    group

  have hM : minpoly G.F ((((η * y * η⁻¹ : grp G β) : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
      minpoly G.F ((((y : grp G β) : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) := by
    have e : ((((η * y * η⁻¹ : grp G β) : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
        (((η : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((((y : grp G β) : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) *
          ((((η : G.Cˣ × ℚˣ).1)⁻¹ : G.Cˣ) : G.C) := by
      simp [Units.val_mul]
    rw [e, minpoly_units_conj]

  obtain ⟨c, hc, hrepl⟩ := rep_smul G v β η a.2
  have hcond : (0 < (star (Projectivization.rep (((η • a).2 : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ))) ⬝ᵥ
        (herm G v β *ᵥ Projectivization.rep (((η • a).2 : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ)))).re ∧
      FixL G v β (η * y * η⁻¹)
        (Projectivization.rep (((η • a).2 : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ)))) ↔
      (0 < (star (Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ))) ⬝ᵥ
        (herm G v β *ᵥ Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ)))).re ∧
      FixL G v β y (Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ)))) := by
    change (0 < (star (Projectivization.rep ((η • a.2 : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ))) ⬝ᵥ
        (herm G v β *ᵥ Projectivization.rep ((η • a.2 : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ)))).re ∧
      FixL G v β (η * y * η⁻¹)
        (Projectivization.rep ((η • a.2 : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ)))) ↔ _
    rw [hrepl, fixL_smul_iff G v β _ _ c hc, ← fixL_conj_iff p G v β y η,
      ← pos_iff_smul_toV p G v β η _ c hc]
  unfold cxF
  by_cases hca : (0 < (star (Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ))) ⬝ᵥ
        (herm G v β *ᵥ Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ)))).re ∧
      FixL G v β y (Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ))))
  · rw [if_pos hca, if_pos (hcond.2 hca), hF, hF', hM]
  · rw [if_neg hca, if_neg (mt hcond.1 hca)]

end GlobalTheory.CxUnfold
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairWeightInvariantFormGroupConjStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairWeight_invariant_form_group_conj : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), ∀ (η : grp G β) (a : GlobalTheory.CxUnfold.Ys G v β x t hx Kf K') (y : grp G β), GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' (η • a) (η * y * η⁻¹) = GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' a y := by
  first | (exact @GlobalTheory.CxUnfold.cxF_smul_conj_gen) | (exact GlobalTheory.CxUnfold.cxF_smul_conj_gen) | (intros; apply GlobalTheory.CxUnfold.cxF_smul_conj_gen  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableRangeOneDetUnitElementary
open NumberField IsDedekindDomain GlobalTheory.HaarLin

namespace GlobalTheory.HaarLin.Gauss

open Matrix

variable {R : Type} [CommRing R]

theorem transvection_mem {κ : Type} [Fintype κ] [DecidableEq κ] {i j : κ} (h : i ≠ j) (c : R) :
    transvection i j c ∈ TD R κ :=
  Submonoid.subset_closure (Or.inl ⟨i, j, c, h, rfl⟩)

theorem diagonal_mem {κ : Type} [Fintype κ] [DecidableEq κ] (d : κ → Rˣ) :
    (diagonal fun i => (d i : R)) ∈ TD R κ :=
  Submonoid.subset_closure (Or.inr ⟨d, rfl⟩)

theorem exists_inv {κ : Type} [Fintype κ] [DecidableEq κ] {A : Matrix κ κ R} (hA : A ∈ TD R κ) :
    ∃ B ∈ TD R κ, B * A = 1 ∧ A * B = 1 := by
  induction hA using Submonoid.closure_induction with
  | mem N hN =>
    rcases hN with ⟨i, j, c, hij, rfl⟩ | ⟨d, rfl⟩
    · refine ⟨transvection i j (-c), transvection_mem hij _, ?_, ?_⟩ <;>
        simp [transvection_mul_transvection_same _ _ hij]
    · refine ⟨_, diagonal_mem (fun i => (d i)⁻¹), ?_, ?_⟩ <;>
        simp [diagonal_mul_diagonal]
  | one => exact ⟨1, one_mem _, by simp, by simp⟩
  | mul A B _ _ IA IB =>
    obtain ⟨A', hA', h1, h2⟩ := IA
    obtain ⟨B', hB', h3, h4⟩ := IB
    refine ⟨B' * A', mul_mem hB' hA', ?_, ?_⟩
    · rw [mul_assoc, ← mul_assoc A', h1, one_mul, h3]
    · rw [mul_assoc, ← mul_assoc B, h4, one_mul, h2]

theorem of_left {κ : Type} [Fintype κ] [DecidableEq κ] {E M : Matrix κ κ R} (hE : E ∈ TD R κ)
    (hM : IsUnit M.det) (h : IsUnit (E * M).det → E * M ∈ TD R κ) : M ∈ TD R κ := by
  obtain ⟨B, hB, h1, h2⟩ := exists_inv hE
  have hd : IsUnit E.det := IsUnit.of_mul_eq_one B.det (by rw [← det_mul, h2, det_one])
  have := mul_mem hB (h (by rw [det_mul]; exact hd.mul hM))
  rwa [← mul_assoc, h1, one_mul] at this

theorem of_right {κ : Type} [Fintype κ] [DecidableEq κ] {E M : Matrix κ κ R} (hE : E ∈ TD R κ)
    (hM : IsUnit M.det) (h : IsUnit (M * E).det → M * E ∈ TD R κ) : M ∈ TD R κ := by
  obtain ⟨B, hB, h1, h2⟩ := exists_inv hE
  have hd : IsUnit E.det := IsUnit.of_mul_eq_one B.det (by rw [← det_mul, h2, det_one])
  have := mul_mem (h (by rw [det_mul]; exact hM.mul hd)) hB
  rwa [mul_assoc, h2, mul_one] at this

theorem rowOp {κ : Type} [Fintype κ] [DecidableEq κ] (p : κ) (w : κ → R) (s : Finset κ) (hs : p ∉ s) :
    ∃ E ∈ TD R κ, ∀ M : Matrix κ κ R, (∀ b, (E * M) p b = M p b + ∑ k ∈ s, w k * M k b) ∧
      ∀ a b, a ≠ p → (E * M) a b = M a b := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, by simp⟩
  | insert k s hk IH =>
    have hkp : p ≠ k := fun h => hs (by simp [h])
    obtain ⟨E, hE, H⟩ := IH (fun h => hs (by simp [h]))
    refine ⟨transvection p k (w k) * E, mul_mem (transvection_mem hkp _) hE, fun M => ⟨fun b => ?_, fun a b ha => ?_⟩⟩
    · rw [mul_assoc, transvection_mul_apply_same, (H M).1, (H M).2 _ _ hkp.symm, Finset.sum_insert hk]
      ring
    · rw [mul_assoc, transvection_mul_apply_of_ne _ _ _ _ ha, (H M).2 _ _ ha]

theorem colOpLeft {κ : Type} [Fintype κ] [DecidableEq κ] (p : κ) (w : κ → R) (s : Finset κ) (hs : p ∉ s) :
    ∃ E ∈ TD R κ, ∀ (M : Matrix κ κ R) a b, (E * M) a b = M a b + if a ∈ s then w a * M p b else 0 := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, by simp⟩
  | insert k s hk IH =>
    have hkp : p ≠ k := fun h => hs (by simp [h])
    have hps : p ∉ s := fun h => hs (by simp [h])
    obtain ⟨E, hE, H⟩ := IH hps
    refine ⟨transvection k p (w k) * E, mul_mem (transvection_mem hkp.symm _) hE, fun M a b => ?_⟩
    by_cases ha : a = k
    · subst ha
      rw [mul_assoc, transvection_mul_apply_same, H, H]
      simp [hk, hps]
    · rw [mul_assoc, transvection_mul_apply_of_ne _ _ _ _ ha, H]
      simp [ha]

theorem colOpRight {κ : Type} [Fintype κ] [DecidableEq κ] (p : κ) (w : κ → R) (s : Finset κ) (hs : p ∉ s) :
    ∃ E ∈ TD R κ, ∀ (M : Matrix κ κ R) a b, (M * E) a b = M a b + if b ∈ s then w b * M a p else 0 := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, by simp⟩
  | insert k s hk IH =>
    have hkp : p ≠ k := fun h => hs (by simp [h])
    have hps : p ∉ s := fun h => hs (by simp [h])
    obtain ⟨E, hE, H⟩ := IH hps
    refine ⟨E * transvection p k (w k), mul_mem hE (transvection_mem hkp _), fun M a b => ?_⟩
    by_cases hb : b = k
    · subst hb
      rw [← mul_assoc, mul_transvection_apply_same, H, H]
      simp [hk, hps]
    · rw [← mul_assoc, mul_transvection_apply_of_ne _ _ _ _ hb, H]
      simp [hb]

theorem reindex_mem {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ'] (e : κ ≃ κ')
    {A : Matrix κ κ R} (hA : A ∈ TD R κ) : A.submatrix e.symm e.symm ∈ TD R κ' := by
  induction hA using Submonoid.closure_induction with
  | mem N hN =>
    rcases hN with ⟨i, j, c, hij, rfl⟩ | ⟨d, rfl⟩
    · have : (transvection i j c).submatrix e.symm e.symm = transvection (e i) (e j) c := by
        ext a b
        simp [transvection, Matrix.one_apply, Matrix.single_apply, Equiv.eq_symm_apply]
      rw [this]
      exact transvection_mem (e.injective.ne hij) c
    · rw [submatrix_diagonal_equiv]
      exact diagonal_mem (fun i => d (e.symm i))
  | one => rw [submatrix_one_equiv]; exact one_mem _
  | mul A B _ _ IA IB =>
    rw [← submatrix_mul_equiv A B e.symm e.symm e.symm]
    exact mul_mem IA IB

theorem fromBlocks_mem {κ : Type} [Fintype κ] [DecidableEq κ]
    {A : Matrix κ κ R} (hA : A ∈ TD R κ) : fromBlocks A 0 0 (1 : Matrix Unit Unit R) ∈ TD R (κ ⊕ Unit) := by
  induction hA using Submonoid.closure_induction with
  | mem N hN =>
    rcases hN with ⟨i, j, c, hij, rfl⟩ | ⟨d, rfl⟩
    · have : transvection (Sum.inl i) (Sum.inl j) c = fromBlocks (transvection i j c) 0 0 (1 : Matrix Unit Unit R) :=
        TransvectionStruct.toMatrix_sumInl Unit (⟨i, j, hij, c⟩ : TransvectionStruct κ R)
      rw [← this]
      exact transvection_mem (Sum.inl_injective.ne hij) c
    · rw [← diagonal_one, fromBlocks_diagonal]
      convert diagonal_mem (R := R) (Sum.elim d (fun _ : Unit => 1)) using 2
      ext x
      cases x <;> rfl
  | one => rw [fromBlocks_one]; exact one_mem _
  | mul A B _ _ IA IB =>
    have := mul_mem IA IB
    rw [fromBlocks_multiply] at this
    simpa using this

theorem step {κ : Type} [Fintype κ] [DecidableEq κ] (hR : HasStableRangeOne R)
    (IH : ∀ N : Matrix κ κ R, IsUnit N.det → N ∈ TD R κ)
    (M : Matrix (κ ⊕ Unit) (κ ⊕ Unit) R) (hM : IsUnit M.det) : M ∈ TD R (κ ⊕ Unit) := by
  set l : κ ⊕ Unit := Sum.inr () with hl
  set s : Finset (κ ⊕ Unit) := Finset.univ.erase l with hs
  have hls : l ∉ s := Finset.notMem_erase _ _
  have hin : ∀ i : κ, Sum.inl i ∈ s := fun i => by simp [hs, hl]
  have h1 : (M⁻¹ * M) l l = 1 := by rw [nonsing_inv_mul M hM, one_apply_eq]
  rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ l)] at h1
  obtain ⟨t, ht⟩ := hR (M l l) (∑ k ∈ s, M⁻¹ l k * M k l) ⟨M⁻¹ l l, 1, by rw [one_mul]; exact h1⟩
  obtain ⟨E₁, hE₁, H₁⟩ := rowOp l (fun k => t * M⁻¹ l k) s hls
  refine of_left hE₁ hM fun hM₁ => ?_
  have hu : IsUnit ((E₁ * M) l l) := by
    rw [(H₁ M).1]
    simpa [Finset.mul_sum, mul_assoc] using ht
  generalize E₁ * M = M₁ at hM₁ hu
  obtain ⟨u, hu⟩ := hu
  obtain ⟨E₂, hE₂, H₂⟩ := colOpLeft l (fun a => - M₁ a l * ↑u⁻¹) s hls
  refine of_left hE₂ hM₁ fun hM₂ => ?_
  have hu₂ : (E₂ * M₁) l l = u := by rw [H₂, if_neg hls, add_zero, hu]
  have hc₂ : ∀ i : κ, (E₂ * M₁) (Sum.inl i) l = 0 := fun i => by
    rw [H₂, if_pos (hin i), ← hu, mul_assoc, Units.inv_mul]; ring
  generalize E₂ * M₁ = M₂ at hM₂ hu₂ hc₂
  obtain ⟨E₃, hE₃, H₃⟩ := colOpRight l (fun b => - M₂ l b * ↑u⁻¹) s hls
  refine of_right hE₃ hM₂ fun hM₃ => ?_
  have hu₃ : (M₂ * E₃) l l = u := by rw [H₃, if_neg hls, add_zero, hu₂]
  have hc₃ : ∀ i : κ, (M₂ * E₃) (Sum.inl i) l = 0 := fun i => by
    rw [H₃, if_neg hls, add_zero, hc₂]
  have hr₃ : ∀ i : κ, (M₂ * E₃) l (Sum.inl i) = 0 := fun i => by
    rw [H₃, if_pos (hin i), hu₂, mul_assoc, Units.inv_mul]; ring
  generalize M₂ * E₃ = M₃ at hM₃ hu₃ hc₃ hr₃
  have hform : M₃ = (diagonal fun i => ((Sum.elim (fun _ => 1) (fun _ => u) : κ ⊕ Unit → Rˣ) i : R)) *
      fromBlocks M₃.toBlocks₁₁ 0 0 (1 : Matrix Unit Unit R) := by
    ext a b
    rw [diagonal_mul]
    rcases a with a | ⟨⟩ <;> rcases b with b | ⟨⟩
    · simp [toBlocks₁₁]
    · simpa using hc₃ a
    · simpa using hr₃ b
    · simpa using hu₃
  have hN : IsUnit M₃.toBlocks₁₁.det := by
    rw [hform, det_mul, det_fromBlocks_zero₂₁, det_one, mul_one] at hM₃
    exact isUnit_of_mul_isUnit_right hM₃
  rw [hform]
  exact mul_mem (diagonal_mem _) (fromBlocks_mem (IH _ hN))

theorem mem_TD_of_isUnit_det : ∀ (R : Type) [CommRing R], HasStableRangeOne R → ∀ (κ : Type) [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ R), IsUnit M.det → M ∈ TD R κ := by
  intro R _ hR κ _ _
  have key : ∀ n : ℕ, ∀ N : Matrix (Fin n) (Fin n) R, IsUnit N.det → N ∈ TD R (Fin n) := by
    intro n
    induction n with
    | zero => intro N _; rw [Subsingleton.elim N 1]; exact one_mem _
    | succ n IH =>
      intro N hN
      let e : Fin n ⊕ Unit ≃ Fin (n + 1) := (Equiv.sumCongr (Equiv.refl _) finOneEquiv.symm).trans finSumFinEquiv
      have := reindex_mem e (step hR IH (N.submatrix e e) (by rwa [det_submatrix_equiv_self]))
      simpa using this
  intro M hM
  let e := (Fintype.equivFin κ).symm
  have := reindex_mem e (key _ (M.submatrix e e) (by rwa [det_submatrix_equiv_self]))
  simpa using this

end GlobalTheory.HaarLin.Gauss
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSystemValueEqRootMulThetaConstant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSystemValueEqRootMulThetaConstant
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical

noncomputable section
namespace GlobalTheory.ZH.EvRoot
open GlobalTheory.ThetaCompare

variable {S : Scheme.{0}}

private theorem val_powFrame_divisor {S : Scheme.{0}} (P : PolAV S) {T : Over S} (h : T ⟶ P.A)
    (τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => h.left) (fun _ => 1))) (k : ℤ)
    (y : T.left) (J : (T.left ⟶ P.A.left) → P.L.ι) :
    val (powFrame P.A P.L h τ k) (𝟙 _) y J = val τ (𝟙 _) y J ^ k := by
  unfold powFrame val gm
  split_ifs
  · exact map_zpow _ _ _
  · exact (one_zpow k).symm

private theorem val_rigPow' {S : Scheme.{0}} (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))) (k : ℤ)
    {Z : Scheme.{0}} (r : Z ⟶ S) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι) :
    val (rigPow P.A P.L rig k) r z J = val rig r z J ^ k := by
  unfold rigPow val gm
  split_ifs
  · exact map_zpow _ _ _
  · exact (one_zpow k).symm


open CommPairing in
theorem exists_root_stalk_pull (hG : GlobalFnsSt) (P : PolAV S) {T : Over S} {N M m : ℕ}
    {rig : LB.Gen (P.L.pull (eSec P.A))}
    {α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![(N : ℤ), -1])}
    (hα : α.IsGen)
    (hn : LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ α (ptSecT P.A 1).left)
      (LB.mulGen P.L _ _ _ _ (rigT P.A P.L rig T N) (rigT P.A P.L rig T (-1))))
    {h w : T ⟶ P.A} (hw : w = h ^ m) {τ τ'} (hτ : IsTorsFrame P rig M h τ)
    (hτ' : IsTorsFrame P rig M w τ') {th : LB.Sec (LPow P.A P.L 1 T)} {s : LB.Sec (LPow P.A P.L N T)}
    (hs : IsTwistPull P.A P.L (mulT P.A T m) (snd T P.A ^ m) (lift_snd _ _) N 1 α th s) {v v' : Γ(T.left, ⊤)}
    (hv : IsValueAt P.A P.L N s h (powFrame P.A P.L h τ N) v) (hv' : IsValueAt P.A P.L 1 th w τ' v') (y : T.left) :
    ∃ ξ : (T.left.presheaf.stalk y)ˣ, ξ ^ (M ^ 2) = 1 ∧ gs (𝟙 _) y ⊤ v = ξ.val * gs (𝟙 _) y ⊤ v' := by
  have hL : P.L.IsLB := P.isLB
  obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt hL y
  have e1 := sval_twist hs (ptSecT P.A h).left hJ
  rw [pt_mulT, ← hw, sval_valueAt hv hJ, sval_valueAt hv' hJ] at e1
  refine ⟨val α (ptSecT P.A h).left y J * val τ' (𝟙 _) y J * (val (powFrame P.A P.L h τ N) (𝟙 _) y J)⁻¹, ?_, ?_⟩
  · unfold IsTorsFrame at hτ hτ'
    obtain ⟨hhM, -, β, hβ, hnβ, hcβ⟩ := hτ
    obtain ⟨-, -, β', hβ', hnβ', hcβ'⟩ := hτ'
    have eτ : val τ (𝟙 _) y J ^ ((M : ℤ) ^ 2) = val β h.left y J * val rig T.hom y J := by
      rw [← val_powFrame_divisor, val_corr hJ hcβ (𝟙 _), val_mul hJ, val_pull hJ, val_rigT rig 1 hJ, zpow_one,
        Category.id_comp]
    have eτ' : val τ' (𝟙 _) y J ^ ((M : ℤ) ^ 2) = val β' w.left y J * val rig T.hom y J := by
      rw [← val_powFrame_divisor, val_corr hJ hcβ' (𝟙 _), val_mul hJ, val_pull hJ, val_rigT rig 1 hJ, zpow_one,
        Category.id_comp]
    have orbitMap_conj_smul_one : val α (ptSecT P.A 1).left y J = val rig T.hom y J ^ (N : ℤ) * val rig T.hom y J ^ (-1 : ℤ) := by
      have := val_corr hJ hn (𝟙 _)
      rw [val_pull hJ, val_mul hJ, val_rigT rig _ hJ, val_rigT rig _ hJ, Category.id_comp] at this
      exact this
    have eB1 : val β (T.hom ≫ eSec P.A) y J = val rig T.hom y J ^ ((M : ℤ) ^ 2) * (val rig T.hom y J)⁻¹ := by
      have := val_corr hJ hnβ T.hom
      rw [val_pull hJ, val_mul hJ, val_inv, val_rigPow'] at this
      exact this
    have eB1' : val β' (T.hom ≫ eSec P.A) y J = val rig T.hom y J ^ ((M : ℤ) ^ 2) * (val rig T.hom y J)⁻¹ := by
      have := val_corr hJ hnβ' T.hom
      rw [val_pull hJ, val_mul hJ, val_inv, val_rigPow'] at this
      exact this
    have rA := Reg.two (L := P.L) (y := y) (J := J) α hα (snd T P.A) (snd T P.A ^ m) rfl rfl
    have rB := Reg.two (L := P.L) (y := y) (J := J) (LB.pullGen P.L _ _ β (snd T P.A).left)
      (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen P.L _ _ β hβ _) (snd T P.A) (snd T P.A ^ M)
      (by simp)
      (by show (snd T P.A).left ≫ (mulA P.A M).left = (snd T P.A ^ M).left
          rw [← Over.comp_left, GlobalTheory.DivisibleHom.comp_mulA])
    have rB' := Reg.two (L := P.L) (y := y) (J := J) (LB.pullGen P.L _ _ β' (snd T P.A).left)
      (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen P.L _ _ β' hβ' _) (snd T P.A) (snd T P.A ^ M)
      (by simp)
      (by show (snd T P.A).left ≫ (mulA P.A M).left = (snd T P.A ^ M).left
          rw [← Over.comp_left, GlobalTheory.DivisibleHom.comp_mulA])
    have rF := ((rA.pow hJ (M ^ 2)).mul hJ (rB'.pull hJ (snd T P.A ^ m))).mul hJ
      (((rB.pow hJ N).inv).mul hJ ((rA.pull hJ (snd T P.A ^ M)).inv))
    have hmM : (snd T P.A ^ m) ^ M = (snd T P.A ^ M) ^ m := by
      rw [← pow_mul, ← pow_mul, _root_.mul_comm]
    have hF := Reg.const hG P.isAb hL hJ rF (by
      intro U _ hh
      simp only [CartesianMonoidalCategory.lift_snd, GlobalTheory.SymLiftOdd.comp_pow', hmM]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_pow, ofMul_inv, ofMul_one]
      simp only [← natCast_zsmul]
      push_cast
      module) h 1
    simp only [val_pull hJ, ← Over.comp_left, pt_snd, GlobalTheory.SymLiftOdd.comp_pow', one_pow, hhM, ← hw,
      GlobalTheory.UU.one_left] at hF
    rw [val_powFrame_divisor]
    apply Additive.ofMul.injective
    have f1 := congrArg Additive.ofMul hF
    have f2 := congrArg Additive.ofMul eτ
    have f3 := congrArg Additive.ofMul eτ'
    have f4 := congrArg Additive.ofMul orbitMap_conj_smul_one
    have f5 := congrArg Additive.ofMul eB1
    have f6 := congrArg Additive.ofMul eB1'
    simp only [ofMul_mul, ofMul_zpow, ofMul_pow, ofMul_inv, ofMul_one, ← natCast_zsmul] at f1 f2 f3 f4 f5 f6 ⊢
    push_cast at f1 f2 f3 f4 f5 f6 ⊢
    linear_combination (norm := module) f1 + f3 - (N : ℤ) • f2 + ((M : ℤ) ^ 2) • f4 + f6 - (N : ℤ) • f5
  · have e2 : gs (𝟙 _) y ⊤ v = gs (𝟙 _) y ⊤ v * (val (powFrame P.A P.L h τ N) (𝟙 _) y J).val *
        ((val (powFrame P.A P.L h τ N) (𝟙 _) y J)⁻¹ : (T.left.presheaf.stalk y)ˣ).val := by
      rw [_root_.mul_assoc, Units.mul_inv, _root_.mul_one]
    rw [e2, e1]
    simp only [Units.val_mul]
    ring

private theorem real_pt_nsmul {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) :
    ∀ (c : ℕ) (b : S.Gam), ρ.pt (c • b) = ρ.pt b ^ c := by
  have h0 : ρ.pt 0 = 1 := by
    have := ρ.pt_add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.mp this.symm)
  intro c b
  induction c with
  | zero => rw [zero_smul, h0, pow_zero]
  | succ c ih => rw [succ_nsmul, ρ.pt_add, ih, pow_succ]

private theorem exists_injective_stalk_hom_gs_eq {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) :
    ∃ (y : (baseOver (Sp S.R)).left) (φ : S.R →+* (baseOver (Sp S.R)).left.presheaf.stalk y),
      Function.Injective φ ∧ ∀ a : S.R, gs (𝟙 _) y ⊤ (fn a) = φ a := by
  have hI : IsIntegral (baseOver (Sp S.R)).left := by
    first
    | infer_instance
    | (show IsIntegral (Spec (CommRingCat.of S.R)); infer_instance)
  refine ⟨genericPoint _, (((baseOver (Sp S.R)).left.presheaf.germ ⊤ (genericPoint _) trivial).hom).comp
    (Scheme.ΓSpecIso (CommRingCat.of S.R)).inv.hom, ?_, ?_⟩
  · intro a b h
    have h1 := AlgebraicGeometry.germ_injective_of_isIntegral (baseOver (Sp S.R)).left (U := ⊤) (genericPoint _) trivial
    exact (Scheme.ΓSpecIso (CommRingCat.of S.R)).commRingCatIsoToRingEquiv.symm.injective (h1 h)
  · intro a
    unfold gs
    rw [dite_eq_left (show _ ∈ (⊤ : (baseOver (Sp S.R)).left.Opens) from trivial)]
    rfl

private theorem exists_rootOfUnity_mul_of_pow_eq_pow {K : Type} [Field K] (a b : K) (n : ℕ) (hn : 0 < n) (h : a ^ n = b ^ n) :
    ∃ u : K, u ^ n = 1 ∧ a = u * b := by
  by_cases hb : b = 0
  · subst hb
    rw [zero_pow hn.ne'] at h
    exact ⟨1, one_pow n, by rw [pow_eq_zero_iff hn.ne'] at h; simp [h]⟩
  · refine ⟨a / b, ?_, (div_mul_cancel₀ a hb).symm⟩
    rw [div_pow, h, div_self (pow_ne_zero n hb)]

theorem ev_eq_root_mul_th : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (x : S.Gam) (j : S.J), ∃ (y : S.Gam) (u : Ω) (k : ℕ), 0 < k ∧ u ^ k = 1 ∧ S.ev x j = u * S.th y := by
  intro o Ω _ _ _ _ S ρ x j
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  obtain ⟨a, e, ha⟩ := ρ.orbit j
  have hpt : ∀ (c : ℕ) (b : S.Gam), ρ.pt (c • b) = ρ.pt b ^ c := real_pt_nsmul ρ
  have hpt0 : ρ.pt 0 = 1 := by simpa using hpt 0 0
  have hzero : ∀ b : S.Gam, (S.r * S.N) • b = 0 := by
    intro b; funext i; simp [nsmul_eq_mul]
  have hN : Odd S.N := by rw [ρ.N_eq]; exact (ρ.n_odd.pow).pow
  have hx : ρ.pt (S.r • a) ^ S.N = 1 := by
    rw [← hpt, smul_smul, show S.N * S.r = 1 * (S.r * S.N) by ring, mul_smul, hzero, smul_zero, hpt0]
  have hM : ρ.pt (S.r • a) ^ (S.r * S.N) = 1 := by
    rw [← hpt, smul_smul, show S.r * S.N * S.r = S.r * (S.r * S.N) by ring, mul_smul, hzero, smul_zero, hpt0]
  have hev : ∀ (i : S.J) (b : S.Gam), IsValueAt ρ.P.A ρ.P.L (S.N : ℤ) (ρ.s i) (ρ.pt b)
      (powFrame ρ.P.A ρ.P.L (ρ.pt b) (ρ.fr b) S.N) (fn (⟨S.ev b i, S.ev_mem b i⟩ : S.R)) := by
    intro i b; have := ρ.ev_val i; unfold IsEvT at this; exact this b
  obtain ⟨y, φ, hφi, hφ⟩ := exists_injective_stalk_hom_gs_eq S
  obtain ⟨ξ1, hξ1, H1⟩ := GlobalTheory.ZH.EvCrd.exists_root_stalk hG ρ.P (T := baseOver (Sp S.R)) (N := S.N)
    (M := S.r * S.N) hN (rig := ρ.rig) (x := ρ.pt (S.r • a)) (h := ρ.pt x) (w := ρ.pt (S.r • a + x)) hx hM
    (ρ.pt_add _ _) (θ := ρ.U a) (ρ.U_sym a) (ρ.fr_tors x) (ρ.fr_tors (S.r • a + x)) y
  have E1 := H1 S.J ρ.s (ρ.s ρ.i₀) (fun l => fn (algebraMap o S.R (S.ρ a l ρ.i₀)))
    (fun l => fn (⟨S.ev x l, S.ev_mem x l⟩ : S.R)) (fn (⟨S.ev (S.r • a + x) ρ.i₀, S.ev_mem _ _⟩ : S.R))
    (ρ.U_act a ρ.i₀) (fun l => hev l x) (hev ρ.i₀ _)
  obtain ⟨ξ2, hξ2, H2⟩ := exists_root_stalk_pull hG ρ.P (T := baseOver (Sp S.R)) (N := S.N) (M := S.r * S.N)
    (m := ρ.n ^ ρ.k) (rig := ρ.rig) (α := ρ.α) ρ.α_gen ρ.α_norm (h := ρ.pt (S.r • a + x))
    (w := ρ.pt ((ρ.n ^ ρ.k) • (S.r • a + x))) (hpt _ _) (ρ.fr_tors _) (ρ.fr_tors _) (th := ρ.th₁)
    (s := ρ.s ρ.i₀) ρ.s_zero (hev ρ.i₀ _) (ρ.th_val _) y
  simp only [hφ] at E1 H2
  rw [Finset.sum_eq_single j (fun l _ hl => by rw [ha l, if_neg hl]; simp)
    (fun hj => absurd (Finset.mem_univ j) hj)] at E1
  rw [ha j, if_pos rfl] at E1
  set K := (S.r * S.N) ^ 2 with hK
  have hKpos : 0 < K := by
    have := S.r_pos; have := S.N_ge; positivity
  have hu1 := congrArg Units.val hξ1
  rw [Units.val_pow_eq_pow_val, Units.val_one] at hu1
  have hu2 := congrArg Units.val hξ2
  rw [Units.val_pow_eq_pow_val, Units.val_one] at hu2
  have hR : (algebraMap o S.R (S.ζ ^ e) * ⟨S.ev x j, S.ev_mem x j⟩) ^ K =
      (⟨S.th ((ρ.n ^ ρ.k) • (S.r • a + x)), S.th_mem _⟩ : S.R) ^ K := by
    apply hφi
    rw [map_pow, map_mul, E1, H2, map_pow, mul_pow, mul_pow, hu1, hu2, _root_.one_mul, _root_.one_mul]
  have hz : (algebraMap o Ω S.ζ) ^ K = 1 := by rw [hK, ← map_pow, S.prim.pow_eq_one, map_one]
  have hΩ := congrArg (fun z : S.R => (z : Ω)) hR
  simp only [SubmonoidClass.coe_pow, Subalgebra.coe_mul, Subalgebra.coe_algebraMap] at hΩ
  rw [mul_pow, map_pow, ← pow_mul, _root_.mul_comm e, pow_mul, hz, one_pow, _root_.one_mul] at hΩ
  obtain ⟨u, hu, hux⟩ := exists_rootOfUnity_mul_of_pow_eq_pow _ _ K hKpos hΩ
  exact ⟨_, u, K, hKpos, hu, hux⟩

end GlobalTheory.ZH.EvRoot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSystemValueEqRootMulThetaConstantStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_system_value_eq_root_mul_theta_constant : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (x : S.Gam) (j : S.J), ∃ (y : S.Gam) (u : Ω) (k : ℕ), 0 < k ∧ u ^ k = 1 ∧ S.ev x j = u * S.th y := by
  first | exact @GlobalTheory.ZH.EvRoot.ev_eq_root_mul_th | exact GlobalTheory.ZH.EvRoot.ev_eq_root_mul_th | (intros; apply GlobalTheory.ZH.EvRoot.ev_eq_root_mul_th <;> assumption)
end
end
