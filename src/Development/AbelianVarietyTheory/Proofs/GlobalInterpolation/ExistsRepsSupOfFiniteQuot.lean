module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrivialClassShortInterval
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLFamRay
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormOneDetIdealTransportedLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRepsSupOfFiniteQuot
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory

theorem exists_reps_sup_of_finite_quot (E : Type) [Field E] (H : Type) [AddCommGroup H]
    [Module (𝓞 E) H] (Z₁ Z₀ : Submodule (𝓞 E) H) (C : AddSubgroup H)
    (hfin : Finite (↥Z₁ ⧸ Z₀.comap Z₁.subtype)) :
    ∃ R : Finset H, (∀ x ∈ R, x ∈ Z₁) ∧
      (∀ x ∈ R, ∀ y ∈ R, x - y ∈ Z₀.toAddSubgroup ⊔ C → x = y) ∧
      ∀ y ∈ Z₁, ∃ x ∈ R, y - x ∈ Z₀.toAddSubgroup ⊔ C := by
  classical
  letI := Fintype.ofFinite (↥Z₁ ⧸ Z₀.comap Z₁.subtype)
  set Z : AddSubgroup H := Z₀.toAddSubgroup ⊔ C with hZ
  let s : (↥Z₁ ⧸ Z₀.comap Z₁.subtype) → ↥Z₁ :=
    Function.surjInv (Submodule.Quotient.mk_surjective (Z₀.comap Z₁.subtype))
  have hs : ∀ z, Submodule.Quotient.mk (s z) = z := fun z =>
    Function.surjInv_eq (Submodule.Quotient.mk_surjective (Z₀.comap Z₁.subtype)) z
  let T : Finset (H ⧸ Z) := Finset.univ.image fun z => QuotientAddGroup.mk (s z : H)
  have hsurj : (Z₁ : Set H).SurjOn (QuotientAddGroup.mk : H → H ⧸ Z) T := by
    intro t ht
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ht)
    exact ⟨s z, (s z).2, rfl⟩
  obtain ⟨R, hR, hinj, him⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn _ _ hsurj
  refine ⟨R, fun x hx => hR hx, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hinj hx hy (QuotientAddGroup.eq_iff_sub_mem.2 hxy)
  · intro y hy
    have h1 : (⟨y, hy⟩ : ↥Z₁) - s (Submodule.Quotient.mk ⟨y, hy⟩) ∈ Z₀.comap Z₁.subtype :=
      (Submodule.Quotient.eq _).1 (hs _).symm
    have h2 : y - (s (Submodule.Quotient.mk ⟨y, hy⟩) : H) ∈ Z :=
      AddSubgroup.mem_sup_left (by simpa using h1)
    have h3 : (QuotientAddGroup.mk y : H ⧸ Z) ∈ T :=
      Finset.mem_image.2 ⟨_, Finset.mem_univ _, (QuotientAddGroup.eq_iff_sub_mem.2 h2).symm⟩
    rw [← him] at h3
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.1 h3
    exact ⟨x, hx, QuotientAddGroup.eq_iff_sub_mem.1 hxy.symm⟩

theorem latSum_eq_sum_sum_reps : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (H : Type) [AddCommGroup H] [Module (𝓞 E) H] (Z₁ Z₀ : Submodule (𝓞 E) H) (C : AddSubgroup H) (J : Finset H), Z₀ ≤ Z₁ → C ≤ Z₁.toAddSubgroup → Finite (↥Z₁ ⧸ Z₀.comap Z₁.subtype) → IsReps Z₀.toAddSubgroup C J → ∃ R : Finset H, (∀ x ∈ R, x ∈ Z₁) ∧ ∀ (M : Type) [AddCommMonoid M] (f : H → M), (∀ x ∈ Z₁, ∀ y ∈ Z₀, f (x + y) = f x) → latSum Z₁ Z₀ f = ∑ x ∈ R, ∑ j ∈ J, f (x + j) := by
  intro E _ _ _ H _ _ Z₁ Z₀ C J h01 hC hfin hJ
  classical
  obtain ⟨R, hR, hRinj, hRsurj⟩ := exists_reps_sup_of_finite_quot E H Z₁ Z₀ C hfin
  obtain ⟨hJC, hJinj, hJsurj⟩ := hJ
  refine ⟨R, hR, ?_⟩
  intro M _ f hf
  letI := Fintype.ofFinite (↥Z₁ ⧸ Z₀.comap Z₁.subtype)
  have hmem : ∀ p ∈ R ×ˢ J, p.1 + p.2 ∈ Z₁ := fun p hp =>
    Z₁.add_mem (hR _ (Finset.mem_product.1 hp).1) (hC (hJC _ (Finset.mem_product.1 hp).2))
  unfold latSum
  rw [finsum_eq_sum_of_fintype, ← Finset.sum_product']
  symm
  refine Finset.sum_bij
    (fun p hp => (Submodule.Quotient.mk ⟨p.1 + p.2, hmem p hp⟩ : ↥Z₁ ⧸ Z₀.comap Z₁.subtype))
    (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · rintro ⟨x, j⟩ hp ⟨x', j'⟩ hp' h
    obtain ⟨hx, hj⟩ := Finset.mem_product.1 hp
    obtain ⟨hx', hj'⟩ := Finset.mem_product.1 hp'
    have h1 : x + j - (x' + j') ∈ Z₀ := by
      simpa using (Submodule.Quotient.eq _).1 h
    have h2 : x = x' := by
      refine hRinj x hx x' hx' ?_
      have : x - x' = (x + j - (x' + j')) + (j' - j) := by abel
      rw [this]
      exact AddSubgroup.add_mem_sup h1 (C.sub_mem (hJC _ hj') (hJC _ hj))
    subst h2
    have h3 : j = j' := by
      refine hJinj j hj j' hj' ?_
      have : j - j' = x + j - (x + j') := by abel
      rw [this]
      exact h1
    rw [h3]
  · intro z _
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨x, hx, hyx⟩ := hRsurj y hy
    obtain ⟨a, ha, c, hc, hac⟩ := AddSubgroup.mem_sup.1 hyx
    obtain ⟨j, hj, hcj⟩ := hJsurj c hc
    refine ⟨(x, j), Finset.mem_product.2 ⟨hx, hj⟩, (Submodule.Quotient.eq _).2 ?_⟩
    have h1 : x + j - y = -(a + (c - j)) := by
      have : y = x + (a + c) := by rw [hac]; abel
      rw [this]; abel
    have h2 : x + j - y ∈ Z₀ := by
      rw [h1]
      exact Z₀.neg_mem (Z₀.add_mem ha hcj)
    simpa using h2
  · intro p hp
    set w := Function.surjInv (Submodule.Quotient.mk_surjective (Z₀.comap Z₁.subtype))
      (Submodule.Quotient.mk ⟨p.1 + p.2, hmem p hp⟩) with hw
    have h0 : Submodule.Quotient.mk w =
        (Submodule.Quotient.mk ⟨p.1 + p.2, hmem p hp⟩ : ↥Z₁ ⧸ Z₀.comap Z₁.subtype) :=
      Function.surjInv_eq _ _
    have h1 : (w : H) - (p.1 + p.2) ∈ Z₀ := by
      simpa using (Submodule.Quotient.eq _).1 h0
    have h2 := hf _ (hmem p hp) _ h1
    rw [← h2]
    congr 1
    abel

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPowPrincipal
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation

namespace GlobalTheory.NormOneIdeal

theorem star_integer_smul {E : Type} [Field E] [NumberField E] [StarRing E] (a : 𝓞 E) :
    ∃ b : 𝓞 E, (b : E) = star (a : E) := by
  refine ⟨⟨star (a : E), ?_⟩, rfl⟩
  have h : IsIntegral ℤ (a : E) := a.isIntegral_coe
  exact h.map (starRingEnd E).toIntAlgHom

theorem star_mem_mul {E : Type} [Field E] [NumberField E] [StarRing E]
    {A B C D : Submodule (𝓞 E) E} (h1 : ∀ x ∈ A, star x ∈ C) (h2 : ∀ x ∈ B, star x ∈ D) :
    ∀ x ∈ A * B, star x ∈ C * D := by
  intro x hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro m hm n hn
    rw [star_mul']
    exact Submodule.mul_mem_mul (h1 m hm) (h2 n hn)
  · intro a b ha hb
    rw [star_add]
    exact add_mem ha hb

theorem star_mem_span {E : Type} [Field E] [NumberField E] [StarRing E] (z x : E)
    (hx : x ∈ Submodule.span (𝓞 E) {z}) : star x ∈ Submodule.span (𝓞 E) {star z} := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
  obtain ⟨b, hb⟩ := star_integer_smul a
  refine Submodule.mem_span_singleton.2 ⟨b, ?_⟩
  rw [Algebra.smul_def, Algebra.smul_def, star_mul']
  exact congrArg (· * star z) hb

theorem star_mem_pow {E : Type} [Field E] [NumberField E] [StarRing E]
    {A C : Submodule (𝓞 E) E} (h1 : ∀ x ∈ A, star x ∈ C) (n : ℕ) :
    ∀ x ∈ A ^ n, star x ∈ C ^ n := by
  induction n with
  | zero =>
    intro x hx
    rw [pow_zero, Submodule.one_eq_span] at hx ⊢
    simpa using star_mem_span 1 x hx
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact star_mem_mul ih h1

theorem exists_pow_principal {E : Type} [Field E] [NumberField E]
    (I : (Submodule (𝓞 E) E)ˣ) :
    ∃ (h : ℕ) (z : E), 0 < h ∧ (I : Submodule (𝓞 E) E) ^ h = Submodule.span (𝓞 E) {z} := by
  let e := FractionalIdeal.unitsMulEquivSubmodule (S := nonZeroDivisors (𝓞 E)) (P := E)
  let F := e.symm I
  have hF : ClassGroup.mk E (F ^ Fintype.card (ClassGroup (𝓞 E))) = 1 := by
    rw [map_pow, pow_card_eq_one]
  obtain ⟨z, hz⟩ := ClassGroup.mk_eq_one_iff.1 hF
  refine ⟨Fintype.card (ClassGroup (𝓞 E)), z, Fintype.card_pos, ?_⟩
  rw [← hz]
  have : e (F ^ Fintype.card (ClassGroup (𝓞 E))) = I ^ Fintype.card (ClassGroup (𝓞 E)) := by
    rw [map_pow, MulEquiv.apply_symm_apply]
  rw [← Units.val_pow_eq_pow_val, ← this]
  rfl

theorem pow_eq_span_norm_one : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (I J : Submodule (𝓞 E) E), (∀ x, x ∈ J ↔ star x ∈ I) → I * J = 1 → (∀ (n : ℕ) (x : E), x ∈ J ^ n ↔ star x ∈ I ^ n) ∧ ∃ (h : ℕ) (y : E), 0 < h ∧ star y * y = 1 ∧ Submodule.span (𝓞 E) {y} = I ^ h := by
  intro E _ _ _ I J hJ hIJ
  have h1 : ∀ (n : ℕ) (x : E), x ∈ J ^ n ↔ star x ∈ I ^ n := by
    intro n x
    refine ⟨star_mem_pow (fun x hx => (hJ x).1 hx) n x, fun hx => ?_⟩
    have := star_mem_pow (A := I) (C := J) (fun x hx => (hJ _).2 (by rwa [star_star])) n _ hx
    rwa [star_star] at this
  refine ⟨h1, ?_⟩
  obtain ⟨h, z, hh, hz⟩ := exists_pow_principal (E := E) ⟨I, J, hIJ, by rw [mul_comm, hIJ]⟩
  change I ^ h = _ at hz
  have hJh : J ^ h = Submodule.span (𝓞 E) {star z} := by
    ext x
    rw [h1, hz]
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · simpa using star_mem_span _ _ hx
    · simpa using star_mem_span _ _ hx
  have hm : I ^ h * J ^ h = 1 := by rw [← mul_pow, hIJ, one_pow]
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [hz] at hm
    simp only [Submodule.span_zero_singleton, Submodule.bot_mul] at hm
    have : (1 : E) ∈ (⊥ : Submodule (𝓞 E) E) := by
      rw [hm, Submodule.one_eq_span]
      exact Submodule.mem_span_singleton_self _
    simp at this
  have hs0 : star z ≠ 0 := star_ne_zero.2 hz0
  have hinv : Submodule.span (𝓞 E) {(star z)⁻¹} = I ^ h := by
    calc Submodule.span (𝓞 E) {(star z)⁻¹}
        = I ^ h * J ^ h * Submodule.span (𝓞 E) {(star z)⁻¹} := by rw [hm, one_mul]
      _ = I ^ h := by
        rw [mul_assoc, hJh, Submodule.span_mul_span, Set.singleton_mul_singleton,
          mul_inv_cancel₀ hs0, ← Submodule.one_eq_span, mul_one]
  refine ⟨h + h, z * (star z)⁻¹, by omega, ?_, ?_⟩
  · rw [star_mul', star_inv₀, star_star]
    field_simp
  · rw [pow_add]
    nth_rewrite 1 [hz]
    rw [← hinv, Submodule.span_mul_span, Set.singleton_mul_singleton]

end GlobalTheory.NormOneIdeal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OrdDetConjFinite
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.OrdDetConj

open GlobalTheory.CharValCompare

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

omit [StarRing E] in
theorem ordE_mul (P : HeightOneSpectrum (𝓞 E)) {a b : E} (ha : a ≠ 0) (hb : b ≠ 0) :
    ordE P (a * b) = ordE P a + ordE P b := by
  unfold ordE
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 ha) ((Valuation.ne_zero_iff _).2 hb), neg_add]

theorem exists_ordE_star (P : HeightOneSpectrum (𝓞 E)) :
    ∃ m : ℤ, 0 ≤ m ∧ ∀ a : E, a ≠ 0 → ordE (conjPrime₂ P) (star a) = m * ordE P a := by
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer E
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hs0 : (conjPrime₂ P).valuation E (star π) ≠ 0 := (Valuation.ne_zero_iff _).2 (star_ne_zero.2 hπ0)
  refine ⟨ordE (conjPrime₂ P) (star π), ?_, fun a ha => ?_⟩
  · have h1 : (conjPrime₂ P).valuation E (star π) ≤ 1 := intAt_iff.1 (intAt_star (intAt_iff.2 (by
      rw [hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num)))
    unfold ordE
    rw [neg_nonneg, WithZero.log_le_iff_le_exp hs0]
    exact h1
  · have ha' : P.valuation E a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
    have hsa : (conjPrime₂ P).valuation E (star a) ≠ 0 := (Valuation.ne_zero_iff _).2 (star_ne_zero.2 ha)
    have h1 : P.valuation E (a * π ^ (WithZero.log (P.valuation E a))) = 1 := by
      rw [map_mul, map_zpow₀, hπ, ← WithZero.exp_zsmul]
      conv_lhs => arg 1; rw [← WithZero.exp_log ha']
      rw [← WithZero.exp_add]
      simp
    have h2 := congrArg WithZero.log (val_star_eq_one h1)
    rw [star_mul', star_zpow₀, map_mul, map_zpow₀, WithZero.log_mul hsa (zpow_ne_zero _ hs0), WithZero.log_zpow,
      WithZero.log_one, smul_eq_mul] at h2
    unfold ordE
    linear_combination -h2

theorem ordE_star (P : HeightOneSpectrum (𝓞 E)) {a : E} (ha : a ≠ 0) : ordE (conjPrime₂ P) (star a) = ordE P a := by
  obtain ⟨m, hm, h⟩ := exists_ordE_star P
  obtain ⟨m', hm', h'⟩ := exists_ordE_star (conjPrime₂ P)
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer E
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have h1 : ordE P π = 1 := by
    unfold ordE
    rw [hπ, WithZero.log_exp, neg_neg]
  have h2 := h' (star π) (star_ne_zero.2 hπ0)
  rw [conjP_conjP, star_star, h π hπ0, h1, mul_one] at h2
  have h3 : m = 1 := Int.eq_one_of_mul_eq_one_left hm h2.symm
  rw [h a ha, h3, one_mul]

theorem ordDet_conjP {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) (P : HeightOneSpectrum (𝓞 E)) :
    ordDet (conjPrime₂ P) N = -ordDet P N := by
  obtain ⟨f, hf⟩ := exists_isFr P hN
  obtain ⟨f', hf'⟩ := exists_isFr (conjPrime₂ P) hN
  have h := val_dual hN hf hf'
  have h0 : star (dt f) ≠ 0 := star_ne_zero.2 (dt_ne _)
  rw [← ordE_eq_zero_iff (mul_ne_zero h0 (dt_ne _)), ordE_mul _ h0 (dt_ne _), ordE_star P (dt_ne _)] at h
  rw [ordDet_eq hf, ordDet_eq hf']
  linear_combination h

theorem finite_pos {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) :
    {Q : HeightOneSpectrum (𝓞 E) | 0 < ordDet Q N}.Finite := by
  rcases Set.eq_empty_or_nonempty {Q : HeightOneSpectrum (𝓞 E) | 0 < ordDet Q N} with h | ⟨P, -⟩
  · rw [h]; exact Set.finite_empty
  obtain ⟨f, hf⟩ := exists_isFr P hN
  obtain ⟨s, hs, hx⟩ := (mem_locP _ _ _).1 (((gen_detI hf).2 _).2 le_rfl)
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hs (zero_mem _)
  have hx0 : s • dt f ≠ 0 := smul_ne_zero hs0 (dt_ne _)
  refine (HeightOneSpectrum.Support.finite (𝓞 E) (s • dt f)⁻¹).subset fun Q hQ => ?_
  obtain ⟨g, hg⟩ := exists_isFr Q hN
  have h1 := ((gen_detI hg).2 _).1 (le_locP Q _ hx)
  have h2 : Q.valuation E (dt g) < 1 := by
    rw [Set.mem_ofPred_eq, ordDet_eq hg, ordE, neg_pos,
      WithZero.log_lt_iff_lt_exp ((Valuation.ne_zero_iff _).2 (dt_ne _))] at hQ
    exact hQ
  show 1 < Q.valuation E (s • dt f)⁻¹
  rw [map_inv₀, one_lt_inv₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx0))]
  exact h1.trans_lt h2

theorem ordDet_conj_finite : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (N : Submodule (𝓞 E) (Sp E n)), IsSdLat N → (∀ P : HeightOneSpectrum (𝓞 E), ordDet (conjPrime₂ P) N = -ordDet P N) ∧ {Q : HeightOneSpectrum (𝓞 E) | ordDet Q N ≠ 0}.Finite := by
  intro E _ _ _ n N hN
  refine ⟨ordDet_conjP hN, ((finite_pos hN).union ((finite_pos hN).image conjPrime₂)).subset fun Q hQ => ?_⟩
  rcases lt_or_gt_of_ne hQ with h | h
  · refine Or.inr ⟨conjPrime₂ Q, ?_, conjP_conjP Q⟩
    rw [Set.mem_ofPred_eq, ordDet_conjP hN]
    exact neg_pos.2 h
  · exact Or.inl h

end GlobalTheory.OrdDetConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexPerDvd
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT.IdxBound

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem mem_of_locP {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (M : Submodule (𝓞 E) W) (x : W)
    (h : ∀ Q : HeightOneSpectrum (𝓞 E), x ∈ localization₂ Q.asIdeal M) : x ∈ M := by
  by_contra hx
  let I : Ideal (𝓞 E) := M.comap (LinearMap.toSpanSingleton (𝓞 E) W x)
  have hI : ∀ s, s ∈ I ↔ s • x ∈ M := fun s => Iff.rfl
  have hne : I ≠ ⊤ := fun e => hx (by simpa using (hI 1).1 (e ▸ Submodule.mem_top))
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I hne
  have hm0 : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)
  obtain ⟨s, hs, hsx⟩ := (mem_locP ⟨m, hm.isPrime, hm0⟩ M x).1 (h _)
  exact hs (hle ((hI s).2 hsx))

theorem mem_localization_of_smul_mem {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) W)
    {x : W} {s : 𝓞 E} (hs : s ∉ P.asIdeal) (h : s • x ∈ localization₂ P.asIdeal M) : x ∈ localization₂ P.asIdeal M := by
  obtain ⟨t, ht, htx⟩ := (mem_locP P M _).1 h
  refine (mem_locP P M _).2 ⟨t * s, fun h' => (P.isPrime.mem_or_mem h').elim ht hs, ?_⟩
  rwa [mul_smul]

theorem per_apply_mem {AA : Submodule (𝓞 E) E} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}
    {P : HeightOneSpectrum (𝓞 E)} (hA : localization₂ P.asIdeal AA = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E))
    {y : HomE E a b} (hy : y ∈ perO AA N N') {v : Sp E a} (hv : v ∈ localization₂ P.asIdeal N) : y v ∈ localization₂ P.asIdeal N' := by
  obtain ⟨s', hs', hv'⟩ := (mem_locP P N v).1 hv
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, hr, x, hx, rfl⟩ := hz
    obtain ⟨s, hs, hr'⟩ := (mem_locP P _ r).1 (hA ▸ le_locP P AA hr)
    obtain ⟨t, ht⟩ := Submodule.mem_one.1 hr'
    refine mem_localization_of_smul_mem P _ hs (mem_localization_of_smul_mem P _ hs' (le_locP P _ ?_))
    have h1 : x (s' • v) ∈ N' := hx _ hv'
    have h2 : s' • s • (r • x) v = t • x (s' • v) := by
      rw [LinearMap.map_smul_of_tower, LinearMap.smul_apply, ← smul_assoc s r, ← ht, algebraMap_smul, smul_comm]
    rw [h2]
    exact N'.smul_mem t h1
  | zero => simp
  | add y z _ _ hy hz => simpa using add_mem hy hz
  | smul r z _ hz => simpa using Submodule.smul_mem _ r hz

theorem mem_localization_perO {AA : Submodule (𝓞 E) E} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}
    {P : HeightOneSpectrum (𝓞 E)} (hA : localization₂ P.asIdeal AA = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)) (hN : N.FG)
    {y : HomE E a b} (hy : ∀ v ∈ N, y v ∈ localization₂ P.asIdeal N') : y ∈ localization₂ P.asIdeal (perO AA N N') := by
  classical
  obtain ⟨S, rfl⟩ := hN
  choose! s hs hsy using fun v (hv : v ∈ S) => (mem_locP P N' _).1 (hy v (Submodule.subset_span hv))
  have hP : ∏ v ∈ S, s v ∉ P.asIdeal := fun h => by
    obtain ⟨v, hv, h'⟩ := (P.isPrime.prod_mem_iff).1 h
    exact hs v hv h'
  have hh : (∏ v ∈ S, s v) • y ∈ homO (Submodule.span (𝓞 E) (S : Set (Sp E a))) N' := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      rw [← Finset.prod_erase_mul S s hv, LinearMap.smul_apply, mul_smul]
      exact N'.smul_mem _ (hsy v hv)
    | zero => simp
    | add v w _ _ hv hw => rw [map_add]; exact add_mem hv hw
    | smul r v _ hv => rw [LinearMap.map_smul_of_tower]; exact N'.smul_mem r hv
  obtain ⟨t, ht, h1⟩ := (mem_locP P AA 1).1 (hA ▸ le_locP P _ (Submodule.one_le.1 le_rfl))
  refine mem_localization_of_smul_mem P _ hP (mem_localization_of_smul_mem P _ ht (le_locP P _ (Submodule.subset_span ⟨_, h1, _, hh, ?_⟩)))
  rw [smul_assoc t (1 : E), one_smul]

theorem smul_mem_per {AA : Submodule (𝓞 E) E} {N : Submodule (𝓞 E) (Sp E a)} {N' N'' : Submodule (𝓞 E) (Sp E b)}
    {w : 𝓞 E} (h : ∀ y ∈ N', (w : E) • y ∈ N'') {y : HomE E a b} (hy : y ∈ perO AA N N') : w • y ∈ perO AA N N'' := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, hr, x, hx, rfl⟩ := hz
    refine Submodule.subset_span ⟨r, hr, w • x, fun v hv => h _ (hx v hv), (smul_comm _ _ _).symm⟩
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | smul r z _ hz => rw [smul_comm]; exact Submodule.smul_mem _ r hz

theorem apply_mem_of_std {N' : Submodule (𝓞 E) (Sp E b)} {P : HeightOneSpectrum (𝓞 E)} {y : HomE E a b}
    (hy : ∀ i, y (Pi.single i 1) ∈ localization₂ P.asIdeal N') {v : Sp E a} (hv : v ∈ stdAt E a P) : y v ∈ localization₂ P.asIdeal N' := by
  obtain ⟨s, hs, hsv⟩ := (mem_locP P _ v).1 hv
  choose t ht using fun i => Submodule.mem_one.1 (Submodule.mem_pi.1 hsv i (Set.mem_univ _))
  refine mem_localization_of_smul_mem P _ hs ?_
  have e : s • v = ∑ i, t i • (Pi.single i 1 : Sp E a) := by
    ext j
    rw [← ht j]
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← LinearMap.map_smul_of_tower, e, map_sum]
  exact Submodule.sum_mem _ fun i _ => by
    rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ _ (hy i)

theorem relIndex_per_dvd : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (p : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (d : DecoSet (E := X.E) (n := b) (ST := divs ϖ) (SG := SG)) (N'' : Submodule (𝓞 X.E) (Sp X.E b)), A.AA.FG → A.AA ≠ ⊥ → A.AAUnit (divs ϖ) → ϖ ≠ 0 → (∀ P ∈ divs ϖ, Ideal.absNorm P.asIdeal = p) → IsSdLat N → IsSdLat N'' → (∀ P ∈ divs ϖ, localization₂ P.asIdeal N = stdAt X.E a P) → ((∀ y ∈ d.1.N, (ϖ : X.E) • y ∈ N'') ∧ (∀ y ∈ N'', star (ϖ : X.E) • y ∈ d.1.N) ∧ ∀ (P : ↥(divs ϖ)) (y : Sp X.E b), y ∈ localization₂ P.1.asIdeal N'' ↔ y ∈ d.1.at P.1 ∧ d.1.f P y = 0) → (per A N N'').toAddSubgroup.relIndex (per A N d.1.N).toAddSubgroup ∣ p ^ ((divs ϖ).card * a) := by
  intro X A a b SG ϖ p N d N'' _ _ hU h0 hp hN _ hstd ⟨h1, _, h3⟩
  have he : ∀ (P : ↥(divs ϖ)) (i : Fin a), (Pi.single i 1 : Sp X.E a) ∈ localization₂ P.1.asIdeal N := fun P i => by
    rw [hstd P.1 P.2]
    exact le_locP P.1 _ (by simpa using single_mem_stdLat (E := X.E) i 1)
  have hm : ∀ (x : (per A N d.1.N).toAddSubgroup) (P : ↥(divs ϖ)) (i : Fin a), x.1 (Pi.single i 1) ∈ d.1.at P.1 :=
    fun x P i => per_apply_mem (hU P.1 P.2) x.2 (he P i)
  let φ : (per A N d.1.N).toAddSubgroup →+ ((P : ↥(divs ϖ)) → Fin a → 𝓞 X.E ⧸ P.1.asIdeal) :=
    AddMonoidHom.mk' (fun x P i => d.1.f P (x.1 (Pi.single i 1))) fun x y => by
      funext P i
      exact d.2.f_add P _ (hm x P i) _ (hm y P i)
  have hker : φ.ker ≤ (per A N N'').toAddSubgroup.addSubgroupOf (per A N d.1.N).toAddSubgroup := by
    intro x hx
    refine mem_of_locP (per A N N'') x.1 fun Q => ?_
    by_cases hQ : Q ∈ divs ϖ
    · refine mem_localization_perO (hU Q hQ) hN.1.fg fun v hv => apply_mem_of_std (fun i => ?_) (hstd Q hQ ▸ le_locP Q N hv)
      exact (h3 ⟨Q, hQ⟩ _).2 ⟨hm x ⟨Q, hQ⟩ i, congrFun (congrFun hx ⟨Q, hQ⟩) i⟩
    · exact mem_localization_of_smul_mem Q _ (fun h => hQ ((mem_divs h0 Q).2 h)) (le_locP Q _ (smul_mem_per h1 x.2))
  have hc : Nat.card ((P : ↥(divs ϖ)) → Fin a → 𝓞 X.E ⧸ P.1.asIdeal) = p ^ ((divs ϖ).card * a) := by
    have : ∀ P : ↥(divs ϖ), Nat.card (Fin a → 𝓞 X.E ⧸ P.1.asIdeal) = p ^ a := fun P => by
      rw [Nat.card_fun, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hp P.1 P.2]
      simp
    rw [Nat.card_pi, Finset.prod_congr rfl fun P _ => this P]
    simp [← pow_mul, mul_comm]
  refine (AddSubgroup.index_dvd_of_le hker).trans ?_
  rw [AddSubgroup.index_ker, ← hc]
  exact AddSubgroup.card_addSubgroup_dvd_card _

end GlobalTheory.MomT.IdxBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexMulVec
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.IdxDet

open GlobalTheory.LatBasisAt

variable {E : Type} [Field E] [NumberField E]

theorem intAt_iff_mem (w : HeightOneSpectrum (𝓞 E)) (a : E) : IntAt w a ↔ a ∈ locRing w := by
  rw [mem_locRing]
  constructor
  · rintro ⟨r, s, hs, h⟩
    have := algebraMap_ne_zero w hs
    exact ⟨r, s, hs, by rw [← h]; field_simp⟩
  · rintro ⟨r, s, hs, h⟩
    have := algebraMap_ne_zero w hs
    exact ⟨r, s, hs, by rw [h]; field_simp⟩

theorem val_le_one (P : HeightOneSpectrum (𝓞 E)) (a : locRing P) : P.valuation E (a : E) ≤ 1 :=
  GlobalTheory.CharValCompare.intAt_iff.1 ((intAt_iff_mem P _).2 a.2)

theorem val_unit (P : HeightOneSpectrum (𝓞 E)) (u : (locRing P)ˣ) :
    P.valuation E ((u : locRing P) : E) = 1 := by
  have h : P.valuation E ((u : locRing P) : E) * P.valuation E (((u⁻¹ : (locRing P)ˣ) : locRing P) : E) = 1 := by
    rw [← map_mul, ← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one, map_one]
  refine le_antisymm (val_le_one P _) ?_
  rw [← h]
  exact mul_le_of_le_one_right' (val_le_one P _)

theorem val_irreducible (P : HeightOneSpectrum (𝓞 E)) [IsDiscreteValuationRing (locRing P)]
    {p : locRing P} (hp : Irreducible p) : P.valuation E (p : E) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer E
  have hπ1 : π ∈ locRing P := by
    rw [← intAt_iff_mem, GlobalTheory.CharValCompare.intAt_iff, hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  have hπ0 : (⟨π, hπ1⟩ : locRing P) ≠ 0 := by
    intro h
    have : π = 0 := congrArg Subtype.val h
    rw [this, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hπ0 hp
  have h1 : π * ((u : locRing P) : E) = (p : E) ^ k := by
    simpa using congrArg Subtype.val hu
  have h2 := congrArg (P.valuation E) h1
  rw [map_mul, val_unit, mul_one, hπ, map_pow] at h2
  have hp0 : P.valuation E (p : E) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact fun h => hp.ne_zero (Subtype.ext h)
  have hle := val_le_one P p
  rw [← WithZero.exp_log hp0] at h2 hle ⊢
  generalize WithZero.log (P.valuation E (p : E)) = a at h2 hle ⊢
  rw [← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul] at h2
  rw [← WithZero.exp_zero, WithZero.exp_le_exp] at hle
  congr 1
  have : a ∣ 1 := ⟨-k, by linarith⟩
  rcases Int.isUnit_iff.1 (isUnit_of_dvd_one this) with h | h
  · omega
  · exact h

theorem relIndex_mulVec : ∀ (E : Type) [Field E] [NumberField E] (ι : Type) [Fintype ι] [DecidableEq ι] (P : HeightOneSpectrum (𝓞 E)) (M : Matrix ι ι E) (L₀ L₁ : AddSubgroup (ι → E)), M.det ≠ 0 → (∀ x, x ∈ L₀ ↔ ∀ i, IntAt P (x i)) → (∀ x, x ∈ L₁ ↔ ∃ y ∈ L₀, x = M.mulVec y) → L₁ ≤ L₀ → ((L₁.relIndex L₀ : ℕ) : ℚ) = ((Ideal.absNorm P.asIdeal : ℕ) : ℚ) ^ ordE P M.det := by
  intro E _ _ ι _ _ P M L₀ L₁ hdet h0 h1 hle
  haveI := P.isPrime
  haveI := P.isMaximal
  haveI : IsDiscreteValuationRing (locRing P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) P.ne_bot (locRing P)
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible (locRing P)
  have hent : ∀ i j, M i j ∈ locRing P := by
    intro i j
    have hs : (Pi.single j 1 : ι → E) ∈ L₀ := by
      rw [h0]
      intro k
      rw [intAt_iff_mem, Pi.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have := (h0 _).1 (hle ((h1 _).2 ⟨_, hs, rfl⟩)) i
    rw [intAt_iff_mem] at this
    simpa using this
  let N : Matrix ι ι (locRing P) := Matrix.of fun i j => ⟨_, hent i j⟩
  have hN : N.map (algebraMap (locRing P) E) = M := by
    ext i j; rfl
  have hNd : ((N.det : locRing P) : E) = M.det := by
    rw [← hN]
    exact RingHom.map_det (algebraMap (locRing P) E) N
  have hne : N.det ≠ 0 := by
    intro h
    rw [h] at hNd
    exact hdet hNd.symm
  have hinj : Function.Injective (Matrix.toLin' N) := by
    rw [← LinearMap.ker_eq_bot, Matrix.ker_toLin'_eq_bot_iff]
    intro v hv
    exact Matrix.eq_zero_of_mulVec_eq_zero hne hv
  obtain ⟨m, ⟨v, hv⟩, hc⟩ := GlobalTheory.HL.LatDet.card_coker (Pi.basisFun (locRing P) ι) hp _ hinj
  rw [LinearMap.det_toLin'] at hv
  have hord : ordE P M.det = m := by
    have e1 : M.det * ((v : locRing P) : E) = (p : E) ^ m := by
      rw [← hNd]; exact_mod_cast congrArg Subtype.val hv
    have e2 := congrArg (P.valuation E) e1
    rw [map_mul, val_unit, mul_one, map_pow, val_irreducible P hp, ← WithZero.exp_nsmul] at e2
    unfold ordE
    rw [e2, WithZero.log_exp]
    simp
  have hq : Nat.card (locRing P ⧸ Ideal.span {p}) = Ideal.absNorm P.asIdeal := by
    rw [← hp.maximalIdeal_eq, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact (Nat.card_congr (IsLocalization.AtPrime.equivQuotMaximalIdeal P.asIdeal (locRing P)).toEquiv).symm
  let e : (ι → locRing P) →+ (ι → E) :=
    { toFun := fun x i => (x i : E)
      map_zero' := rfl
      map_add' := fun x y => rfl }
  have hei : Function.Injective e := by
    intro x y hxy
    funext i
    exact Subtype.ext (congrFun hxy i)
  have hW0 : L₀ = AddSubgroup.map e ⊤ := by
    ext x
    rw [h0]
    constructor
    · intro hx
      exact ⟨fun i => ⟨_, (intAt_iff_mem P _).1 (hx i)⟩, trivial, rfl⟩
    · rintro ⟨y, -, rfl⟩ i
      exact (intAt_iff_mem P _).2 (y i).2
  have hcomm : ∀ y, M.mulVec (e y) = e (Matrix.toLin' N y) := by
    intro y
    funext i
    rw [← hN]
    exact (RingHom.map_mulVec (algebraMap (locRing P) E) N y i).symm
  have hW1 : L₁ = AddSubgroup.map e (LinearMap.range (Matrix.toLin' N)).toAddSubgroup := by
    ext x
    rw [h1, hW0]
    constructor
    · rintro ⟨_, ⟨y, -, rfl⟩, rfl⟩
      exact ⟨_, ⟨y, rfl⟩, (hcomm y).symm⟩
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨_, ⟨y, trivial, rfl⟩, (hcomm y).symm⟩
  have : L₁.relIndex L₀ = Ideal.absNorm P.asIdeal ^ m := by
    rw [hW1, hW0, AddSubgroup.relIndex_map_map_of_injective _ _ hei, AddSubgroup.relIndex_top_right, ← hq]
    exact hc
  rw [this, hord, zpow_natCast, Nat.cast_pow]

end GlobalTheory.IdxDet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormPrimesImagQuadShortIntervalLowerBound
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormPrimesImagQuadShortIntervalLowerBound
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk

theorem sum_lam_zero_le_card_normPrimes (𝓕 : LFam) (d M : ℕ)
    (hN : ∀ p : ℕ, p.Prime → 𝓕.lam 0 p ≠ 0 → GlobalTheory.Mem.An.NormOne d M p) (X Y : ℝ) (hY : 1 ≤ Y) :
    ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊Y⌋₊, 𝓕.lam 0 n ≤
      2 * Real.log Y * ((GlobalTheory.Mem.An.normPrimes d M X Y).card : ℝ) +
        2 * (Chebyshev.psi Y - Chebyshev.theta Y) := by
  have hl : ∀ n, 𝓕.lam 0 n ≤ 2 * vonMangoldt n := fun n =>
    le_trans (Finset.single_le_sum (f := fun g => 𝓕.lam g n) (fun g _ => 𝓕.lam_nonneg g n)
      (Finset.mem_univ _)) (𝓕.lam_le n)
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun n : ℕ => n.Prime)]
  apply add_le_add
  · have h1 : ∑ n ∈ (Finset.Ioc ⌊X⌋₊ ⌊Y⌋₊).filter (fun n : ℕ => n.Prime), 𝓕.lam 0 n =
        ∑ n ∈ GlobalTheory.Mem.An.normPrimes d M X Y, 𝓕.lam 0 n := by
      symm
      apply Finset.sum_subset
      · intro p hp
        simp only [GlobalTheory.Mem.An.normPrimes, Finset.mem_filter] at hp ⊢
        exact ⟨hp.1, hp.2.1⟩
      · intro p hp hq
        simp only [GlobalTheory.Mem.An.normPrimes, Finset.mem_filter] at hp hq
        by_contra h
        exact hq ⟨hp.1, hp.2, hN p hp.2 h⟩
    rw [h1, mul_comm, ← nsmul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro p hp
    simp only [GlobalTheory.Mem.An.normPrimes, Finset.mem_filter, Finset.mem_Ioc] at hp
    have h2 : (p : ℝ) ≤ Y := (Nat.le_floor_iff (by linarith)).1 hp.1.2
    have h3 : Real.log p ≤ Real.log Y :=
      Real.log_le_log (by exact_mod_cast hp.2.1.pos) h2
    have h4 := hl p
    rw [vonMangoldt_apply_prime hp.2.1] at h4
    linarith
  · rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum fun n _ => hl n) ?_
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_left (Nat.zero_le _))
    · intro n _ _
      have := @vonMangoldt_nonneg n
      positivity

theorem sqrt_le_short_main {A K c B X h : ℝ} (hA : 0 < A) (hK : 0 < K) (hc : 0 < c)
    (hcT : c ≤ 1 / (2 * (1 + A) + 2 + K)) (hB : 4 ≤ B) (hX : 1 ≤ X)
    (hBX : Real.log B ≤ c * Real.sqrt (Real.log X))
    (hh : Real.exp (-c * Real.sqrt (Real.log X)) ≤ h) :
    1 ≤ Real.log X ∧ K * Real.sqrt X ≤ h * X / B ^ A := by
  set s := Real.sqrt (Real.log X) with hs
  have hL : 0 ≤ Real.log X := Real.log_nonneg hX
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s * s = Real.log X := Real.mul_self_sqrt hL
  have hB0 : 0 < B := by linarith
  have hB1 : 1 ≤ Real.log B := by
    rw [Real.le_log_iff_exp_le hB0]
    have := Real.exp_one_lt_d9
    linarith
  set T := 2 * (1 + A) + 2 + K with hT
  have hT0 : 0 < T := by positivity
  have hcT' : c * T ≤ 1 := by rwa [le_div_iff₀ hT0] at hcT
  have hsT : T ≤ s := by
    by_contra h'
    have : c * s < c * T := mul_lt_mul_of_pos_left (not_le.1 h') hc
    linarith
  have hc1 : c ≤ 1 := by nlinarith
  have hs1 : 1 ≤ s := by linarith
  refine ⟨by nlinarith, ?_⟩
  have hX0 : 0 < X := by linarith
  have hsq : Real.sqrt X = Real.exp (s * s / 2) := by
    rw [hss, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hX0]
    congr 1; ring
  have hXe : X = Real.exp (s * s) := by rw [hss, Real.exp_log hX0]
  have hcs : c * s ≤ s := by nlinarith
  have hBA : B ^ A ≤ Real.exp (A * s) := by
    rw [Real.rpow_def_of_pos hB0]
    apply Real.exp_le_exp.2
    nlinarith
  have hh' : Real.exp (-s) ≤ h := le_trans (Real.exp_le_exp.2 (by linarith)) hh
  have hKe : K ≤ Real.exp (s * s / 2 - (1 + A) * s) := by
    have := Real.add_one_le_exp (s * s / 2 - (1 + A) * s)
    have h5 : s * 1 ≤ s * (s / 2 - (1 + A)) := mul_le_mul_of_nonneg_left (by linarith) hs0
    nlinarith
  have hBA0 : 0 < B ^ A := Real.rpow_pos_of_pos hB0 A
  rw [le_div_iff₀ hBA0, hsq]
  calc K * Real.exp (s * s / 2) * B ^ A
      ≤ Real.exp (s * s / 2 - (1 + A) * s) * Real.exp (s * s / 2) * Real.exp (A * s) := by
        gcongr
    _ = Real.exp (-s) * Real.exp (s * s) := by
        simp only [← Real.exp_add]; congr 1; ring
    _ ≤ h * X := by
        rw [← hXe]; gcongr

theorem normPrimes_short_interval_lower : ∃ A c c' : ℝ, 0 < A ∧ 0 < c ∧ 0 < c' ∧ ∀ (d M : ℕ) (X h : ℝ), d.Prime → d % 4 = 3 → 100 ≤ d → 3 ≤ M → 1 ≤ X → Real.log (4 * (d : ℝ) * (M : ℝ) ^ 2) ≤ c * Real.sqrt (Real.log X) → Real.exp (-c * Real.sqrt (Real.log X)) ≤ h → h ≤ 1 → c' * h * X / ((4 * (d : ℝ) * (M : ℝ) ^ 2) ^ A * Real.log X) ≤ ((GlobalTheory.Mem.An.normPrimes d M X (X * (1 + h))).card : ℝ) := by
  obtain ⟨A, c₀, e, hA, hc₀, he, H⟩ := GlobalTheory.T.exists_lam_zero_sum_shortInterval_ge
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  set K : ℝ := 8 * (|C| + 1) / e with hKdef
  have hK : 0 < K := by positivity
  refine ⟨A, min c₀ (1 / (2 * (1 + A) + 2 + K)), e / 8, hA, lt_min hc₀ (by positivity),
    by positivity, ?_⟩
  intro d M X h hd hd4 hd100 hM hX hB hh hh1
  obtain ⟨𝓕, hFB, hN⟩ := GlobalTheory.T.exists_lFam_normOne_of_mod_four_eq_three d M hd hd4 hd100 hM
  rw [← hFB] at hB ⊢
  set c := min c₀ (1 / (2 * (1 + A) + 2 + K)) with hc
  have hc0 : 0 < c := lt_min hc₀ (by positivity)
  have hcc : c * Real.sqrt (Real.log X) ≤ c₀ * Real.sqrt (Real.log X) :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _)
  have h0 : 0 < h := lt_of_lt_of_le (Real.exp_pos _) hh
  have H1 := H 𝓕 X h hX (hB.trans hcc) (le_trans (Real.exp_le_exp.2 (by linarith)) hh) hh1
  obtain ⟨hL, hS⟩ := sqrt_le_short_main hA hK hc0 (min_le_right _ _) 𝓕.B_ge hX hB hh
  have hY1 : 1 ≤ X * (1 + h) := by nlinarith
  have hY2 : X * (1 + h) ≤ 2 * X := by nlinarith
  have H2 := sum_lam_zero_le_card_normPrimes 𝓕 d M hN X (X * (1 + h)) hY1
  have hlog : Real.log (X * (1 + h)) ≤ 2 * Real.log X := by
    rw [Real.log_mul (by linarith) (by linarith)]
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + h by linarith)
    linarith
  have hsq : Real.sqrt (X * (1 + h)) ≤ 2 * Real.sqrt X := by
    rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt (by linarith)]
    linarith
  have H3 : Chebyshev.psi (X * (1 + h)) - Chebyshev.theta (X * (1 + h)) ≤
      (|C| + 1) * (2 * Real.sqrt X) := by
    refine (hC _).trans ?_
    have := le_abs_self C
    have := abs_nonneg C
    have := Real.sqrt_nonneg (X * (1 + h))
    gcongr
    linarith
  have hBA0 : 0 < 𝓕.B ^ A := Real.rpow_pos_of_pos (by linarith [𝓕.B_ge]) A
  set N : ℝ := ((GlobalTheory.Mem.An.normPrimes d M X (X * (1 + h))).card : ℝ) with hNdef
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have H4 : 8 * (|C| + 1) * Real.sqrt X ≤ e * (h * X / 𝓕.B ^ A) := by
    have : 8 * (|C| + 1) * Real.sqrt X = e * (K * Real.sqrt X) := by
      rw [hKdef]; field_simp
    rw [this]; gcongr
  have H5 : e * h * X / 𝓕.B ^ A = e * (h * X / 𝓕.B ^ A) := by ring
  have H6 : 2 * Real.log (X * (1 + h)) * N ≤ 4 * Real.log X * N := by
    apply mul_le_mul_of_nonneg_right _ hN0
    linarith
  have H7 : e / 8 * h * X / (𝓕.B ^ A * Real.log X) = e * (h * X / 𝓕.B ^ A) / (8 * Real.log X) := by
    field_simp
  rw [H7, div_le_iff₀ (by linarith)]
  linarith

end GlobalTheory.Hk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormPrimesImagQuadShortIntervalLowerBoundStatement
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normPrimesImagQuad_short_interval_lower_bound : ∃ A c c' : ℝ, 0 < A ∧ 0 < c ∧ 0 < c' ∧ ∀ (d M : ℕ) (X h : ℝ), d.Prime → d % 4 = 3 → 100 ≤ d → 3 ≤ M → 1 ≤ X → Real.log (4 * (d : ℝ) * (M : ℝ) ^ 2) ≤ c * Real.sqrt (Real.log X) → Real.exp (-c * Real.sqrt (Real.log X)) ≤ h → h ≤ 1 → c' * h * X / ((4 * (d : ℝ) * (M : ℝ) ^ 2) ^ A * Real.log X) ≤ ((GlobalTheory.Mem.An.normPrimes d M X (X * (1 + h))).card : ℝ) := by
  first | exact @GlobalTheory.Hk.normPrimes_short_interval_lower | exact GlobalTheory.Hk.normPrimes_short_interval_lower | (intros; apply GlobalTheory.Hk.normPrimes_short_interval_lower <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitChoiceSizeNodes
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitChoiceSizeNodes
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_sizeNodes : SzRow (fun _ _ L => SizeNodes L) := by
  intro eps he0 he1 C _
  obtain ⟨x1, hx1⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he0 he1
  refine ⟨0, fun cD hcD => ⟨1300 + cD, fun ch hch => ⟨max x1 200, fun D L hε hx hV => ?_⟩⟩⟩
  simp only [max_le_iff, ge_iff_le] at hx hch
  obtain ⟨hxa, hxb⟩ := hx
  obtain ⟨hf, hm, hr, hkr, -, hL, hL1, -, -, -, -, -, -, ht, hN, -, -⟩ := hx1 L.sc D.R hε hxa hV.ranks
  have hxone : 1 ≤ L.sc.x := by linarith
  have hxpos : 0 < L.sc.x := by linarith
  have cast : ∀ a : ℕ, L.sc.x ^ (a : ℝ) = L.sc.x ^ a := fun a => Real.rpow_natCast _ _
  have hf' : (D.R.f : ℝ) ≤ L.sc.x ^ 3 := by rw [← cast]; exact_mod_cast hf
  have hr' : (D.R.r : ℝ) ≤ L.sc.x ^ 5 := by rw [← cast]; exact_mod_cast hr
  have ht' : (D.R.t : ℝ) ≤ L.sc.x ^ 401 := by rw [← cast]; exact_mod_cast ht
  have hN' : (D.R.N D.R.m : ℝ) ≤ L.sc.x ^ 402 := by rw [← cast]; exact_mod_cast hN
  have hk' : (D.R.k : ℝ) ≤ L.sc.x ^ 5 := le_trans (by exact_mod_cast hkr) hr'
  have hnf : (D.R.n : ℝ) ≤ D.R.f := by
    have : D.R.n ≤ D.R.f := by unfold Ranks.f; omega
    exact_mod_cast this
  have hm2 := D.R.two_le_m
  have hm1 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hMN : (D.R.r : ℝ) + D.R.m * D.R.t ≤ D.R.N D.R.m := by
    have : D.R.r + D.R.m * D.R.t ≤ D.R.N D.R.m := by
      unfold Ranks.N Ranks.r
      rw [Nat.mul_add, Nat.mul_one]; omega
    exact_mod_cast this
  have hY : 1 ≤ L.sc.x ^ cD := Real.one_le_rpow hxone hcD
  have hDel : ((Delv L.sc cD : ℕ) : ℝ) ≤ 2 * L.sc.x ^ cD := by
    have := Nat.ceil_lt_add_one (a := L.sc.x ^ cD) (by linarith)
    unfold Delv; linarith
  have hSc : L.Sc = (D.R.k : ℝ) * (4 * ((Delv L.sc cD : ℕ) : ℝ)) := by
    rw [L.Sc_eq, hV.Del_eq]; push_cast; ring
  have hS0 : 0 ≤ L.Sc := by rw [hSc]; positivity
  have hS : L.Sc ≤ L.sc.x ^ 6 * L.sc.x ^ cD := by
    rw [hSc]
    calc (D.R.k : ℝ) * (4 * ((Delv L.sc cD : ℕ) : ℝ)) ≤ L.sc.x ^ 5 * (4 * (2 * L.sc.x ^ cD)) := by gcongr
      _ = L.sc.x ^ 5 * 8 * L.sc.x ^ cD := by ring
      _ ≤ L.sc.x ^ 5 * L.sc.x * L.sc.x ^ cD := by gcongr; linarith
      _ = _ := by ring
  have hh0 : L.sc.x ^ ch ≤ L.etaSz / D.R.m := by
    have e : L.etaSz / D.R.m = (h0v L.sc ch : ℝ) := by
      rw [hV.eta_eq]; field_simp
    have := Nat.le_ceil (L.sc.x ^ ch)
    have h0' : (0 : ℝ) ≤ (⌈L.sc.x ^ ch⌉₊ : ℕ) := Nat.cast_nonneg _
    rw [e]; unfold h0v; push_cast; linarith
  have hH : L.sc.x ^ 1300 * L.sc.x ^ cD ≤ L.etaSz / D.R.m := by
    refine le_trans ?_ hh0
    rw [← cast, ← Real.rpow_add hxpos]
    exact Real.rpow_le_rpow_of_exponent_le hxone (by exact_mod_cast hch)
  have hth : L.sc.x ^ szTh L ≤ L.sc.x := by
    have : szTh L ≤ 1 := by unfold szTh; rw [hε]; linarith
    simpa using Real.rpow_le_rpow_of_exponent_le hxone this
  obtain ⟨a1, a2, a3, a5, a6, a7, -, a9, -⟩ := nodeGap_poly hxb hY
    (Nat.cast_nonneg D.R.n) (Nat.cast_nonneg D.R.f) hm1 (Nat.cast_nonneg D.R.k) (Nat.cast_nonneg D.R.r)
    (Nat.cast_nonneg D.R.t) (Nat.cast_nonneg (D.R.N D.R.m))
    (by positivity : (0 : ℝ) ≤ (D.R.r : ℝ) + D.R.m * D.R.t) (by linarith : 0 ≤ L.sc.L) hS0
    (hnf.trans hf') hf' hm hk' hr' ht' hN' (hMN.trans hN') hL hS hth hth hH
  refine ⟨?_, a2, a3, a5, a6, a7, a9⟩
  have hb : 0 < L.sc.b := by unfold Scale.b; positivity
  refine le_trans (le_of_eq ?_) a1
  unfold szlStar
  rw [div_div_eq_mul_div]
  field_simp

end GlobalTheory.EX
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitChoiceSizeNodesStatement
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.explicitChoice_sizeNodes : SzRow (fun _ _ L => SizeNodes L) := by
  first | exact @GlobalTheory.EX.szRow_sizeNodes | exact GlobalTheory.EX.szRow_sizeNodes | (intros; apply GlobalTheory.EX.szRow_sizeNodes <;> assumption)
end
end
