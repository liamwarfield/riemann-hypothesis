module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousAtOfSqBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeThirdProperty
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicLawOfBlockDet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColSqOfKerBasic

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentLocalizationDichotomy
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentLocalizationDichotomy
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.CompDich

theorem one_sub_mem_compI {S : Type} [CommRing S] {P : Ideal S} (hP : P.IsPrime) {e : S}
    (he : IsIdempotentElem e) (heP : e ∉ P) : 1 - e ∈ compI P := by
  refine Ideal.subset_span ⟨he.one_sub, ?_⟩
  have h0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  have h1 : e * (1 - e) ∈ P := by rw [h0]; exact P.zero_mem
  exact (hP.mem_or_mem h1).resolve_left heP

theorem dich_comp : ∀ {S : Type} [CommRing S] (ϖ : S) (P : Ideal S), P.IsPrime →
    (Val ϖ → Dich (Ideal.Quotient.mk (compI P) ϖ)) ∧
    (ϖ ∈ nonZeroDivisors S → Ideal.Quotient.mk (compI P) ϖ ∈ nonZeroDivisors (S ⧸ compI P)) := by
  intro S _ ϖ P hP
  refine ⟨fun hV => ?_, fun hϖ => ?_⟩
  · rintro f g ⟨N, hN⟩
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective g
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 hN
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have h1 : ϖ ^ N - (a * f + b * g) ∈ compI P := by
      rw [← Ideal.Quotient.eq]
      simpa only [map_add (f := _), map_mul, map_pow] using hab.symm
    obtain ⟨e, he, heP, hez⟩ := (GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff P hP _).1 h1
    have hc := one_sub_mem_compI hP he heP
    have hee : e * e = e := he
    have hff : Ideal.Quotient.mk (compI P) (e * f + (1 - e)) = Ideal.Quotient.mk (compI P) f := by
      rw [Ideal.Quotient.eq]
      have h2 : e * f + (1 - e) - f = (1 - f) * (1 - e) := by ring
      rw [h2]
      exact Ideal.mul_mem_left _ _ hc
    have hmem : ϖ ^ N ∈ Ideal.span {e * f + (1 - e), g} := by
      refine Ideal.mem_span_pair.2 ⟨a * e + (1 - e) * ϖ ^ N, b * e, ?_⟩
      linear_combination (a * f - a - ϖ ^ N * f + ϖ ^ N) * hee - hez
    obtain ⟨e1, he1, h2, h3⟩ := hV (e * f + (1 - e)) g ⟨N, hmem⟩
    rw [Ideal.mem_span_singleton] at h2 h3
    by_cases h : e1 ∈ P
    · right
      have h0 : Ideal.Quotient.mk (compI P) e1 = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨he1, h⟩)
      obtain ⟨c, hc'⟩ := h3
      refine ⟨Ideal.Quotient.mk (compI P) c, ?_⟩
      rw [← hff, ← map_mul, ← hc', map_mul, map_sub, h0, map_one, sub_zero, one_mul]
    · left
      have h0 : Ideal.Quotient.mk (compI P) (1 - e1) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (one_sub_mem_compI hP he1 h)
      have h1' : Ideal.Quotient.mk (compI P) e1 = 1 := by
        rw [map_sub, map_one] at h0
        exact (sub_eq_zero.1 h0).symm
      obtain ⟨c, hc'⟩ := h2
      refine ⟨Ideal.Quotient.mk (compI P) c, ?_⟩
      rw [← hff, ← map_mul, ← hc', map_mul, h1', one_mul]
  · refine mem_nonZeroDivisors_iff_right.2 fun x hx => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 : x * ϖ ∈ compI P := Ideal.Quotient.eq_zero_iff_mem.1 (by rwa [map_mul])
    obtain ⟨e, he, heP, hez⟩ := (GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff P hP _).1 h1
    have h2 : e * x = 0 :=
      (mul_right_mem_nonZeroDivisors_eq_zero_iff hϖ).1 (by rw [mul_assoc]; exact hez)
    exact Ideal.Quotient.eq_zero_iff_mem.2 ((GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff P hP x).2 ⟨e, he, heP, h2⟩)

end GlobalTheory.CompanionTheory.CompDich
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentLocalizationDichotomyStatement
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_localization_dichotomy : ∀ {S : Type} [CommRing S] (ϖ : S) (P : Ideal S), P.IsPrime → (Val ϖ → Dich (Ideal.Quotient.mk (compI P) ϖ)) ∧ (ϖ ∈ nonZeroDivisors S → Ideal.Quotient.mk (compI P) ϖ ∈ nonZeroDivisors (S ⧸ compI P)) := by
  first | exact @GlobalTheory.CompanionTheory.CompDich.dich_comp | exact GlobalTheory.CompanionTheory.CompDich.dich_comp | (intros; apply GlobalTheory.CompanionTheory.CompDich.dich_comp <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DichotomyOfComparableModSquare
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DivisibilityChainPowerFactorization
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.NormalForm

theorem normal_form_of_dichotomy :
    ∀ {S : Type} [CommRing S] (ϖ : S), (∀ f : S, ϖ ∣ f ∨ f ∣ ϖ) →
      ∀ (f : S) (M : ℕ), ϖ ^ M ∣ f ∨ ∃ (j : ℕ) (f' : S), f = ϖ ^ j * f' ∧ f' ∣ ϖ := by
  intro S _ ϖ hd f M
  induction M generalizing f with
  | zero => exact Or.inl (by simp)
  | succ M ih =>
    rcases hd f with ⟨g, rfl⟩ | hf
    · rcases ih g with hg | ⟨j, f', hg, hf'⟩
      · left
        rw [pow_succ']
        exact mul_dvd_mul_left ϖ hg
      · right
        refine ⟨j + 1, f', ?_, hf'⟩
        rw [hg, pow_succ', mul_assoc]
    · exact Or.inr ⟨0, f, by simp, hf⟩

end GlobalTheory.CompanionTheory.NormalForm
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DichotomyOfComparableModSquare
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.DichMod

variable {S : Type} [CommRing S]

theorem isUnit_one_sub_mul {ϖ : S} (hJ : ϖ ∈ (⊥ : Ideal S).jacobson) (w : S) :
    IsUnit (1 - w * ϖ) := by
  have h := Ideal.mem_jacobson_bot.mp hJ (-w)
  have e : ϖ * -w + 1 = 1 - w * ϖ := by ring
  rwa [e] at h

theorem dvd_or_dvd {ϖ : S} (hJ : ϖ ∈ (⊥ : Ideal S).jacobson)
    (hc : ∀ f g : S, f ∈ Ideal.span {g, ϖ ^ 2} ∨ g ∈ Ideal.span {f, ϖ ^ 2}) (f : S) :
    ϖ ∣ f ∨ f ∣ ϖ := by
  rcases hc f ϖ with h | h
  · left
    obtain ⟨c, d, e⟩ := Ideal.mem_span_pair.mp h
    exact ⟨c + d * ϖ, by rw [← e]; ring⟩
  · right
    obtain ⟨c, w, e⟩ := Ideal.mem_span_pair.mp h
    have hu := isUnit_one_sub_mul hJ w
    have key : (1 - w * ϖ) * ϖ = c * f := by
      have : c * f = ϖ - w * ϖ ^ 2 := by linear_combination e
      rw [this]; ring
    exact hu.dvd_mul_left.mp (key ▸ dvd_mul_left f c)

theorem comparable {ϖ : S}
    (hc : ∀ f g : S, f ∈ Ideal.span {g, ϖ ^ 2} ∨ g ∈ Ideal.span {f, ϖ ^ 2}) {f g : S}
    (hf : f ∣ ϖ) (hg : g ∣ ϖ) : g ∣ f ∨ f ∣ g := by
  rcases hc f g with h | h
  · left
    obtain ⟨c, d, e⟩ := Ideal.mem_span_pair.mp h
    rw [← e]
    exact dvd_add (dvd_mul_left g c) ((hg.trans (dvd_pow_self ϖ two_ne_zero)).mul_left d)
  · right
    obtain ⟨c, d, e⟩ := Ideal.mem_span_pair.mp h
    rw [← e]
    exact dvd_add (dvd_mul_left f c) ((hf.trans (dvd_pow_self ϖ two_ne_zero)).mul_left d)

theorem dvd_of_high {ϖ : S} (hJ : ϖ ∈ (⊥ : Ideal S).jacobson) {f g a b : S} {N : ℕ}
    (e : a * f + b * g = ϖ ^ N) (h : ϖ ^ (N + 1) ∣ f) : g ∣ f := by
  obtain ⟨t, ht⟩ := h
  have hu := isUnit_one_sub_mul hJ (a * t)
  have key : (1 - a * t * ϖ) * ϖ ^ N = b * g := by
    have : b * g = ϖ ^ N - a * f := by linear_combination e
    rw [this, ht]; ring
  have hg : g ∣ ϖ ^ N := hu.dvd_mul_left.mp (key ▸ dvd_mul_left g b)
  exact hg.trans ⟨ϖ * t, by rw [ht]; ring⟩

theorem dvd_of_lt {ϖ f g f' g' : S} {i j : ℕ} (hf : f = ϖ ^ i * f') (hg : g = ϖ ^ j * g')
    (hf' : f' ∣ ϖ) (hij : i < j) : f ∣ g := by
  have h1 : f ∣ ϖ ^ (i + 1) := by
    rw [hf, pow_succ]
    exact mul_dvd_mul_left _ hf'
  have h2 : ϖ ^ (i + 1) ∣ g := by
    rw [hg]
    exact (pow_dvd_pow ϖ hij).mul_right g'
  exact h1.trans h2

theorem dich_of_mod : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson →
    (∀ f g : S, f ∈ Ideal.span {g, ϖ ^ 2} ∨ g ∈ Ideal.span {f, ϖ ^ 2}) → Dich ϖ := by
  intro S _ ϖ hJ hc f g hN
  obtain ⟨N, hN⟩ := hN
  obtain ⟨a, b, e⟩ := Ideal.mem_span_pair.mp hN
  have hd := dvd_or_dvd hJ hc
  rcases GlobalTheory.CompanionTheory.NormalForm.normal_form_of_dichotomy ϖ hd f (N + 1) with hf | ⟨i, f', hf, hf'⟩
  · exact Or.inl (dvd_of_high hJ e hf)
  rcases GlobalTheory.CompanionTheory.NormalForm.normal_form_of_dichotomy ϖ hd g (N + 1) with hg | ⟨j, g', hg, hg'⟩
  · exact Or.inr (dvd_of_high hJ (by rw [add_comm]; exact e) hg)
  rcases lt_trichotomy i j with hij | hij | hij
  · exact Or.inr (dvd_of_lt hf hg hf' hij)
  · subst hij
    rw [hf, hg]
    rcases comparable hc hf' hg' with h | h
    · exact Or.inl (mul_dvd_mul_left _ h)
    · exact Or.inr (mul_dvd_mul_left _ h)
  · exact Or.inl (dvd_of_lt hg hf hg' hij)

end GlobalTheory.CompanionTheory.DichMod
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DichotomyOfComparableModSquareStatement
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dichotomy_of_comparable_mod_square : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson → (∀ f g : S, f ∈ Ideal.span {g, ϖ ^ 2} ∨ g ∈ Ideal.span {f, ϖ ^ 2}) → Dich ϖ := by
  first | exact @GlobalTheory.CompanionTheory.DichMod.dich_of_mod | exact GlobalTheory.CompanionTheory.DichMod.dich_of_mod | (intros; apply GlobalTheory.CompanionTheory.DichMod.dich_of_mod <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionOverIdempotentProperties
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionOverIdempotentProperties
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.SecRules

theorem secOn_zero {S : Type} [CommRing S] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)) :
    SecOn f 0 := by
  haveI : Subsingleton (Localization.Away (0 : S)) :=
    IsLocalization.subsingleton (M := Submonoid.powers (0 : S)) (Submonoid.mem_powers 0)
  haveI : IsEmpty (Spec (CommRingCat.of (Localization.Away (0 : S)))) :=
    inferInstanceAs (IsEmpty (PrimeSpectrum (Localization.Away (0 : S))))
  exact ⟨isInitialOfIsEmpty.to Y, isInitialOfIsEmpty.hom_ext _ _⟩

theorem secOn_mul {S : Type} [CommRing S] {Y : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of S)}
    (e e' : S) (h : SecOn f e) : SecOn f (e * e') := by
  obtain ⟨s, hs⟩ := h
  refine ⟨Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayRight
    (S := Localization.Away e) (P := Localization.Away (e * e')) e e')) ≫ s, ?_⟩
  rw [Category.assoc, hs, ← Spec.map_comp]
  congr 1
  ext a
  simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom]
  exact IsLocalization.Away.awayToAwayRight_eq e e' a

theorem section_of_secOn_one {S : Type} [CommRing S] {Y : Scheme.{0}}
    {f : Y ⟶ Spec (CommRingCat.of S)} (h : SecOn f 1) :
    ∃ s : Spec (CommRingCat.of S) ⟶ Y, s ≫ f = 𝟙 _ := by
  obtain ⟨s, hs⟩ := h
  let eqv := IsLocalization.atUnit S (Localization.Away (1 : S)) 1 isUnit_one
  refine ⟨Spec.map (CommRingCat.ofHom (eqv.symm : Localization.Away (1 : S) →+* S)) ≫ s, ?_⟩
  rw [Category.assoc, hs, ← Spec.map_comp]
  have hid : CommRingCat.ofHom (Algebra.algebraMap S (Localization.Away (1 : S))) ≫
      CommRingCat.ofHom (eqv.symm : Localization.Away (1 : S) →+* S) = 𝟙 _ := by
    ext a
    simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom, CommRingCat.id_apply]
    exact eqv.symm.commutes a
  rw [hid, Spec.map_id]

theorem main : ∀ {S : Type} [CommRing S] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)),
    SecOn f 0 ∧ (∀ e e' : S, SecOn f e → SecOn f (e * e')) ∧
      (SecOn f 1 → ∃ s : Spec (CommRingCat.of S) ⟶ Y, s ≫ f = 𝟙 _) := by
  intro S _ Y f
  exact ⟨secOn_zero Y f, fun e e' h => secOn_mul e e' h, section_of_secOn_one⟩

end GlobalTheory.CompanionTheory.SecRules
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionOverIdempotentPropertiesStatement
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_over_idempotent_properties : ∀ {S : Type} [CommRing S] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)), SecOn f 0 ∧ (∀ e e' : S, SecOn f e → SecOn f (e * e')) ∧ (SecOn f 1 → ∃ s : Spec (CommRingCat.of S) ⟶ Y, s ≫ f = 𝟙 _) := by
  first | exact @GlobalTheory.CompanionTheory.SecRules.main | exact GlobalTheory.CompanionTheory.SecRules.main | (intros; apply GlobalTheory.CompanionTheory.SecRules.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationPowerIff
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationPowerIff
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.PowComp

theorem smodEq_span_iff {S : Type} [CommRing S] (a x y : S) (n : ℕ) :
    x ≡ y [SMOD ((Ideal.span {a}) ^ n • ⊤ : Submodule S S)] ↔ a ^ n ∣ x - y := by
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem val_pow_iff {S : Type} [CommRing S] (ϖ : S) (k : ℕ) (hk : k ≠ 0) : Val (ϖ ^ k) ↔ Val ϖ := by
  have hiff : ∀ f g : S, (∃ N, (ϖ ^ k) ^ N ∈ Ideal.span {f, g}) ↔ (∃ N, ϖ ^ N ∈ Ideal.span {f, g}) := by
    intro f g
    constructor
    · rintro ⟨N, hN⟩
      exact ⟨k * N, by rwa [pow_mul]⟩
    · rintro ⟨N, hN⟩
      refine ⟨N, ?_⟩
      rw [← pow_mul]
      have hle : N ≤ k * N := Nat.le_mul_of_pos_left N (Nat.pos_of_ne_zero hk)
      rw [← Nat.add_sub_cancel' hle, pow_add]
      exact Ideal.mul_mem_right _ _ hN
  unfold Val
  constructor
  · intro h f g hfg
    exact h f g ((hiff f g).mpr hfg)
  · intro h f g hfg
    exact h f g ((hiff f g).mp hfg)

theorem isAdicComplete_of_pow {S : Type} [CommRing S] (ϖ : S) (k : ℕ) (hk : k ≠ 0)
    (h : IsAdicComplete (Ideal.span {ϖ ^ k}) S) : IsAdicComplete (Ideal.span {ϖ}) S := by
  have hH : IsHausdorff (Ideal.span {ϖ ^ k}) S := h.toIsHausdorff
  have hP : IsPrecomplete (Ideal.span {ϖ ^ k}) S := h.toIsPrecomplete
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  have H1 : IsHausdorff (Ideal.span {ϖ}) S := by
    refine ⟨fun x hx => hH.haus' x (fun n => ?_)⟩
    have := hx (k * n)
    rw [smodEq_span_iff] at this ⊢
    rwa [← pow_mul]
  have H2 : IsPrecomplete (Ideal.span {ϖ}) S := by
    refine ⟨fun f hf => ?_⟩
    obtain ⟨L, hL⟩ := hP.prec' (fun n => f (k * n)) (fun {m n} hmn => by
      have := hf (Nat.mul_le_mul_left k hmn)
      rw [smodEq_span_iff] at this ⊢
      rwa [← pow_mul])
    refine ⟨L, fun n => ?_⟩
    have h1 := hf (Nat.le_mul_of_pos_left n hkpos)
    have h2 := hL n
    rw [smodEq_span_iff] at h1 h2 ⊢
    rw [← pow_mul] at h2
    have h3 : ϖ ^ n ∣ f (k * n) - L := (pow_dvd_pow ϖ (Nat.le_mul_of_pos_left n hkpos)).trans h2
    have := dvd_add h1 h3
    rwa [sub_add_sub_cancel] at this
  exact { toIsHausdorff := H1, toIsPrecomplete := H2 }

theorem val_pow : ∀ {S : Type} [CommRing S] (ϖ : S) (k : ℕ), k ≠ 0 →
    (Val (ϖ ^ k) ↔ Val ϖ) ∧ (IsAdicComplete (Ideal.span {ϖ ^ k}) S → IsAdicComplete (Ideal.span {ϖ}) S) := by
  intro S _ ϖ k hk
  exact ⟨val_pow_iff ϖ k hk, isAdicComplete_of_pow ϖ k hk⟩

end GlobalTheory.CompanionTheory.PowComp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationPowerIffStatement
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_power_iff : ∀ {S : Type} [CommRing S] (ϖ : S) (k : ℕ), k ≠ 0 → (Val (ϖ ^ k) ↔ Val ϖ) ∧ (IsAdicComplete (Ideal.span {ϖ ^ k}) S → IsAdicComplete (Ideal.span {ϖ}) S) := by
  first | exact @GlobalTheory.CompanionTheory.PowComp.val_pow | exact GlobalTheory.CompanionTheory.PowComp.val_pow | (intros; apply GlobalTheory.CompanionTheory.PowComp.val_pow <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsolutelyIntegrallyClosedOfNewton
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsolutelyIntegrallyClosedOfNewton
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.AicLimit

theorem mem_pow_smul_top_iff {S : Type} [CommRing S] (t y : S) (n : ℕ) :
    y ∈ ((Ideal.span {t}) ^ n • ⊤ : Submodule S S) ↔ t ^ n ∣ y := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem step_at {S : Type} [CommRing S] {ϖ : S} (hS : Step ϖ) (P : Polynomial S) (hP : P.Monic)
    (hd : 0 < P.natDegree) (n : ℕ) (x : S) (hx : ϖ ^ n ∣ P.eval x) :
    ∃ z, ϖ ^ (n + 1) ∣ P.eval (x + z) ∧ ϖ ^ n ∣ z ^ P.natDegree := by
  have hnt : Nontrivial S := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [Subsingleton.elim P 0, Polynomial.natDegree_zero] at hd
    exact lt_irrefl 0 hd
  have hq : (Polynomial.X + Polynomial.C x).natDegree = 1 := Polynomial.natDegree_X_add_C x
  have hQm : (P.comp (Polynomial.X + Polynomial.C x)).Monic :=
    hP.comp (Polynomial.monic_X_add_C x) (by rw [hq]; exact one_ne_zero)
  have hQd : (P.comp (Polynomial.X + Polynomial.C x)).natDegree = P.natDegree := by
    rw [Polynomial.natDegree_comp_eq_of_mul_ne_zero (by
      rw [hP.leadingCoeff, (Polynomial.monic_X_add_C x).leadingCoeff, one_pow, one_mul]
      exact one_ne_zero), hq, mul_one]
  obtain ⟨z, hz1, hz2⟩ := hS (P.comp (Polynomial.X + Polynomial.C x)) n hQm (by rw [hQd]; exact hd)
    (by simpa [Polynomial.eval_comp] using hx)
  refine ⟨z, ?_, ?_⟩
  · simpa [Polynomial.eval_comp, add_comm] using hz1
  · rwa [hQd] at hz2

theorem exists_seq {S : Type} [CommRing S] {ϖ : S} (hS : Step ϖ) (P : Polynomial S) (hP : P.Monic)
    (hd : 0 < P.natDegree) :
    ∃ x : ℕ → S, (∀ n, ϖ ^ n ∣ P.eval (x n)) ∧ ∀ n, ϖ ^ n ∣ (x (n + 1) - x n) ^ P.natDegree := by
  let next : ∀ n, {x : S // ϖ ^ n ∣ P.eval x} → {x : S // ϖ ^ (n + 1) ∣ P.eval x} := fun n x =>
    ⟨x.1 + Classical.choose (step_at hS P hP hd n x.1 x.2),
      (Classical.choose_spec (step_at hS P hP hd n x.1 x.2)).1⟩
  let seq : ∀ n, {x : S // ϖ ^ n ∣ P.eval x} := fun n =>
    Nat.rec (motive := fun n => {x : S // ϖ ^ n ∣ P.eval x}) ⟨0, by simp⟩ next n
  refine ⟨fun n => (seq n).1, fun n => (seq n).2, fun n => ?_⟩
  have h := (Classical.choose_spec (step_at hS P hP hd n (seq n).1 (seq n).2)).2
  have he : (seq (n + 1)).1 - (seq n).1 = Classical.choose (step_at hS P hP hd n (seq n).1 (seq n).2) :=
    add_sub_cancel_left (seq n).1 _
  show ϖ ^ n ∣ ((seq (n + 1)).1 - (seq n).1) ^ P.natDegree
  rw [he]
  exact h

theorem aic_of_step : ∀ {S : Type} [CommRing S] (ϖ : S) [IsAdicComplete (Ideal.span {ϖ}) S],
    Step ϖ → (∀ (z : S) (m d : ℕ), 0 < d → ϖ ^ (m * d) ∣ z ^ d → ϖ ^ m ∣ z) → Aic (S := S) := by
  intro S _ ϖ _ hS hroot P hP hd0
  obtain ⟨x, hx1, hx2⟩ := exists_seq hS P hP hd0
  obtain ⟨d, hdd⟩ : ∃ d, d = P.natDegree := ⟨_, rfl⟩
  rw [← hdd] at hx2 hd0
  have hΔ : ∀ n, ϖ ^ (n / d) ∣ x (n + 1) - x n := fun n =>
    hroot _ (n / d) d hd0 ((pow_dvd_pow ϖ (Nat.div_mul_le_self n d)).trans (hx2 n))
  have hstep : ∀ k, ϖ ^ k ∣ x ((k + 1) * d) - x (k * d) := by
    intro k
    have hi : ∀ i, ϖ ^ k ∣ x (k * d + i) - x (k * d) := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        have h1 : ϖ ^ k ∣ x (k * d + i + 1) - x (k * d + i) :=
          (pow_dvd_pow ϖ ((Nat.le_div_iff_mul_le hd0).2 (Nat.le_add_right _ _))).trans (hΔ (k * d + i))
        rw [show k * d + (i + 1) = k * d + i + 1 from rfl,
          ← sub_add_sub_cancel (x (k * d + i + 1)) (x (k * d + i)) (x (k * d))]
        exact dvd_add h1 ih
    have h3 := hi d
    rwa [show k * d + d = (k + 1) * d by ring] at h3
  have hcauchy : ∀ m n, m ≤ n → ϖ ^ m ∣ x (n * d) - x (m * d) := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [← sub_add_sub_cancel (x ((n + 1) * d)) (x (n * d)) (x (m * d))]
      exact dvd_add ((pow_dvd_pow ϖ hmn).trans (hstep n)) ih
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {ϖ}) inferInstance
    (f := fun k => x (k * d)) (fun {m n} hmn => by
      rw [SModEq.sub_mem, mem_pow_smul_top_iff]
      exact dvd_sub_comm.1 (hcauchy m n hmn))
  refine ⟨L, ?_⟩
  show Polynomial.eval L P = 0
  apply IsHausdorff.haus (I := Ideal.span {ϖ}) inferInstance
  intro k
  rw [SModEq.sub_mem, sub_zero, mem_pow_smul_top_iff]
  have h1 : ϖ ^ k ∣ x (k * d) - L := by
    have h0 := hL k
    rw [SModEq.sub_mem, mem_pow_smul_top_iff] at h0
    exact h0
  have h2 : ϖ ^ k ∣ P.eval (x (k * d)) :=
    (pow_dvd_pow ϖ (Nat.le_mul_of_pos_right k hd0)).trans (hx1 (k * d))
  have h4 : ϖ ^ k ∣ P.eval (x (k * d)) - P.eval L := h1.trans (Polynomial.sub_dvd_eval_sub _ _ _)
  have h5 : P.eval L = P.eval (x (k * d)) - (P.eval (x (k * d)) - P.eval L) := by ring
  rw [h5]
  exact dvd_sub h2 h4

end GlobalTheory.CompanionTheory.AicLimit
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsolutelyIntegrallyClosedOfNewtonStatement
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absolutely_integrally_closed_of_newton : ∀ {S : Type} [CommRing S] (ϖ : S) [IsAdicComplete (Ideal.span {ϖ}) S], Step ϖ → (∀ (z : S) (m d : ℕ), 0 < d → ϖ ^ (m * d) ∣ z ^ d → ϖ ^ m ∣ z) → Aic (S := S) := by
  first | exact @GlobalTheory.CompanionTheory.AicLimit.aic_of_step | exact GlobalTheory.CompanionTheory.AicLimit.aic_of_step | (intros; apply GlobalTheory.CompanionTheory.AicLimit.aic_of_step <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowerDivisibilityRootExtraction
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowerDivisibilityRootExtraction
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.ValPowDvd

theorem dvd_of_pow_mul_dvd_pow : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ nonZeroDivisors S → Val ϖ →
    ∀ (z : S) (m d : ℕ), 0 < d → ϖ ^ (m * d) ∣ z ^ d → ϖ ^ m ∣ z := by
  intro S _ ϖ hϖ hV z m d hd hdiv
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  obtain ⟨w, hw⟩ := hdiv
  obtain ⟨e, he, h1, h2⟩ := hV (ϖ ^ m) z ⟨m, Ideal.subset_span (Set.mem_insert _ _)⟩
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp h1
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h2
  have h3 : (e * ϖ ^ m) ^ (d' + 1) = (c' * z) ^ (d' + 1) := by rw [hc']
  rw [mul_pow, mul_pow, hw, he.pow_succ_eq d', ← pow_mul] at h3
  have key : (e - w * c' ^ (d' + 1)) * ϖ ^ (m * (d' + 1)) = 0 := by linear_combination h3
  have he' : e = w * c' ^ (d' + 1) :=
    sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp (pow_mem hϖ (m * (d' + 1)))).2 _ key)
  have hee : e * e = e := he.eq
  exact ⟨e * w * c' ^ d' + c, by
    linear_combination (-1 : S) * hc + (-z) * hee + (z * e) * he' + (e * w * c' ^ d') * hc' +
      (w * c' ^ d' * ϖ ^ m) * hee⟩

end GlobalTheory.CompanionTheory.ValPowDvd
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowerDivisibilityRootExtractionStatement
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.power_divisibility_root_extraction : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ nonZeroDivisors S → Val ϖ → ∀ (z : S) (m d : ℕ), 0 < d → ϖ ^ (m * d) ∣ z ^ d → ϖ ^ m ∣ z := by
  first | exact @GlobalTheory.CompanionTheory.ValPowDvd.dvd_of_pow_mul_dvd_pow | exact GlobalTheory.CompanionTheory.ValPowDvd.dvd_of_pow_mul_dvd_pow | (intros; apply GlobalTheory.CompanionTheory.ValPowDvd.dvd_of_pow_mul_dvd_pow <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerMorphismCompatible
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerMorphismCompatible
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.PdMor

theorem isDPMorphism_of_isPd : ∀ {S : Type} [CommRing S] {S' E E' : Type} [CommRing S'] [CommRing E] [CommRing E'] (π : S →+* E) (π' : S' →+* E') (I : Ideal S) (I' : Ideal S') {J : Ideal E} {J' : Ideal E'} (δ : DividedPowers J) (δ' : DividedPowers J') (F₀ : S →+* S') (F : E →+* E'), Function.Surjective π → PdI I → IsPd π I δ → IsPd π' I' δ' → (∀ x ∈ I, F₀ x ∈ I') → (∀ x, F (π x) = π' (F₀ x)) → DividedPowers.IsDPMorphism δ δ' F := by
  intro S _ S' E E' _ _ _ π π' I I' J J' δ δ' F₀ F hπ hI hP hP' hF₀ hF
  have hmem : ∀ a ∈ J, ∃ x ∈ I, π x = a := fun a ha => by
    rw [hP.1] at ha
    exact (Ideal.mem_map_iff_of_surjective π hπ).mp ha
  have hdp : ∀ (k : ℕ) (x : S), x ∈ I → ∃ y : S, (k.factorial : S) * y = x ^ k := by
    intro k x hx
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact ⟨1, by simp⟩
    · obtain ⟨y, -, hy⟩ := hI x hx k hk.ne'
      exact ⟨y, hy⟩
  refine ⟨?_, ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    obtain ⟨x, hx, rfl⟩ := hmem a ha
    rw [Ideal.mem_comap, hF, hP'.1]
    exact Ideal.mem_map_of_mem π' (hF₀ x hx)
  · intro n a ha
    obtain ⟨x, hx, rfl⟩ := hmem a ha
    obtain ⟨y, hy⟩ := hdp n x hx
    rw [hP.2 n x y hx hy, hF, hF,
      hP'.2 n (F₀ x) (F₀ y) (hF₀ x hx) (by rw [← map_pow, ← hy, map_mul, map_natCast])]

end GlobalTheory.CompanionTheory.PdMor
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerMorphismCompatibleStatement
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divided_power_morphism_compatible : ∀ {S : Type} [CommRing S] {S' E E' : Type} [CommRing S'] [CommRing E] [CommRing E'] (π : S →+* E) (π' : S' →+* E') (I : Ideal S) (I' : Ideal S') {J : Ideal E} {J' : Ideal E'} (δ : DividedPowers J) (δ' : DividedPowers J') (F₀ : S →+* S') (F : E →+* E'), Function.Surjective π → PdI I → IsPd π I δ → IsPd π' I' δ' → (∀ x ∈ I, F₀ x ∈ I') → (∀ x, F (π x) = π' (F₀ x)) → DividedPowers.IsDPMorphism δ δ' F := by
  first | exact @GlobalTheory.CompanionTheory.PdMor.isDPMorphism_of_isPd | exact GlobalTheory.CompanionTheory.PdMor.isDPMorphism_of_isPd | (intros; apply GlobalTheory.CompanionTheory.PdMor.isDPMorphism_of_isPd <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalizationPreservesClosedness
open CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.LocAic

theorem mem_of_compare {A : Type} [CommRing A] {e f : A}
    (h1 : e * (1 - f) ∈ Ideal.span {f}) (h2 : (1 - e) * f ∈ Ideal.span {1 - f}) :
    e ∈ Ideal.span {f} ∧ 1 - e ∈ Ideal.span {1 - f} := by
  constructor
  · have hsplit : e = e * (1 - f) + e * f := by ring
    rw [hsplit]
    exact Ideal.add_mem _ h1 (Ideal.mul_mem_left _ e (Ideal.mem_span_singleton_self f))
  · have hsplit : 1 - e = (1 - e) * f + (1 - e) * (1 - f) := by ring
    rw [hsplit]
    exact Ideal.add_mem _ h2 (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

theorem local_of_val {S : Type} [CommRing S] (π : S) (hV : Val π) (f : S) :
    ∃ e : S, IsIdempotentElem e ∧ e ∈ Ideal.span {f} ∧ 1 - e ∈ Ideal.span {1 - f} := by
  have hV' : ∀ f g : S, (∃ N : ℕ, π ^ N ∈ Ideal.span {f, g}) →
      ∃ e, IsIdempotentElem e ∧ e * f ∈ Ideal.span {g} ∧ (1 - e) * g ∈ Ideal.span {f} := hV
  obtain ⟨e, he, h1, h2⟩ := hV' f (1 - f) ⟨0, by
    rw [pow_zero, Ideal.mem_span_pair]
    exact ⟨1, 1, by ring⟩⟩
  refine ⟨1 - e, he.one_sub, mem_of_compare h2 ?_⟩
  rw [sub_sub_cancel]
  exact h1

theorem local_away_of_val {S : Type} [CommRing S] (π : S) (hV : Val π) (f : Localization.Away π) :
    ∃ e : Localization.Away π, IsIdempotentElem e ∧ e ∈ Ideal.span {f} ∧ 1 - e ∈ Ideal.span {1 - f} := by
  have hV' : ∀ f g : S, (∃ N : ℕ, π ^ N ∈ Ideal.span {f, g}) →
      ∃ e, IsIdempotentElem e ∧ e * f ∈ Ideal.span {g} ∧ (1 - e) * g ∈ Ideal.span {f} := hV
  obtain ⟨⟨a, s⟩, hf⟩ := IsLocalization.surj (Submonoid.powers π) f
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).1 s.2
  have hu : IsUnit (algebraMap S (Localization.Away π) (s : S)) :=
    IsLocalization.map_units (Localization.Away π) s
  have hA : algebraMap S (Localization.Away π) a = f * algebraMap S (Localization.Away π) (s : S) := hf.symm
  have hB : algebraMap S (Localization.Away π) ((s : S) - a) =
      (1 - f) * algebraMap S (Localization.Away π) (s : S) := by
    rw [map_sub, hA]
    ring
  obtain ⟨e, he, h1, h2⟩ := hV' a ((s : S) - a) ⟨n, by
    rw [hn, Ideal.mem_span_pair]
    exact ⟨1, 1, by ring⟩⟩
  have d1 : (1 - f) ∣ algebraMap S (Localization.Away π) e * f := by
    have hd := map_dvd (algebraMap S (Localization.Away π)) (Ideal.mem_span_singleton.1 h1)
    rw [hB, map_mul, hA, ← mul_assoc] at hd
    exact hu.dvd_mul_right.1 (dvd_trans (dvd_mul_right _ _) hd)
  have d2 : f ∣ (1 - algebraMap S (Localization.Away π) e) * (1 - f) := by
    have hd := map_dvd (algebraMap S (Localization.Away π)) (Ideal.mem_span_singleton.1 h2)
    rw [map_mul, hB, map_sub, map_one, hA, ← mul_assoc] at hd
    exact hu.dvd_mul_right.1 (dvd_trans (dvd_mul_right _ _) hd)
  have hē : IsIdempotentElem (algebraMap S (Localization.Away π) e) := by
    rw [IsIdempotentElem, ← map_mul, he.eq]
  refine ⟨1 - algebraMap S (Localization.Away π) e, hē.one_sub,
    mem_of_compare (Ideal.mem_span_singleton.2 d2) ?_⟩
  rw [sub_sub_cancel]
  exact Ideal.mem_span_singleton.2 d1


open Polynomial in
theorem aic_away {S : Type} [CommRing S] (π : S) (hA : Aic (S := S)) :
    Aic (S := Localization.Away π) := by
  have hA' : ∀ P : Polynomial S, P.Monic → 0 < P.natDegree → ∃ x, P.IsRoot x := hA
  unfold Aic
  intro P hP hdeg
  have hlift := IsLocalization.scaleRoots_commonDenom_mem_lifts (M := Submonoid.powers π)
    (Rₘ := Localization.Away π) P (by rw [hP.leadingCoeff]; exact ⟨1, map_one _⟩)
  obtain ⟨q, hq, hqdeg, hqm⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlift ((Polynomial.monic_scaleRoots_iff _).2 hP)
  obtain ⟨y, hy⟩ := hA' q hqm (by rw [hqdeg, Polynomial.natDegree_scaleRoots]; exact hdeg)
  have hs : IsUnit (algebraMap S (Localization.Away π)
      (IsLocalization.commonDenom (Submonoid.powers π) P.support P.coeff : S)) :=
    IsLocalization.map_units (Localization.Away π) _
  refine ⟨↑hs.unit⁻¹ * algebraMap S (Localization.Away π) y, ?_⟩
  have h1 := Polynomial.scaleRoots_eval₂_mul (p := P) (RingHom.id (Localization.Away π))
    (↑hs.unit⁻¹ * algebraMap S (Localization.Away π) y)
    (algebraMap S (Localization.Away π) (IsLocalization.commonDenom (Submonoid.powers π) P.support P.coeff : S))
  simp only [RingHom.id_apply] at h1
  rw [← mul_assoc, hs.mul_val_inv, one_mul] at h1
  have h3 : Polynomial.eval₂ (RingHom.id _) (algebraMap S (Localization.Away π) y)
      (P.scaleRoots (algebraMap S (Localization.Away π)
        (IsLocalization.commonDenom (Submonoid.powers π) P.support P.coeff : S))) = 0 := by
    rw [← hq, Polynomial.eval₂_map, RingHom.id_comp, Polynomial.eval₂_hom]
    rw [show q.eval y = 0 from hy, map_zero]
  rw [h3] at h1
  exact (hs.pow _).mul_right_eq_zero.1 h1.symm

theorem main : ∀ {S : Type} [CommRing S] (ϖ : S),
    (Val ϖ → Loc (S := S) ∧ Loc (S := Localization.Away ϖ)) ∧
      (Aic (S := S) → Aic (S := Localization.Away ϖ)) := by
  intro S _ ϖ
  refine ⟨fun hV => ⟨?_, ?_⟩, fun hA => aic_away ϖ hA⟩
  · unfold Loc
    exact fun f => local_of_val ϖ hV f
  · unfold Loc
    exact fun f => local_away_of_val ϖ hV f

end GlobalTheory.CompanionTheory.LocAic
end

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

theorem CrystallineSemistableComparison.RL.surj_pass : ∀ {S : Type} [CommRing S] {T : Type} [CommRing T] (φ : S →+* T), Function.Surjective φ → (Aic (S := S) → Aic (S := T)) ∧ (Val0 (S := S) → Val0 (S := T)) := GlobalTheory.T.surjective_preserves_closedness_comparability

theorem CrystallineSemistableComparison.RL.glue : ∀ {S : Type} [CommRing S] (Q : S → Prop), Q 0 → (∀ e e' : S, IsIdempotentElem e → IsIdempotentElem e' → Q e → Q (e * e')) → (∀ e e' : S, IsIdempotentElem e → IsIdempotentElem e' → e * e' = 0 → Q e → Q e' → Q (e + e')) → (∀ m : Ideal S, m.IsMaximal → ∃ e, IsIdempotentElem e ∧ e ∉ m ∧ Q e) → Q 1 := GlobalTheory.T.idempotent_local_induction

theorem CrystallineSemistableComparison.RL.dich_comp : ∀ {S : Type} [CommRing S] (ϖ : S) (P : Ideal S), P.IsPrime → (Val ϖ → Dich (Ideal.Quotient.mk (compI P) ϖ)) ∧ (ϖ ∈ nonZeroDivisors S → Ideal.Quotient.mk (compI P) ϖ ∈ nonZeroDivisors (S ⧸ compI P)) := GlobalTheory.T.idempotent_localization_dichotomy

theorem CrystallineSemistableComparison.RL.val_of_dich : ∀ {S : Type} [CommRing S] (ϖ : S), (∀ m : Ideal S, m.IsMaximal → Dich (Ideal.Quotient.mk (compI m) ϖ)) → Val ϖ := GlobalTheory.T.valuation_of_local_dichotomy

theorem CrystallineSemistableComparison.RL.valuation_square_of_valuation_mod : ∀ {S : Type} [CommRing S] (ϖ : S) [IsAdicComplete (Ideal.span {ϖ}) S], Val0 (S := S ⧸ Ideal.span {ϖ ^ 2}) → ∀ P : Ideal S, P.IsPrime → ∀ f g : S ⧸ compI P, f ∈ Ideal.span {g, Ideal.Quotient.mk (compI P) ϖ ^ 2} ∨ g ∈ Ideal.span {f, Ideal.Quotient.mk (compI P) ϖ ^ 2} := by
  intro S _ ϖ _ h P hP f g
  have hcomp := GlobalTheory.CompanionTheory.CompMod.mem_span_or_mem_span ϖ h P hP f g
  exact hcomp

theorem CrystallineSemistableComparison.RL.dich_of_mod : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson → (∀ f g : S, f ∈ Ideal.span {g, ϖ ^ 2} ∨ g ∈ Ideal.span {f, ϖ ^ 2}) → Dich ϖ := GlobalTheory.T.dichotomy_of_comparable_mod_square

open Polynomial in
theorem CrystallineSemistableComparison.RL.step_comp : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson → ϖ ∈ nonZeroDivisors S → Dich ϖ → Aic (S := S ⧸ Ideal.span {ϖ ^ 2}) → Step ϖ := by
  intro S _ ϖ hj hnz hD hA
  have hStep : Step ϖ := by
    intro Q n hQ hd hn
    have hRoots : Roots ϖ := GlobalTheory.T.polynomial_roots_of_closed_quotient ϖ hj hnz hD hA
    have hq0 : Q.coeff 0 = Q.eval 0 := Polynomial.coeff_zero_eq_eval_zero Q
    have hspan : ϖ ^ (n + 1) ∈ Ideal.span {Q.coeff 0, ϖ ^ (n + 1)} :=
      Ideal.subset_span (by simp)
    rcases hD (Q.coeff 0) (ϖ ^ (n + 1)) ⟨n + 1, hspan⟩ with hdiv | hdiv
    · refine ⟨0, ?_, ?_⟩
      · rw [← hq0]; exact hdiv
      · rw [zero_pow hd.ne']; exact dvd_zero _
    ·
      have hpow : ϖ ^ (n + 1) ∈ nonZeroDivisors S := pow_mem hnz _
      have hcancel : ∀ x : S, Q.coeff 0 * x = 0 → x = 0 := by
        intro x hx
        obtain ⟨e, he⟩ := hdiv
        have h0 : ϖ ^ (n + 1) * x = 0 := by
          rw [he]; linear_combination e * hx
        exact (mem_nonZeroDivisors_iff_right.mp hpow) x (by rw [mul_comm]; exact h0)
      obtain ⟨c, hc1, i0, hi1, hi2, hi3⟩ := GlobalTheory.T.newton_polygon_slope_existence ϖ hD hRoots (fun i => Q.coeff i)
        Q.natDegree (n + 1) hd hQ.coeff_natDegree hdiv
      have hs : ∀ i, ∃ t, (i = 0 → t = 1) ∧
          (i ≤ Q.natDegree → Q.coeff i * c ^ i = Q.coeff 0 * t) := by
        intro i
        rcases Nat.eq_zero_or_pos i with rfl | hi
        · exact ⟨1, fun _ => rfl, fun _ => by simp⟩
        · by_cases hid : i ≤ Q.natDegree
          · obtain ⟨t, ht⟩ := hc1 i hi hid
            exact ⟨t, fun h => by omega, fun _ => ht⟩
          · exact ⟨0, fun h => by omega, fun h => by omega⟩
      choose s hs0 hsd using hs
      have hunit : IsUnit (s i0) := by
        obtain ⟨t, ht⟩ := hi3
        have h5 : Q.coeff 0 * (s i0 * t - 1) = 0 := by
          have h6 := hsd i0 hi2
          rw [h6] at ht
          linear_combination -ht
        have h7 := hcancel _ h5
        exact IsUnit.of_mul_eq_one t (by linear_combination h7)
      let R : Polynomial S := ∑ i ∈ Finset.range (Q.natDegree + 1),
        Polynomial.C (s i) * Polynomial.X ^ i
      have hRc : ∀ j, j ≤ Q.natDegree → R.coeff j = s j := by
        intro j hj'
        simp only [R, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
        rw [Finset.sum_ite_eq]
        simp [Nat.lt_succ_of_le hj']
      have hRe : ∀ y, R.eval y = ∑ i ∈ Finset.range (Q.natDegree + 1), s i * y ^ i := by
        intro y
        simp [R, Polynomial.eval_finsetSum]
      let P : Polynomial (S ⧸ Ideal.span {ϖ ^ 2}) := R.map (Ideal.Quotient.mk _)
      have hP0 : P.coeff 0 = 1 := by
        simp only [P, Polynomial.coeff_map]
        rw [hRc 0 (Nat.zero_le _), hs0 0 rfl, map_one]
      have hPi : IsUnit (P.coeff i0) := by
        simp only [P, Polynomial.coeff_map]
        rw [hRc i0 hi2]
        exact hunit.map _
      have hroot : ∃ y', P.eval y' = 0 := by
        let T := S ⧸ Ideal.span {ϖ ^ 2}
        rcases subsingleton_or_nontrivial T with hT | hT
        · exact ⟨0, Subsingleton.elim _ _⟩
        have hAdd : ∀ a b : T, IsUnit (a + b) → IsUnit a ∨ IsUnit b :=
          GlobalTheory.CompanionTheory.NewtonStep.isUnit_or_of_add_quot ϖ hj hD
        have unitRoot : ∀ (d : ℕ) (F : Polynomial T), F.Monic → F.natDegree = d →
            ∀ k < d, IsUnit (F.coeff k) → ∃ u : Tˣ, F.eval (u : T) = 0 := by
          intro d
          induction d with
          | zero =>
            intro F hF hdeg k hk
            omega
          | succ d ih =>
            intro F hF hdeg k hk hcoeff
            obtain ⟨x, hx⟩ := hA F hF (by omega)
            by_cases hxu : IsUnit x
            · obtain ⟨u, rfl⟩ := hxu
              exact ⟨u, hx⟩
            let G := F /ₘ (X - C x)
            have hfactor : (X - C x) * G = F := mul_divByMonic_eq_iff_isRoot.mpr hx
            have hG : G.Monic := (monic_X_sub_C x).of_mul_monic_left (hfactor.symm ▸ hF)
            have hGdeg : G.natDegree = d := by
              have h := (monic_X_sub_C x).natDegree_mul hG
              rw [hfactor, hdeg, natDegree_X_sub_C] at h
              omega
            cases k with
            | zero =>
              rw [← hfactor, sub_mul, coeff_sub, coeff_X_mul_zero, coeff_C_mul, zero_sub] at hcoeff
              have hprod : IsUnit (x * G.coeff 0) := by simpa only [neg_neg] using hcoeff.neg
              exact (hxu (isUnit_of_mul_isUnit_left hprod)).elim
            | succ k =>
              rw [← hfactor, coeff_X_sub_C_mul, sub_eq_add_neg] at hcoeff
              rcases hAdd _ _ hcoeff with hGu | hneg
              · obtain ⟨u, hu⟩ := ih G hG hGdeg k (by omega) hGu
                exact ⟨u, by rw [← hfactor, eval_mul, hu, mul_zero]⟩
              · have hprod : IsUnit (x * G.coeff (k + 1)) := by
                  simpa only [neg_neg] using hneg.neg
                exact (hxu (isUnit_of_mul_isUnit_left hprod)).elim
        have htd : P.natTrailingDegree = 0 :=
          Nat.le_zero.mp (natTrailingDegree_le_of_ne_zero (by rw [hP0]; exact one_ne_zero))
        have hmon : P.reverse.Monic := by
          rw [Monic, reverse_leadingCoeff, trailingCoeff, htd, hP0]
        have hdeg : P.reverse.natDegree = P.natDegree := by
          rw [reverse_natDegree, htd, Nat.sub_zero]
        have hle : i0 ≤ P.natDegree := le_natDegree_of_ne_zero hPi.ne_zero
        have hcoeff : P.reverse.coeff (P.natDegree - i0) = P.coeff i0 := by
          rw [coeff_reverse, revAt_le (Nat.sub_le _ _)]
          congr 1
          omega
        obtain ⟨u, hu⟩ := unitRoot P.natDegree P.reverse hmon hdeg (P.natDegree - i0)
          (by omega) (hcoeff.symm ▸ hPi)
        refine ⟨↑(u⁻¹), ?_⟩
        let : Invertible ((u⁻¹ : Tˣ) : T) := (u⁻¹).invertible
        have hre := eval₂_reverse_mul_pow (RingHom.id T) ((u⁻¹ : Tˣ) : T) P
        have hinv : ⅟((u⁻¹ : Tˣ) : T) = (u : T) := by simp
        rw [hinv, eval₂_id, eval₂_id, hu, zero_mul] at hre
        exact hre.symm
      obtain ⟨y', hy'⟩ := hroot
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y'
      have hRy : ϖ ^ 2 ∣ R.eval y := by
        rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
        simp only [P, Polynomial.eval_map] at hy'
        rwa [Polynomial.eval₂_at_apply] at hy'
      have hQz : Q.eval (c * y) = Q.coeff 0 * R.eval y := by
        rw [Polynomial.eval_eq_sum_range, hRe, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        have h8 := hsd i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
        rw [mul_pow]
        linear_combination (y ^ i) * h8
      have hn0 : ϖ ^ n ∣ Q.coeff 0 := by rw [hq0]; exact hn
      refine ⟨c * y, ?_, ?_⟩
      · rw [hQz]
        have h9 : ϖ ^ n * ϖ ^ 2 ∣ Q.coeff 0 * R.eval y := mul_dvd_mul hn0 hRy
        refine dvd_trans ?_ h9
        rw [← pow_add]
        exact pow_dvd_pow _ (by omega)
      · have h10 : Q.coeff 0 ∣ c ^ Q.natDegree := by
          have h11 := hc1 Q.natDegree hd le_rfl
          simpa [hQ.coeff_natDegree] using h11
        rw [mul_pow]
        exact dvd_mul_of_dvd_left (dvd_trans hn0 h10) _
  exact hStep

theorem CrystallineSemistableComparison.RL.step_glob : ∀ {S : Type} [CommRing S] (ϖ : S), (∀ m : Ideal S, m.IsMaximal → Step (Ideal.Quotient.mk (compI m) ϖ)) → Step ϖ := GlobalTheory.T.newton_approximation_local_to_global

theorem CrystallineSemistableComparison.RL.pow_dvd : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ nonZeroDivisors S → Val ϖ → ∀ (z : S) (m d : ℕ), 0 < d → ϖ ^ (m * d) ∣ z ^ d → ϖ ^ m ∣ z := GlobalTheory.T.power_divisibility_root_extraction

theorem CrystallineSemistableComparison.RL.aic_limit : ∀ {S : Type} [CommRing S] (ϖ : S) [IsAdicComplete (Ideal.span {ϖ}) S], Step ϖ → (∀ (z : S) (m d : ℕ), 0 < d → ϖ ^ (m * d) ∣ z ^ d → ϖ ^ m ∣ z) → Aic (S := S) := GlobalTheory.T.absolutely_integrally_closed_of_newton

theorem CrystallineSemistableComparison.RL.int_closed : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ nonZeroDivisors S → Val ϖ → ∀ x : Localization.Away ϖ, IsIntegral S x → ∃ y : S, algebraMap S (Localization.Away ϖ) y = x := GlobalTheory.T.integral_localization_away_in_ring

theorem CrystallineSemistableComparison.RL.loc_aic : ∀ {S : Type} [CommRing S] (ϖ : S), (Val ϖ → Loc (S := S) ∧ Loc (S := Localization.Away ϖ)) ∧ (Aic (S := S) → Aic (S := Localization.Away ϖ)) := by
  intro S _ ϖ
  have hloc := GlobalTheory.CompanionTheory.LocAic.main ϖ
  exact hloc

theorem CrystallineSemistableComparison.RL.val_pow : ∀ {S : Type} [CommRing S] (ϖ : S) (k : ℕ), k ≠ 0 → (Val (ϖ ^ k) ↔ Val ϖ) ∧ (IsAdicComplete (Ideal.span {ϖ ^ k}) S → IsAdicComplete (Ideal.span {ϖ}) S) := GlobalTheory.T.valuation_power_iff

theorem CrystallineSemistableComparison.RL.split_pt : ∀ {S : Type} [CommRing S] , Aic (S := S) → Loc (S := S) → ∀ (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)), Etale f → Surjective f → ∀ m : Ideal S, m.IsMaximal → ∃ e : S, IsIdempotentElem e ∧ e ∉ m ∧ SecOn f e := by
  intro S _ hA hL Y f hE hS m hm
  let x : Spec (CommRingCat.of S) := ⟨m, hm.isPrime⟩
  obtain ⟨y, hy⟩ := hS.surj x
  obtain ⟨B, i, hi, z, hz⟩ := Y.exists_Spec_apply_eq y
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ f)
  have hEt : Etale (Spec.map φ) := by rw [hφ]; infer_instance
  have hφe : φ.hom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).1 hEt
  let _ : Algebra S B := φ.hom.toAlgebra
  have : Algebra.Etale S B := RingHom.etale_algebraMap.1 hφe
  let Q : Ideal B := z.asIdeal
  have hQ : Q.IsPrime := z.2
  have hQm : Q.comap (algebraMap S B) = m := by
    have hx : (Spec.map φ) z = x := by rw [hφ, Scheme.Hom.comp_apply, hz, hy]
    exact congrArg PrimeSpectrum.asIdeal hx
  obtain ⟨g, hg, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := S) Q
  let Bg := Localization.Away g
  let q := Q.map (algebraMap B Bg)
  have hdisj : Disjoint (Submonoid.powers g : Set B) (Q : Set B) := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hg (hQ.mem_of_pow_mem n hn)
  have hq : q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) Bg Q hQ hdisj
  have hcomap : q.comap (algebraMap B Bg) = Q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) Bg hQ hdisj
  have hqm : q.comap (algebraMap S Bg) = m := by
    rw [IsScalarTower.algebraMap_eq S B Bg, ← Ideal.comap_comap, hcomap, hQm]
  obtain ⟨P⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := S) (S := Bg)
  have hroot_of_mem (F : Polynomial S) (hF : F.Monic) (hmem : Polynomial.aeval P.x F ∈ q) :
      ∃ b : S, F.IsRoot b ∧ P.x - algebraMap S Bg b ∈ q := by
    have : Nontrivial S := nontrivial_of_ne 0 1 fun h =>
      hm.ne_top ((Ideal.eq_top_iff_one m).2 (h ▸ m.zero_mem))
    induction hd : F.natDegree using Nat.strong_induction_on generalizing F with
    | ind n ih =>
      by_cases hn : n = 0
      · have h1 := Polynomial.eq_one_of_monic_natDegree_zero hF (hd.trans hn)
        rw [h1, map_one] at hmem
        exact (hq.ne_top ((Ideal.eq_top_iff_one q).2 hmem)).elim
      obtain ⟨b, hb⟩ := hA F hF (by omega)
      let G := F /ₘ (Polynomial.X - Polynomial.C b)
      have hFG : (Polynomial.X - Polynomial.C b) * G = F :=
        Polynomial.mul_divByMonic_eq_iff_isRoot.2 hb
      have hG : G.Monic := (Polynomial.Monic.of_mul_monic_left (Polynomial.monic_X_sub_C b))
        (hFG.symm ▸ hF)
      have hdeg := (Polynomial.monic_X_sub_C b).natDegree_mul hG
      rw [hFG, Polynomial.natDegree_X_sub_C, hd] at hdeg
      rw [← hFG, map_mul] at hmem
      rcases hq.mem_or_mem hmem with hbq | hGq
      · exact ⟨b, hb, by simpa using hbq⟩
      · obtain ⟨c, hc, hcq⟩ := ih G.natDegree (by omega) G hG hGq rfl
        exact ⟨c, by rw [← hFG, Polynomial.IsRoot, Polynomial.eval_mul, hc, mul_zero], hcq⟩
  obtain ⟨b, hb, hbq⟩ := hroot_of_mem P.f P.monic_f (P.hasMap.1.symm ▸ q.zero_mem)
  let c : S := Polynomial.eval b P.g
  have hcm : c ∉ m := by
    rw [← hqm]
    intro hcq
    have hdvd : P.x - algebraMap S Bg b ∣ Polynomial.aeval P.x P.g - algebraMap S Bg c := by
      have h := Polynomial.sub_dvd_eval_sub P.x (algebraMap S Bg b) (P.g.map (algebraMap S Bg))
      rwa [Polynomial.eval_map_algebraMap, Polynomial.eval_map_algebraMap,
        Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval] at h
    have hgq : Polynomial.aeval P.x P.g ∈ q := by
      simpa using q.add_mem (Ideal.mem_of_dvd q hdvd hbq) (show algebraMap S Bg c ∈ q from hcq)
    exact hq.ne_top (Ideal.eq_top_of_isUnit_mem q hgq P.hasMap.2)
  obtain ⟨a, μ, hμ, haμ⟩ := hm.exists_inv hcm
  obtain ⟨e, he, hec, he1⟩ := hL (a * c)
  have h1ac : 1 - a * c = μ := by rw [← haμ]; ring
  have he1m : 1 - e ∈ m := by
    rw [h1ac] at he1
    exact (Ideal.span_singleton_le_iff_mem _).2 hμ he1
  have hem : e ∉ m := by
    intro hem
    have h1 : (1 : S) ∈ m := by simpa using m.add_mem hem he1m
    exact hm.ne_top ((Ideal.eq_top_iff_one m).2 h1)
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hec
  have heu : IsUnit (algebraMap S (Localization.Away e) e) :=
    IsLocalization.Away.algebraMap_isUnit e
  have hcu : IsUnit (algebraMap S (Localization.Away e) c) := by
    have hmul : algebraMap S (Localization.Away e) e =
        algebraMap S (Localization.Away e) (r * a) * algebraMap S (Localization.Away e) c := by
      rw [← map_mul, ← hr]; ring_nf
    rw [hmul] at heu
    exact isUnit_of_mul_isUnit_right heu
  have hmap : P.P.HasMap (algebraMap S (Localization.Away e) b) := by
    refine ⟨?_, ?_⟩
    · rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, hb.eq_zero, map_zero]
    · rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
      exact hcu
  let ψ := ((P.P.lift _ hmap).comp P.equivRing.toAlgHom).comp (IsScalarTower.toAlgHom S B Bg)
  refine ⟨e, he, hem, Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ i, ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp]
  congr 1
  ext a
  exact ψ.commutes a

theorem CrystallineSemistableComparison.RL.sec_rules : ∀ {S : Type} [CommRing S] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)), SecOn f 0 ∧ (∀ e e' : S, SecOn f e → SecOn f (e * e')) ∧ (SecOn f 1 → ∃ s : Spec (CommRingCat.of S) ⟶ Y, s ≫ f = 𝟙 _) := GlobalTheory.T.section_over_idempotent_properties

theorem CrystallineSemistableComparison.RL.sec_add : ∀ {S : Type} [CommRing S] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)) (e e' : S), IsIdempotentElem e → IsIdempotentElem e' → e * e' = 0 → SecOn f e → SecOn f e' → SecOn f (e + e') := GlobalTheory.T.section_orthogonal_idempotent_sum

theorem CrystallineSemistableComparison.RL.pd_quot : ∀ {S : Type} [CommRing S] , TF (S := S) → ∀ I J : Ideal S, PdI I → (∀ x ∈ I, x ∈ J → ∀ k : ℕ, k ≠ 0 → ∀ y : S, (k.factorial : S) * y = x ^ k → y ∈ J) → ∃ δ : DividedPowers (I.map (Ideal.Quotient.mk J)), IsPd (Ideal.Quotient.mk J) I δ := by
  intro S _ hS I J hI hJ
  have hpd := GlobalTheory.CompanionTheory.PdTF.exists_dividedPowers_map_quotient hS I J hI hJ
  exact hpd

theorem CrystallineSemistableComparison.RL.pd_mor : ∀ {S : Type} [CommRing S] {S' E E' : Type} [CommRing S'] [CommRing E] [CommRing E'] (π : S →+* E) (π' : S' →+* E') (I : Ideal S) (I' : Ideal S') {J : Ideal E} {J' : Ideal E'} (δ : DividedPowers J) (δ' : DividedPowers J') (F₀ : S →+* S') (F : E →+* E'), Function.Surjective π → PdI I → IsPd π I δ → IsPd π' I' δ' → (∀ x ∈ I, F₀ x ∈ I') → (∀ x, F (π x) = π' (F₀ x)) → DividedPowers.IsDPMorphism δ δ' F := GlobalTheory.T.divided_power_morphism_compatible
