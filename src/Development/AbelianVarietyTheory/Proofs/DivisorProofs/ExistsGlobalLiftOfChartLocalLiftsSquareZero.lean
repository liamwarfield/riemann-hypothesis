module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowCocycle

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecHomExtOfLocalizationAwaySpanEqTop
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecHomExtOfLocalizationAwaySpanEqTop
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecGlue

theorem hom_ext_of_span_eq_top (S : Type) [CommRing S] (ι : Type) (s : ι → S)
    (hs : Ideal.span (Set.range s) = ⊤) (Y : Scheme.{0}) (a b : Sp S ⟶ Y)
    (h : ∀ i, spMap (algebraMap S (Localization.Away (s i))) ≫ a =
      spMap (algebraMap S (Localization.Away (s i))) ≫ b) :
    a = b :=
  Scheme.Cover.hom_ext (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of S) s hs).openCover
    a b h

end GlobalTheory.SecGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecHomExtOfLocalizationAwaySpanEqTopStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specHom_ext_of_localizationAway_span_eq_top : ∀ (S : Type) [CommRing S] (ι : Type) (s : ι → S), Ideal.span (Set.range s) = ⊤ →
    ∀ (Y : Scheme.{0}) (a b : Sp S ⟶ Y),
    (∀ i, spMap (algebraMap S (Localization.Away (s i))) ≫ a = spMap (algebraMap S (Localization.Away (s i))) ≫ b) →
    a = b := by
  first | exact @GlobalTheory.SecGlue.hom_ext_of_span_eq_top | exact GlobalTheory.SecGlue.hom_ext_of_span_eq_top | (intros; apply GlobalTheory.SecGlue.hom_ext_of_span_eq_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroLocalLiftsCorrectedAgreeOnOverlaps
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftsAgreeOfCocycle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftsAgreeOfCocycle
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SecGlue.Cocycle

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (a : A →+* B) (b : B →+* C) : spMap b ≫ spMap a = spMap (b.comp a) := by
  rw [← Spec.map_comp]; rfl

theorem awayMap_surjective {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) (r : R) : Function.Surjective (Localization.awayMap π r) := by
  intro y
  obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (π r)) y
  obtain ⟨b, rfl⟩ := hπ a
  refine ⟨IsLocalization.mk' _ b (⟨r ^ m, m, rfl⟩ : Submonoid.powers r), ?_⟩
  simp only [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_mk']
  congr 1
  ext
  simp

theorem ker_awayMap_le {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) (r : R) :
    RingHom.ker (Localization.awayMap π r) ≤
      (RingHom.ker π).map (algebraMap R (Localization.Away r)) := by
  intro x hx
  obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers r) x
  rw [RingHom.mem_ker] at hx
  simp only [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_mk'] at hx
  rw [IsLocalization.mk'_eq_zero_iff] at hx
  obtain ⟨⟨_, p, rfl⟩, hp⟩ := hx
  rw [IsLocalization.mk'_mem_map_algebraMap_iff]
  refine ⟨r ^ p, ⟨p, rfl⟩, ?_⟩
  rw [RingHom.mem_ker, map_mul, map_pow]
  exact hp

theorem ker_awayMap_sq {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (h2 : RingHom.ker π ^ 2 = ⊥) (r : R) :
    RingHom.ker (Localization.awayMap π r) ^ 2 = ⊥ := by
  refine le_bot_iff.1 ((Ideal.pow_right_mono (ker_awayMap_le π r) 2).trans ?_)
  rw [← Ideal.map_pow, h2, Ideal.map_bot]

theorem isCombIn_restrict_chart {Y : Scheme.{0}} {V V' : Y.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen V') {S T S' : Type} [CommRing S] [CommRing T] [CommRing S']
    (q : S →+* T) (hq : Function.Surjective q) (h2 : RingHom.ker q ^ 2 = ⊥) (g : S →+* S')
    {ι : Type} [Fintype ι] (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S)
    (hw : ∀ i, spMap q ≫ w i = spMap q ≫ u) (hC : IsCombIn V u c w a)
    (hu : (spMap g ≫ u) ⁻¹ᵁ V' = ⊤) :
    IsCombIn V' (spMap g ≫ u) (spMap g ≫ c) (fun i => spMap g ≫ w i) (fun i => g (a i)) := by
  let J : Ideal S' := (RingHom.ker q).map g
  have hle : RingHom.ker q ≤ RingHom.ker ((Ideal.Quotient.mk J).comp g) := by
    intro x hx
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem g hx
  let g' : T →+* S' ⧸ J := RingHom.liftOfSurjective q hq ⟨(Ideal.Quotient.mk J).comp g, hle⟩
  have hg' : g'.comp q = (Ideal.Quotient.mk J).comp g := RingHom.liftOfSurjective_comp q hq _
  refine GlobalTheory.T.isAffineCombination_independent_of_chart Y V V' hV hV' S' (S' ⧸ J) (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    ?_ ι _ _ _ _ (fun i => ?_) (isCombIn_spMap_comp Y V S S' g ι u c w a hC) hu
  · rw [Ideal.mk_ker, ← Ideal.map_pow, h2, Ideal.map_bot]
  · rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, ← hg', ← spMap_comp_spMap,
      Category.assoc, Category.assoc, hw i]

theorem eq_of_cocycle {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W) {S : Type} [CommRing S]
    {κ : Type} [Fintype κ] (u u' c c' : Sp S ⟶ Y) (w w' : κ → (Sp S ⟶ Y)) (a b : κ → S)
    (hab : ∑ k, a k * b k = 1) (h : IsCombIn W u c w a) (h' : IsCombIn W u' c' w' a)
    (hco : ∀ k, IsCombIn W u' (w k) ![w' k, u] ![1, 1 - b k]) : c = c' := by
  obtain ⟨hu, hc, hw, e⟩ := h
  obtain ⟨hu', hc', hw', e'⟩ := h'
  refine eq_of_chartHom_eq hW c c' hc hc' fun x => ?_
  have key : ∀ k, chartHom W (w k) (hw k) x - chartHom W u hu x =
      (chartHom W (w' k) (hw' k) x - chartHom W u' hu' x) -
        b k * (chartHom W u hu x - chartHom W u' hu' x) := by
    intro k
    obtain ⟨_, _, _, e''⟩ := hco k
    have := e'' x
    rw [Fin.sum_univ_two] at this
    have this' : chartHom W (w k) (hw k) x = chartHom W u' hu' x +
        (1 * (chartHom W (w' k) (hw' k) x - chartHom W u' hu' x) +
          (1 - b k) * (chartHom W u hu x - chartHom W u' hu' x)) := this
    rw [this']; ring
  rw [e x, e' x]
  simp only [key, mul_sub (a _) (_ - _), Finset.sum_sub_distrib, ← mul_assoc, ← Finset.sum_mul, hab]
  ring

theorem exists_lifts_agree_of_cocycle : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (κ : Type) [Fintype κ] (f : κ → R), Ideal.span (Set.range f) = ⊤ → ∀ (V : κ → X.left.Opens), (∀ k, IsAffineOpen (V k)) →
    ∀ (e : ∀ k, Sp (Localization.Away (f k)) ⟶ X.left),
    (∀ k, e k ≫ X.hom = spMap (algebraMap R (Localization.Away (f k)))) →
    (∀ k, spMap (Localization.awayMap π (f k)) ≫ e k = spMap (algebraMap R₀ (Localization.Away (π (f k)))) ≫ g₀) →
    (∀ k, e k ⁻¹ᵁ V k = ⊤) →
    ∀ (N : ℕ) (t : κ → ∀ j, Sp (Localization.Away (f j)) ⟶ X.left),
    (∀ k j, t k j ≫ X.hom = spMap (algebraMap R (Localization.Away (f j)))) →
    (∀ k j, spMap (Localization.awayMap π (f j)) ≫ t k j = spMap (algebraMap R₀ (Localization.Away (π (f j)))) ≫ g₀) →
    (∀ k j, t k j ⁻¹ᵁ V j = ⊤) →
    ∀ (n : κ → κ → ℕ) (s : ∀ j l, Fin (n j l) → Localization.Away (f j * f l)) (W : ∀ j l, Fin (n j l) → X.left.Opens),
    (∀ j l, Ideal.span (Set.range (s j l)) = ⊤) → (∀ j l i, IsAffineOpen (W j l i)) →
    (∀ j l i, (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ e j) ⁻¹ᵁ W j l i = ⊤) →
    (∀ j l k i, GlobalTheory.SecGlue.IsCombIn (W j l i) (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f l)) (f l) (f j)) ≫ e l)
        (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ t k j)
        ![spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f l)) (f l) (f j)) ≫ t k l, spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ e j]
        ![1, 1 - algebraMap R (Localization.Away (s j l i)) (f k) ^ (N)]) →
    ∃ e : ∀ k, Sp (Localization.Away (f k)) ⟶ X.left,
      (∀ k, e k ≫ X.hom = spMap (algebraMap R (Localization.Away (f k)))) ∧
      (∀ k, spMap (Localization.awayMap π (f k)) ≫ e k = spMap (algebraMap R₀ (Localization.Away (π (f k)))) ≫ g₀) ∧
      ∀ j k, spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f k)) (f j) (f k)) ≫ e j =
        spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f k)) (f k) (f j)) ≫ e k := by
  intro R R₀ _ _ π hπ h2 X g₀ hg₀ κ _ f hf V hV e he he₀ heV N t ht ht₀ htV n s W hs hW heW hco
  have hpow : Ideal.span (Set.range fun k => f k ^ N) = ⊤ := by
    have := Ideal.span_pow_eq_top _ hf N
    rwa [← Set.range_comp] at this
  obtain ⟨a, ha⟩ : ∃ a : κ → R, ∑ k, a k * f k ^ N = 1 :=
    Ideal.mem_span_range_iff_exists_fun.1 (hpow ▸ Submodule.mem_top)
  have hte : ∀ j k, spMap (Localization.awayMap π (f j)) ≫ t k j =
      spMap (Localization.awayMap π (f j)) ≫ e j := fun j k => (ht₀ k j).trans (he₀ j).symm
  choose c hc hc₀ hcp using fun j => GlobalTheory.T.exists_affineCombination_squareZero_lifts_chart X.left (V j) (hV j) _ _
    (Localization.awayMap π (f j)) (awayMap_surjective π hπ _) (ker_awayMap_sq π h2 _) κ (e j)
    (fun k => t k j) (fun k => algebraMap R _ (a k)) (heV j) (hte j)
  refine ⟨c, fun j => (hcp j R X.hom fun k => (ht k j).trans (he j).symm).trans (he j),
    fun j => (hc₀ j).trans (he₀ j), fun j l => ?_⟩
  refine hom_ext_of_span_eq_top _ _ (s j l) (hs j l) _ _ _ fun i => ?_
  obtain ⟨hlW, -⟩ := hco j l j i
  have hjW := heW j l i
  rw [← Category.assoc, spMap_comp_spMap] at hlW hjW
  have h₁ := isCombIn_restrict_chart (hV j) (hW j l i) _ (awayMap_surjective π hπ _)
    (ker_awayMap_sq π h2 _) _ _ _ _ _ (hte j) (hc j) hjW
  have h₂ := isCombIn_restrict_chart (hV l) (hW j l i) _ (awayMap_surjective π hπ _)
    (ker_awayMap_sq π h2 _) _ _ _ _ _ (hte l) (hc l) hlW
  simp only [RingHom.comp_apply, IsLocalization.Away.awayToAwayRight_eq,
    IsLocalization.Away.awayToAwayLeft_eq, ← IsScalarTower.algebraMap_apply,
    ← spMap_comp_spMap, Category.assoc] at h₁ h₂
  refine eq_of_cocycle (hW j l i) _ _ _ _ _ _ _
    (fun k => algebraMap R (Localization.Away (s j l i)) (f k) ^ N) ?_ h₁ h₂ fun k => hco j l k i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← map_pow, ← map_mul, ← map_sum, ha, map_one]

end GlobalTheory.SecGlue.Cocycle
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftsAgreeOfCocycleStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lifts_agree_of_cocycle_alt : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (κ : Type) [Fintype κ] (f : κ → R), Ideal.span (Set.range f) = ⊤ → ∀ (V : κ → X.left.Opens), (∀ k, IsAffineOpen (V k)) →
    ∀ (e : ∀ k, Sp (Localization.Away (f k)) ⟶ X.left),
    (∀ k, e k ≫ X.hom = spMap (algebraMap R (Localization.Away (f k)))) →
    (∀ k, spMap (Localization.awayMap π (f k)) ≫ e k = spMap (algebraMap R₀ (Localization.Away (π (f k)))) ≫ g₀) →
    (∀ k, e k ⁻¹ᵁ V k = ⊤) →
    ∀ (N : ℕ) (t : κ → ∀ j, Sp (Localization.Away (f j)) ⟶ X.left),
    (∀ k j, t k j ≫ X.hom = spMap (algebraMap R (Localization.Away (f j)))) →
    (∀ k j, spMap (Localization.awayMap π (f j)) ≫ t k j = spMap (algebraMap R₀ (Localization.Away (π (f j)))) ≫ g₀) →
    (∀ k j, t k j ⁻¹ᵁ V j = ⊤) →
    ∀ (n : κ → κ → ℕ) (s : ∀ j l, Fin (n j l) → Localization.Away (f j * f l)) (W : ∀ j l, Fin (n j l) → X.left.Opens),
    (∀ j l, Ideal.span (Set.range (s j l)) = ⊤) → (∀ j l i, IsAffineOpen (W j l i)) →
    (∀ j l i, (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ e j) ⁻¹ᵁ W j l i = ⊤) →
    (∀ j l k i, GlobalTheory.SecGlue.IsCombIn (W j l i) (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f l)) (f l) (f j)) ≫ e l)
        (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ t k j)
        ![spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f l)) (f l) (f j)) ≫ t k l, spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ e j]
        ![1, 1 - algebraMap R (Localization.Away (s j l i)) (f k) ^ (N)]) →
    ∃ e : ∀ k, Sp (Localization.Away (f k)) ⟶ X.left,
      (∀ k, e k ≫ X.hom = spMap (algebraMap R (Localization.Away (f k)))) ∧
      (∀ k, spMap (Localization.awayMap π (f k)) ≫ e k = spMap (algebraMap R₀ (Localization.Away (π (f k)))) ≫ g₀) ∧
      ∀ j k, spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f k)) (f j) (f k)) ≫ e j =
        spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f k)) (f k) (f j)) ≫ e k := by
  first | exact @GlobalTheory.SecGlue.Cocycle.exists_lifts_agree_of_cocycle | exact GlobalTheory.SecGlue.Cocycle.exists_lifts_agree_of_cocycle | (intros; apply GlobalTheory.SecGlue.Cocycle.exists_lifts_agree_of_cocycle <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroLiftBasicOpenPairAgree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqZeroExtendLocalizationAwayPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqZeroExtendLocalizationAwayPow
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SecGlue

def sqZeroInterp {R B S : Type} [CommRing R] [CommRing B] [CommRing S] [Algebra R B]
    [Algebra R S] (J : Ideal S) (hJ : J ^ 2 = ⊥) (α β : B →ₐ[R] S) (h : ∀ x, β x - α x ∈ J)
    (c : S) : B →ₐ[R] S where
  toFun x := α x + c * (β x - α x)
  map_one' := by simp
  map_mul' x y := by
    have hxy : (β x - α x) * (β y - α y) = 0 := by
      have hm := Ideal.mul_mem_mul (h x) (h y)
      rw [← pow_two, hJ] at hm
      simpa using hm
    simp only [map_mul]
    linear_combination (c - c ^ 2) * hxy
  map_zero' := by simp
  map_add' x y := by simp only [map_add (f := _)]; ring
  commutes' r := by simp

@[simp] theorem sqZeroInterp_apply {R B S : Type} [CommRing R] [CommRing B] [CommRing S]
    [Algebra R B] [Algebra R S] (J : Ideal S) (hJ : J ^ 2 = ⊥) (α β : B →ₐ[R] S)
    (h : ∀ x, β x - α x ∈ J) (c : S) (x : B) :
    sqZeroInterp J hJ α β h c x = α x + c * (β x - α x) := rfl

theorem exists_sqZero_extend_base (R' A S : Type) [CommRing R'] [CommRing A] [CommRing S]
    [Algebra R' A] [Algebra R' S]
    [hfp : Algebra.FinitePresentation R' A] (J : Ideal S) (hJ : J ^ 2 = ⊥) (g : S)
    (φ : A →ₐ[R'] S) (ψ : A →ₐ[R'] Localization.Away g)
    (hψ : ∀ x, ψ x - algebraMap S (Localization.Away g) (φ x) ∈
      J.map (algebraMap S (Localization.Away g))) :
    ∃ N₀ : ℕ, ∃ χ : A →ₐ[R'] S, (∀ x, χ x - φ x ∈ J) ∧
      ∀ x, algebraMap S (Localization.Away g) (χ x) = algebraMap S (Localization.Away g) (φ x) +
        algebraMap S (Localization.Away g) g ^ N₀ *
          (ψ x - algebraMap S (Localization.Away g) (φ x)) := by
  obtain ⟨n, π, hπ, hker⟩ := hfp.out
  have hJg : (J.map (algebraMap S (Localization.Away g))) ^ 2 = ⊥ := by
    rw [← Ideal.map_pow, hJ, Ideal.map_bot]
  have hy : ∀ i : Fin n, ∃ k : ℕ, ∃ y ∈ J, algebraMap S (Localization.Away g) y =
      algebraMap S (Localization.Away g) g ^ k * (ψ (π (MvPolynomial.X i)) -
        algebraMap S (Localization.Away g) (φ (π (MvPolynomial.X i)))) := by
    intro i
    obtain ⟨⟨⟨j, hj⟩, ⟨m, ⟨k, rfl⟩⟩⟩, e⟩ := (IsLocalization.mem_map_algebraMap_iff
      (Submonoid.powers g) (Localization.Away g)).1 (hψ (π (MvPolynomial.X i)))
    refine ⟨k, j, hj, ?_⟩
    simp only [map_pow] at e
    rw [← e]; ring
  choose k y hyJ hyeq using hy
  set M := Finset.univ.sup k with hM
  set y' : Fin n → S := fun i => g ^ (M - k i) * y i with hy'
  have hy'J : ∀ i, y' i ∈ J := fun i => J.mul_mem_left _ (hyJ i)
  have hy'eq : ∀ i, algebraMap S (Localization.Away g) (y' i) =
      algebraMap S (Localization.Away g) g ^ M * (ψ (π (MvPolynomial.X i)) -
        algebraMap S (Localization.Away g) (φ (π (MvPolynomial.X i)))) := by
    intro i
    have hk : k i ≤ M := Finset.le_sup (Finset.mem_univ i)
    simp only [y', map_mul, map_pow, hyeq, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hk]
  set α₀ : MvPolynomial (Fin n) R' →ₐ[R'] S := φ.comp π with hα₀
  set β₀ : MvPolynomial (Fin n) R' →ₐ[R'] S :=
    MvPolynomial.aeval (fun i => φ (π (MvPolynomial.X i)) + y' i) with hβ₀
  have hβα : ∀ p, β₀ p - α₀ p ∈ J := by
    intro p
    rw [← Ideal.Quotient.eq]
    have e : (Ideal.Quotient.mkₐ R' J).comp β₀ = (Ideal.Quotient.mkₐ R' J).comp α₀ := by
      apply MvPolynomial.algHom_ext; intro i
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, β₀, α₀, MvPolynomial.aeval_X]
      rw [Ideal.Quotient.eq]; simpa using hy'J i
    exact DFunLike.congr_fun e p
  have hloc : ∀ p, algebraMap S (Localization.Away g) (β₀ p) =
      algebraMap S (Localization.Away g) (α₀ p) + algebraMap S (Localization.Away g) g ^ M *
        (ψ (π p) - algebraMap S (Localization.Away g) (α₀ p)) := by
    intro p
    have e : (IsScalarTower.toAlgHom R' S (Localization.Away g)).comp β₀ =
        sqZeroInterp _ hJg ((IsScalarTower.toAlgHom R' S (Localization.Away g)).comp α₀)
          (ψ.comp π) (fun q => hψ (π q)) (algebraMap S (Localization.Away g) g ^ M) := by
      apply MvPolynomial.algHom_ext; intro i
      simp only [AlgHom.comp_apply, sqZeroInterp_apply, IsScalarTower.coe_toAlgHom', β₀, α₀,
        MvPolynomial.aeval_X, map_add, hy'eq]
      rfl
    exact DFunLike.congr_fun e p

  obtain ⟨s, hs⟩ := hker
  have hrel : ∀ r ∈ s, ∃ K : ℕ, g ^ K * (β₀ r - α₀ r) = 0 := by
    intro r hr
    have hrk : r ∈ RingHom.ker π.toRingHom := hs ▸ Ideal.subset_span hr
    have hπr : π r = 0 := hrk
    have hz : algebraMap S (Localization.Away g) (β₀ r - α₀ r) = 0 := by
      rw [map_sub, hloc]; simp [α₀, hπr]
    obtain ⟨⟨m, ⟨K, rfl⟩⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g) _ _).1 hz
    exact ⟨K, hm⟩
  choose! Kf hKf using hrel
  set K := s.sup Kf with hK
  set θ := sqZeroInterp J hJ α₀ β₀ hβα (g ^ K) with hθ
  have hθker : ∀ r ∈ RingHom.ker π.toRingHom, θ r = 0 := by
    intro r hr
    rw [← hs] at hr
    have hle : Ideal.span (s : Set (MvPolynomial (Fin n) R')) ≤ RingHom.ker θ := by
      rw [Ideal.span_le]
      intro r hr
      have hrk : r ∈ RingHom.ker π.toRingHom := hs ▸ Ideal.subset_span hr
      have hπr : π r = 0 := hrk
      have hle' : Kf r ≤ K := Finset.le_sup hr
      show θ r = 0
      rw [hθ, sqZeroInterp_apply]
      have : α₀ r = 0 := by simp [α₀, hπr]
      have h2 := hKf r hr
      rw [this, sub_zero] at h2
      rw [this, sub_zero, zero_add, ← Nat.sub_add_cancel hle', pow_add, mul_assoc, h2, mul_zero]
    exact hle hr
  let χ₀ : A →ₐ[R'] S := (Ideal.Quotient.liftₐ (RingHom.ker π.toRingHom) θ hθker).comp
    (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom
  have hχ₀ : ∀ p, χ₀ (π p) = θ p := by
    intro p
    have : (Ideal.quotientKerAlgEquivOfSurjective hπ).symm (π p) = Ideal.Quotient.mk _ p := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    show Ideal.Quotient.liftₐ _ θ hθker ((Ideal.quotientKerAlgEquivOfSurjective hπ).symm (π p)) = θ p
    rw [this]
    rfl
  refine ⟨K + M, χ₀, ?_, ?_⟩
  · intro x
    obtain ⟨p, rfl⟩ := hπ x
    rw [hχ₀, hθ, sqZeroInterp_apply]
    have : φ (π p) = α₀ p := rfl
    rw [this, add_sub_cancel_left]
    exact J.mul_mem_left _ (hβα p)
  · intro x
    obtain ⟨p, rfl⟩ := hπ x
    rw [hχ₀, hθ, sqZeroInterp_apply]
    have : φ (π p) = α₀ p := rfl
    rw [this, map_add (f := _), map_mul, map_sub, hloc, map_pow, pow_add]
    ring

theorem exists_sqZero_extend_pow : ∀ (R' A S : Type) [CommRing R'] [CommRing A] [CommRing S] [Algebra R' A] [Algebra R' S]
    [Algebra.FinitePresentation R' A] (J : Ideal S), J ^ 2 = ⊥ → ∀ (g : S) (φ : A →ₐ[R'] S)
    (ψ : A →ₐ[R'] Localization.Away g),
    (∀ x, ψ x - algebraMap S (Localization.Away g) (φ x) ∈ J.map (algebraMap S (Localization.Away g))) →
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ χ : A →ₐ[R'] S, (∀ x, χ x - φ x ∈ J) ∧
      ∀ x, algebraMap S (Localization.Away g) (χ x) = algebraMap S (Localization.Away g) (φ x) +
        algebraMap S (Localization.Away g) g ^ N * (ψ x - algebraMap S (Localization.Away g) (φ x)) := by
  intro R' A S _ _ _ _ _ _ J hJ g φ ψ hψ
  obtain ⟨N₀, χ₀, h1, h2⟩ := exists_sqZero_extend_base R' A S J hJ g φ ψ hψ
  refine ⟨N₀, fun N hN => ⟨sqZeroInterp J hJ φ χ₀ h1 (g ^ (N - N₀)), ?_, ?_⟩⟩
  · intro x
    rw [sqZeroInterp_apply, add_sub_cancel_left]
    exact J.mul_mem_left _ (h1 x)
  · intro x
    rw [sqZeroInterp_apply, map_add (f := _), map_mul, map_sub, h2, map_pow, add_sub_cancel_left,
      ← mul_assoc, ← pow_add, Nat.sub_add_cancel hN]

end GlobalTheory.SecGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqZeroExtendLocalizationAwayPowStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sqZero_extend_localizationAway_pow : ∀ (R' A S : Type) [CommRing R'] [CommRing A] [CommRing S] [Algebra R' A] [Algebra R' S]
    [Algebra.FinitePresentation R' A] (J : Ideal S), J ^ 2 = ⊥ → ∀ (g : S) (φ : A →ₐ[R'] S)
    (ψ : A →ₐ[R'] Localization.Away g),
    (∀ x, ψ x - algebraMap S (Localization.Away g) (φ x) ∈ J.map (algebraMap S (Localization.Away g))) →
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ χ : A →ₐ[R'] S, (∀ x, χ x - φ x ∈ J) ∧
      ∀ x, algebraMap S (Localization.Away g) (χ x) = algebraMap S (Localization.Away g) (φ x) +
        algebraMap S (Localization.Away g) g ^ N * (ψ x - algebraMap S (Localization.Away g) (φ x)) := by
  first | exact @GlobalTheory.SecGlue.exists_sqZero_extend_pow | exact GlobalTheory.SecGlue.exists_sqZero_extend_pow | (intros; apply GlobalTheory.SecGlue.exists_sqZero_extend_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroLiftBasicOpenPairAgree
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SecGlue.Pair

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]; rfl

theorem chart_rebuild {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (x : Sp S ⟶ Y) (hx : x ⁻¹ᵁ V = ⊤) : spMap (chartHom V x hx) ≫ hV.fromSpec = x := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec x hV (isAffineOpen_top (Sp S)) hx.ge
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  have e : CommRingCat.ofHom (chartHom V x hx) =
      x.appLE V ⊤ hx.ge ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom := rfl
  show Spec.map (CommRingCat.ofHom (chartHom V x hx)) ≫ hV.fromSpec = x
  rw [e, Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
    Spec.map_id, Category.id_comp]

theorem fromSpec_comp_top {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (χ : Γ(Y, V) →+* S) : (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V = ⊤ :=
  top_le_iff.1 fun _ _ => hV.range_fromSpec.subset ⟨_, rfl⟩

theorem chartHom_fromSpec {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (χ : Γ(Y, V) →+* S) (hc : (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V = ⊤) :
    chartHom V (spMap χ ≫ hV.fromSpec) hc = χ := by
  have e := chart_rebuild hV (spMap χ ≫ hV.fromSpec) hc
  rw [cancel_mono] at e
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

theorem chartHom_congr {Y : Scheme.{0}} (V : Y.Opens) {S : Type} [CommRing S] {x x' : Sp S ⟶ Y}
    (e : x = x') (h : x ⁻¹ᵁ V = ⊤) (h' : x' ⁻¹ᵁ V = ⊤) : chartHom V x h = chartHom V x' h' := by
  subst e; rfl

def strHom {R : Type} [CommRing R] (X : Over (Sp R)) (V : X.left.Opens) : R →+* Γ(X.left, V) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ X.hom.appLE ⊤ V (le_top : V ≤ X.hom ⁻¹ᵁ ⊤)).hom

theorem fromSpec_over {R : Type} [CommRing R] (X : Over (Sp R)) {V : X.left.Opens} (hV : IsAffineOpen V) :
    hV.fromSpec ≫ X.hom = spMap (strHom X V) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec X.hom (isAffineOpen_top (Sp R)) hV
    (le_top : V ≤ X.hom ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [← h, ← Spec.map_comp]; rfl

theorem chartHom_comp_strHom {R : Type} [CommRing R] (X : Over (Sp R)) {V : X.left.Opens}
    (hV : IsAffineOpen V) {S : Type} [CommRing S] (f : R →+* S) (u : Sp S ⟶ X.left) (hu : u ⁻¹ᵁ V = ⊤)
    (hf : u ≫ X.hom = spMap f) : (chartHom V u hu).comp (strHom X V) = f := by
  have e : spMap ((chartHom V u hu).comp (strHom X V)) = spMap f := by
    rw [spMap_comp', ← fromSpec_over X hV, ← Category.assoc, chart_rebuild, hf]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

theorem smooth_strHom {R : Type} [CommRing R] (X : Over (Sp R)) [Smooth X.hom] {V : X.left.Opens}
    (hV : IsAffineOpen V) : (strHom X V).Smooth := by
  have h1 : RingHom.Smooth (X.hom.appLE ⊤ V le_top).hom :=
    X.hom.smooth_appLE (isAffineOpen_top (Sp R)) hV le_top
  have h2 : RingHom.Smooth (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.bijective
  exact h2.comp h1

theorem awayMap_surjective {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) (c : R) : Function.Surjective (Localization.awayMap π c) :=
  (IsLocalization.Away.map_surjective_iff _ _ π c).2 fun y =>
    let ⟨x, hx⟩ := hπ y; ⟨x, 0, by simp [hx]⟩

theorem ker_awayMap {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) (c : R) :
    RingHom.ker (Localization.awayMap π c) = (RingHom.ker π).map (algebraMap R (Localization.Away c)) := by
  exact IsLocalization.ker_map (S := Localization.Away c) (Localization.Away (π c)) π
    (M := Submonoid.powers c) (Submonoid.map_powers π c)

theorem ker_awayMap_sq {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hsq : RingHom.ker π ^ 2 = ⊥) (c : R) : RingHom.ker (Localization.awayMap π c) ^ 2 = ⊥ := by
  rw [ker_awayMap, ← Ideal.map_pow, hsq, Ideal.map_bot]

theorem awayMap_comp_algebraMap {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) (c : R) :
    (Localization.awayMap π c).comp (algebraMap R (Localization.Away c)) =
      (algebraMap R₀ (Localization.Away (π c))).comp π :=
  IsLocalization.map_comp _

end GlobalTheory.SecGlue.Pair

namespace GlobalTheory.SecGlue.Pair

theorem red_comp {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) {Y : Scheme.{0}} (g₀ : Sp R₀ ⟶ Y)
    (c d : R) (hcd : c ∣ d) (e : Sp (Localization.Away c) ⟶ Y)
    (he : spMap (Localization.awayMap π c) ≫ e = spMap (algebraMap R₀ (Localization.Away (π c))) ≫ g₀)
    (r : Localization.Away c →+* Localization.Away d)
    (hr : r.comp (algebraMap R (Localization.Away c)) = algebraMap R (Localization.Away d)) :
    spMap (Localization.awayMap π d) ≫ spMap r ≫ e =
      spMap (algebraMap R₀ (Localization.Away (π d))) ≫ g₀ := by
  have hu : IsUnit (algebraMap R₀ (Localization.Away (π d)) (π c)) :=
    isUnit_of_dvd_unit (map_dvd _ (map_dvd π hcd)) (IsLocalization.Away.algebraMap_isUnit (π d))
  let h : Localization.Away (π c) →+* Localization.Away (π d) := IsLocalization.Away.lift (π c) hu
  have e1 : (Localization.awayMap π d).comp r = h.comp (Localization.awayMap π c) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers c)
    rw [RingHom.comp_assoc, hr, awayMap_comp_algebraMap, RingHom.comp_assoc, awayMap_comp_algebraMap,
      ← RingHom.comp_assoc, IsLocalization.Away.lift_comp]
  rw [← Category.assoc, ← spMap_comp', e1, spMap_comp', Category.assoc, he, ← Category.assoc,
    ← spMap_comp', IsLocalization.Away.lift_comp]

end GlobalTheory.SecGlue.Pair

namespace GlobalTheory.SecGlue.Pair

theorem equiv_restrict {R : Type} [CommRing R] (a b : R)
    (eP : Localization.Away (a * b) ≃ₐ[R] Localization.Away (algebraMap R (Localization.Away a) b))
    (ρ : Localization.Away a →+* Localization.Away (a * b))
    (hρ : ρ.comp (algebraMap R (Localization.Away a)) = algebraMap R (Localization.Away (a * b)))
    (y : Localization.Away a) :
    eP (ρ y) = algebraMap (Localization.Away a) (Localization.Away (algebraMap R (Localization.Away a) b)) y := by
  have e : (eP.toAlgHom : Localization.Away (a * b) →+* _).comp ρ =
      algebraMap (Localization.Away a) (Localization.Away (algebraMap R (Localization.Away a) b)) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers a)
    rw [RingHom.comp_assoc, hρ, eP.toAlgHom.comp_algebraMap]
    exact IsScalarTower.algebraMap_eq _ _ _
  exact RingHom.congr_fun e y

theorem exists_awayEquiv {R : Type} [CommRing R] (a b : R) :
    Nonempty (Localization.Away (a * b) ≃ₐ[R] Localization.Away (algebraMap R (Localization.Away a) b)) :=
  ⟨IsLocalization.algEquiv (Submonoid.powers (a * b)) _ _⟩

end GlobalTheory.SecGlue.Pair

namespace GlobalTheory.SecGlue.Pair

theorem comp_over {Y : Scheme.{0}} {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (e : Sp B ⟶ Y)
    (p : Y ⟶ Sp A) (f : A →+* B) (he : e ≫ p = spMap f) (r : B →+* C) (g : A →+* C) (hr : r.comp f = g) :
    (spMap r ≫ e) ≫ p = spMap g := by
  rw [Category.assoc, he, ← spMap_comp', hr]

end GlobalTheory.SecGlue.Pair

namespace GlobalTheory.SecGlue


open GlobalTheory.SecGlue.Pair in
set_option maxHeartbeats 1000000 in
theorem exists_pair_lift_comb : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (a b : R) (V : X.left.Opens), IsAffineOpen V →
    ∀ (ea : Sp (Localization.Away a) ⟶ X.left), ea ≫ X.hom = spMap (algebraMap R (Localization.Away a)) →
      spMap (Localization.awayMap π a) ≫ ea = spMap (algebraMap R₀ (Localization.Away (π a))) ≫ g₀ → ea ⁻¹ᵁ V = ⊤ →
    ∀ (eb : Sp (Localization.Away b) ⟶ X.left), eb ≫ X.hom = spMap (algebraMap R (Localization.Away b)) →
      spMap (Localization.awayMap π b) ≫ eb = spMap (algebraMap R₀ (Localization.Away (π b))) ≫ g₀ →
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ t : Sp (Localization.Away a) ⟶ X.left,
      t ≫ X.hom = spMap (algebraMap R (Localization.Away a)) ∧
      spMap (Localization.awayMap π a) ≫ t = spMap (algebraMap R₀ (Localization.Away (π a))) ≫ g₀ ∧ t ⁻¹ᵁ V = ⊤ ∧
      GlobalTheory.SecGlue.IsCombIn V
        (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (a * b)) a b) ≫ ea)
        (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (a * b)) a b) ≫ t)
        ![spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (a * b)) b a) ≫ eb]
        ![algebraMap R (Localization.Away (a * b)) b ^ N] := by
  intro R R₀ _ _ π hπ hsq X hX g₀ hg₀ a b V hV ea hea hea₀ heaV eb heb heb₀
  haveI := hX
  letI : Algebra R Γ(X.left, V) := (strHom X V).toAlgebra
  haveI : Algebra.Smooth R Γ(X.left, V) := smooth_strHom X hV

  have hρ : (IsLocalization.Away.awayToAwayRight (S := Localization.Away a) (P := Localization.Away (a * b))
      a b).comp (algebraMap R (Localization.Away a)) = algebraMap R (Localization.Away (a * b)) :=
    RingHom.ext (IsLocalization.Away.awayToAwayRight_eq a b)
  have hρ' : (IsLocalization.Away.awayToAwayLeft (S := Localization.Away b) (P := Localization.Away (a * b))
      b a).comp (algebraMap R (Localization.Away b)) = algebraMap R (Localization.Away (a * b)) :=
    RingHom.ext (IsLocalization.Away.awayToAwayLeft_eq b a)
  generalize IsLocalization.Away.awayToAwayRight (S := Localization.Away a) (P := Localization.Away (a * b))
      a b = ρ at hρ ⊢
  generalize IsLocalization.Away.awayToAwayLeft (S := Localization.Away b) (P := Localization.Away (a * b))
      b a = ρ' at hρ' ⊢
  have hred : spMap (Localization.awayMap π (a * b)) ≫ spMap ρ' ≫ eb =
      spMap (Localization.awayMap π (a * b)) ≫ spMap ρ ≫ ea :=
    (red_comp π g₀ b (a * b) (dvd_mul_left b a) eb heb₀ ρ' hρ').trans
      (red_comp π g₀ a (a * b) (dvd_mul_right a b) ea hea₀ ρ hρ).symm
  have h2 : (spMap ρ ≫ ea) ⁻¹ᵁ V = ⊤ := preimage_spMap_comp_eq_top ρ heaV
  have hbV : (spMap ρ' ≫ eb) ⁻¹ᵁ V = ⊤ :=
    (GlobalTheory.T.preimage_eq_of_square_zero_thickening (Localization.Away (a * b)) (Localization.Away (π (a * b))) (Localization.awayMap π (a * b))
      (awayMap_surjective π hπ _) (ker_awayMap_sq π hsq _) X.left (spMap ρ' ≫ eb) (spMap ρ ≫ ea) hred V).trans h2

  let φ : Γ(X.left, V) →ₐ[R] Localization.Away a :=
    { chartHom V ea heaV with
      commutes' := fun r => RingHom.congr_fun (chartHom_comp_strHom X hV _ ea heaV hea) r }

  obtain ⟨eP⟩ := exists_awayEquiv a b
  have hePc : (eP.toAlgHom : Localization.Away (a * b) →+* Localization.Away (algebraMap R (Localization.Away a) b)).comp
      (algebraMap R (Localization.Away (a * b))) = algebraMap R (Localization.Away (algebraMap R (Localization.Away a) b)) :=
    eP.toAlgHom.comp_algebraMap
  have heP := equiv_restrict a b eP ρ hρ
  have heb' : (spMap ρ' ≫ eb) ≫ X.hom = spMap (algebraMap R (Localization.Away (a * b))) :=
    comp_over eb X.hom _ heb ρ' _ hρ'
  let ψ : Γ(X.left, V) →ₐ[R] Localization.Away (algebraMap R (Localization.Away a) b) :=
    { (eP : Localization.Away (a * b) →+* Localization.Away (algebraMap R (Localization.Away a) b)).comp (chartHom V (spMap ρ' ≫ eb) hbV) with
      commutes' := fun r => by
        show eP (chartHom V (spMap ρ' ≫ eb) hbV (strHom X V r)) = _
        rw [← RingHom.comp_apply, chartHom_comp_strHom X hV _ _ hbV heb', AlgEquiv.commutes] }
  have hJ : RingHom.ker (Localization.awayMap π a) ^ 2 = ⊥ := ker_awayMap_sq π hsq a
  have hcond : ∀ x, ψ x - algebraMap (Localization.Away a) (Localization.Away (algebraMap R (Localization.Away a) b)) (φ x) ∈
      (RingHom.ker (Localization.awayMap π a)).map (algebraMap (Localization.Away a) (Localization.Away (algebraMap R (Localization.Away a) b))) := by
    intro x
    have hd : chartHom V (spMap ρ' ≫ eb) hbV x - chartHom V (spMap ρ ≫ ea) h2 x ∈
        RingHom.ker (Localization.awayMap π (a * b)) := by
      rw [RingHom.mem_ker, map_sub, sub_eq_zero,
        ← chartHom_spMap_comp V _ _ hbV (preimage_spMap_comp_eq_top _ hbV),
        ← chartHom_spMap_comp V _ _ h2 (preimage_spMap_comp_eq_top _ h2)]
      exact RingHom.congr_fun (chartHom_congr V hred _ _) x
    rw [ker_awayMap] at hd
    have h3 := Ideal.mem_map_of_mem (eP : Localization.Away (a * b) →+* Localization.Away (algebraMap R (Localization.Away a) b)) hd
    rw [Ideal.map_map, show (eP : Localization.Away (a * b) →+* Localization.Away (algebraMap R (Localization.Away a) b)).comp
        (algebraMap R (Localization.Away (a * b))) = algebraMap R (Localization.Away (algebraMap R (Localization.Away a) b)) from
        RingHom.ext fun r => eP.commutes r, map_sub] at h3
    rw [ker_awayMap, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    have e2 : algebraMap (Localization.Away a) (Localization.Away (algebraMap R (Localization.Away a) b)) (φ x) =
        eP (chartHom V (spMap ρ ≫ ea) h2 x) := by
      rw [chartHom_spMap_comp V ρ ea heaV h2 x, heP]
      rfl
    rw [e2]
    exact h3
  obtain ⟨N₀, hN⟩ := GlobalTheory.T.exists_sqZero_extend_localizationAway_pow R Γ(X.left, V) (Localization.Away a) (RingHom.ker (Localization.awayMap π a)) hJ (algebraMap R (Localization.Away a) b) φ ψ hcond
  refine ⟨N₀, fun N hN' => ?_⟩
  obtain ⟨χ, hχJ, hχ⟩ := hN N hN'
  have htop := fromSpec_comp_top hV (χ : Γ(X.left, V) →+* Localization.Away a)
  refine ⟨spMap (χ : Γ(X.left, V) →+* Localization.Away a) ≫ hV.fromSpec, ?_, ?_, htop, ?_⟩
  · rw [Category.assoc, fromSpec_over, ← spMap_comp']
    exact congrArg spMap (RingHom.ext fun r => χ.commutes r)
  · rw [← hea₀, ← chart_rebuild hV ea heaV, ← Category.assoc, ← Category.assoc, ← spMap_comp',
      ← spMap_comp']
    refine congrArg (fun f => spMap f ≫ hV.fromSpec) (RingHom.ext fun x => ?_)
    have := hχJ x
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
    exact this
  · refine ⟨h2, preimage_spMap_comp_eq_top ρ htop, fun i => by rw [Matrix.cons_val_fin_one]; exact hbV, fun x => ?_⟩
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero]
    rw [chartHom_spMap_comp V ρ _ htop, chartHom_fromSpec hV _ htop, chartHom_spMap_comp V ρ ea heaV]
    apply eP.injective
    rw [map_add (f := _), map_mul, map_sub, map_pow, heP, heP, AlgEquiv.commutes,
      IsScalarTower.algebraMap_apply R (Localization.Away a) (Localization.Away (algebraMap R (Localization.Away a) b))]
    exact hχ x

end GlobalTheory.SecGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroLiftBasicOpenPairAgreeStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_squareZeroLift_basicOpen_pair_agree : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (a b : R) (V : X.left.Opens), IsAffineOpen V →
    ∀ (ea : Sp (Localization.Away a) ⟶ X.left), ea ≫ X.hom = spMap (algebraMap R (Localization.Away a)) →
      spMap (Localization.awayMap π a) ≫ ea = spMap (algebraMap R₀ (Localization.Away (π a))) ≫ g₀ → ea ⁻¹ᵁ V = ⊤ →
    ∀ (eb : Sp (Localization.Away b) ⟶ X.left), eb ≫ X.hom = spMap (algebraMap R (Localization.Away b)) →
      spMap (Localization.awayMap π b) ≫ eb = spMap (algebraMap R₀ (Localization.Away (π b))) ≫ g₀ →
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ t : Sp (Localization.Away a) ⟶ X.left,
      t ≫ X.hom = spMap (algebraMap R (Localization.Away a)) ∧
      spMap (Localization.awayMap π a) ≫ t = spMap (algebraMap R₀ (Localization.Away (π a))) ≫ g₀ ∧ t ⁻¹ᵁ V = ⊤ ∧
      GlobalTheory.SecGlue.IsCombIn V
        (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (a * b)) a b) ≫ ea)
        (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (a * b)) a b) ≫ t)
        ![spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (a * b)) b a) ≫ eb]
        ![algebraMap R (Localization.Away (a * b)) b ^ N] := by
  first | exact @GlobalTheory.SecGlue.exists_pair_lift_comb | exact GlobalTheory.SecGlue.exists_pair_lift_comb | (intros; apply GlobalTheory.SecGlue.exists_pair_lift_comb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenCoverAffineOpenSpec
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenCoverAffineOpenSpec
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecGlue

theorem spMap_away_mem_basicOpen {S : Type} [CommRing S] (s : S)
    (x : Sp (Localization.Away s)) :
    (spMap (algebraMap S (Localization.Away s))).base x ∈ PrimeSpectrum.basicOpen s := by
  show algebraMap S (Localization.Away s) s ∉ x.asIdeal
  intro h
  exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit s))

theorem exists_basicOpen_cover_affine (S : Type) [CommRing S] (Y : Scheme.{0}) (u : Sp S ⟶ Y) :
    ∃ (n : ℕ) (s : Fin n → S) (W : Fin n → Y.Opens), Ideal.span (Set.range s) = ⊤ ∧
      (∀ i, IsAffineOpen (W i)) ∧ ∀ i, (spMap (algebraMap S (Localization.Away (s i))) ≫ u) ⁻¹ᵁ W i = ⊤ := by
  classical
  let T : Set S := {s | ∃ W : Y.Opens, IsAffineOpen W ∧
    ∀ x : Sp S, x ∈ PrimeSpectrum.basicOpen s → u.base x ∈ W}
  have hT : Ideal.span T = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff', eq_top_iff]
    intro x _
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (u.base x)) isOpen_univ
    obtain ⟨_, ⟨s, rfl⟩, hxs, hsW⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        hxW (u ⁻¹ᵁ W).isOpen
    have hsT : s ∈ T := ⟨W, hW, fun y hy => hsW hy⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨s, TopologicalSpace.Opens.mem_iSup.mpr ⟨hsT, hxs⟩⟩
  obtain ⟨F, hFT, hF⟩ := (Ideal.span_eq_top_iff_finite T).mp hT
  have hW : ∀ t : F, ∃ W : Y.Opens, IsAffineOpen W ∧
      ∀ x : Sp S, x ∈ PrimeSpectrum.basicOpen (t : S) → u.base x ∈ W := fun t => hFT t.2
  choose Wf hWa hWs using hW
  refine ⟨F.card, fun i => (F.equivFin.symm i : S), fun i => Wf (F.equivFin.symm i), ?_,
    fun i => hWa _, fun i => ?_⟩
  · have : Set.range (fun i => (F.equivFin.symm i : S)) = (F : Set S) := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact (F.equivFin.symm i).2
      · intro hy
        exact ⟨F.equivFin ⟨y, hy⟩, by simp⟩
    rw [this, hF]
  · rw [eq_top_iff]
    intro x _
    exact hWs _ _ (spMap_away_mem_basicOpen _ x)

end GlobalTheory.SecGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenCoverAffineOpenSpecStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_cover_affineOpen_spec : ∀ (S : Type) [CommRing S] (Y : Scheme.{0}) (u : Sp S ⟶ Y),
    ∃ (n : ℕ) (s : Fin n → S) (W : Fin n → Y.Opens), Ideal.span (Set.range s) = ⊤ ∧
      (∀ i, IsAffineOpen (W i)) ∧ ∀ i, (spMap (algebraMap S (Localization.Away (s i))) ≫ u) ⁻¹ᵁ W i = ⊤ := by
  first | exact @GlobalTheory.SecGlue.exists_basicOpen_cover_affine | exact GlobalTheory.SecGlue.exists_basicOpen_cover_affine | (intros; apply GlobalTheory.SecGlue.exists_basicOpen_cover_affine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroLocalLiftsCorrectedAgreeOnOverlaps
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecGlue

theorem lifts_corrected_agree_on_overlaps : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (κ : Type) [Finite κ] (f : κ → R), Ideal.span (Set.range f) = ⊤ → ∀ V : κ → X.left.Opens, (∀ k, IsAffineOpen (V k)) →
    (∀ k, GlobalTheory.SecLift.LiftIn π X g₀ (f k) (V k)) →
    ∃ e : ∀ k, Sp (Localization.Away (f k)) ⟶ X.left,
      (∀ k, e k ≫ X.hom = spMap (algebraMap R (Localization.Away (f k)))) ∧
      (∀ k, spMap (Localization.awayMap π (f k)) ≫ e k = spMap (algebraMap R₀ (Localization.Away (π (f k)))) ≫ g₀) ∧
      ∀ j k, spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f k)) (f j) (f k)) ≫ e j =
        spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f k)) (f k) (f j)) ≫ e k := by
  intro R R₀ _ _ π hπ hI X hX g₀ hg₀ κ _ f hf V hV hL
  classical
  have : Fintype κ := Fintype.ofFinite κ
  choose e he1 he2 he3 using hL
  choose N₀ hN₀ using fun k j => GlobalTheory.T.exists_squareZeroLift_basicOpen_pair_agree R R₀ π hπ hI X hX g₀ hg₀ (f j) (f k) (V j) (hV j) (e j) (he1 j) (he2 j) (he3 j) (e k) (he1 k) (he2 k)
  have hN : ∀ k j, N₀ k j ≤ Finset.univ.sup (fun p : κ × κ => N₀ p.1 p.2) := fun k j =>
    Finset.le_sup (f := fun p : κ × κ => N₀ p.1 p.2) (Finset.mem_univ (k, j))
  choose t ht1 ht2 ht3 ht4 using fun k j => hN₀ k j _ (hN k j)
  choose n s W hs hW hWl using fun j l => GlobalTheory.T.exists_basicOpen_cover_affineOpen_spec _ _ (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ e j)
  obtain ⟨M, t', h1, h2, h3, h4⟩ := GlobalTheory.T.exists_pow_cocycle_alt R R₀ π hπ hI X hX g₀ hg₀ κ f V hV e he1 he2 he3 _ t ht1 ht2 ht3 ht4 n s W hs hW hWl
  exact GlobalTheory.T.exists_lifts_agree_of_cocycle_alt R R₀ π hπ hI X g₀ hg₀ κ f hf V hV e he1 he2 he3 _ t' h1 h2 h3 n s W hs hW hWl h4

end GlobalTheory.SecGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroLocalLiftsCorrectedAgreeOnOverlapsStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareZero_local_lifts_corrected_agree_on_overlaps : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (κ : Type) [Finite κ] (f : κ → R), Ideal.span (Set.range f) = ⊤ → ∀ V : κ → X.left.Opens, (∀ k, IsAffineOpen (V k)) →
    (∀ k, GlobalTheory.SecLift.LiftIn π X g₀ (f k) (V k)) →
    ∃ e : ∀ k, Sp (Localization.Away (f k)) ⟶ X.left,
      (∀ k, e k ≫ X.hom = spMap (algebraMap R (Localization.Away (f k)))) ∧
      (∀ k, spMap (Localization.awayMap π (f k)) ≫ e k = spMap (algebraMap R₀ (Localization.Away (π (f k)))) ≫ g₀) ∧
      ∀ j k, spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f k)) (f j) (f k)) ≫ e j =
        spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f k)) (f k) (f j)) ≫ e k := by
  first | exact @GlobalTheory.SecGlue.lifts_corrected_agree_on_overlaps | exact GlobalTheory.SecGlue.lifts_corrected_agree_on_overlaps | (intros; apply GlobalTheory.SecGlue.lifts_corrected_agree_on_overlaps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueSpecLocalizationAwayMorphisms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueSpecLocalizationAwayMorphisms
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SecGlue


open Limits in
theorem glue_away : ∀ (S : Type) [CommRing S] (ι : Type) (s : ι → S), Ideal.span (Set.range s) = ⊤ →
    ∀ (Y : Scheme.{0}) (e : ∀ i, Sp (Localization.Away (s i)) ⟶ Y),
    (∀ i j, spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (s i * s j)) (s i) (s j)) ≫ e i =
      spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (s i * s j)) (s j) (s i)) ≫ e j) →
    ∃ a : Sp S ⟶ Y, ∀ i, spMap (algebraMap S (Localization.Away (s i))) ≫ a = e i := by
  intro S _ ι s hs Y e he
  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of S) s hs).openCover
  have hf : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ e i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ e j := by
    intro i j
    refine Scheme.Cover.hom_ext (pullback (𝒰.f i) (𝒰.f j)).affineOpenCover.openCover _ _ fun k => ?_
    let a : Spec ((pullback (𝒰.f i) (𝒰.f j)).affineOpenCover.X k) ⟶ pullback (𝒰.f i) (𝒰.f j) :=
      (pullback (𝒰.f i) (𝒰.f j)).affineOpenCover.f k
    let T := (pullback (𝒰.f i) (𝒰.f j)).affineOpenCover.X k
    let A : CommRingCat.of (Localization.Away (s i)) ⟶ T := Spec.preimage (a ≫ pullback.fst (𝒰.f i) (𝒰.f j))
    let B : CommRingCat.of (Localization.Away (s j)) ⟶ T := Spec.preimage (a ≫ pullback.snd (𝒰.f i) (𝒰.f j))
    have ea : Spec.map A = a ≫ pullback.fst (𝒰.f i) (𝒰.f j) := Spec.map_preimage _
    have eb : Spec.map B = a ≫ pullback.snd (𝒰.f i) (𝒰.f j) := Spec.map_preimage _
    have e1 : Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s i))) ≫ A) =
        Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s j))) ≫ B) := by
      rw [Spec.map_comp, Spec.map_comp, ea, eb]
      exact (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)
    have key : A.hom.comp (algebraMap S (Localization.Away (s i))) =
        B.hom.comp (algebraMap S (Localization.Away (s j))) :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective e1)
    have hu : IsUnit ((A.hom.comp (algebraMap S (Localization.Away (s i)))) (s i * s j)) := by
      rw [map_mul]
      refine IsUnit.mul ?_ ?_
      · exact (IsLocalization.Away.algebraMap_isUnit (s i)).map A.hom
      · rw [key]; exact (IsLocalization.Away.algebraMap_isUnit (s j)).map B.hom
    let L : Localization.Away (s i * s j) →+* T := IsLocalization.Away.lift (s i * s j) hu
    have hL : L.comp (algebraMap S (Localization.Away (s i * s j))) =
        A.hom.comp (algebraMap S (Localization.Away (s i))) := IsLocalization.Away.lift_comp _ _
    have hLA : L.comp (IsLocalization.Away.awayToAwayRight (P := Localization.Away (s i * s j)) (s i) (s j)) = A.hom := by
      refine IsLocalization.ringHom_ext (Submonoid.powers (s i)) (RingHom.ext fun x => ?_)
      have := congrArg (fun f => f x) hL
      simp only [RingHom.comp_apply] at this ⊢
      rw [IsLocalization.Away.awayToAwayRight_eq, this]
    have hLB : L.comp (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (s i * s j)) (s j) (s i)) = B.hom := by
      refine IsLocalization.ringHom_ext (Submonoid.powers (s j)) (RingHom.ext fun x => ?_)
      have := congrArg (fun f => f x) (hL.trans key)
      simp only [RingHom.comp_apply] at this ⊢
      rw [IsLocalization.Away.awayToAwayLeft_eq, this]
    have hA : Spec.map A = Spec.map (CommRingCat.ofHom L) ≫
        spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (s i * s j)) (s i) (s j)) := by
      rw [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hLA]; rfl
    have hB : Spec.map B = Spec.map (CommRingCat.ofHom L) ≫
        spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (s i * s j)) (s j) (s i)) := by
      rw [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hLB]; rfl
    have h2 : Spec.map A ≫ e i = Spec.map B ≫ e j := by
      rw [hA, hB, Category.assoc, Category.assoc, he i j]
    rw [ea, eb] at h2
    exact (Category.assoc _ _ _).symm.trans (h2.trans (Category.assoc _ _ _))
  exact ⟨𝒰.glueMorphisms e hf, fun i => Scheme.Cover.ι_glueMorphisms 𝒰 e hf i⟩

end GlobalTheory.SecGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueSpecLocalizationAwayMorphismsStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glue_spec_localizationAway_morphisms : ∀ (S : Type) [CommRing S] (ι : Type) (s : ι → S), Ideal.span (Set.range s) = ⊤ →
    ∀ (Y : Scheme.{0}) (e : ∀ i, Sp (Localization.Away (s i)) ⟶ Y),
    (∀ i j, spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (s i * s j)) (s i) (s j)) ≫ e i =
      spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (s i * s j)) (s j) (s i)) ≫ e j) →
    ∃ a : Sp S ⟶ Y, ∀ i, spMap (algebraMap S (Localization.Away (s i))) ≫ a = e i := by
  first | exact @GlobalTheory.SecGlue.glue_away | exact GlobalTheory.SecGlue.glue_away | (intros; apply GlobalTheory.SecGlue.glue_away <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalLiftOfChartLocalLiftsSquareZero
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecGlue

theorem exists_lift_of_chart_lifts : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (κ : Type) [Finite κ] (f : κ → R), Ideal.span (Set.range f) = ⊤ → ∀ V : κ → X.left.Opens, (∀ k, IsAffineOpen (V k)) →
    (∀ k, GlobalTheory.SecLift.LiftIn π X g₀ (f k) (V k)) → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ spMap π ≫ e = g₀ := by
  intro R R₀ _ _ π hπ hI X hX g₀ hg₀ κ _ f hf V hV hL
  obtain ⟨e, he1, he2, he3⟩ := GlobalTheory.T.squareZero_local_lifts_corrected_agree_on_overlaps R R₀ π hπ hI X hX g₀ hg₀ κ f hf V hV hL
  obtain ⟨E, hE⟩ := GlobalTheory.T.exists_glue_spec_localizationAway_morphisms R κ f hf X.left e he3
  refine ⟨E, ?_, ?_⟩
  · refine GlobalTheory.T.specHom_ext_of_localizationAway_span_eq_top R κ f hf (Sp R) _ _ (fun k => ?_)
    rw [← Category.assoc, hE k, he1 k, Category.comp_id]
  · have hf₀ : Ideal.span (Set.range (fun k => π (f k))) = ⊤ := by
      rw [show (fun k => π (f k)) = π ∘ f from rfl, Set.range_comp, ← Ideal.map_span, hf, Ideal.map_top]
    refine GlobalTheory.T.specHom_ext_of_localizationAway_span_eq_top R₀ κ (fun k => π (f k)) hf₀ X.left _ _ (fun k => ?_)
    rw [← he2 k, ← hE k, ← Category.assoc, ← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (IsLocalization.map_comp _).symm

end GlobalTheory.SecGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalLiftOfChartLocalLiftsSquareZeroStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_lift_of_chartLocal_lifts_squareZero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (κ : Type) [Finite κ] (f : κ → R), Ideal.span (Set.range f) = ⊤ → ∀ V : κ → X.left.Opens, (∀ k, IsAffineOpen (V k)) →
    (∀ k, GlobalTheory.SecLift.LiftIn π X g₀ (f k) (V k)) → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ spMap π ≫ e = g₀ := by
  first | exact @GlobalTheory.SecGlue.exists_lift_of_chart_lifts | exact GlobalTheory.SecGlue.exists_lift_of_chart_lifts | (intros; apply GlobalTheory.SecGlue.exists_lift_of_chart_lifts <;> assumption)
end
