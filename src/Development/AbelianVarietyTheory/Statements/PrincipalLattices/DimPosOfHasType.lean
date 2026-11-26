module

public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEqSmulOfFinrankOne
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyPolAVGenericFibreWithLieBasis
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.CMLattices.CmHostBarHalfIntegerGenerator
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM.Test

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem bar_rt (H : Host E) : H.bar H.rt = -H.rt := by
  have hsq : (H.bar H.rt - H.rt) * (H.bar H.rt + H.rt) = 0 := by
    have e : H.bar (H.rt ^ 2) = H.bar (-(H.d : 𝓞 E)) := by rw [H.rt_sq]
    rw [map_pow, map_neg, map_natCast, ← H.rt_sq] at e
    linear_combination e
  rcases mul_eq_zero.mp hsq with h | h
  · exfalso
    have hfix : H.bar H.rt = H.rt := sub_eq_zero.mp h
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have hc := H.bar_eq H.rt
    rw [hfix] at hc
    have hconj : starRingEnd ℂ (φ (H.rt : E)) = φ (H.rt : E) := by
      rw [← NumberField.IsCMField.complexEmbedding_complexConj, ← hc]
    have hsqC : (φ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
      rw [← map_pow]
      have e : ((H.rt ^ 2 : 𝓞 E) : E) = ((-(H.d : 𝓞 E) : 𝓞 E) : E) := by rw [H.rt_sq]
      push_cast at e
      rw [e]
      simp
    have him : (φ (H.rt : E)).im = 0 := Complex.conj_eq_iff_im.mp hconj
    have hre := congrArg Complex.re hsqC
    simp only [pow_two, Complex.mul_re, him, mul_zero, sub_zero, Complex.neg_re, Complex.natCast_re] at hre
    have hd : (2 : ℝ) ≤ H.d := by exact_mod_cast H.d_prime.two_le
    nlinarith [mul_self_nonneg (φ (H.rt : E)).re]
  · linear_combination h

variable {D : Datum H} {ε : ℤˣ} {h : D.La → D.La → OK H}

variable {K : Type} [Field K] [NumberField K]

theorem hasType_neg {ρ : 𝓞 K} (hρ : ρ ^ 2 = -(H.d : 𝓞 K)) {G : Over (Sp (𝓞 K))} [GrpObj G] {act : OAct (𝓞 E) G}
    {p q : ℕ} (h : HasType H act ρ p q) : HasType H act (-ρ) q p := by
  intro k _ _ β hβ τ
  obtain ⟨h1, h2⟩ := h k β hβ τ
  have e1 : τ H.rt ^ 2 = -(H.d : k) := by rw [← map_pow, H.rt_sq, map_neg, map_natCast]
  have e2 : β ρ ^ 2 = -(H.d : k) := by rw [← map_pow, hρ, map_neg, map_natCast]
  have hτ : (τ H.rt - β ρ) * (τ H.rt + β ρ) = 0 := by linear_combination e1 - e2
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    have hd0 : ((H.d : ℕ) : 𝓞 K) = 0 := by
      have e := hρ
      rw [zero_pow two_ne_zero] at e
      exact neg_eq_zero.mp e.symm
    exact H.d_prime.ne_zero (by exact_mod_cast hd0)
  have h2k : (2 : k) ≠ 0 := by
    intro h0
    have e : β 2 = β 0 := by rw [map_ofNat, h0, map_zero]
    have := hβ e
    norm_num at this
  have hβρ : β ρ ≠ 0 := by
    intro h0
    exact hρ0 (hβ (h0.trans (map_zero β).symm))
  have hne : β ρ ≠ -β ρ := by
    intro h0
    have e : (2 : k) * β ρ = 0 := by linear_combination h0
    rcases mul_eq_zero.mp e with e' | e'
    · exact h2k e'
    · exact hβρ e'
  constructor
  · intro hneg
    rw [map_neg] at hneg
    apply h2
    intro heq
    rw [heq] at hneg
    exact hne hneg
  · intro hne'
    apply h1
    rcases mul_eq_zero.mp hτ with h0 | h0
    · exact sub_eq_zero.mp h0
    · exfalso
      apply hne'
      rw [map_neg]
      exact eq_neg_of_add_eq_zero_left h0

end GlobalTheory.CM.Test
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM.NumInh

variable {K : Type} [Field K] [NumberField K]


variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem dim_pos_of_lieMult {S : Scheme.{0}} {O k : Type} [CommRing O] [Field k] {G : Over S} [GrpObj G] {act : OAct O G}
    {t : Sp k ⟶ S} {τ : O →+* k} (h : LieMult act t τ 1) {g : ℕ} (hg : SmoothOfRelativeDimension g G.hom) : 1 ≤ g := by
  by_contra h0
  obtain rfl : g = 0 := by omega
  have : Etale G.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 hg
  obtain ⟨v, hv, hu⟩ := h
  have hs : Function.Surjective (TrivSqZeroExt.fstHom k k k).toRingHom := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) hs
  have hnil : IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro r hr s hs
    have hr' : r.fst = 0 := hr
    have hs' : s.fst = 0 := hs
    rw [Ideal.mem_bot]
    ext <;> simp [hr', hs']
  have key : ∀ c : k, (v 0).left = spMap (epsScale c) ≫ (v 0).left := fun c => by
    refine FormallyUnramified.hom_ext (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)
      (isNilpotent_ker_specMap _ hnil) G.hom ?_ ?_
    · rw [← Category.assoc, spMap_comp_spMap]
      congr 2
      ext a <;> simp [epsScale]
    · rw [Category.assoc, Over.w (v 0)]
      show spMap _ ≫ t = spMap _ ≫ spMap _ ≫ t
      rw [← Category.assoc, spMap_comp_spMap]
      congr 2
      ext a <;> simp [epsScale, TrivSqZeroExt.algebraMap_eq_inl]
  have e : ∀ c : Fin 1 → k, ∃ u : Fin 1 → (epsPt t ⟶ G),
      (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (v i).left) ∧ v 0 = (List.ofFn u).prod := fun c =>
    ⟨v, fun i => by rw [Subsingleton.elim i 0]; exact key _, by simp⟩
  exact zero_ne_one (congrFun ((hu _ (hv 0)).unique (e 0) (e 1)) 0)

theorem exists_char (hs : Splits E K) {ρ : 𝓞 K} (hρ : ρ ^ 2 = -(H.d : 𝓞 K)) : ∃ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ := by
  obtain ⟨τ⟩ : Nonempty (𝓞 E →+* 𝓞 K) := (Nat.card_pos_iff.1 (hs ▸ Module.finrank_pos)).1
  have e : τ H.rt ^ 2 = ρ ^ 2 := by rw [← map_pow, H.rt_sq, hρ]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 e with e | e
  · exact ⟨τ, e⟩
  · exact ⟨τ.comp H.bar.toRingHom, by
      show τ (H.bar H.rt) = ρ
      rw [Test.bar_rt, map_neg, e, neg_neg]⟩

theorem dim_pos_of_hasType (hs : Splits E K) {ρ : 𝓞 K} (hρ : ρ ^ 2 = -(H.d : 𝓞 K)) (T : PAT H (Sp (𝓞 K))) {q : ℕ}
    (hT : HasType H T.t.act ρ 1 q) : 1 ≤ T.g := by
  obtain ⟨τ, hτ⟩ := exists_char hs hρ
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  exact dim_pos_of_lieMult ((hT ℂ (σ.comp (algebraMap (𝓞 K) K)) (σ.injective.comp RingOfIntegers.coe_injective)
    ((σ.comp (algebraMap (𝓞 K) K)).comp τ)).1 (by rw [RingHom.comp_apply, hτ])) T.dim


end GlobalTheory.CM.NumInh
end
