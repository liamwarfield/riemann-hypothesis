module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpModel

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

theorem HomLocRingMem.algebraMap_mk_ne_zero {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    (P : Ideal (MRing ι R)) [P.IsPrime] {g : MRing ι R} (hg : g ∉ P) :
    algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P g) ≠ 0 := by
  rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  exact hg

theorem HomLocRingMem.proof : HomLocRingMem.Statement := by
  intro R _ K _ ι P W _ hW hPW z
  have hne : ∀ g : MRing ι R, g ∉ W →
      algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P g) ≠ 0 :=
    fun g hg => HomLocRingMem.algebraMap_mk_ne_zero P (fun h => hg (hPW h))
  have h1W : (1 : MRing ι R) ∉ W := fun h => hW.ne_top ((Ideal.eq_top_iff_one W).mpr h)
  constructor
  · intro hz
    refine Subring.closure_induction (fun x hx => hx) ?_ ?_ ?_ ?_ ?_ hz
    · exact ⟨0, 0, 1, isWeightedHomogeneous_zero R _ _, isWeightedHomogeneous_one R _, h1W, by simp⟩
    · exact ⟨0, 1, 1, isWeightedHomogeneous_one R _, isWeightedHomogeneous_one R _, h1W, by simp⟩
    · rintro x y - - ⟨b₁, f₁, g₁, hf₁, hg₁, hW₁, rfl⟩ ⟨b₂, f₂, g₂, hf₂, hg₂, hW₂, rfl⟩
      refine ⟨b₁ + b₂, f₁ * g₂ + g₁ * f₂, g₁ * g₂, (hf₁.mul hg₂).add ?_, hg₁.mul hg₂,
        fun h => (hW.mem_or_mem h).elim hW₁ hW₂, ?_⟩
      · rw [add_comm b₁ b₂, mul_comm g₁ f₂]
        exact hf₂.mul hg₁
      · set_option synthInstance.maxHeartbeats 200000 in
        simp only [map_add, map_mul]
        rw [div_add_div _ _ (hne g₁ hW₁) (hne g₂ hW₂)]
    · rintro x - ⟨b, f, g, hf, hg, hgW, rfl⟩
      exact ⟨b, -f, g, hf.neg, hg, hgW, by simp only [map_neg, neg_div]⟩
    · rintro x y - - ⟨b₁, f₁, g₁, hf₁, hg₁, hW₁, rfl⟩ ⟨b₂, f₂, g₂, hf₂, hg₂, hW₂, rfl⟩
      refine ⟨b₁ + b₂, f₁ * f₂, g₁ * g₂, hf₁.mul hf₂, hg₁.mul hg₂,
        fun h => (hW.mem_or_mem h).elim hW₁ hW₂, ?_⟩
      simp only [map_mul]
      rw [div_mul_div_comm]
  · intro hz
    exact Subring.subset_closure hz

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingIsLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem HomLocRingIsLocal.proof (h : HomLocRingMem.Statement.{u}) : HomLocRingIsLocal.Statement.{u} := by
  intro R _ K _ ι P W _ hW hPW
  let F := FractionRing (MRing ι R ⧸ P)
  let φ : MRing ι R →+* F := (algebraMap (MRing ι R ⧸ P) F).comp (Ideal.Quotient.mk P)
  have hφ : ∀ a, φ a = 0 ↔ a ∈ P := by
    intro a
    simp only [φ, RingHom.comp_apply]
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hne : ∀ a, a ∉ W → φ a ≠ 0 := fun a ha h0 => ha (hPW ((hφ a).1 h0))
  have key : ∀ (b : K → ℕ) (f g : MRing ι R), IsMultiHomog f b → IsMultiHomog g b → g ∉ W →
      ∀ hz : φ f / φ g ∈ homLocRing P W, IsUnit (⟨_, hz⟩ : homLocRing P W) ↔ f ∉ W := by
    intro b f g hf hg hgW hz
    constructor
    · rintro ⟨u, hu⟩ hfW
      obtain ⟨b', f', g', -, -, hg'W, hw⟩ :=
        (h R K ι P W hW hPW ((u⁻¹ : (homLocRing P W)ˣ) : homLocRing P W)).1 (u⁻¹ : (homLocRing P W)ˣ).1.2
      have h1 : (φ f / φ g) * (φ f' / φ g') = 1 := by
        have e := congrArg Subtype.val u.mul_inv
        rw [Subring.coe_mul, hu, Subring.coe_one] at e
        rw [← e]
        congr 1
        exact hw.symm
      have h2 : φ (f * f' - g * g') = 0 := by
        rw [div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero (hne g hgW) (hne g' hg'W))] at h1
        rw [map_sub, map_mul, map_mul, h1, sub_self]
      have h3 : f * f' - g * g' ∈ W := hPW ((hφ _).1 h2)
      have h4 : g * g' ∈ W := by
        have := W.sub_mem (W.mul_mem_right f' hfW) h3
        simpa using this
      rcases hW.mem_or_mem h4 with h5 | h5
      exacts [hgW h5, hg'W h5]
    · intro hfW
      have hgf : φ g / φ f ∈ homLocRing P W := Subring.subset_closure ⟨b, g, f, hg, hf, hfW, rfl⟩
      refine IsUnit.of_mul_eq_one ⟨_, hgf⟩ ?_
      apply Subtype.ext
      rw [Subring.coe_mul, Subring.coe_one]
      rw [div_mul_div_comm, mul_comm (φ f) (φ g)]
      exact div_self (mul_ne_zero (hne g hgW) (hne f hfW))
  refine ⟨?_, key⟩
  have hnu : ∀ z : homLocRing P W, ¬ IsUnit z → ∃ (b : K → ℕ) (f g : MRing ι R),
      IsMultiHomog f b ∧ IsMultiHomog g b ∧ g ∉ W ∧ f ∈ W ∧ (z : F) = φ f / φ g := by
    intro z hz
    obtain ⟨b, f, g, hf, hg, hgW, hzfg⟩ := (h R K ι P W hW hPW z).1 z.2
    refine ⟨b, f, g, hf, hg, hgW, ?_, hzfg⟩
    by_contra hfW
    have hmem : φ f / φ g ∈ homLocRing P W := hzfg ▸ z.2
    have e : z = ⟨_, hmem⟩ := Subtype.ext hzfg
    exact hz (e ▸ (key b f g hf hg hgW hmem).2 hfW)
  refine IsLocalRing.of_nonunits_add ?_
  intro x y hx hy
  obtain ⟨b₁, f₁, g₁, hf₁, hg₁, hg₁W, hf₁W, hx'⟩ := hnu x hx
  obtain ⟨b₂, f₂, g₂, hf₂, hg₂, hg₂W, hf₂W, hy'⟩ := hnu y hy
  have hnum : IsMultiHomog (f₁ * g₂ + f₂ * g₁) (b₁ + b₂) :=
    IsWeightedHomogeneous.add (IsWeightedHomogeneous.mul hf₁ hg₂)
      (by rw [add_comm]; exact IsWeightedHomogeneous.mul hf₂ hg₁)
  have hden : IsMultiHomog (g₁ * g₂) (b₁ + b₂) := IsWeightedHomogeneous.mul hg₁ hg₂
  have hdenW : g₁ * g₂ ∉ W := fun h5 => (hW.mem_or_mem h5).elim hg₁W hg₂W
  have hsum : ((x + y : homLocRing P W) : F) = φ (f₁ * g₂ + f₂ * g₁) / φ (g₁ * g₂) := by
    rw [Subring.coe_add, hx', hy', div_add_div _ _ (hne g₁ hg₁W) (hne g₂ hg₂W), map_add (f := _), map_mul, map_mul,
      map_mul, mul_comm (φ g₁) (φ f₂)]
  have hmem : φ (f₁ * g₂ + f₂ * g₁) / φ (g₁ * g₂) ∈ homLocRing P W := hsum ▸ (x + y).2
  have e : x + y = ⟨_, hmem⟩ := Subtype.ext hsum
  rw [mem_nonunits_iff, e, key (b₁ + b₂) _ _ hnum hden hdenW hmem, not_not]
  exact W.add_mem (W.mul_mem_right _ hf₁W) (W.mul_mem_right _ hf₂W)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem homLocRing_form_not_mem {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    {R : Type u} [CommRing R] {W : Ideal (MRing ι R)} (hW : W.IsPrime) (hrel : IsRelevant W)
    (c : K → ℕ) : ∃ g : MRing ι R, IsMultiHomog g c ∧ g ∉ W := by
  choose i hi using hrel
  refine ⟨∏ k, X ⟨k, i k⟩ ^ c k, ?_, ?_⟩
  · have hc : c = ∑ k, c k • blockWeight ι ⟨k, i k⟩ := by
      funext j
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    have h := IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, i k⟩ : MRing ι R) ^ c k)
      (fun k => c k • blockWeight ι ⟨k, i k⟩)
      fun k _ => (isWeightedHomogeneous_X R (blockWeight ι) _).pow _
    rw [← hc] at h
    exact h
  · intro h
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hW)).mp h
    exact hi k (hW.mem_of_pow_mem _ hk)

theorem HomLocRingLocal.proof (hloc : HomLocRingIsLocal.Statement.{u})
    (hnoeth : HomLocRingNoetherian.Statement.{u}) (hdim : HomLocRingDimLe.Statement.{u}) :
    HomLocRingLocal.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ P hP c x hx hxP W hW hWrel
  have := hP.isPrime
  have hWp : W.IsPrime := hW.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  have hxW : x ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
  obtain ⟨hlocal, hunit⟩ := hloc O K ι P W hWp hPW
  have hnoe := hnoeth O K ι P W hP.multiHomog hWp hWrel hPW
  refine ⟨hlocal, hnoe, le_antisymm ?_ ?_⟩
  · refine (hdim O K ι P W hP.multiHomog hWp hWrel hPW).trans ?_
    have h1 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
    exact_mod_cast h1
  · obtain ⟨g, hg, hgW⟩ := homLocRing_form_not_mem hWp hWrel c
    have hz : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P x) /
        algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P g) ∈
          homLocRing P W :=
      Subring.subset_closure ⟨c, x, g, hx, hg, hgW, rfl⟩
    have hnu : ¬ IsUnit (⟨_, hz⟩ : homLocRing P W) :=
      fun h => (hunit c x g hx hg hgW hz).mp h hxW
    have hne : (⟨_, hz⟩ : homLocRing P W) ≠ 0 := by
      intro h0
      have h1 := congrArg Subtype.val h0
      simp only [ZeroMemClass.coe_zero, div_eq_zero_iff,
        IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h1
      rcases h1 with h1 | h1
      · exact hxP h1
      · exact hgW (hPW h1)
    have hlt : (⊥ : Ideal (homLocRing P W)) < IsLocalRing.maximalIdeal (homLocRing P W) := by
      refine bot_lt_iff_ne_bot.mpr fun h => hne ?_
      have hm := (IsLocalRing.mem_maximalIdeal _).mpr hnu
      rwa [h, Ideal.mem_bot] at hm
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    have h3 : (1 : ℕ∞) ≤ (IsLocalRing.maximalIdeal (homLocRing P W)).height :=
      le_trans le_add_self h2
    exact_mod_cast h3

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureModel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace SegreFlagClosureModel

theorem exists_flag_ne_zero {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
    {Φ : Type*} [Field Φ] [Algebra Ω Φ] {N P : ℕ} (w e : Module.Basis (Fin N) Ω E)
    {t : Fin N → Φ} (ht : LinearIndependent Ω t) (ψ : Fin P → Module.Dual Ω E)
    (hψ : Submodule.span Ω (Set.range ψ) = ⊤) {k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) :
    ∃ l, ∑ j, flagCoord w e t k j * algebraMap Ω Φ (ψ l (w j)) ≠ 0 := by
  have hN : 0 < N := by omega
  by_contra! h0

  let θ : Fin P → Module.Dual Ω E := fun l =>
    ∑ j : Fin N, (if (j : ℕ) < k then ψ l (w j) else 0) • w.coord j
  have hθe : ∀ l i, θ l (e i) = ∑ j : Fin N, (if (j : ℕ) < k then ψ l (w j) else 0) * w.repr (e i) j := by
    intro l i
    simp only [θ, LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]
  have hθ : ∀ l, θ l = 0 := by
    intro l
    refine e.ext fun i => ?_
    have key := Fintype.linearIndependent_iff.1 ht (fun i => θ l (e i)) (by
      rw [← h0 l]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hθe, Algebra.smul_def, map_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [flagCoord]
      split_ifs
      · rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul]
        ring
      · simp)
    simpa using key i
  have hw0 : ∀ l, ψ l (w ⟨0, hN⟩) = 0 := by
    intro l
    have h := congrArg (fun f : Module.Dual Ω E => f (w ⟨0, hN⟩)) (hθ l)
    simp only [θ, LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
      Module.Basis.repr_self, LinearMap.zero_apply] at h
    rw [Finset.sum_eq_single ⟨0, hN⟩ (fun j _ hj => by simp [Ne.symm hj])
      (by simp)] at h
    simpa [show (0 : ℕ) < k by omega] using h
  have hall : ∀ f ∈ Submodule.span Ω (Set.range ψ), f (w ⟨0, hN⟩) = 0 := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx => obtain ⟨l, rfl⟩ := hx; exact hw0 l
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  have := hall (w.coord ⟨0, hN⟩) (hψ ▸ Submodule.mem_top)
  simp at this

end SegreFlagClosureModel


open GenericProjClosureDim GenericProjClosureDivisor SegreFlagClosureModel in
theorem SegreFlagClosureModel.proof (hTr : SegreFlagClosureTrdeg.Statement) :
    SegreFlagClosureModel.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk hkN
  have hpt : flagClosurePt y w e φ φ' t k = pairProjCoord y w φ φ' (flagCoord w e t k) := rfl

  have hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0 := fun k => by
    obtain ⟨j, hj⟩ := hV.multiProj.relevant k
    refine ⟨j, fun h0 => hj ?_⟩
    rw [pointIdeal, RingHom.mem_ker]
    simp [pointConeMap, h0]
  choose c hc using hne
  have hyc : segreVec y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hli := ht.linearIndependent

  have hz : ∀ o, ∃ i, flagClosurePt y w e φ φ' t k ⟨o, i⟩ ≠ 0 := by
    rintro (_ | _ | k')
    · exact exists_flag_ne_zero w e hli φ'
        (TwistedDualGensSpan.proof O Ω K ι y N E B' a₀' M' φ' hφ' c hyc) hk hkN
    · exact exists_flag_ne_zero w e hli φ
        (TwistedDualGensSpan.proof O Ω K ι y N E B a₀ M φ hφ c hyc) hk hkN
    · exact ⟨c k', fun h0 => hc k' ((FaithfulSMul.algebraMap_injective Ω Φ)
        (by simpa [flagClosurePt, pairProjCoord, projCoord] using h0))⟩
  have hP := isMultiProjPrime_pointIdeal (R := O) _ hz

  have hnt : (pointIdeal O (flagClosurePt y w e φ φ' t k)).comap (C : O →+* _) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply,
      C_eq_zero, IsScalarTower.algebraMap_apply O Ω Φ, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective Ω Φ)] at ha
    have hy : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := by
      rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, ha,
        map_zero]
    rw [hV.noTorsion] at hy
    simpa using hy

  have hdy := DvrConeDimTrdeg.proof O K ι (pointIdeal O y) hV.multiProj hV.noTorsion
  rw [hV.dim] at hdy
  have hty : Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) = ((d + Fintype.card K : ℕ) : Cardinal) := by
    have h1 : (((d + Fintype.card K : ℕ) : ℕ∞) + 1) =
        (Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y)).toENat + 1 := by
      have := WithBot.coe_injective hdy
      rw [← this]
      push_cast
      ring
    exact (Cardinal.toENat_eq_natCast.1 (WithTop.add_right_cancel ENat.one_ne_top h1).symm)
  have hZ : IsModelOver (pointIdeal O (flagClosurePt y w e φ φ' t k)) (d + (k - 1)) := by
    refine ⟨hP, hnt, ?_⟩
    rw [DvrConeDimTrdeg.proof _ _ _ _ hP hnt,
      hTr O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk hkN, hty,
      ← Nat.cast_add, Cardinal.toENat_nat, Fintype.card_option, Fintype.card_option,
      show d + (k - 1) + 1 + (Fintype.card K + 1 + 1) = d + Fintype.card K + (k + 1) + 1 by omega]
    norm_cast
  refine ⟨hZ, ?_⟩

  rw [hpt] at hZ ⊢
  have hP' : (pointIdeal O (pairProjCoord y w φ φ' (flagCoord w e t k))).IsPrime := hZ.multiProj.isPrime
  have hϖP : (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉
      pointIdeal O (pairProjCoord y w φ φ' (flagCoord w e t k)) := by
    intro hm
    have h1 : ϖ ∈ (pointIdeal O (pairProjCoord y w φ φ' (flagCoord w e t k))).comap
        (C : O →+* MRing (bundleIdx (bundleIdx ι M) M') O) := hm
    rw [hZ.noTorsion, Ideal.mem_bot] at h1
    exact hϖ.ne_zero h1
  have pairs := pairs_at TwistedDualGensExpress.proof y B B' hB a₀ a₀' φ φ' hφ hφ' w (flagCoord w e t k)
  obtain ⟨⟨f₀, g₀, hp₀, hg₀⟩, -⟩ := pairs _ hP' le_rfl hZ.multiProj.relevant hϖP
  have hf₀ : f₀ ∉ pointIdeal O (pairProjCoord y w φ φ' (flagCoord w e t k)) := by
    intro hm
    obtain ⟨⟨bf, bg, -, hg, -⟩, hv⟩ := hp₀
    exact hg₀ (mem_of_homog hg (by rw [← hv]; exact aeval_eq_zero_of_mem hm))
  refine ⟨f₀, g₀, IsVerticalDivisor.of_unit_off_special hp₀.1 hf₀ hg₀ ?_, hp₀.2⟩
  intro W hW hPW hWr hϖW
  obtain ⟨⟨f₁, g₁, hp₁, hg₁⟩, ⟨f₂, g₂, hp₂, hf₂⟩⟩ := pairs W hW hPW hWr hϖW
  have h12 := hPW (hp₁.cross hp₂)
  refine ⟨g₁, f₁, hg₁, fun hf₁ => ?_, ?_⟩
  · have h' : f₁ * g₂ - (f₁ * g₂ - f₂ * g₁) ∈ W := W.sub_mem (W.mul_mem_right _ hf₁) h12
    rw [sub_sub_cancel] at h'
    rcases hW.mem_or_mem h' with h | h
    · exact hf₂ h
    · exact hg₁ h
  · rw [show g₁ * f₀ - f₁ * g₀ = f₀ * g₁ - f₁ * g₀ by ring]
    exact hp₀.cross hp₁

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpLocRingIso
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Abstract

variable {D A : Type*} [CommRing D] [IsDomain D] [CommRing A] [IsDomain A]

theorem exists_ringEquiv_closure_div_of_eq_C_mul_X_pow (θ : A →+* Polynomial D)
    (hθ : Function.Injective θ) {I : Type*} (f g : I → A) (a c : I → D) (n : I → ℕ)
    (hf : ∀ i, θ (f i) = Polynomial.C (a i) * Polynomial.X ^ n i)
    (hg : ∀ i, θ (g i) = Polynomial.C (c i) * Polynomial.X ^ n i)
    (s₁ : Subring (FractionRing A)) (s₂ : Subring (FractionRing D))
    (h₁ : s₁ = Subring.closure (Set.range fun i =>
        algebraMap A (FractionRing A) (f i) / algebraMap A (FractionRing A) (g i)))
    (h₂ : s₂ = Subring.closure (Set.range fun i =>
        algebraMap D (FractionRing D) (a i) / algebraMap D (FractionRing D) (c i))) :
    ∃ φ : s₁ ≃+* s₂, ∀ i (hi : algebraMap A (FractionRing A) (f i) / algebraMap A (FractionRing A) (g i) ∈ s₁),
      (φ ⟨_, hi⟩ : FractionRing D) =
        algebraMap D (FractionRing D) (a i) / algebraMap D (FractionRing D) (c i) := by
  subst h₁ h₂
  let M := FractionRing (Polynomial D)
  have hM : Function.Injective (algebraMap (Polynomial D) M) := IsFractionRing.injective _ M
  let g₁ : A →+* M := (algebraMap (Polynomial D) M).comp θ
  let g₂ : D →+* M := (algebraMap (Polynomial D) M).comp Polynomial.C
  have hg₁ : Function.Injective g₁ := hM.comp hθ
  have hg₂ : Function.Injective g₂ := hM.comp Polynomial.C_injective
  let ι₁ : FractionRing A →+* M := IsFractionRing.lift hg₁
  let ι₂ : FractionRing D →+* M := IsFractionRing.lift hg₂
  have hgen : ∀ i, ι₁ (algebraMap A (FractionRing A) (f i) / algebraMap A (FractionRing A) (g i)) =
      ι₂ (algebraMap D (FractionRing D) (a i) / algebraMap D (FractionRing D) (c i)) := by
    intro i
    rw [map_div₀, map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap,
      IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap]
    have hX : algebraMap (Polynomial D) M (Polynomial.X ^ n i) ≠ 0 := fun h =>
      pow_ne_zero _ Polynomial.X_ne_zero (hM (h.trans (map_zero _).symm))
    simp only [g₁, g₂, RingHom.comp_apply, hf, hg, map_mul]
    exact mul_div_mul_right _ _ hX
  have himg : (Subring.closure (Set.range fun i =>
        algebraMap A (FractionRing A) (f i) / algebraMap A (FractionRing A) (g i))).map ι₁ =
      (Subring.closure (Set.range fun i =>
        algebraMap D (FractionRing D) (a i) / algebraMap D (FractionRing D) (c i))).map ι₂ := by
    rw [RingHom.map_closure, RingHom.map_closure]
    congr 1
    ext z
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, (hgen i).symm⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, hgen i⟩
  refine ⟨(Subring.equivMapOfInjective _ ι₁ ι₁.injective).trans ((RingEquiv.subringCongr himg).trans
    (Subring.equivMapOfInjective _ ι₂ ι₂.injective).symm), fun i hi => ?_⟩
  apply ι₂.injective
  rw [← hgen i, ← Subring.coe_equivMapOfInjective_apply _ ι₂ ι₂.injective, RingEquiv.trans_apply,
    RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  rfl

end Abstract

variable {K : Type*} [DecidableEq K] {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

theorem aeval_blowUpSubst_of_isMultiHomog (P : Ideal (MRing ι R)) (u : J → MRing ι R)
    {F : MRing (extIdx ι J) R} {b : Option K → ℕ} (hF : IsMultiHomog F b) :
    aeval (blowUpSubst P u) F = Polynomial.C (blowUpEval P u F) * Polynomial.X ^ (b none) := by
  classical
  set w := blockWeight (extIdx ι J)
  set ωT : (Σ o, extIdx ι J o) → ℕ := fun v => Pi.evalAddMonoidHom (fun _ => ℕ) none (w v)
  have hT : ∀ d, Finsupp.weight ωT d = Finsupp.weight w d none := fun d =>
    weight_comp_addMonoidHom_apply w (Pi.evalAddMonoidHom (fun _ => ℕ) none) d
  have hsubst : blowUpSubst P u = fun v =>
      Polynomial.C (Ideal.Quotient.mkₐ R P (blowUpAtOne u v)) * Polynomial.X ^ ωT v := by
    funext v
    obtain ⟨o, i⟩ := v
    cases o <;> simp [blowUpSubst, blowUpAtOne, ωT, w, blockWeight]
  have hFT : IsWeightedHomogeneous ωT F (b none) := by
    intro d hd
    rw [hT]
    exact congrFun (hF hd) none
  set c := aeval (fun v => Ideal.Quotient.mkₐ R P (blowUpAtOne u v)) F
  have key : aeval (blowUpSubst P u) F = Polynomial.C c * Polynomial.X ^ (b none) := by
    refine Polynomial.ext fun n => ?_
    rw [hsubst, coeff_aeval_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow]
    split_ifs with hn
    · rw [hn, hFT.weightedHomogeneousComponent_same]
    · rw [hFT.weightedHomogeneousComponent_ne n hn, map_zero]
  have hσ : blowUpEval P u F = c := by
    show Polynomial.eval 1 (aeval (blowUpSubst P u) F) = c
    rw [key]
    simp
  rw [hσ]
  exact key

theorem BlowUpLocRingIso.proof : BlowUpLocRingIso.Statement.{u} := by
  intro R _ K _ ι J P _ u Q _
  have hB : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  let θ : MRing (extIdx ι J) R ⧸ blowUpOf P u →+* Polynomial (MRing ι R ⧸ P) :=
    Ideal.Quotient.lift (blowUpOf P u) (aeval (blowUpSubst P u)).toRingHom
      (fun a ha => RingHom.mem_ker.mp ha)
  have hθ : Function.Injective θ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.lift_mk] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (RingHom.mem_ker.mpr ha)
  let I := {t : (Option K → ℕ) × MRing (extIdx ι J) R × MRing (extIdx ι J) R //
    IsMultiHomog t.2.1 t.1 ∧ IsMultiHomog t.2.2 t.1 ∧ t.2.2 ∉ Q}
  have hf : ∀ i : I, θ (Ideal.Quotient.mk (blowUpOf P u) i.1.2.1) =
      Polynomial.C (blowUpEval P u i.1.2.1) * Polynomial.X ^ (i.1.1 none) := fun i => by
    rw [Ideal.Quotient.lift_mk]
    exact aeval_blowUpSubst_of_isMultiHomog P u i.2.1
  have hg : ∀ i : I, θ (Ideal.Quotient.mk (blowUpOf P u) i.1.2.2) =
      Polynomial.C (blowUpEval P u i.1.2.2) * Polynomial.X ^ (i.1.1 none) := fun i => by
    rw [Ideal.Quotient.lift_mk]
    exact aeval_blowUpSubst_of_isMultiHomog P u i.2.2.1
  have h₁ : homLocRing (blowUpOf P u) Q = Subring.closure (Set.range fun i : I =>
      algebraMap _ (FractionRing (MRing (extIdx ι J) R ⧸ blowUpOf P u)) (Ideal.Quotient.mk (blowUpOf P u) i.1.2.1) /
        algebraMap _ (FractionRing (MRing (extIdx ι J) R ⧸ blowUpOf P u)) (Ideal.Quotient.mk (blowUpOf P u) i.1.2.2)) := by
    rw [homLocRing]
    congr 1
    ext z
    constructor
    · rintro ⟨b, F, G, hF, hG, hGQ, rfl⟩
      exact ⟨⟨(b, F, G), hF, hG, hGQ⟩, rfl⟩
    · rintro ⟨⟨⟨b, F, G⟩, hF, hG, hGQ⟩, rfl⟩
      exact ⟨b, F, G, hF, hG, hGQ, rfl⟩
  have h₂ : blowUpLocRing P u Q = Subring.closure (Set.range fun i : I =>
      algebraMap _ (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u i.1.2.1) /
        algebraMap _ (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u i.1.2.2)) := by
    rw [blowUpLocRing]
    congr 1
    ext z
    constructor
    · rintro ⟨b, F, G, hF, hG, hGQ, rfl⟩
      exact ⟨⟨(b, F, G), hF, hG, hGQ⟩, rfl⟩
    · rintro ⟨⟨⟨b, F, G⟩, hF, hG, hGQ⟩, rfl⟩
      exact ⟨b, F, G, hF, hG, hGQ, rfl⟩
  obtain ⟨φ, hφ⟩ := exists_ringEquiv_closure_div_of_eq_C_mul_X_pow θ hθ
    (fun i : I => Ideal.Quotient.mk (blowUpOf P u) i.1.2.1) (fun i : I => Ideal.Quotient.mk (blowUpOf P u) i.1.2.2)
    (fun i : I => blowUpEval P u i.1.2.1) (fun i : I => blowUpEval P u i.1.2.2) (fun i : I => i.1.1 none)
    hf hg _ _ h₁ h₂
  refine ⟨φ, ?_⟩
  intro b F G hF hG hGQ
  exact hφ ⟨(b, F, G), hF, hG, hGQ⟩ _

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOverLocFiniteCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Objects

variable {A : Type*} [CommRing A] (L : Type*) [Field L] [Algebra A L]

def blowUpColon (I : Ideal A) : Submodule A L :=
  ⨆ n : ℕ, (Submodule.map (Algebra.linearMap A L) I) ^ n / (Submodule.map (Algebra.linearMap A L) I) ^ n

end Objects

section Lemmas

def BlowUpOverLocInChart.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) (J : Type)
    (P W : Ideal (MRing ι R)) [P.IsPrime], IsMultiHomogIdeal P → W.IsPrime → P ≤ W → IsRelevant W →
    ∀ (N : K → ℕ) (u : J → MRing ι R), (∀ j, IsMultiHomog (u j) N) → ∀ j, u j ∉ P →
      blowUpOverLoc P W u ≤ Subring.closure ((homLocRing P W : Set (FractionRing (MRing ι R ⧸ P))) ∪
        Set.range fun k =>
          algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P (u k)) /
            algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P (u j)))

def ChartsInColon.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (L : Type u) [Field L] [Algebra A L] (J : Type) [Fintype J] (a : J → A) (f : L),
    (∀ j, algebraMap A L (a j) ≠ 0 →
      f ∈ Algebra.adjoin A (Set.range fun k => algebraMap A L (a k) / algebraMap A L (a j))) →
    f ∈ blowUpColon L (Ideal.span (Set.range a))

def BlowUpColonFinite.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (L : Type u) [Field L]
    [Algebra A L], Function.Injective (algebraMap A L) → ringKrullDim A = 1 →
    ∀ I : Ideal A, I ≠ ⊥ → (blowUpColon L I).FG

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOverLocMaxCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpOverLocMaxPoint.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), (C ϖ : MRing ι O) ∈ W → W ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
      IsRelevant W →
      haveI := hP.multiProj.isPrime
      ∀ (𝔫 : Ideal (blowUpOverLoc P W u)) (h𝔫 : 𝔫.IsMaximal),
        ∃ W' : Ideal (MRing (extIdx ι J) O),
          (W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes ∧ IsRelevant W' ∧
            W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W) ∧
          (∃ h : blowUpOverLoc P W u ≤ blowUpLocRing P u W',
            letI := (Subring.inclusion h).toAlgebra
            haveI := h𝔫.isPrime
            IsLocalization.AtPrime (blowUpLocRing P u W') 𝔫) ∧
          𝔫.inertiaDeg (homLocRing P W) = specialRelDeg W'

def BlowUpOverLocPointMax.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), (C ϖ : MRing ι O) ∈ W → W ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
      IsRelevant W →
      haveI := hP.multiProj.isPrime
      ∀ W' : Ideal (MRing (extIdx ι J) O), W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes →
        IsRelevant W' → W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W →
        ∃ (h : blowUpOverLoc P W u ≤ blowUpLocRing P u W') (𝔫 : Ideal (blowUpOverLoc P W u))
          (h𝔫 : 𝔫.IsMaximal),
          letI := (Subring.inclusion h).toAlgebra
          haveI := h𝔫.isPrime
          IsLocalization.AtPrime (blowUpLocRing P u W') 𝔫

def BlowUpLocRingInj.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [DecidableEq K] (ι : K → Type) (J : Type)
    (P : Ideal (MRing ι R)) [P.IsPrime] (u : J → MRing ι R) (Q Q' : Ideal (MRing (extIdx ι J) R)),
    Q.IsPrime → IsMultiHomogIdeal Q → IsRelevant Q → blowUpOf P u ≤ Q →
    Q'.IsPrime → IsMultiHomogIdeal Q' → IsRelevant Q' → blowUpOf P u ≤ Q' →
    blowUpLocRing P u Q = blowUpLocRing P u Q' → Q = Q'

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutLiesOver
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Objects

variable {K : Type*} {ι : K → Type} {Ω : Type*} [Field Ω] {N M M' : ℕ} {E : Type*} [AddCommGroup E]
  [Module Ω E] {Φ : Type*} [Field Φ] [Algebra Ω Φ]

def flagProjPt {K' : Type*} (j : K' ↪ Option (Option K)) (y : (Σ k, ι k) → Ω) (w e : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E) (t : Fin N → Φ) (k : ℕ) :
    (Σ o, bundleIdx (bundleIdx ι M) M' (j o)) → Φ :=
  fun p => flagClosurePt y w e φ φ' t k (FieldNumbers.blockIncl j (bundleIdx (bundleIdx ι M) M') p)

end Objects

theorem comap_pointIdeal_blockIncl {R : Type*} [CommRing R] {Φ : Type*} [Field Φ] [Algebra R Φ] {K K' : Type*}
    (j : K ↪ K') {ι' : K' → Type*} (pt : (Σ k', ι' k') → Φ) :
    (pointIdeal R pt).comap (rename (FieldNumbers.blockIncl j ι')) =
      pointIdeal R (fun p => pt (FieldNumbers.blockIncl j ι' p)) := by
  have key : ((pointConeMap R pt).comp (rename (FieldNumbers.blockIncl j ι'))) =
      ((rename j).restrictScalars R).comp (pointConeMap R (fun p => pt (FieldNumbers.blockIncl j ι' p))) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [pointConeMap, FieldNumbers.blockIncl]
  ext f
  simp only [pointIdeal, Ideal.mem_comap, RingHom.mem_ker]
  have hf := congrArg (fun φ => φ f) key
  simp only [AlgHom.comp_apply] at hf
  rw [hf, AlgHom.restrictScalars_apply]
  exact map_eq_zero_iff _ (rename_injective _ j.injective)

def SegreFlagCutLiesOver.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ (k : ℕ) (hk : k < N),
      (∀ (cs ch : Option (Option K) → ℕ) (s h : MRing (bundleIdx (bundleIdx ι M) M') O),
        IsMultiHomog s cs → IsMultiHomog h ch →
        (fun o => (cs o : ℤ) - ch o) = zetaFirst a₀ + liftPairDeg (x ⟨k, hk⟩) →
        s ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) → h ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) →
        aeval (flagClosurePt y w e φ φ' t (k + 1)) s = flagLineCoord w w e t (k + 1) ⟨k, hk⟩ * aeval (flagClosurePt y w e φ φ' t (k + 1)) h →
        ∀ W, (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∈ W → ratDiv (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) s h W ≠ 0 →
        pointIdeal O (flagProjPt Function.Embedding.some y w e φ φ' t k) ≤
          W.comap (rename (FieldNumbers.blockIncl Function.Embedding.some (bundleIdx (bundleIdx ι M) M')))) ∧
      (∀ (cs ch : Option (Option K) → ℕ) (s h : MRing (bundleIdx (bundleIdx ι M) M') O),
        IsMultiHomog s cs → IsMultiHomog h ch →
        (fun o => (cs o : ℤ) - ch o) = zetaSecond a₀' + liftPairDeg (x' ⟨k, hk⟩) →
        s ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) → h ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) →
        aeval (flagClosurePt y w e φ φ' t (k + 1)) s = flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ * aeval (flagClosurePt y w e φ φ' t (k + 1)) h →
        ∀ W, (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∈ W → ratDiv (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) s h W ≠ 0 →
        pointIdeal O (flagProjPt secondFactorBlocks y w e φ φ' t k) ≤
          W.comap (rename (FieldNumbers.blockIncl secondFactorBlocks (bundleIdx (bundleIdx ι M) M'))))

def SegreFlagProjSpecialDim.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ k : ℕ, k < N →
      FieldNumbers.relDim (specialIdeal (pointIdeal O (flagProjPt Function.Embedding.some y w e φ φ' t k))) <
          ((d + k : ℕ) : WithBot (WithTop ℤ)) ∧
        FieldNumbers.relDim (specialIdeal (pointIdeal O (flagProjPt secondFactorBlocks y w e φ φ' t k))) <
          ((d + k : ℕ) : WithBot (WithTop ℤ))

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMoreMore
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

def VerticalDivisorFibreVariety.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O P d →
    ∀ (b : K → ℤ) (f g : MRing ι O), IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O P b f g →
    ∀ W ∈ (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O P f g).support,
      ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W) d

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.FullFlag
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

open ReciprocityTheory.ChartRestriction.G.Geo

def FlagPair.fullFlag' (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type*} [Field Ω]
    [Algebra O Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {x : (Σ k, ι k) → Ω} {N : ℕ}
    {V : Type*} [AddCommGroup V] [Module Ω V] {E E' : ChartBundle O (mseg x) N V} (φ : FlagPair O x E E') :
    FullFlag O x E' where
  Vs := φ.Vs
  mono := φ.mono
  dim := φ.dim
  top := φ.top
  deg := φ.deg'
  gen := φ.gen'
  gen_mem := φ.gen'_mem
  frame := φ.frame'

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)

def FullFlagVerticalSymmetric.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (B : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d →
    ∀ (fl₁ fl₂ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FullFlag O x B)
      (I : IFamily (IsLocalRing.ResidueField O) ι), IsFieldIntersection I →
    ∀ G : MvPolynomial (Fin N) ℤ, G.IsSymmetric →
    ∀ (n : ℕ) (Y : Fin n → K → ℤ) (R : MvPolynomial (Fin n) ℤ) (b : K → ℤ) (f g : MRing ι O),
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) b f g →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O
                                (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I W d (Fin.append fl₁.deg Y)
                                  (rename (Fin.castAdd n) G * rename (Fin.natAdd N) R))
                                (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) f g) =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O
          (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I W d (Fin.append fl₂.deg Y)
            (rename (Fin.castAdd n) G * rename (Fin.natAdd N) R))
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) f g)

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SegreFlagCutChart.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ (k : ℕ) (hk : k < N) (W : Ideal (MRing (bundleIdx (bundleIdx ι M) M') O)),
      W.IsPrime → IsRelevant W → pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ≤ W →
      (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ W →
      ∃ (cl cm : Option (Option K) → ℕ) (l μ u : MRing (bundleIdx (bundleIdx ι M) M') O),
        IsMultiHomog l cl ∧ IsMultiHomog μ cm ∧
        (fun o => (cl o : ℤ) - cm o) = zetaSecond a₀' + liftPairDeg (x' ⟨k, hk⟩) ∧
        μ ∉ W ∧ u ∉ W ∧
        aeval (flagClosurePt y w e φ φ' t (k + 1)) l =
          flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ * aeval (flagClosurePt y w e φ φ' t (k + 1)) μ ∧
        (k = 0 → l ∉ W) ∧
        (0 < k → ∀ q ∈ pointIdeal O (flagClosurePt y w e φ φ' t k), ∃ n : ℕ,
          u ^ n * q ∈ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ⊔ Ideal.span {l})

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
