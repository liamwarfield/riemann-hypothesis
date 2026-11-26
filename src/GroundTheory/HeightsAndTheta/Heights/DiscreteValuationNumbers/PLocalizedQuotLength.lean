module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreDegree
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.WithBotLtNatCastOfAddOneLe
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemDivSuppOfDivCycleNeZero
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemMinimalPrimesIff

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalizedQuotLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

private theorem length_self_eq_of_ringEquiv' {S T : Type*} [CommRing S] [CommRing T] (e : S ≃+* T) :
    Module.length S S = Module.length T T := by
  rw [Module.length_eq_coheight, Module.length_eq_coheight]
  have := Ideal.coheight_comap_of_surjective (e : S →+* T) e.surjective ⊥
  have hb : Ideal.comap (e : S →+* T) ⊥ = ⊥ := Ideal.comap_bot_of_injective _ e.injective
  rw [hb] at this
  exact this

private theorem length_localizedModule_quot' {R : Type*} [CommRing R] (J W : Ideal R) [W.IsPrime] :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J)) =
      Module.length (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
        (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) := by
  let S := Localization.AtPrime W
  have hJ : (J : Submodule R R).localized' S W.primeCompl (Algebra.linearMap R S) =
      J.map (algebraMap R S) := by
    rw [Submodule.localized'_eq_span, Ideal.map]
    rfl
  let e := (IsLocalizedModule.linearEquiv W.primeCompl
    ((J : Submodule R R).toLocalizedQuotient' S W.primeCompl (Algebra.linearMap R S))
    (LocalizedModule.mkLinearMap W.primeCompl (R ⧸ J))).extendScalarsOfIsLocalization W.primeCompl S
  rw [← e.length_eq, (Submodule.quotEquivOfEq _ _ hJ).length_eq]
  exact Module.length_eq_of_surjective Ideal.Quotient.mk_surjective

theorem LocalizedQuotLength.proof : LocalizedQuotLength.Statement.{u} := by
  intro S _ P W₀ _ z
  set W := W₀.comap (Ideal.Quotient.mk P) with hWdef
  set A := Localization.AtPrime W₀
  set J := P ⊔ Ideal.span {z} with hJdef
  let ψ : Localization.AtPrime W →+* A := Localization.localRingHom W W₀ (Ideal.Quotient.mk P) rfl

  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective W₀.primeCompl x
    obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨t', ht'⟩ := Ideal.Quotient.mk_surjective (t : S ⧸ P)
    have hs : t' ∈ W.primeCompl := by
      intro h
      apply t.2
      rw [← ht']
      exact h
    refine ⟨IsLocalization.mk' _ a' ⟨t', hs⟩, ?_⟩
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext ht'

  have hker : Ideal.comap ψ ⊥ ≤ J.map (algebraMap S (Localization.AtPrime W)) := by
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective W.primeCompl x
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨⟨t, ht⟩, htr⟩ := hx
    obtain ⟨t', rfl⟩ := Ideal.Quotient.mk_surjective t
    have ht'W : t' ∈ W.primeCompl := ht
    have hmemP : t' * r ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
      exact htr
    have hrJ : algebraMap S (Localization.AtPrime W) r ∈ J.map (algebraMap S (Localization.AtPrime W)) := by
      rw [← Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units (Localization.AtPrime W) ⟨_, ht'W⟩),
        ← map_mul]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_left hmemP)
    show IsLocalization.mk' (Localization.AtPrime W) r s ∈ _
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ hrJ

  have hcomp : ψ.comp (algebraMap S (Localization.AtPrime W)) =
      (algebraMap (S ⧸ P) A).comp (Ideal.Quotient.mk P) :=
    RingHom.ext fun x => Localization.localRingHom_to_map W W₀ (Ideal.Quotient.mk P) rfl x
  have hJmk : J.map (Ideal.Quotient.mk P) = Ideal.span {Ideal.Quotient.mk P z} := by
    rw [hJdef, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span, Set.image_singleton]
  have hI : (J.map (algebraMap S (Localization.AtPrime W))).map ψ =
      Ideal.span {algebraMap (S ⧸ P) A (Ideal.Quotient.mk P z)} := by
    rw [Ideal.map_map, hcomp, ← Ideal.map_map, hJmk, Ideal.map_span, Set.image_singleton]
  let : CommRing A := inferInstance
  let g := (Ideal.Quotient.mk (Ideal.span {algebraMap (S ⧸ P) A (Ideal.Quotient.mk P z)})).comp ψ
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hψ
  have hgk : J.map (algebraMap S (Localization.AtPrime W)) = RingHom.ker g := by
    rw [← RingHom.comap_ker, Ideal.mk_ker, ← hI, Ideal.comap_map_of_surjective _ hψ, sup_eq_left.mpr hker]
  have key := length_self_eq_of_ringEquiv'
    ((Ideal.quotEquivOfEq hgk).trans (RingHom.quotientKerEquivOfSurjective hg))
  rw [length_localizedModule_quot', key]
  exact (Module.length_eq_of_surjective Ideal.Quotient.mk_surjective).symm

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpVerticalFibre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

section Helpers

theorem mem_map_iff_of_ker_le {A B : Type*} [CommRing A] [CommRing B] {f : A →+* B}
    (hf : Function.Surjective f) {I : Ideal A} (hI : RingHom.ker f ≤ I) (a : A) :
    f a ∈ I.map f ↔ a ∈ I := by
  rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective f hf, ← RingHom.ker_eq_comap_bot,
    sup_eq_left.mpr hI]

theorem contractPrime_specialIdeal {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {J : Type}
    (W' : Ideal (MRing (extIdx ι J) O)) (hϖW : (C ϖ : MRing (extIdx ι J) O) ∈ W') :
    (FieldNumbers.contractPrime Function.Embedding.some (specialIdeal W') :
        Ideal (MRing ι (IsLocalRing.ResidueField O))) =
      specialIdeal (W'.comap (liftForm (ι := ι) (J := J) (R := O))) := by
  have hres := IsLocalRing.residue_surjective (R := O)
  have hs : Function.Surjective
      (MvPolynomial.map (IsLocalRing.residue O) : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O)) :=
    MvPolynomial.map_surjective _ hres
  have hker' : RingHom.ker (MvPolynomial.map (IsLocalRing.residue O) :
      MRing (extIdx ι J) O →+* MRing (extIdx ι J) (IsLocalRing.ResidueField O)) ≤ W' := by
    rw [ker_map_residue_eq_span hϖ, Ideal.span_le, Set.singleton_subset_iff]
    exact hϖW
  have hker : RingHom.ker (MvPolynomial.map (IsLocalRing.residue O) :
      MRing ι O →+* MRing ι (IsLocalRing.ResidueField O)) ≤
        W'.comap (liftForm (ι := ι) (J := J) (R := O)) := by
    rw [ker_map_residue_eq_span hϖ, Ideal.span_le, Set.singleton_subset_iff]
    change liftForm (J := J) (C ϖ : MRing ι O) ∈ W'
    rw [liftForm_C]
    exact hϖW
  ext y
  obtain ⟨z, rfl⟩ := hs y
  have e : rename (FieldNumbers.blockIncl Function.Embedding.some (extIdx ι J))
      (MvPolynomial.map (IsLocalRing.residue O) z) =
      MvPolynomial.map (IsLocalRing.residue O) (liftForm (J := J) z) :=
    (map_rename (IsLocalRing.residue O) _ z).symm
  refine Iff.trans ?_ (mem_map_iff_of_ker_le hs hker z).symm
  refine Iff.trans ?_ (mem_map_iff_of_ker_le (MvPolynomial.map_surjective _ hres) hker' (liftForm z))
  exact Iff.of_eq (congrArg (· ∈ specialIdeal W') e)

theorem relDim_eq_of_dim {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
    (I : Ideal (MRing ι F)) (m : ℕ)
    (h : ringKrullDim (MRing ι F ⧸ I) = ((m + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    FieldNumbers.relDim I = (m : WithBot (WithTop ℤ)) := by
  rw [FieldNumbers.relDim, h]
  have : (((m + Fintype.card K : ℕ) : ℤ) - Fintype.card K) = m := by push_cast; ring
  exact congrArg (fun z : ℤ => ((z : WithTop ℤ) : WithBot (WithTop ℤ))) this

theorem relDim_lt_of_dim_lt {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {F : Type*}
    [Field F] (I : Ideal (MRing ι F)) (m : ℕ)
    (h : ringKrullDim (MRing ι F ⧸ I) < ((m + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    FieldNumbers.relDim I < (m : WithBot (WithTop ℤ)) := by
  unfold FieldNumbers.relDim
  generalize ringKrullDim (MRing ι F ⧸ I) = x at h ⊢
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe y =>
    induction y using ENat.recTopCoe with
    | top => exact absurd h (by simp)
    | coe e =>
      have he : e < m + Fintype.card K := by exact_mod_cast h
      show (((e : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) < (((m : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))
      exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by omega))

theorem lt_of_two_drops {x y : WithBot ℕ∞} {N : ℕ} (h1 : x + 1 ≤ y)
    (h2 : y + 1 ≤ ((N + 1 : ℕ) : WithBot ℕ∞)) : x < (N : WithBot ℕ∞) := by
  have hy := withBot_lt_natCast_of_add_one_le y (N + 1) h2
  have hx : x + 1 < ((N + 1 : ℕ) : WithBot ℕ∞) := lt_of_le_of_lt h1 hy
  have hx' : x + 1 ≤ (N : WithBot ℕ∞) := by
    induction x using WithBot.recBotCoe with
    | bot => simp
    | coe a =>
      induction a using ENat.recTopCoe with
      | top =>
        exfalso
        have h3 : ((⊤ : ℕ∞) + 1 : ℕ∞) < ((N + 1 : ℕ) : ℕ∞) := by exact_mod_cast hx
        simp at h3
      | coe a =>
        have : a + 1 < N + 1 := by exact_mod_cast hx
        exact_mod_cast (by omega : a + 1 ≤ N)
  exact withBot_lt_natCast_of_add_one_le x N hx'

end Helpers

theorem BlowUpVerticalFibre.proof (hmodel : BlowUpModel.Statement.{u})
    (hdeg : BlowUpFibreDegree.Statement.{u})
    (hpf : FieldNumbers.ProjectionFormulaDegree.Statement.{u}) :
    BlowUpVerticalFibre.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP a W hϖW
  classical
  have hB : IsModelOver (blowUpOf P u) n := hmodel O K ι J P n hP N u hu hu'
  have hxB : liftForm (J := J) x ∉ blowUpOf P u := liftForm_not_mem_blowUpOf hxP
  have hxl : IsMultiHomog (liftForm (J := J) x) (liftMDeg c) := isMultiHomog_liftForm hx
  have hl : liftDegs a = fun i => FieldNumbers.pullDeg Function.Embedding.some (a i) := by
    funext i
    exact FlagBundlePullbackVanish.liftDeg_eq_pullDeg (a i)

  have key : ∀ W' : Ideal (MRing (extIdx ι J) O), divCycle (blowUpOf P u) (liftForm x) W' ≠ 0 →
      W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W →
      IsMultiProjPrime (specialIdeal W') ∧ FieldNumbers.relDim (specialIdeal W') = (n : ℕ) ∧
        (FieldNumbers.contractPrime Function.Embedding.some (specialIdeal W') :
          Ideal (MRing ι (IsLocalRing.ResidueField O))) = specialIdeal W := by
    intro W' hW' hcomap
    obtain ⟨hWp, hWrel, -, hWh⟩ := divCycle_ne_zero_facts hB.multiProj.multiHomog hxl hW'
    have hϖ' : (C ϖ : MRing (extIdx ι J) O) ∈ W' := by
      rw [← hcomap, Ideal.mem_comap, liftForm_C] at hϖW
      exact hϖW
    obtain ⟨hsp, -, hrel, -⟩ :=
      SpecialIdealCorresp.proof O ϖ hϖ (Option K) (extIdx ι J) (blowUpOf P u) W' hWp hϖ'
    refine ⟨⟨hsp, SpecialIdealMultiHomog.proof O (Option K) (extIdx ι J) W' hWh, hrel.mp hWrel⟩, ?_, ?_⟩
    · apply relDim_eq_of_dim
      rw [SpecialQuotDim.proof O ϖ hϖ (Option K) (extIdx ι J) W' hϖ',
        ComponentDim.proof O ϖ hϖ (Option K) (extIdx ι J) (blowUpOf P u) n hB (liftMDeg c) _ hxl hxB
          W' hW' hϖ']
    · rw [← hcomap]
      exact contractPrime_specialIdeal hϖ W' hϖ'
  by_cases hW : divCycle P x W ≠ 0
  ·
    have hdimW : FieldNumbers.relDim (specialIdeal W) = (n : ℕ) := by
      apply relDim_eq_of_dim
      rw [SpecialQuotDim.proof O ϖ hϖ K ι W hϖW, ComponentDim.proof O ϖ hϖ K ι P n hP c x hx hxP W hW hϖW]
    have hterm : ∀ W' : Ideal (MRing (extIdx ι J) O),
        (if W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W then
          divCycle (blowUpOf P u) (liftForm x) W' * vNum W' (liftDegs a) else 0) =
        (if W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W then
          divCycle (blowUpOf P u) (liftForm x) W' * (specialRelDeg W' : ℤ) else 0) * vNum W a := by
      intro W'
      split_ifs with h1
      · by_cases h0 : divCycle (blowUpOf P u) (liftForm x) W' = 0
        · simp [h0]
        obtain ⟨hmp, hrd, hcon⟩ := key W' h0 h1
        have hpf' := (hpf (IsLocalRing.ResidueField O) K (Option K) Function.Embedding.some (extIdx ι J)
          (specialIdeal W') hmp n hrd (by rw [hcon]; exact hdimW) a).2
        rw [mul_assoc]
        congr 1
        unfold vNum specialRelDeg
        rw [dite_eq_left hmp.isPrime, hl, hpf', hcon]
        rfl
      · simp
    rw [finsum_congr hterm, ← finsum_mul, hdeg O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hW]
  ·
    rw [not_not] at hW
    rw [hW, zero_mul]
    refine finsum_eq_zero_of_forall_eq_zero fun W' => ?_
    split_ifs with h1
    · by_cases h0 : divCycle (blowUpOf P u) (liftForm x) W' = 0
      · rw [h0, zero_mul]
      obtain ⟨hmp, hrd, hcon⟩ := key W' h0 h1
      obtain ⟨hWmin', hWrel'⟩ :
          W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes ∧ IsRelevant W' := by
        by_contra hc
        exact h0 (by unfold divCycle; rw [dite_eq_right hc])
      obtain ⟨hWp, hPW, hWrel, -⟩ := comap_liftForm_facts hWmin'.1.1
        (le_sup_left.trans hWmin'.1.2) hWrel'
      rw [h1] at hWp hPW hWrel
      have hxW : x ∈ W := by
        rw [← h1, Ideal.mem_comap]
        exact hWmin'.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
      have hJW : P ⊔ Ideal.span {x} ≤ W := sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hxW)

      have hnmin : W ∉ (P ⊔ Ideal.span {x}).minimalPrimes := by
        intro hWmin
        refine (show divCycle P x W ≠ 0 from ?_) hW
        unfold divCycle
        rw [dite_eq_left ⟨hWmin, hWrel⟩]
        have := localizedQuot_nontrivial_of_le (P ⊔ Ideal.span {x}) W hJW
        have h0 : multAt (P ⊔ Ideal.span {x}) W ≠ 0 :=
          (Module.length_pos (R := Localization.AtPrime W)
            (M := LocalizedModule W.primeCompl (MRing ι O ⧸ (P ⊔ Ideal.span {x})))).ne'
        have htop := length_localizedQuot_ne_top _ W hWmin
        exact_mod_cast (ENat.toNat_pos h0 htop).ne'
      obtain ⟨Q, hQ, hQW⟩ := Ideal.exists_minimalPrimes_le hJW
      have hQp : Q.IsPrime := hQ.1.1
      have hQW' : Q < W := lt_of_le_of_ne hQW (fun h => hnmin (h ▸ hQ))
      have hPQ : P < Q := lt_of_le_of_ne (le_sup_left.trans hQ.1.2) (fun h =>
        hxP (h ▸ hQ.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))))
      have := hP.multiProj.isPrime
      have hd1 := DimStrictDrop.proof (MRing ι O) Q W hQW'
      have hd2 := DimStrictDrop.proof (MRing ι O) P Q hPQ
      rw [hP.dim, show n + 1 + Fintype.card K = (n + Fintype.card K) + 1 by omega] at hd2
      have hlt := lt_of_two_drops hd1 hd2
      have hltW : FieldNumbers.relDim (specialIdeal W) < ((n : ℕ) : WithBot (WithTop ℤ)) :=
        relDim_lt_of_dim_lt _ _ (by rw [SpecialQuotDim.proof O ϖ hϖ K ι W hϖW]; exact hlt)
      have hz := FieldNumbers.ProjectionFormulaContracted.full (IsLocalRing.ResidueField O) K (Option K)
        Function.Embedding.some (extIdx ι J) (specialIdeal W') hmp n hrd (by rw [hcon]; exact hltW) a
      unfold vNum
      rw [hl, hz, mul_zero]
    · rfl

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocCycleSpanMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

theorem LocCycleSpanMul.mem_minimalPrimes_iff {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {z : A} (hz : z ≠ 0) (W : Ideal A) :
    W ∈ (Ideal.span {z}).minimalPrimes ↔ W.IsPrime ∧ W.height = 1 ∧ z ∈ W :=
  _root_.UpperTheory.Reformulated.B.Yhd1.mem_minimalPrimes_iff hz W

theorem LocCycleSpanMul.proof : LocCycleSpanMul.Statement := by
  intro A _ _ _ x y hx hy W
  by_cases hP : W.IsPrime ∧ W.height = 1
  · obtain ⟨hp, h1⟩ := hP
    have key : ∀ z : A, z ≠ 0 →
        locCycle (Ideal.span {z}) W = ((locLen (A ⧸ Ideal.span {z}) ⟨W, hp⟩).toNat : ℤ) ∧
          locLen (A ⧸ Ideal.span {z}) ⟨W, hp⟩ ≠ ⊤ := by
      intro z hz
      by_cases hzW : z ∈ W
      · have hm : W ∈ (Ideal.span {z}).minimalPrimes :=
          (LocCycleSpanMul.mem_minimalPrimes_iff hz W).mpr ⟨hp, h1, hzW⟩
        refine ⟨?_, locLen_ne_top hm⟩
        unfold locCycle
        rw [dite_eq_left hm]
        rfl
      · have hm : W ∉ (Ideal.span {z}).minimalPrimes := fun h =>
          hzW ((LocCycleSpanMul.mem_minimalPrimes_iff hz W).mp h).2.2
        have h0 : locLen (A ⧸ Ideal.span {z}) ⟨W, hp⟩ = 0 := by
          have := locLen_quot_eq_zero (V := (⊥ : Ideal A)) (g := z) ⟨W, hp⟩ hzW
          rwa [bot_sup_eq] at this
        refine ⟨?_, by rw [h0]; exact ENat.zero_ne_top⟩
        unfold locCycle
        rw [dite_eq_right hm, h0]
        simp
    obtain ⟨ex, fx⟩ := key x hx
    obtain ⟨ey, fy⟩ := key y hy
    obtain ⟨exy, -⟩ := key (x * y) (mul_ne_zero hx hy)
    have hmul := locLen_mul (V := (⊥ : Ideal A)) Ideal.isPrime_bot (f := x)
      (by rw [Ideal.mem_bot]; exact hx) y ⟨W, hp⟩
    rw [bot_sup_eq, bot_sup_eq, bot_sup_eq] at hmul
    rw [exy, ex, ey, hmul, ENat.toNat_add fy fx]
    push_cast
    ring
  · have hz : ∀ z : A, z ≠ 0 → locCycle (Ideal.span {z}) W = 0 := by
      intro z hz
      unfold locCycle
      rw [dite_eq_right]
      intro hm
      have h := (LocCycleSpanMul.mem_minimalPrimes_iff hz W).mp hm
      exact hP ⟨h.1, h.2.1⟩
    rw [hz _ (mul_ne_zero hx hy), hz x hx, hz y hy]
    simp

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem LeftSideAdditiveInDegree.proof
    (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ)
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι O)) (d : ℕ) (hP : IsModelOver P (d + 1))
    (b : K → ℤ) (f g : MRing ι O) (hD : IsVerticalDivisor P ϖ b f g)
    (c₁ c₂ : K → ℕ) (L : Fin d → K → ℤ) :
    cutIdentityLeftSide P f g (c₁ + c₂) L =
      cutIdentityLeftSide P f g c₁ L + cutIdentityLeftSide P f g c₂ L := by
  obtain ⟨bf, bg, hbf, hbg, -⟩ := hD.degrees
  have hPmh : IsMultiHomogIdeal P := hP.multiProj.multiHomog
  have : P.IsPrime := hP.multiProj.isPrime
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have h' : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hP.noTorsion, Ideal.mem_bot] at h'
    exact hϖ.ne_zero h'

  have hmh : ∀ (h : MRing ι O) (e : K → ℕ), IsMultiHomog h e → ∀ W, divCycle P h W ≠ 0 →
      IsMultiHomogIdeal W ∧ W.IsPrime ∧ P ≤ W := by
    intro h e he W hW
    unfold divCycle at hW
    split_ifs at hW with hW'
    · exact ⟨MinimalPrimeMultiHomog.full O K ι _ W (SupSpanMultiHomog.full O K ι P h e hPmh he) hW'.1,
        hW'.1.1.1, le_sup_left.trans hW'.1.1.2⟩
    · exact absurd rfl hW

  have hadd : ∀ W, ratDiv P f g W ≠ 0 →
      vNum W (Matrix.vecCons (fun k => ((c₁ + c₂) k : ℤ)) L) =
        vNum W (Matrix.vecCons (fun k => (c₁ k : ℤ)) L) +
          vNum W (Matrix.vecCons (fun k => (c₂ k : ℤ)) L) := by
    intro W hW
    have hϖW : (C ϖ : MRing ι O) ∈ W := hD.vertical W hW
    obtain ⟨hWm, hWp, hPW⟩ : IsMultiHomogIdeal W ∧ W.IsPrime ∧ P ≤ W := by
      by_cases hWf : divCycle P f W = 0
      · exact hmh g bg hbg W fun hWg => hW (by simp [ratDiv, hWf, hWg])
      · exact hmh f bf hbf W hWf
    have hlt : P < W := lt_of_le_of_ne hPW (fun e => hϖP (e ▸ hϖW))
    have hdrop := DimStrictDrop.full (MRing ι O) P W hlt
    rw [hP.dim] at hdrop
    have hdim : ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) <
        ((d + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      rw [SpecialQuotDim.full O ϖ hϖ K ι W hϖW]
      have e : d + 1 + 1 + Fintype.card K = d + 2 + Fintype.card K := by omega
      rw [e] at hdrop
      exact lt_natCast_of_add_one_le hdrop
    have key := IntNumAddFirst.full (IsLocalRing.ResidueField O) K ι d (specialIdeal W)
      (SpecialIdealCorresp.full O ϖ hϖ K ι P W hWp hϖW).1 (SpecialIdealMultiHomog.full O K ι W hWm)
      hdim (fun k => (c₁ k : ℤ)) (fun k => (c₂ k : ℤ)) L
    have hsum : (fun k => ((c₁ + c₂) k : ℤ)) = (fun k => (c₁ k : ℤ)) + (fun k => (c₂ k : ℤ)) := by
      funext k; simp
    unfold vNum
    rw [hsum, key]
  have hZfin := ratDiv_support_finite DivCycleFiniteSupport.full P f g
  unfold cutIdentityLeftSide cycEval
  rw [← finsum_add_distrib (hZfin.subset (Function.support_mul_subset_left _ _))
    (hZfin.subset (Function.support_mul_subset_left _ _))]
  refine finsum_congr fun W => ?_
  by_cases hW : ratDiv P f g W = 0
  · simp [hW]
  · beta_reduce
    rw [hadd W hW, mul_add]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinRootPolyNum
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

namespace RootPolynomialNumber

variable {K : Type} [DecidableEq K] {ι : K → Type}
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem classNum_rename_mul {N q : ℕ} (x : Fin N → K → ℤ) (L : Fin q → K → ℤ)
    (G : MvPolynomial (Fin N) ℤ) (Q : MvPolynomial (Fin q) ℤ) (W : Ideal (MRing ι O)) :
    classNum (Sum.elim x L) (rename Sum.inl G * rename Sum.inr Q) [] W =
      ∑ μ ∈ Q.support, Q.coeff μ * classNum x G (classList L μ) W := by
  classical
  have hQ : rename Sum.inl G * rename Sum.inr Q =
      ∑ μ ∈ Q.support, Q.coeff μ •
        (rename Sum.inl G * monomial (Finsupp.mapDomain Sum.inr μ) (1 : ℤ)) := by
    conv_lhs => rw [Q.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [rename_monomial, ← C_mul', ← mul_one (Q.coeff μ), ← C_mul_monomial, mul_one]
    ring
  change classNumAddHom (Sum.elim x L) [] W _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hQ, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_zsmul, smul_eq_mul]
  congr 1
  change classNum (Sum.elim x L) _ [] W = _
  rw [plainPairNumber.classNum_mul_monomial, plainPairNumber.classNum_rename _ Sum.inl_injective,
    classList_mapDomain, List.append_nil, Sum.elim_comp_inl, Sum.elim_comp_inr]

end RootPolynomialNumber

theorem RootPolynomialNumber.proof : RootPolynomialNumber.Statement := by
  intro O _ _ _ K _ _ ι _ P d N x c G hG hc q L Q hQ a
  classical
  have hH : (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q).IsHomogeneous d := by
    have h := (hG.rename_isHomogeneous (f := Fin.castAdd q)).mul
      (hQ.rename_isHomogeneous (f := Fin.natAdd N))
    rwa [show c + (d - c) = d by omega] at h
  have hcls : Sum.elim x L ∘ (finSumFinEquiv.symm : Fin (N + q) ≃ Fin N ⊕ Fin q) =
      Fin.append x L := by
    funext i
    induction i using Fin.addCases <;> simp
  have hren : rename (finSumFinEquiv.symm : Fin (N + q) ≃ Fin N ⊕ Fin q)
      (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q) =
        rename Sum.inl G * rename Sum.inr Q := by
    have e1 : (finSumFinEquiv.symm : Fin (N + q) ≃ Fin N ⊕ Fin q) ∘ Fin.castAdd q = Sum.inl := by
      funext i
      simp
    have e2 : (finSumFinEquiv.symm : Fin (N + q) ≃ Fin N ⊕ Fin q) ∘ Fin.natAdd N = Sum.inr := by
      funext i
      simp
    rw [map_mul, rename_rename, rename_rename, e1, e2]
  have hZ : ⇑(Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero
      (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (C a))) = divCycle P (C a) := by
    funext W
    simp [FlagTypings.divCycle_eq]
  have hW : ∀ W : Ideal (MRing ι O),
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs)
                                (specialIdeal W) d (Fin.append x L) (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q) =
        ∑ μ ∈ Q.support, Q.coeff μ * classNum x G (classList L μ) W := by
    intro W
    rw [BundleExamples.polyNum_eq_classNum (Fin.append x L) finSumFinEquiv.symm (Sum.elim x L) hcls hH W,
      hren, RootPolynomialNumber.classNum_rename_mul]
  rw [BundleExamples.vEval_eq, hZ]
  simp only [hW]
  have hfin : (Function.support (divCycle P (C a))).Finite := by
    rw [← hZ, Finsupp.fun_support_eq]
    exact Finset.finite_toSet _
  rw [cycEval_eq_sum hfin]
  simp only [cycEval_eq_sum hfin, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun W _ => ?_
  ring

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocalCoeffLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.AI

universe u

theorem mem_minimalPrimes_of_locCycle_ne_zero' {S : Type*} [CommRing S] {J W : Ideal S}
    (h : locCycle J W ≠ 0) : W ∈ J.minimalPrimes := by
  by_contra hc
  exact h (by unfold locCycle; rw [dite_eq_right hc])

theorem LocalCoeffLocal.proof (h₁ : LocCycleSpanMul.Statement.{u}) (h₂ : LocCyclePos.Statement.{u})
    (h₃ : MinimalPrimesSpanSingleton.Statement.{u}) (h₄ : LocalDomainDimTwo.Statement.{u})
    (h₅ : DimTwoSumReading.Statement.{u}) : LocalCoeffLocal.Statement.{u} := by
  intro A _ _ _ _ hchain f g s u v hf hg hs hu huv hno

  have hv : v ≠ 0 := by
    rintro rfl
    rw [zero_mul] at huv
    exact hf ((IsUnit.mul_right_eq_zero hu).mp huv)
  have hspan : Ideal.span {f} = Ideal.span {v * g} := by
    rw [← huv]
    exact (Ideal.span_singleton_mul_left_unit hu f).symm
  have hcolon : (Ideal.span {f}).colon {g} = Ideal.span {v} := by
    ext x
    rw [hspan, Submodule.mem_colon_singleton, smul_eq_mul, Ideal.mem_span_singleton,
      Ideal.mem_span_singleton, mul_dvd_mul_iff_right hg]
  have hadd : ∀ W : Ideal A, locCycle (Ideal.span {f}) W =
      locCycle (Ideal.span {v}) W + locCycle (Ideal.span {g}) W := by
    intro W
    rw [hspan]
    exact h₁ A v g hv hg W

  have hmin1 : ∀ x : A, x ≠ 0 → ∀ W : Ideal A, locCycle (Ideal.span {x}) W ≠ 0 →
      W.IsPrime ∧ W.height = 1 ∧ x ∈ W :=
    fun x hx W h => (h₃ A x hx W).mp (mem_minimalPrimes_of_locCycle_ne_zero' h)
  have hpos : ∀ x : A, x ≠ 0 → ∀ p : Ideal A, p.IsPrime → p.height = 1 → x ∈ p →
      locCycle (Ideal.span {x}) p ≠ 0 :=
    fun x hx p hp h1 hxp => (h₂ A _ p ((h₃ A x hx p).mpr ⟨hp, h1, hxp⟩)).ne'

  have nb : ∀ p : Ideal A, p.IsPrime → p.height = 1 → v ∈ p → s ∉ p := by
    intro p hp h1 hvp hsp
    have e := hno p (hpos s hs p hp h1 hsp)
    rw [hadd] at e
    exact hpos v hv p hp h1 hvp (by omega)
  have hne : ∀ x : A, x ≠ 0 → ∀ p : Ideal A, x ∈ p → p ≠ ⊥ :=
    fun x hx p hxp h => hx (by rw [h] at hxp; exact (Submodule.mem_bot A).mp hxp)
  have hL : ∀ G : Ideal A, (locCycle (Ideal.span {f}) G - locCycle (Ideal.span {g}) G) *
      locCycle (G ⊔ Ideal.span {s}) (IsLocalRing.maximalIdeal A) =
      locCycle (Ideal.span {v}) G * locCycle (G ⊔ Ideal.span {s}) (IsLocalRing.maximalIdeal A) := by
    intro G
    rw [hadd]
    ring
  rw [finsum_congr hL, hcolon]
  by_cases hQ : ∃ Q : Ideal A, Q.IsPrime ∧ ⊥ < Q ∧ Q < IsLocalRing.maximalIdeal A
  ·
    obtain ⟨hd, -, hht⟩ := h₄ A hchain hQ
    obtain ⟨n₁, e₁, e₁'⟩ := h₅ A hd v s hv nb
    obtain ⟨n₂, e₂, e₂'⟩ := h₅ A hd s v hs (fun p hp h1 hsp hvp => nb p hp h1 hvp hsp)
    have hlen : Module.length A (A ⧸ Ideal.span {v, s}) ≠ ⊤ := by
      by_cases hvs : Ideal.span {v, s} = ⊤
      · have : Subsingleton (A ⧸ Ideal.span {v, s}) := Ideal.Quotient.subsingleton_iff.mpr hvs
        rw [Module.length_eq_zero]
        exact ENat.zero_ne_top
      · have hvm : v ∈ Ideal.span {v, s} := Ideal.subset_span (Set.mem_insert _ _)
        have hsm : s ∈ Ideal.span {v, s} := Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
        have hI : IsLocalRing.maximalIdeal A ∈ (Ideal.span {v, s}).minimalPrimes := by
          refine ⟨⟨inferInstance, IsLocalRing.le_maximalIdeal hvs⟩, fun Q hQ' hQm => ?_⟩
          obtain ⟨hQp, hQI⟩ := hQ'
          by_contra hmQ
          have hlt : Q < IsLocalRing.maximalIdeal A := lt_of_le_of_ne hQm fun h => hmQ h.ge
          have h0 : ⊥ < Q := bot_lt_iff_ne_bot.mpr (hne v hv Q (hQI hvm))
          exact nb Q hQp (hht Q hQp h0 hlt) (hQI hvm) (hQI hsm)
        have : IsArtinianRing (A ⧸ Ideal.span {v, s}) :=
          IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hI
        have : IsArtinian A (A ⧸ Ideal.span {v, s}) :=
          isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := Ideal.span {v, s}))
        exact Module.length_ne_top
    have key := (lengthFormulaDimTwo A v s hd hv hs hlen).2.2
    rw [e₁', e₂'] at key
    rw [e₁, e₂, Nat.cast_inj.mp key]
  ·
    have hQ' : ∀ Q : Ideal A, Q.IsPrime → Q ≠ ⊥ → Q = IsLocalRing.maximalIdeal A := by
      intro Q hQp h0
      by_contra hQm
      exact hQ ⟨Q, hQp, bot_lt_iff_ne_bot.mpr h0,
        lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hQp.ne_top) hQm⟩
    have zl : ∀ G : Ideal A, locCycle (Ideal.span {v}) G *
        locCycle (G ⊔ Ideal.span {s}) (IsLocalRing.maximalIdeal A) = 0 := by
      intro G
      by_contra h
      obtain ⟨hGp, hG1, hvG⟩ := hmin1 v hv G (left_ne_zero_of_mul h)
      have hGm := hQ' G hGp (hne v hv G hvG)
      have hsG : s ∈ G := by
        have h' := (mem_minimalPrimes_of_locCycle_ne_zero' (right_ne_zero_of_mul h)).1.2
        rw [← hGm] at h'
        exact h' (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
      exact nb G hGp hG1 hvG hsG
    have zr : ∀ W : Ideal A, locCycle (Ideal.span {s}) W *
        locCycle (W ⊔ Ideal.span {v}) (IsLocalRing.maximalIdeal A) = 0 := by
      intro W
      by_contra h
      obtain ⟨hWp, hW1, hsW⟩ := hmin1 s hs W (left_ne_zero_of_mul h)
      have hWm := hQ' W hWp (hne s hs W hsW)
      have hvW : v ∈ W := by
        have h' := (mem_minimalPrimes_of_locCycle_ne_zero' (right_ne_zero_of_mul h)).1.2
        rw [← hWm] at h'
        exact h' (Ideal.mem_sup_right (Ideal.mem_span_singleton_self v))
      exact nb W hWp hW1 hvW hsW
    rw [(finsum_congr zl).trans finsum_zero, (finsum_congr zr).trans finsum_zero]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHorizontalComponentModel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

universe u

theorem sup_span_C_ne_top_of_multiHomog {O : Type*} [CommRing O] {K : Type} [DecidableEq K]
    (ι : K → Type) {W : Ideal (MRing ι O)} (hW : IsMultiHomogIdeal W)
    (h0 : W.comap (C : O →+* MRing ι O) = ⊥) {ϖ : O} (hϖ : ¬ IsUnit ϖ) :
    W ⊔ Ideal.span {(C ϖ : MRing ι O)} ≠ ⊤ := by
  intro htop
  have h1 : (1 : MRing ι O) ∈ W ⊔ Ideal.span {(C ϖ : MRing ι O)} := htop ▸ Submodule.mem_top
  obtain ⟨w, hw, t, ht, hwt⟩ := Submodule.mem_sup.mp h1
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp ht
  have hw0 : (C (AddMonoidAlgebra.coeff w 0) : MRing ι O) ∈ W := by
    have h := hW w hw 0
    rwa [weightedHomogeneousComponent_zero] at h
    intro v hv
    have := congrFun hv v.1
    simp [blockWeight] at this
  have hc : AddMonoidAlgebra.coeff w 0 = 0 := by
    have h : AddMonoidAlgebra.coeff w 0 ∈ W.comap (C : O →+* MRing ι O) := hw0
    rw [h0] at h
    exact h
  have h2 := congrArg (AddMonoidAlgebra.coeff · 0) hwt
  rw [MvPolynomial.coeff_add, mul_comm s, coeff_C_mul, hc, zero_add, coeff_zero_one] at h2
  exact hϖ (isUnit_iff_exists_inv.mpr ⟨_, h2⟩)

theorem ringKrullDim_quotient_eq_of_minimalPrime_of_sup_ne_top {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P W : Ideal (MRing ι O)} [P.IsPrime] {f : MRing ι O} (hfP : f ∉ P)
    (hWmin : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes)
    (hWϖ : W ⊔ Ideal.span {(C ϖ : MRing ι O)} ≠ ⊤) (N : ℕ)
    (hdim : ringKrullDim (MRing ι O ⧸ P) = ((N + 1 : ℕ) : WithBot ℕ∞)) :
    ringKrullDim (MRing ι O ⧸ W) = (N : WithBot ℕ∞) := by
  have hWp : W.IsPrime := hWmin.1.1
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2
  have hfW : f ∈ W := hWmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  have hup := ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_dim_add_one_le hPW hfW hfP

  have hq : W.map (Ideal.Quotient.mk P) ∈ (Ideal.span {Ideal.Quotient.mk P f}).minimalPrimes := by
    have e : Ideal.span {Ideal.Quotient.mk P f} = (Ideal.span {f}).map (Ideal.Quotient.mk P) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [e, Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_comm]
    exact ⟨W, hWmin, rfl⟩
  have : (W.map (Ideal.Quotient.mk P)).IsPrime := hq.1.1
  have : (Ideal.span {Ideal.Quotient.mk P f}).IsPrincipal := ⟨⟨_, rfl⟩⟩
  have hk : (W.map (Ideal.Quotient.mk P)).height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hq

  obtain ⟨m, hm, hWm'⟩ := Ideal.exists_le_maximal _ hWϖ
  have hWm : W ≤ m := le_sup_left.trans hWm'
  have : m.IsPrime := hm.isPrime
  have hmge := le_height_of_isMaximal_of_uniformiser_mem hϖ m hm
    (hWm' (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  have hdimS := ringKrullDim_mvPolynomial_dvr (σ := Σ k, ι k) O
  have hfin : FiniteRingKrullDim (MRing ι O) := by
    rw [finiteRingKrullDim_iff_ne_bot_and_top, hdimS]
    exact ⟨by rw [← WithBot.coe_natCast]; exact WithBot.coe_ne_bot, by
      rw [← WithBot.coe_natCast]
      exact ne_of_lt (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _))⟩
  have hmax : ∀ m' : Ideal (MRing ι O), m'.IsMaximal →
      m'.height ≤ ((Nat.card (Σ k, ι k) + 1 : ℕ) : ℕ∞) := by
    intro m' hm'
    have := Ideal.height_le_ringKrullDim_of_ne_top hm'.ne_top
    rw [hdimS] at this
    exact_mod_cast this
  have hmeq : m.height = ((Nat.card (Σ k, ι k) + 1 : ℕ) : ℕ∞) := le_antisymm (hmax m hm) hmge

  have hcat1 := DimF.height_eq_height_add_of_isRegularRing P W hPW
  have hcat2 := DimF.height_eq_height_add_of_isRegularRing W m hWm
  have hsum : P.height + (W.map (Ideal.Quotient.mk P)).height + (m.map (Ideal.Quotient.mk W)).height
      = ((Nat.card (Σ k, ι k) + 1 : ℕ) : ℕ∞) := by
    rw [← hcat1, ← hcat2, hmeq]
  have hPfin : P.height ≠ ⊤ := fun h => by
    simp only [h, top_add] at hsum; exact ENat.top_ne_natCast _ hsum
  have hafin : (W.map (Ideal.Quotient.mk P)).height ≠ ⊤ := fun h => by
    simp only [h, top_add, add_top] at hsum; exact ENat.top_ne_natCast _ hsum
  have hbfin : (m.map (Ideal.Quotient.mk W)).height ≠ ⊤ := fun h => by
    simp only [h, add_top] at hsum; exact ENat.top_ne_natCast _ hsum
  obtain ⟨h0, hh0⟩ : ∃ h0 : ℕ, P.height = h0 := ⟨_, (ENat.natCast_toNat hPfin).symm⟩
  obtain ⟨a0, ha0⟩ : ∃ a0 : ℕ, (W.map (Ideal.Quotient.mk P)).height = a0 :=
    ⟨_, (ENat.natCast_toNat hafin).symm⟩
  obtain ⟨b0, hb0⟩ : ∃ b0 : ℕ, (m.map (Ideal.Quotient.mk W)).height = b0 :=
    ⟨_, (ENat.natCast_toNat hbfin).symm⟩
  rw [hh0, ha0, hb0] at hsum
  rw [ha0] at hk
  have hsum' : h0 + a0 + b0 = Nat.card (Σ k, ι k) + 1 := by exact_mod_cast hsum
  have hk' : a0 ≤ 1 := by exact_mod_cast hk

  have hPdim := ringKrullDim_quotient_le_sub_height P (Nat.card (Σ k, ι k) + 1) h0 hmax hh0
  rw [hdim] at hPdim
  have hPdim' : N + 1 ≤ Nat.card (Σ k, ι k) + 1 - h0 := by exact_mod_cast hPdim

  have hlow := Ideal.height_le_ringKrullDim_of_ne_top
    (DimF.isPrime_map_mk (A := MRing ι O) (q := W) (M := m) hWm).ne_top
  rw [hb0] at hlow
  have hb' : N ≤ b0 := by omega
  have hlow' : ((N : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι O ⧸ W) :=
    le_trans (by exact_mod_cast hb') hlow
  rw [hdim] at hup
  exact withBot_eq_of_le_of_add_one_le hlow' hup

theorem HorizontalComponentModel.proof : HorizontalComponentModel.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP c x hxc hxP W hW hϖW
  have hWd : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h
    · exact absurd rfl hW
  obtain ⟨hWmin, hrel⟩ := hWd
  have hWp : W.IsPrime := hWmin.1.1
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hWh : IsMultiHomogIdeal W :=
    MinimalPrimeMultiHomog.proof O K ι _ W
      (SupSpanMultiHomog.proof O K ι P x c hP.multiProj.multiHomog hxc) hWmin

  have h0 : W.comap (C : O →+* MRing ι O) = ⊥ := by
    by_contra hne
    have hmx : (W.comap (C : O →+* MRing ι O)).IsMaximal :=
      haveI : (W.comap (C : O →+* MRing ι O)).IsPrime := Ideal.IsPrime.comap _
      IsPrime.to_maximal_ideal hne
    have hϖm : ϖ ∈ W.comap (C : O →+* MRing ι O) := by
      rw [IsLocalRing.eq_maximalIdeal hmx]
      exact (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
    exact hϖW hϖm
  have hdim := ringKrullDim_quotient_eq_of_minimalPrime_of_sup_ne_top hϖ hxP hWmin
    (sup_span_C_ne_top_of_multiHomog ι hWh h0 hϖ.not_isUnit) (d + 1 + Fintype.card K)
    (by rw [hP.dim, show d + 1 + 1 + Fintype.card K = d + 1 + Fintype.card K + 1 by ring])
  exact ⟨⟨hWp, hWh, hrel⟩, h0, hdim⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
