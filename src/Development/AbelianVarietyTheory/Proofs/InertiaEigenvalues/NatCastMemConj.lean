module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmallCoeffFieldEmbeddingCompHostMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaChrTied
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDataLevelForms
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffPolynomialEqZeroOfVanishingOnGLFamily
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockHarmonicLatticeFgAndSpansValueSpace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRowsMap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameAtOfCongr
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TameConjPlace

open GlobalTheory.ExportSeries Formalism.L2.JoinChr

section Density

variable {E : Type} [Field E] [NumberField E]

theorem tameAt_of_congr (H : Formalism.L2.Host.HChar E) (PP : HeightOneSpectrum (𝓞 E))
    (hc : ∀ (a b : 𝓞 E) (ka kb : Eˣ), (ka : E) = (a : E) → (kb : E) = (b : E) → a ∉ PP.asIdeal →
      a - b ∈ PP.asIdeal → H.locK PP ka = H.locK PP kb) : H.TameAt PP := by
  have hone : ∀ k : Eˣ, PP.valuation E ((k : E) - 1) < 1 → H.locK PP k = 1 := by
    intro k hk
    have hv1 : PP.valuation E (k : E) = 1 := by
      have e : (k : E) = 1 + ((k : E) - 1) := by ring
      have h1 : PP.valuation E ((k : E) - 1) < PP.valuation E 1 := by rwa [map_one]
      rw [e]
      first
        | rw [Valuation.map_add_eq_of_lt_right _ h1, map_one]
        | rw [Valuation.map_add_eq_of_lt_left _ h1, map_one]
        | rw [add_comm, Valuation.map_add_eq_of_lt_right _ h1, map_one]
        | rw [add_comm, Valuation.map_add_eq_of_lt_left _ h1, map_one]
    obtain ⟨a, s, h⟩ := PP.exists_primeCompl_mul_eq_of_integer (k : E) hv1.le
    have hs : (s : 𝓞 E) ∉ PP.asIdeal := s.2
    have hsv := GlobalTheory.ChainOnto.TameRes.valuation_eq_one_of_not_mem PP _ hs
    have hav : PP.valuation E (algebraMap (𝓞 E) E a) = 1 := by
      rw [← h, map_mul, hv1, hsv, one_mul]
    have ha : a ∉ PP.asIdeal := by
      intro hm
      have hlt : PP.valuation E (algebraMap (𝓞 E) E a) < 1 :=
        (PP.valuation_lt_one_iff_mem (K := E) a).mpr hm
      exact absurd hav (ne_of_lt hlt)
    have hs0 : algebraMap (𝓞 E) E s ≠ 0 := fun h0 => by
      rw [h0, map_zero] at hsv; exact zero_ne_one hsv
    have ha0 : algebraMap (𝓞 E) E a ≠ 0 := fun h0 => by
      rw [h0, map_zero] at hav; exact zero_ne_one hav
    have hdiff : a - (s : 𝓞 E) ∈ PP.asIdeal := by
      apply (PP.valuation_lt_one_iff_mem (K := E) _).mp
      show PP.valuation E (algebraMap (𝓞 E) E (a - (s : 𝓞 E))) < 1
      rw [map_sub, ← h, ← sub_one_mul, map_mul, hsv, mul_one]
      exact hk
    let ka : Eˣ := Units.mk0 _ ha0
    let ks : Eˣ := Units.mk0 _ hs0
    have e1 : H.locK PP ka = H.locK PP ks := hc a (s : 𝓞 E) ka ks rfl rfl ha hdiff
    have hk' : k = ka * ks⁻¹ := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, ka, ks]
      rw [← h, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
    rw [hk', map_mul, map_inv, e1, mul_inv_cancel]
  unfold Formalism.L2.Host.HChar.TameAt Formalism.L2.Host.HChar.LevelLe
  intro x _ hx1
  by_contra hne
  have hcont : Continuous (H.loc PP) := H.2.1.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele PP)
  have hW : IsOpen {y : (PP.adicCompletion E)ˣ | H.loc PP y ≠ 1} := isOpen_ne_fun hcont continuous_const
  obtain ⟨T, hT, hTe⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hW
  have hlt : WithZero.exp (-((1 : ℕ) : ℤ)) < 1 := by
    rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by norm_num)
  have hxT : (x : PP.adicCompletion E) ∈ T ∩ {z | Valued.v (z - 1) < 1} := by
    refine ⟨?_, lt_of_le_of_lt hx1 hlt⟩
    have : x ∈ (Units.val ⁻¹' T : Set (PP.adicCompletion E)ˣ) := by rw [hTe]; exact hne
    exact this
  have hU : IsOpen (T ∩ {z : PP.adicCompletion E | Valued.v (z - 1) < 1}) :=
    hT.inter ((GlobalTheory.ChainOnto.TameRes.isOpen_ltOne PP).preimage (continuous_sub_right 1))
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap E PP).exists_mem_open hU ⟨_, hxT⟩
  have hk1 : PP.valuation E (k - 1) < 1 := by
    rw [← GlobalTheory.ChainOnto.TameRes.val_alg, map_sub, map_one]; exact hk.2
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk1
  have hloc := hone (Units.mk0 k hk0) hk1
  have hmem : Formalism.L2.Host.atFin PP (Units.mk0 k hk0) ∈ (Units.val ⁻¹' T : Set (PP.adicCompletion E)ˣ) := hk.1
  rw [hTe] at hmem
  exact hmem hloc

end Density

variable {D : D7}


set_option maxHeartbeats 800000 in
theorem chi_locE_congr (δ : Twist D Circle) (hδ : δ.Good) {PP : Pl D.host.E} (hPP : PP ∈ δ.Q) (a b : 𝓞 D.host.E)
    (ha : a ∉ PP.asIdeal) (hab : a - b ∈ PP.asIdeal) (x y : (AE D)ˣ)
    (hx : (x : AE D) = 1 + idemAt PP * (incA D (a : D.host.E) - 1))
    (hy : (y : AE D) = 1 + idemAt PP * (incA D (b : D.host.E) - 1)) : δ.chi x = δ.chi y := by
  have he := hδ.split.isIdemAt hPP
  have hee : idemAt PP * idemAt PP = idemAt PP := he.1.1
  obtain ⟨hi, h1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D _ PP he
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  have hma : (Ideal.Quotient.mk PP.asIdeal a : kP PP) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact ha
  let u : (kP PP)ˣ := Units.mk0 _ hma
  have key : ∀ (c : 𝓞 D.host.E) (z : (AE D)ˣ), (z : AE D) = 1 + idemAt PP * (incA D (c : D.host.E) - 1) →
      Ideal.Quotient.mk PP.asIdeal c = (u : kP PP) → δ.chi z = δ.res PP u := by
    intro c z hz hcu
    have hv : Formalism.IndefR.Datum.toEAf D (z : AE D) =
        ((1 + ⟨_, hi⟩ * (oToS D.host.F D.host.E c - 1) : Formalism.L2.Herm.intAf D.host.F D.host.E) : Formalism.IndefR.Datum.EAf D) := by
      have hb : Formalism.IndefR.Datum.toEAf D (incA D (c : D.host.E)) =
          ((oToS D.host.F D.host.E c : Formalism.L2.Herm.intAf D.host.F D.host.E) : Formalism.IndefR.Datum.EAf D) := rfl
      rw [hz, GlobalTheory.ConjTwist.map_loc, hb]
      rfl
    have hzi : Formalism.IndefR.Datum.toEAf D (z : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [hv]; exact Subtype.property _
    refine hδ.res PP hPP z ?_ hzi u ?_
    · rw [hz]; linear_combination (1 - incA D (c : D.host.E)) * hee
    · have e2 : (⟨_, hzi⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = 1 + ⟨_, hi⟩ * (oToS D.host.F D.host.E c - 1) :=
        Subtype.ext hv
      rw [e2, GlobalTheory.ConjTwist.map_loc, h1, resS_oToS, hcu]
      ring
  have hb : Ideal.Quotient.mk PP.asIdeal b = (u : kP PP) := by
    show Ideal.Quotient.mk PP.asIdeal b = Ideal.Quotient.mk PP.asIdeal a
    exact (Ideal.Quotient.eq.mpr hab).symm
  rw [key a x hx rfl, key b y hy hb]


set_option maxHeartbeats 800000 in
theorem locK_congr_conj (δ : Twist D Circle) (hδ : δ.Good) (χ : Formalism.L2.Host.HChar D.host.E) (hc : ChrEq δ.chi χ)
    {P' : Pl D.host.E} (hP' : P' ∈ δ.Q) {P : Pl D.host.E} (hPP : Formalism.IndefR.Lev.IsConjPl P' P)
    (a b : 𝓞 D.host.E) (ka kb : D.host.Eˣ) (hka : (ka : D.host.E) = (a : D.host.E)) (hkb : (kb : D.host.E) = (b : D.host.E))
    (ha : a ∉ P.asIdeal) (hab : a - b ∈ P.asIdeal) : χ.locK P ka = χ.locK P kb := by
  have he' := hδ.split.isIdemAt hP'
  have he : Formalism.L2.NTheta.IsIdemAt (cA D (idemAt P')) P :=
    (GlobalTheory.IdemSupport.supported_group_and_prime_idempotents D.sp.X').2.2.2 P' _ _ he' hPP
  have hee : cA D (idemAt P') * cA D (idemAt P') = cA D (idemAt P') := he.1.1
  have hcc : cA D (cA D (idemAt P')) = idemAt P' := GlobalTheory.MovedIdem.cA_cA _

  have step : ∀ (k : D.host.Eˣ) (c : 𝓞 D.host.E), (k : D.host.E) = star (c : D.host.E) →
      ∀ z : (AE D)ˣ, (z : AE D) = 1 + idemAt P' * (incA D (c : D.host.E) - 1) →
      ((χ.locK P k : ℂˣ) : ℂ) = ((δ.chi z : Circle) : ℂ)⁻¹ := by
    intro k c hk z hz
    let x := locU hee k
    have h1 : ((δ.chi x : Circle) : ℂ) = ((χ.locK P k : ℂˣ) : ℂ) :=
      hc.2 P _ (GlobalTheory.HeckeDetChar.isPlIdem he) k x (locU_val hee k)
    have hxz : cA D (x : AE D) = (z : AE D) := by
      rw [locU_val, locE, hz, RingHom.map_add (f := _), RingHom.map_one, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, hcc,
        GlobalTheory.MovedIdem.cA_incA, hk, star_star]
    have hfix : cA D ((x * z : (AE D)ˣ) : AE D) = ((x * z : (AE D)ˣ) : AE D) := by
      rw [Units.val_mul, RingHom.map_mul, hxz, ← hxz, GlobalTheory.MovedIdem.cA_cA, mul_comm]
    obtain ⟨α, hα⟩ := (GlobalTheory.DetRootRows.fixed_iff_idF (x * z)).1 hfix
    have h2 : δ.chi x * δ.chi z = 1 := by rw [← map_mul, ← hα, hδ.real]
    rw [← h1]
    have h3 : ((δ.chi x : Circle) : ℂ) * ((δ.chi z : Circle) : ℂ) = 1 := by
      rw [← Circle.coe_mul, h2, Circle.coe_one]
    exact eq_inv_of_mul_eq_one_left h3
  have hsym := GlobalTheory.ParahoricLift.isConjPl_symm hPP

  have hca : Formalism.L2.Col.cO _ a ∉ P'.asIdeal := by
    intro hm
    obtain ⟨c', hc', hc'e⟩ := hPP _ hm
    apply ha
    have : c' = a := RingOfIntegers.ext (by rw [hc'e]; exact star_star (a : D.host.E))
    rwa [← this]
  have hcab : Formalism.L2.Col.cO _ a - Formalism.L2.Col.cO _ b ∈ P'.asIdeal := by
    obtain ⟨c', hc', hc'e⟩ := hsym _ hab
    have : c' = Formalism.L2.Col.cO _ a - Formalism.L2.Col.cO _ b := RingOfIntegers.ext (by
      rw [hc'e]
      show star (((a - b : 𝓞 D.host.E)) : D.host.E) = star (a : D.host.E) - star (b : D.host.E)
      push_cast
      exact star_sub _ _)
    rwa [← this]
  have hcne : ∀ c : 𝓞 D.host.E, c ∉ P'.asIdeal → (c : D.host.E) ≠ 0 := fun c hc0 h0 =>
    hc0 (by rw [show c = 0 from RingOfIntegers.ext h0]; exact zero_mem _)
  have hcb : Formalism.L2.Col.cO _ b ∉ P'.asIdeal := fun hm => hca (by
    have := add_mem hcab hm
    rwa [sub_add_cancel] at this)
  have he'e : idemAt P' * idemAt P' = idemAt P' := he'.1.1
  let za := locU he'e (Units.mk0 _ (hcne _ hca))
  let zb := locU he'e (Units.mk0 _ (hcne _ hcb))
  have hza := step ka (Formalism.L2.Col.cO _ a) (by rw [hka]; exact (star_star (a : D.host.E)).symm) za (locU_val he'e _)
  have hzb := step kb (Formalism.L2.Col.cO _ b) (by rw [hkb]; exact (star_star (b : D.host.E)).symm) zb (locU_val he'e _)
  have heq := chi_locE_congr δ hδ hP' _ _ hca hcab za zb (locU_val he'e _) (locU_val he'e _)
  apply Units.ext
  rw [hza, hzb, heq]

theorem tameAt_conj : ∀ (D : D7) (δ : GlobalTheory.ExportSeries.Twist D Circle), δ.Good → ∀ (χ : Formalism.L2.Host.HChar D.host.E),
    ChrEq δ.chi χ → ∀ P' ∈ δ.Q, ∀ P : Pl D.host.E, Formalism.IndefR.Lev.IsConjPl P' P → χ.TameAt P := by
  intro D δ hδ χ hc P' hP' P hPP
  exact tameAt_of_congr χ P fun a b ka kb hka hkb ha hab =>
    locK_congr_conj δ hδ χ hc hP' hPP a b ka kb hka hkb ha hab

end GlobalTheory.TameConjPlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnrAtOfOff
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwistUnrOff

theorem unrAt_of_off : ∀ (D : D7) (δ : GlobalTheory.ExportSeries.Twist D Circle), δ.Good → ∀ (χ : Formalism.L2.Host.HChar D.host.E), ChrEq δ.chi χ → ∀ P : Pl D.host.E, P ∉ δ.Q → (¬ ∃ P' ∈ δ.Q, Formalism.IndefR.Lev.IsConjPl P' P) → χ.UnrAt P := by
  intro D δ hδ χ hc P hPQ hconj
  rw [← GlobalTheory.LFun.unrAt_iff_of_chrEq hc P]
  apply GlobalTheory.GoodModUnr.unrAt_of_unrPl
  intro e f hp x hx h2 h3
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨-, ε, hε, rfl⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ hp
  have hoff := GlobalTheory.ExportSeries.TupleChars.unrOff_of_unram hδ.unram hδ.split (Finset.Subset.refl _)
  refine hoff _ ε hε ?_ x hx h2 h3
  intro PP hPP hu
  rcases GlobalTheory.IdemSupport.eq_or_eq_cP hu.symm with h | h
  · exact hPQ (h ▸ hPP)
  · exact hconj ⟨PP, hPP, (GlobalTheory.IdemSupport.isConjPl_iff PP P).2 h⟩

end GlobalTheory.TwistUnrOff
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterTrivialOnSubfieldOfIdelicReading
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterTrivialOnSubfieldOfIdelicReading
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Links NumberField IsDedekindDomain
open Formalism.L2.JoinChr Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TrivOnRead

section General

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem infIdele_snd_one {K : Type} [Field K] [NumberField K] (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    (infIdele K w x : AdeleRing (𝓞 K) K).2 = 1 := rfl

theorem fst_prod_apply {K : Type} [Field K] [NumberField K] {ι : Type} (s : Finset ι) (f : ι → AdeleRing (𝓞 K) K)
    (w : InfinitePlace K) : (∏ i ∈ s, f i).1 w = ∏ i ∈ s, (f i).1 w :=
  map_prod ((Pi.evalMonoidHom (fun v : InfinitePlace K => v.Completion) w).comp
    (MonoidHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))) f s

theorem snd_prod {K : Type} [Field K] [NumberField K] {ι : Type} (s : Finset ι) (f : ι → AdeleRing (𝓞 K) K) :
    (∏ i ∈ s, f i).2 = ∏ i ∈ s, (f i).2 :=
  map_prod (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) f s

theorem ideleMap_inf (w : InfinitePlace F) (k : Fˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap F E (infIdele F w (atInf w k)) = CharEx.aFi (L := E) F w k := by
  classical
  refine Units.ext (Prod.ext (funext fun w' => ?_) ?_)
  · show GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E (infIdele F w (atInf w k) : AdeleRing (𝓞 F) F).1 w' = _
    rw [CharEx.aFi, Units.coe_prod, fst_prod_apply]
    change AbsoluteValue.Completion.map (w'.comap (algebraMap F E)).1 w'.1
      ((infIdele F w (atInf w k) : AdeleRing (𝓞 F) F).1 (w'.comap (algebraMap F E))) = _
    by_cases hw : w'.comap (algebraMap F E) = w
    · have hm : w' ∈ aboveInf (L := E) F w := by simp [aboveInf, hw]
      rw [Finset.prod_eq_single_of_mem w' hm (fun w'' _ h => infIdele_fst_ne E w'' w' (Ne.symm h) _),
        infIdele_fst_self]
      subst hw
      rw [infIdele_fst_self]
      change AbsoluteValue.Completion.map (w'.comap (algebraMap F E)).1 w'.1
        (algebraMap F _ (k : F)) = algebraMap E _ (algebraMap F E (k : F))
      rw [InfinitePlace.Completion.algebraMap_apply, InfinitePlace.Completion.algebraMap_apply,
        AbsoluteValue.Completion.map_coe]
      rfl
    · rw [infIdele_fst_ne F w _ hw, map_one]
      refine (Finset.prod_eq_one fun w'' hw'' => infIdele_fst_ne E w'' w' ?_ _).symm
      rintro rfl
      simp [aboveInf] at hw''
      exact hw hw''
  · show GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap F E (infIdele F w (atInf w k) : AdeleRing (𝓞 F) F).2 = _
    rw [CharEx.aFi, Units.coe_prod, snd_prod]
    rw [Finset.prod_eq_one fun w'' _ => infIdele_snd_one w'' _]
    exact map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap F E)

end General


open GlobalTheory.CharTransport in
set_option maxHeartbeats 800000 in
theorem exists_hom_tmul (D : D7) : ∃ Θ : AE D →+* AdeleRing (𝓞 D.host.E) D.host.E, Continuous Θ ∧
    (∀ a x, Θ (a ⊗ₜ[D.host.F] x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap D.host.F D.host.E a * algebraMap D.host.E _ x) ∧
    (∀ x, Θ (incA D x) = algebraMap D.host.E _ x) ∧
    ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : AE D), IsPlIdem D e P → ∀ k : D.host.Eˣ,
      Θ (locE D e (k : D.host.E)) =
        ((localIdele D.host.E P (atFin P k) : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E) := by
  obtain ⟨Θ, hc, hΘ⟩ := exists_toAdele D.host.F D.host.E
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have hinc : ∀ x, Θ (incA D x) = algebraMap D.host.E _ x := fun x => by
    change Θ ((1 : AF D.host.F) ⊗ₜ[D.host.F] x) = _
    rw [hΘ, map_one, one_mul]
  have hfin : ∀ z, (Θ z).2 = Φ z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [RingHom.map_zero, RingHom.map_zero]; rfl
    | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ← hx, ← hy]; rfl
    | tmul a x =>
      have e : (a ⊗ₜ[D.host.F] x : AE D) = algebraMap (AF D.host.F) (AE D) a * incA D x := by
        change _ = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hΘ, e, RingHom.map_mul, hΦ.inc]
      refine FiniteAdeleRing.ext _ fun Q => ?_
      change _ = Φ _ Q * _
      rw [hΦ.base, locMap_eq]
      rfl
  have hinf : ∀ z, infPart D z = 0 → (Θ z).1 = 0 := fun z hz => by
    let u : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0)
    have h1 : u * z = 0 := by
      refine GlobalTheory.PlaceIdem.parts_inj D _ _ ?_ ?_
      · rw [RingHom.map_mul, hz, mul_zero, RingHom.map_zero]
      · have : finPart D u = 0 := TensorProduct.zero_tmul _ _
        rw [RingHom.map_mul, this, zero_mul, RingHom.map_zero]
    have h2 : (Θ u).1 = 1 := by
      change (Θ (pairA D.host.F 1 0 ⊗ₜ[D.host.F] (1 : D.host.E))).1 = 1
      rw [hΘ, map_one, mul_one]
      exact map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap D.host.F D.host.E)
    have h3 : (Θ u).1 * (Θ z).1 = 0 := by
      change (Θ u * Θ z).1 = 0
      rw [← RingHom.map_mul, h1, RingHom.map_zero]
      rfl
    rwa [h2, one_mul] at h3
  refine ⟨Θ, hc, hΘ, hinc, fun P e he k => ?_⟩
  obtain ⟨d0, d1, d2⟩ := isDelta_of_isPlIdem hΦ he
  have hl : Θ (locE D e (k : D.host.E)) =
      1 + Θ e * (algebraMap D.host.E (AdeleRing (𝓞 D.host.E) D.host.E) (k : D.host.E) - 1) :=
    (map_loc Θ e (incA D (k : D.host.E))).trans (by rw [hinc])
  rw [hl]
  refine Prod.ext ?_ (FiniteAdeleRing.ext _ fun Q => ?_)
  · change 1 + (Θ e).1 * _ = 1
    rw [hinf e d0, zero_mul, add_zero]
  · classical
    change 1 + (Θ e).2 Q * (algebraMap D.host.E (Q.adicCompletion D.host.E) (k : D.host.E) - 1) =
      Function.update (fun w : HeightOneSpectrum (𝓞 D.host.E) => (1 : w.adicCompletion D.host.E)) P
        (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) Q
    rw [hfin]
    by_cases hQ : Q = P
    · subst hQ
      rw [d1, Function.update_self]
      ring
    · rw [d2 Q hQ, Function.update_of_ne hQ]
      ring

theorem trivOn_of_chrEq : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ →
    (∀ a : (AF D.host.F)ˣ, c (idF D a) = 1) → χ.TrivOn D.host.F := by
  intro D c χ hc ha
  have hχ := GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D c χ hc
  obtain ⟨Θ, hΘc, hΘt, hinc, hloc⟩ := exists_hom_tmul D
  let u : (AE D)ˣ →* Ideles D.host.E := Units.map Θ.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΘc
  let c' : (AE D)ˣ →* Circle :=
    { toFun := fun x => ⟨((χ.1 (u x) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (hχ _)⟩
      map_one' := Circle.ext (by simp)
      map_mul' := fun x y => Circle.ext (by
        change ((χ.1 (u (x * y)) : ℂˣ) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) * ((χ.1 (u y) : ℂˣ) : ℂ)
        rw [map_mul, map_mul, Units.val_mul]) }
  have hcoe : ∀ x, ((c' x : Circle) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) := fun x => rfl
  have hc' : ChrEq c' χ := by
    refine ⟨⟨?_, fun x => Circle.ext ?_⟩, fun P e he k x hx => ?_⟩
    · exact Continuous.subtype_mk (Units.continuous_val.comp (χ.2.1.comp hu)) _
    · have : u (Units.map (incA D).toMonoidHom x) = diagUnits D.host.E x := Units.ext (hinc x)
      rw [hcoe, this, χ.2.2]
      rfl
    · have : u x = localIdele D.host.E P (atFin P k) := by
        refine Units.ext ?_
        change Θ (x : AE D) = _
        rw [hx, hloc P e he]
      rw [hcoe, this]
      rfl
  have hcc : c = c' := GlobalTheory.ChrEqUnique.idc_unique D c c' χ hc hc'
  have key : ∀ a : (AF D.host.F)ˣ, χ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap D.host.F D.host.E a) = 1 := fun a => by
    have h1 : u (idF D a) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap D.host.F D.host.E a := Units.ext (by
      change Θ ((a : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) = _
      rw [hΘt, map_one, mul_one]
      rfl)
    have h2 := hcoe (idF D a)
    rw [← hcc, ha, h1] at h2
    exact Units.ext (by rw [← h2]; rfl)
  refine ⟨fun v k => ?_, fun w k => ?_⟩
  · rw [CharEx.resFin_eq]
    change χ.1 (GlobalTheory.Mem.Chr.locF D.host.F v k) = 1
    rw [← GlobalTheory.ToricDistribution.ideleMap_local]
    exact key _
  · rw [CharEx.resInf_eq, ← ideleMap_inf]
    exact key _

end GlobalTheory.TrivOnRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterTrivialOnSubfieldOfIdelicReadingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Links NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharacter_trivialOnSubfield_of_idelicReading : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → (∀ a : (AF D.host.F)ˣ, c (idF D a) = 1) → χ.TrivOn D.host.F := by
  first | exact @GlobalTheory.TrivOnRead.trivOn_of_chrEq | exact GlobalTheory.TrivOnRead.trivOn_of_chrEq | (intros; apply GlobalTheory.TrivOnRead.trivOn_of_chrEq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsResOfChrEq
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwistResidue

open Formalism.IndefR.Datum

variable {D : D7}


set_option maxHeartbeats 800000 in
theorem isRes_of_chrEq : ∀ (D : D7) (δ : GlobalTheory.ExportSeries.Twist D Circle), δ.Good → ∀ (χ : Formalism.L2.Host.HChar D.host.E),
    ChrEq δ.chi χ → ∀ P ∈ δ.Q, IsRes χ P (δ.resC P) := by
  intro D δ hδ χ hχ P hP a k u hka hu
  have h := hδ.split.isIdemAt hP
  have he : GlobalTheory.ExportSeries.idemAt P * GlobalTheory.ExportSeries.idemAt P = GlobalTheory.ExportSeries.idemAt P := h.1.1
  have e1 := hχ.2 P _ (by obtain ⟨⟨g1, g2, v, ε, hv, hs⟩, g3⟩ := h; exact ⟨g1, ⟨v, ε, hv, Or.inl ⟨g2, hs⟩⟩, g3⟩) k (locU he k) (locU_val he k)
  obtain ⟨hi, h1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D _ P h
  have hb : toEAf D (incA D (k : D.host.E)) = ((oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
    rw [hka]; rfl
  have hx0 : ((locU he k : (AE D)ˣ) : AE D) = 1 + GlobalTheory.ExportSeries.idemAt P * (incA D (k : D.host.E) - 1) := rfl
  have hv : toEAf D ((locU he k : (AE D)ˣ) : AE D) =
      ((1 + ⟨_, hi⟩ * (oToS D.host.F D.host.E a - 1) : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
    rw [hx0, GlobalTheory.ConjTwist.map_loc, hb]
    rfl
  have hx : toEAf D ((locU he k : (AE D)ˣ) : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [hv]
    exact Subtype.property _
  have hoff : (1 - GlobalTheory.ExportSeries.idemAt P) * ((locU he k : (AE D)ˣ) : AE D) = 1 - GlobalTheory.ExportSeries.idemAt P := by
    rw [hx0]
    linear_combination (1 - incA D (k : D.host.E)) * he
  have hres : resS D.host.F P ⟨_, hx⟩ = u := by
    have e2 : (⟨_, hx⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = 1 + ⟨_, hi⟩ * (oToS D.host.F D.host.E a - 1) :=
      Subtype.ext hv
    refine (congrArg (resS D.host.F P) e2).trans ?_
    rw [GlobalTheory.ConjTwist.map_loc, h1, resS_oToS, hu]
    ring
  have e3 := hδ.res P hP _ hoff hx u hres
  refine Units.ext ?_
  rw [← e1, e3]
  rfl

end GlobalTheory.TwistResidue
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.SeriesTie
open Formalism.L2.Host (embLL0)
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.TwistProduct

variable {D : D7}

theorem chrEq_pow {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (h : ChrEq c χ) (n : ℕ) (hn : 0 < n) :
    ChrEq (c ^ n) (χ ^ n) := by
  induction n, hn using Nat.le_induction with
  | base => simpa using h
  | succ n _ ih => rw [pow_succ, pow_succ]; exact GlobalTheory.TowerCharRead.chrEq_mul ih h

theorem chrEq_one_one : ChrEq (1 : (AE D)ˣ →* Circle) (1 : Formalism.L2.Host.HChar D.host.E) :=
  ⟨⟨continuous_const, fun _ => rfl⟩, fun _ _ _ _ _ _ => rfl⟩

theorem natCast_mem_conj {P P' : Pl D.host.E} (h : Formalism.IndefR.Lev.IsConjPl P P') {n : ℕ}
    (hn : (n : 𝓞 D.host.E) ∈ P.asIdeal) : (n : 𝓞 D.host.E) ∈ P'.asIdeal := by
  obtain ⟨c, hc, e⟩ := h _ hn
  have : c = (n : 𝓞 D.host.E) := RingOfIntegers.ext (by rw [e]; simp)
  exact this ▸ hc

theorem tameAt_of_good (t : Twist D Circle) (ht : t.Good) (χ : Formalism.L2.Host.HChar D.host.E) (hχ : ChrEq t.chi χ)
    (v : Pl D.host.E) : χ.TameAt v := by
  by_cases hv : v ∈ t.Q
  · have hr := GlobalTheory.TwistResidue.isRes_of_chrEq D t ht χ hχ v hv
    refine GlobalTheory.TameConjPlace.tameAt_of_congr χ v fun a b ka kb hka hkb ha hab => ?_
    haveI : v.asIdeal.IsMaximal := v.isMaximal
    have hma : (Ideal.Quotient.mk v.asIdeal a : kP v) ≠ 0 := by
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact ha
    have e1 := hr a ka (Units.mk0 _ hma) hka rfl
    have e2 := hr b kb (Units.mk0 _ hma) hkb (Ideal.Quotient.eq.mpr hab)
    rw [← e1, ← e2]
  · by_cases hc : ∃ P' ∈ t.Q, Formalism.IndefR.Lev.IsConjPl P' v
    · obtain ⟨P', hP', hPc⟩ := hc
      exact GlobalTheory.TameConjPlace.tameAt_conj D t ht χ hχ P' hP' v hPc
    · have hu := GlobalTheory.TwistUnrOff.unrAt_of_off D t ht χ hχ v hv hc
      intro x hx _
      exact hu x hx

theorem unrAt_of_good (t : Twist D Circle) (ht : t.Good) (χ : Formalism.L2.Host.HChar D.host.E) (hχ : ChrEq t.chi χ) (pd : ℕ)
    (hpd : ∀ PP ∈ t.Q, ((pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (v : Pl D.host.E)
    (hv : ((pd : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) : χ.UnrAt v := by
  refine GlobalTheory.TwistUnrOff.unrAt_of_off D t ht χ hχ v (fun h => hv (hpd v h)) ?_
  rintro ⟨P', hP', hc⟩
  exact hv (natCast_mem_conj hc (hpd P' hP'))

theorem isTwist_mul : ∀ (D : D7) (t t' : Twist D Circle), t.Good → t'.Good → SplitSet (t.Q ∪ t'.Q) → Disjoint t.Q t'.Q →
    ∀ (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ), (∃ n : ℕ, 0 < n ∧ ∀ x, (t.chi * t'.chi) x ^ n = 1) →
    (∀ PP ∈ t.Q ∪ t'.Q, ((pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ x, (((t.chi * t'.chi) x : Circle) : ℂ) ∈ σ.fieldRange) →
    ∃ δ : Formalism.L2.Host.HChar D.host.E, IsTwist pd σ δ (t.chi * t'.chi) := by
  intro D t t' ht ht' _ _ pd k _ σ hn hpd hval
  obtain ⟨χ, hχ⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D t.chi ht.isHeckeChar
  obtain ⟨χ', hχ'⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D t'.chi ht'.isHeckeChar
  have hc : ChrEq (t.chi * t'.chi) (χ * χ') := GlobalTheory.TowerCharRead.chrEq_mul hχ hχ'
  have hpd1 : ∀ PP ∈ t.Q, ((pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP h => hpd PP (Finset.mem_union_left _ h)
  have hpd2 : ∀ PP ∈ t'.Q, ((pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP h => hpd PP (Finset.mem_union_right _ h)
  refine ⟨χ * χ', hc, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨n, hn0, hnx⟩ := hn
    refine ⟨n, hn0, ?_⟩
    have hp := chrEq_pow hc n hn0
    have h1 : (t.chi * t'.chi) ^ n = 1 := MonoidHom.ext fun x => by
      rw [MonoidHom.pow_apply, hnx x, MonoidHom.one_apply]
    rw [h1] at hp
    exact GlobalTheory.ChrEqUnique.hchar_unique D 1 _ _ hp chrEq_one_one
  · exact GlobalTheory.T.heckeCharacter_trivialOnSubfield_of_idelicReading D _ _ hc fun a => by rw [MonoidHom.mul_apply, ht.real, ht'.real, one_mul]
  · intro v x hx hx1
    show χ.loc v x * χ'.loc v x = 1
    rw [tameAt_of_good t ht χ hχ v x hx hx1, tameAt_of_good t' ht' χ' hχ' v x hx hx1, one_mul]
  · intro v hv x hx
    show χ.loc v x * χ'.loc v x = 1
    rw [unrAt_of_good t ht χ hχ pd hpd1 v hv x hx, unrAt_of_good t' ht' χ' hχ' pd hpd2 v hv x hx, one_mul]
  · intro v _
    obtain ⟨j, j1, j2, j3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
    obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D j j1 j2 j3 v
    have hee : e * e = e := he.1
    obtain ⟨y, hy⟩ := RingHom.mem_fieldRange.1 (hval (Formalism.L2.JoinChr.locU hee (Formalism.L2.Host.unif v)))
    refine ⟨y, ?_⟩
    rw [hy, hc.2 v e he (Formalism.L2.Host.unif v) _ (Formalism.L2.JoinChr.locU_val hee _)]
    simp [Formalism.L2.Host.HChar.valTw, Formalism.L2.Host.HChar.val]

end GlobalTheory.TwistProduct
