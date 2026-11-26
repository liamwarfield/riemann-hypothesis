module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIneOfUnit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KeepSideBMtVPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAuxiliaryPlaceFamilyAtLevelMono

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstTwistCharactersEqLadicCharactersAllReadings
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsZmodEq
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfPowEqSelf
open Polynomial

namespace GlobalTheory.RangeOfPowerFixed

theorem mem_range_of_pow_eq_self {g : ℕ} [Fact (Nat.Prime g)] {K : Type*} [Field K] [Algebra (ZMod g) K]
    (z : K) (hz : z ^ g = z) : ∃ c : ZMod g, algebraMap (ZMod g) K c = z := by
  classical
  by_contra hne
  simp only [not_exists] at hne
  have hg : 1 < g := (Fact.out : Nat.Prime g).one_lt
  set P : K[X] := X ^ g - X with hPeq
  have hP0 : P ≠ 0 := Polynomial.X_pow_sub_X_ne_zero hg
  have hdeg : P.natDegree = g := Polynomial.natDegree_X_pow_sub_X (R := K) hg

  have hroot : ∀ x : K, x ^ g = x → x ∈ P.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, mem_roots hP0, hPeq]
    simp [hx]

  set S : Finset K := insert z (Finset.univ.image (algebraMap (ZMod g) K)) with hSeq
  have hzS : z ∉ Finset.univ.image (algebraMap (ZMod g) K) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact hne
  have hcard : S.card = g + 1 := by
    rw [hSeq, Finset.card_insert_of_notMem hzS,
      Finset.card_image_of_injective _ (algebraMap (ZMod g) K).injective, Finset.card_univ, ZMod.card]
  have hsub : S ⊆ P.roots.toFinset := by
    intro x hx
    rw [hSeq, Finset.mem_insert, Finset.mem_image] at hx
    rcases hx with rfl | ⟨c, -, rfl⟩
    · exact hroot _ hz
    · exact hroot _ (by rw [← map_pow, ZMod.pow_card])
  have := (Finset.card_le_card hsub).trans
    ((Multiset.toFinset_card_le _).trans (card_roots' P))
  omega

theorem main : ∀ {g : ℕ} [inst : Fact (Nat.Prime g)] (z : Formalism.CyclotomicNorms.Fbar g), z ^ g = z →
    ∃ (c : ZMod g), (Algebra.algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) : ZMod g → Formalism.CyclotomicNorms.Fbar g) c = z := by
  intro g _ z hz
  exact mem_range_of_pow_eq_self z hz

end GlobalTheory.RangeOfPowerFixed
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TameGenRep

open Formalism.L2.NT

theorem exists_zmod_eq {g : ℕ} [Fact g.Prime] (z : Formalism.CyclotomicNorms.Fbar g) (hz : z ^ g = z) :
    ∃ c : ZMod g, algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c = z := by
  first
  | exact @_root_.GlobalTheory.RangeOfPowerFixed.main
  | exact _root_.GlobalTheory.RangeOfPowerFixed.main
  | (apply _root_.GlobalTheory.RangeOfPowerFixed.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.RangeOfPowerFixed.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RangeOfPowerFixed.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RangeOfPowerFixed.main ..)

theorem exists_rep : ∀ (D : D7), GrpSide D → ∀ (k : Fin 2) (v : D.nd.PlG k), normV (D.naut.plGw k v) = D.host.g k ∧ ∃ (u ϖ : 𝓞 D.host.E) (π : D.nd.Om), u ∉ (D.naut.plGw k v).asIdeal ∧ ϖ ∈ (D.naut.plGw k v).asIdeal ∧ ϖ ∉ (D.naut.plGw k v).asIdeal ^ 2 ∧ π ^ (normV (D.naut.plGw k v) - 1) = algebraMap D.host.E D.nd.Om (ϖ : D.host.E) ∧ (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) < 1 ∧ orderOf (D.ntypes.tg k v π / π) = normV (D.naut.plGw k v) - 1 := by
  intro D hG k v
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  haveI : CharZero D.nd.Om := charZero_of_injective_ringHom (f := algebraMap D.host.E D.nd.Om) (algebraMap D.host.E D.nd.Om).injective
  have hgp : (D.host.g k).Prime := D.host.g_prime k
  have hAP : IsPlaceOver (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) :=
    D.nd.plOm.2 (D.naut.plGw k v)
  have hgP : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  have hspl := GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) hgp (D.nd.g_split k) (D.naut.plGw k v) hgP
  have hN : normV (D.naut.plGw k v) = D.host.g k := by
    rw [← hspl.1, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hg1 : 0 < D.host.g k - 1 := by have := hgp.two_le; omega
  have hgΩ : ((D.host.g k : ℕ) : D.nd.Om) ≠ 0 := Nat.cast_ne_zero.mpr hgp.ne_zero
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq ((D.host.g k : ℕ) : D.nd.Om) hg1
  have hT : redThrough (D.nd.plOm.1 (D.naut.plGw k v)) (hG.kv k v) (D.ntypes.tg k v π / π) = hG.ζ k 1 :=
    hG.tg_tame k v 1 one_pos π (by rw [pow_one]; exact hπ)
  have hq : D.ntypes.tg k v π / π ∈ D.nd.plOm.1 (D.naut.plGw k v) :=
    tameQuot_mem (D.nd.plOm.1 (D.naut.plGw k v)) (D.ntypes.tg k v) hg1 hgΩ hπ
  have hpow : (D.ntypes.tg k v π / π) ^ (D.host.g k - 1) = 1 := tameQuot_pow (D.ntypes.tg k v) hgΩ hπ
  have hζ := (hG.ζ_gen k 1 one_pos).1
  rw [pow_one] at hζ
  have hζ1 : hG.ζ k 1 ^ (D.host.g k - 1) = 1 := by rw [← hζ]; exact pow_orderOf_eq_one _
  have hζpow : hG.ζ k 1 ^ D.host.g k = hG.ζ k 1 := by
    calc _ = hG.ζ k 1 ^ (D.host.g k - 1) * hG.ζ k 1 := by rw [← pow_succ, Nat.sub_add_cancel hgp.one_le]
      _ = _ := by rw [hζ1, one_mul]
  have hζ0 : hG.ζ k 1 ≠ 0 := by
    intro h
    rw [h, zero_pow hg1.ne'] at hζ1
    exact zero_ne_one hζ1
  obtain ⟨c, hc⟩ := exists_zmod_eq _ hζpow
  have hca : ((c.val : ℕ) : Formalism.CyclotomicNorms.Fbar (D.host.g k)) = hG.ζ k 1 := by
    rw [← hc, ← map_natCast (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))), ZMod.natCast_zmod_val]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = c.val := ⟨_, rfl⟩
  rw [← hn] at hca
  have hcast : algebraMap D.host.E D.nd.Om ((n : 𝓞 D.host.E) : D.host.E) = (n : D.nd.Om) := by
    simp
  have haA : (n : D.nd.Om) ∈ D.nd.plOm.1 (D.naut.plGw k v) := natCast_mem _ _
  have hra : redThrough (D.nd.plOm.1 (D.naut.plGw k v)) (hG.kv k v) (n : D.nd.Om) =
      hG.kv k v (IsLocalRing.residue _ ⟨_, haA⟩) := by
    unfold redThrough; rw [dite_eq_left haA]
  have hra' : hG.kv k v (IsLocalRing.residue _ ⟨_, haA⟩) = hG.ζ k 1 := by
    have : (⟨(n : D.nd.Om), haA⟩ : D.nd.plOm.1 (D.naut.plGw k v)) = (n : D.nd.plOm.1 (D.naut.plGw k v)) :=
      Subtype.ext (by simp)
    rw [this, map_natCast, map_natCast, hca]
  have hrq : redThrough (D.nd.plOm.1 (D.naut.plGw k v)) (hG.kv k v) (D.ntypes.tg k v π / π) =
      hG.kv k v (IsLocalRing.residue _ ⟨_, hq⟩) := by
    unfold redThrough; rw [dite_eq_left hq]
  have hval : (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - (n : D.nd.Om)) < 1 := by
    have h1 := (hG.kv k v).injective (((hrq.symm.trans hT).trans hra'.symm))
    have h2 := Ideal.Quotient.eq.1 h1
    have h3 := ((D.nd.plOm.1 (D.naut.plGw k v)).valuation_lt_one_iff _).1 h2
    exact h3
  have hu : (n : 𝓞 D.host.E) ∉ (D.naut.plGw k v).asIdeal := by
    intro h
    have h1 := (hAP _).2 h
    have h2 : (n : D.nd.Om) ∈ D.nd.plOm.1 (D.naut.plGw k v) := haA
    have h3 : (⟨_, haA⟩ : D.nd.plOm.1 (D.naut.plGw k v)) ∈ IsLocalRing.maximalIdeal _ :=
      ((D.nd.plOm.1 (D.naut.plGw k v)).valuation_lt_one_iff _).2 (by rw [hcast] at h1; exact h1)
    rw [← IsLocalRing.residue_eq_zero_iff] at h3
    rw [h3, map_zero] at hra'
    exact hζ0 hra'.symm
  have hord : orderOf (D.ntypes.tg k v π / π) = D.host.g k - 1 := by
    apply Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hpow)
    rw [← hζ]
    apply orderOf_dvd_of_pow_eq_one
    have h1 : (⟨_, hq⟩ : D.nd.plOm.1 (D.naut.plGw k v)) ^ orderOf (D.ntypes.tg k v π / π) = 1 :=
      Subtype.ext (by simp [pow_orderOf_eq_one])
    rw [← hT, hrq, ← map_pow, ← map_pow, h1, map_one, map_one]
  refine ⟨hN, (n : 𝓞 D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E), π, hu, hgP, hspl.2.1, ?_, ?_, ?_⟩
  · rw [hN]; simpa using hπ
  · rw [hcast]; exact hval
  · rw [hN]; exact hord

end GlobalTheory.TameGenRep

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstTwistCharactersEqLadicCharactersAllReadings
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwInputs.isChars_of_sideB : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ChiTOk D cf → GrpSide D → CharSide D cf → ValLL0 D cf → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om), GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ i b (ρ : GlobalTheory.Triple.Reading D.ntw i b), GlobalTheory.Triple.IsChars cf art ρ := by
  intro _hCh hGAR D cf Rw low Pq S hL eig θ Bs hT hG _hCS hV _hroots art ha i b ρ
  have hchi := GlobalTheory.TwChiGal.firstTwistCharacter_eq_ladic_heckeCharacter D cf Bs.chiD Bs.chi Bs.eta_eq Bs.ringSpec_normalisedCharacter_eq Bs.del_eq hV art ha i b ρ
  refine ⟨hchi, fun j k hk v => ?_⟩
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨hN, u, ϖ, π, hu, hϖ1, hϖ2, hπ, hval, hord⟩ := GlobalTheory.TameGenRep.exists_rep D hG k v
  have hAw : IsPlaceOver (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) := D.nd.plOm.2 _
  have hu0 : (u : D.host.E) ≠ 0 := fun h => hu (by
    rw [show u = 0 from RingOfIntegers.coe_eq_zero_iff.1 h]; exact zero_mem _)
  have hTR : NX.TameRep (D.naut.plGw k v) 1 (D.ntypes.tg k v) u :=
    ⟨_, hAw, D.ntypes.tg_mem k v, ϖ, π, hϖ1, hϖ2, hπ, by simpa using hval⟩
  obtain ⟨c, hc, hcv⟩ := hT k v j u hu0 hTR
  have hxu : IsUnitAt (D.naut.plGw k v) (atFin (D.naut.plGw k v) (Units.mk0 (u : D.host.E) hu0)) := by
    show Valued.v (((u : D.host.E) : (D.naut.plGw k v).adicCompletion D.host.E)) = 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem _).2 hu
  obtain ⟨σ, hσI, hσart, hσval⟩ := GlobalTheory.TameRecip.exists_ine_of_unit hGAR D.host.E D.nd.Om art ha
    (D.naut.plGw k v) _ hAw ϖ hϖ1 hϖ2 π hπ (atFin (D.naut.plGw k v) (Units.mk0 (u : D.host.E) hu0)) u hxu
    (by simp [atFin])
  obtain ⟨n, hn⟩ := hchi j
  have hl := GlobalTheory.Triple.Model.notMem_l (X := D.ntw) hk v
  have e1 := hn.loc (Or.inl hl) hσart.symm
  obtain ⟨h1, -, h3, -, h5⟩ := GlobalTheory.GalChar.inertialOrderFifteenChar_auxiliaryPrime_spec (GlobalTheory.Triple.hframe cf) (l := D.ntw.l i)
  have hdel : (cf.delAt (D.ntw.l i)).UnrAt (D.naut.plGw k v) :=
    h5.unr _ (GlobalTheory.GalChar.notMem_of_ne (D.host.g_prime k) h1 (h3 k).symm (D.naut.plGw_over k v))
  rw [GlobalTheory.Triple.blockChar, GlobalTheory.GalChar.block_loc (cf.isEta.unr _) hxu, GlobalTheory.Triple.muBase] at e1
  change _ = ((cf.mu0 j).loc _ _ : ℂ) * ((cf.delAt (D.ntw.l i)).loc _ _ : ℂ) at e1
  simp only [hdel _ hxu, Units.val_one, mul_one] at e1
  have hg2 := (D.host.g_prime k).two_le
  have hgw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  have hm : ((normV (D.naut.plGw k v) - 1 : ℕ) : 𝓞 D.host.E) ∉ (D.naut.plGw k v).asIdeal := by
    rw [hN]
    intro h
    apply (D.naut.plGw k v).isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have := (D.naut.plGw k v).asIdeal.sub_mem hgw h
    rwa [Nat.cast_sub (by omega), Nat.cast_one, sub_sub_cancel] at this
  have hI : ∀ τ ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)),
      GlobalTheory.GalChar.inQ ρ.κ (D.ntw.chi1 i (j.1 + 1) b) τ ^ (normV (D.naut.plGw k v) - 1) = 1 := by
    intro τ hτ
    rw [hN, GlobalTheory.GalChar.inQ, MonoidHom.comp_apply, ← map_pow, D.ntw.twistCharacterFamily_tame i (j.1 + 1) b k _ hgw hl _ hAw τ hτ, map_one]
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow (by rw [hN]; omega)] at hπ
    apply hϖ2
    have h0 : (ϖ : D.host.E) = 0 := (map_eq_zero_iff _ (algebraMap D.host.E D.nd.Om).injective).1 hπ.symm
    rw [show ϖ = 0 from RingOfIntegers.coe_eq_zero_iff.1 h0]
    exact zero_mem _
  have hsub : (D.nd.plOm.1 (D.naut.plGw k v)).valuation (σ π / π - D.ntypes.tg k v π / π) < 1 := by
    have e : σ π / π - D.ntypes.tg k v π / π = (σ π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) -
      (D.ntypes.tg k v π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) := by ring
    rw [e]
    exact Valuation.map_sub_lt _ hσval hval
  have e2 := GlobalTheory.TameCharDet.eq_of_tameChar D.host.E D.nd.Om (D.naut.plGw k v) _ hAw _ (D.ntypes.tg_gen k v) _
    (GlobalTheory.GalChar.inQ ρ.κ (D.ntw.chi1 i (j.1 + 1) b)) (hn.cont (D.ntw.twistBaseCoefficientRing_isAdic i) ρ.κ_alg) _ (by omega) hm hI π _
    hπ0 hπ hord σ hσI hsub
  refine ⟨c, hc, ?_⟩
  rw [GlobalTheory.Triple.Reading.toC_apply, ← GlobalTheory.GalChar.inQ_val, ← e2, GlobalTheory.GalChar.inQ_val, e1]
  exact hcv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstTwistCharactersEqLadicCharactersAllReadingsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstTwistCharacters_eq_ladic_characters_allReadings : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ChiTOk D cf → GrpSide D → CharSide D cf → ValLL0 D cf → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om), GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ i b (ρ : GlobalTheory.Triple.Reading D.ntw i b), GlobalTheory.Triple.IsChars cf art ρ := by
  first | exact @GlobalTheory.TwInputs.isChars_of_sideB | exact GlobalTheory.TwInputs.isChars_of_sideB | (intros; apply GlobalTheory.TwInputs.isChars_of_sideB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistTripleEigenvectorInGoodPart
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistTripleEigenvectorInGoodPart
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwInputs

open Formalism.IndefR.NX

theorem goodE_of_eigOcc : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ∀ Sb : Finset (PlE D.host), (∀ i, Sb ⊆ D.ntw.S0 i) → (∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm) → EigOcc D S θ hL Sb eig → ∀ i (s : D.ntw.Sig i), Formalism.MainNotions.BlochKatoReduction.Gen.goodE D.nexp i s := by
  intro D cf Rw low Pq S hL eig θ Bs Sb hSb hKs hOcc i s
  classical
  obtain ⟨h1, h2⟩ := D.ntw.jS_range i s
  obtain ⟨hiso, hgood, -⟩ := Bs.rhoS i s
  obtain ⟨x, hxg, hx0, hxe⟩ := hOcc _ h1 h2 _ hiso hgood
  obtain ⟨Φ, hΦ0, hΦs, hΦT⟩ := GlobalTheory.T.exists_descent_map_nonzero_of_small_field_form D S _ (hKs _ h1 h2) i (D.ntw.side i s) x hx0
  set e := Bs.eF i (D.ntw.jS i s) (D.ntw.side i s) h1 h2 with he
  refine ⟨e.symm (Φ x), by simpa using hΦ0, ?_, ?_⟩
  · letI : Fintype (G0g D.nd) := Formalism.MainNotions.PrimeDegreeVariant.finiteLevelGroupFintype D
    have hx1 := Module.End.mem_eigenspace_iff.1 (Submodule.mem_inf.1 hxg).1
    rw [one_smul, finsum_eq_sum_of_fintype, LinearMap.sum_apply] at hx1
    apply e.injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ _ (by intros; simp), LinearMap.sum_apply,
      map_sum, e.apply_symm_apply]
    conv_rhs => rw [← hx1]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, map_smul, LinearMap.smul_apply, hΦs, D.nexp.eAlg_def]
    change readLL0 S i _ (D.nexp.eLL0 g) • e (D.nexp.actG i _ _ g (e.symm (Φ x))) = _
    rw [Bs.act i _ _ h1 h2 g, e.apply_symm_apply]
    congr 1
    have hc : ((((S.A (D.ntw.jS i s)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL))⁻¹ =
        (((chiL S _ (Bs.chiL _ h1 h2) (S.eG.symm g))⁻¹ : ↥D.LL0) : D.what₂.LL) := by
      simp [chiL]
    change _ = Φ (((((S.A (D.ntw.jS i s)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL))⁻¹ •
      (S.A (D.ntw.jS i s)).ρ (S.eG.symm g) x)
    rw [hc, hΦs, hΦT _ (Bs.rho _ h1 h2 (S.eG.symm g)), map_inv₀]
    rfl
  · intro k P hk1 hk2 hsp hP
    apply e.injective
    rw [Bs.hkEq i _ _ h1 h2 k P _ hP hsp hk2, e.apply_symm_apply, map_smul, e.apply_symm_apply,
      Bs.rowS_eig i s k P hk1 hk2 hsp hP]
    have h3 := hΦT (hL (D.ntw.jS i s) k P) (Bs.hs _ h1 h2 k P) x
    rw [hxe k P hk1 hk2 hsp (fun h => hP (hSb i h)), hΦs] at h3
    rw [mul_smul]
    congr 1
    exact h3.symm

end GlobalTheory.TwInputs

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistTripleEigenvectorInGoodPartStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistTriple_eigenvector_in_good_part : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ∀ Sb : Finset (PlE D.host), (∀ i, Sb ⊆ D.ntw.S0 i) → (∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm) → EigOcc D S θ hL Sb eig → ∀ i (s : D.ntw.Sig i), Formalism.MainNotions.BlochKatoReduction.Gen.goodE D.nexp i s := by
  first | exact @GlobalTheory.TwInputs.goodE_of_eigOcc | exact GlobalTheory.TwInputs.goodE_of_eigOcc | (intros; apply GlobalTheory.TwInputs.goodE_of_eigOcc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmallRingElemOfFractionMapIntegral
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs.HEig

open GlobalTheory.Triple GlobalTheory.EigTie

theorem exists_small_ring_elem_of_fraction_map_integral {D : D7} (X : NTw D.R D.host D.what₂ D.LL0 D.nd) (i : X.Tw) (z : FractionRing (X.O0 i))
    (y : X.O i) (h : fracMap X i z = algebraMap (X.O i) (FractionRing (X.O i)) y) :
    ∃ a : X.O0 i, algebraMap (X.O0 i) (FractionRing (X.O0 i)) a = z := by
  haveI := GlobalTheory.TwistChoice.isLocalHom_O (X := X) i
  rcases eq_or_ne z 0 with rfl | hz
  · exact ⟨0, map_zero _⟩
  rcases ValuationRing.isInteger_or_isInteger (X.O0 i) z with ⟨a, e⟩ | ⟨c, e⟩
  · exact ⟨a, e⟩
  · by_cases hc : IsUnit c
    · obtain ⟨u, rfl⟩ := hc
      refine ⟨↑u⁻¹, ?_⟩
      have h1 : algebraMap (X.O0 i) (FractionRing (X.O0 i)) (u : X.O0 i) *
          algebraMap (X.O0 i) (FractionRing (X.O0 i)) ((u⁻¹ : (X.O0 i)ˣ) : X.O0 i) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      rw [e] at h1
      rw [← inv_inv z]
      exact (eq_inv_of_mul_eq_one_right h1)
    · exfalso
      have e2 : algebraMap (X.O i) (FractionRing (X.O i)) (y * algebraMap (X.O0 i) (X.O i) c) = 1 := by
        rw [map_mul, ← h, ← fracMap_algebraMap, ← map_mul, e, mul_inv_cancel₀ hz, map_one]
      have e3 : y * algebraMap (X.O0 i) (X.O i) c = 1 :=
        IsFractionRing.injective (X.O i) (FractionRing (X.O i)) (by rw [e2, map_one])
      exact hc (isUnit_of_map_unit (algebraMap (X.O0 i) (X.O i)) c (isUnit_iff_exists_inv.2 ⟨y, by rw [mul_comm]; exact e3⟩))

end GlobalTheory.TwInputs.HEig

namespace GlobalTheory.TwInputs.HEig

open GlobalTheory.Triple GlobalTheory.EigTie

theorem delAt_unr {D : D7} (cf : CharFrame D) (i : D.ntw.Tw) {P : PlE D.host} (hS : P ∉ D.ntw.S0 i) :
    (cf.delAt (D.ntw.l i)).UnrAt P := by
  have hD : P ∉ placesOver D.host.E (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde) := fun h =>
    hS (D.ntw.primes_subset_exceptional i (by rw [← Finset.mem_coe, D.ntw.pD_eq i]; exact h))
  unfold CharFrame.delAt
  split_ifs with h
  · rw [if_pos h] at hD
    exact cf.isDel'.unr P hD
  · rw [if_neg h] at hD
    exact cf.isDel.unr P hD

end GlobalTheory.TwInputs.HEig

namespace GlobalTheory.TwInputs.HEig

open GlobalTheory.Triple GlobalTheory.EigTie

theorem toC_delta {D : D7} (cf : CharFrame D) (i : D.ntw.Tw) {b : Bool} (ρ : GlobalTheory.Triple.Reading D.ntw i b)
    {P : PlE D.host} (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) (xd : D.LL0)
    (hxd : D.what₂.embLL (xd : D.what₂.LL) = (((cf.delAt (D.ntw.l i)).val P)⁻¹ : ℂˣ).1)
    (hdel : algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) ((D.ntw.delta i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) =
      D.ntw.emb0 i xd) :
    ρ.toC (((if b then D.ntw.delta i σ else (D.ntw.delta i σ)⁻¹ : (D.ntw.O0 i)ˣ)) : D.ntw.O0 i) =
      (((cf.delAt (D.ntw.l i)).val P : ℂˣ) : ℂ)⁻¹ := by
  set δ : ℂ := (((cf.delAt (D.ntw.l i)).val P : ℂˣ) : ℂ) with hδ
  have hδ0 : δ ≠ 0 := Units.ne_zero _
  have hz : ‖δ‖ = 1 := cf.delAt_unitary _ _
  rw [Units.val_inv_eq_inv_val] at hxd
  have hread : ρ.toC ((D.ntw.delta i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = ρ.ι (ρ.κ (D.ntw.emb0 i xd)) := by
    rw [Reading.toC_apply, ← hdel]; rfl
  cases b
  ·
    have hx0 : (xd : D.what₂.LL) ≠ 0 := by
      intro h0; rw [h0, map_zero] at hxd; exact inv_ne_zero hδ0 hxd.symm
    have hstar : ((xd⁻¹ : D.LL0) : D.what₂.LL) = star (xd : D.what₂.LL) := by
      apply D.what₂.embLL.injective
      rw [D.starLL_cx, hxd, ← Complex.inv_eq_conj (by rw [norm_inv, hz, inv_one]), inv_inv]
      rw [IntermediateField.coe_inv, map_inv₀, hxd, inv_inv]
    have e : D.ntw.emb0 i xd = D.ntw.emb0b i xd⁻¹ := (D.ntw.restX_coefficientEmbedding_conj i xd⁻¹ xd ?_).symm
    · have h1 := ρ.read xd⁻¹
      simp only [embSide, Bool.false_eq_true, if_false] at h1
      simp only [Bool.false_eq_true, if_false]
      rw [map_units_inv, hread, e, h1]
      show (D.what₂.embLL ((xd⁻¹ : D.LL0) : D.what₂.LL))⁻¹ = δ⁻¹
      rw [IntermediateField.coe_inv, map_inv₀, hxd, inv_inv]
    · rw [hstar, star_star]
  · have h1 := ρ.read xd
    simp only [embSide, if_true] at h1
    simp only [if_true, hread, h1]
    exact hxd

end GlobalTheory.TwInputs.HEig

namespace GlobalTheory.TwInputs.HEig

open GlobalTheory.Triple GlobalTheory.EigTie

theorem hEig_eq_heckeVal : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ∀ Sb : Finset (PlE D.host), (∀ i, Sb ⊆ D.ntw.S0 i) → EigTrue D cf Rw Sb eig → ∀ i (s : D.ntw.Sig i) (ρ : GlobalTheory.Triple.Reading D.ntw i (D.ntw.side i s)) (π : D.naut.CG D.R.r), GlobalTheory.EigTie.IsRowPar Rw (Bs.rowS i s) π → ∀ k P, k ≤ D.R.r → IsSplitPl D.host P → P ∉ D.ntw.S0 i → ∃ x : D.ntw.O0 i, algebraMap (D.ntw.O0 i) (D.ntw.O i) x = D.ntw.hEig i s k P ∧ ρ.toC x = GlobalTheory.Triple.heckeVal (GlobalTheory.Triple.muBase cf (D.ntw.l i) (GlobalTheory.Triple.jIdx s)) π k P := by
  intro D cf Rw low Pq S hL eig θ Bs Sb hSb hET i s ρ π hπ k P hk hP hS
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · exact ⟨1, by rw [map_one, Bs.hEig_zero], by rw [map_one, heckeVal_zero]⟩
  obtain ⟨σ, -, hσ⟩ := GlobalTheory.TripleGal.exists_mem_Dec_isFrob D P (D.nd.plOm.1 P) (D.nd.plOm.2 P)
  have hl : P ∉ placesOver D.host.E (D.ntw.l i) := fun h => hS (D.ntw.twistExcludedPlaces_contains_residueChar i h)
  obtain ⟨xd, hxd, hdel⟩ := Bs.deltaRead i P hl (delAt_unr cf i hS) _ σ (D.nd.plOm.2 P) hσ
  set u : (D.ntw.O0 i)ˣ := if D.ntw.side i s then D.ntw.delta i σ else (D.ntw.delta i σ)⁻¹ with hu
  have hc : Bs.cHk i (D.ntw.side i s) P = Units.map (algebraMap (D.ntw.O0 i) (D.ntw.O i)).toMonoidHom u :=
    Bs.cHk_del i (D.ntw.side i s) P hS σ hσ
  set e : ↥D.LL0 := eig (D.ntw.jS i s) (Bs.rowS i s) k P with he
  set z : FractionRing (D.ntw.O0 i) := embSide D.ntw i (D.ntw.side i s) e with hz
  have hrow := Bs.rowS_eig i s k P hk1 hk hP hS
  have hread : (show FractionRing (D.ntw.O i) from readLL0 S i (D.ntw.side i s) e) = fracMap D.ntw i z := rfl
  rw [hread, hc] at hrow
  set A : D.ntw.O0 i →+* FractionRing (D.ntw.O i) :=
    (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i)) with hA
  have hcu : algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))
      ((Units.map (algebraMap (D.ntw.O0 i) (D.ntw.O i)).toMonoidHom u : (D.ntw.O i)ˣ) : D.ntw.O i) = A u := rfl
  rw [hcu] at hrow
  have hAu : A (u : D.ntw.O0 i) * A ((u⁻¹ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]

  have hzO : fracMap D.ntw i z = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))
      (D.ntw.hEig i s k P * algebraMap (D.ntw.O0 i) (D.ntw.O i) (((u⁻¹ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) ^ k)) := by
    rw [map_mul, hrow, map_pow, map_pow]
    change _ = A (u : D.ntw.O0 i) ^ k * fracMap D.ntw i z * A ((u⁻¹ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) ^ k
    rw [mul_comm _ (fracMap D.ntw i z), mul_assoc, ← mul_pow, hAu, one_pow, mul_one]
  obtain ⟨a, ha⟩ := exists_small_ring_elem_of_fraction_map_integral D.ntw i z _ hzO
  refine ⟨(u : D.ntw.O0 i) ^ k * a, ?_, ?_⟩
  · apply IsFractionRing.injective (D.ntw.O i) (FractionRing (D.ntw.O i))
    rw [hrow, ← fracMap_algebraMap, map_mul, map_mul, ha, map_pow, map_pow, fracMap_algebraMap]
    rfl
  · have hloc : D.naut.locG π P = Rw.locR (Bs.rowS i s) P := hπ.2 P hP
    obtain ⟨hocc, hgood, -⟩ := Bs.rhoS i s
    have hocc' : D.what₂.isot ((jIdx s).1 + 1) (Bs.rowS i s) ≠ ⊥ := by rwa [jIdx_add_one]
    have hET' := (hET (jIdx s) (Bs.rowS i s) hocc' hgood P hP (fun h => hS (hSb i h))).2 k hk1 hk
    rw [jIdx_add_one] at hET'
    have hδ : ρ.toC (u : D.ntw.O0 i) = _ := toC_delta cf i ρ σ xd hxd hdel
    have hae : ρ.toC a = D.what₂.embLL (e : D.what₂.LL) := by
      rw [Reading.toC_apply]
      change ρ.ι (ρ.κ (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) a)) = _
      rw [ha, hz, ρ.read]
      rfl
    rw [map_mul, map_pow, hδ, hae, he, hET', heckeVal, satake, hloc, muBase, HChar.val_mul, Units.val_mul]
    set q : ℂ := ((normV P : ℕ) : ℂ)
    set c : ℂ := (((cf.delAt (D.ntw.l i)).val P : ℂˣ) : ℂ)⁻¹
    have hmap : (D.naut.frobEig (Rw.locR (Bs.rowS i s) P)).map (fun a =>
        a⁻¹ * ((((cf.mu0 (jIdx s)).val P : ℂˣ) : ℂ) * (((cf.delAt (D.ntw.l i)).val P : ℂˣ) : ℂ))⁻¹ * (q ^ (D.R.nV / 2))⁻¹) =
        ((D.naut.frobEig (Rw.locR (Bs.rowS i s) P)).map (fun a =>
          a⁻¹ * (((cf.mu0 (jIdx s)).val P : ℂˣ) : ℂ)⁻¹ * (q ^ (D.R.nV / 2))⁻¹)).map (fun y => c • y) := by
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun a _ => ?_
      simp only [Function.comp_apply, smul_eq_mul, c, mul_inv]
      ring
    rw [hmap, ← Multiset.pow_smul_esymm, smul_eq_mul]
    ring

end GlobalTheory.TwInputs.HEig
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TripInhab

open GlobalTheory.Triple GlobalTheory.EigTie
open GlobalTheory.GalChar (IsGal toQ inQ)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf GalE)
open GlobalTheory.TwistAbove (twGL)

theorem isInv_twGL_iff {Γ K : Type} [Group Γ] [Field K] {a : ℕ} (χ : Γ →* Kˣ) (r : Γ →* GL (Fin a) K)
    (W : Submodule K (Fin a → K)) : IsInv (twGL χ r) W ↔ IsInv r W := by
  constructor
  · intro h g v hv
    have := W.smul_mem (((χ g)⁻¹ : Kˣ) : K) (h g v hv)
    rwa [GlobalTheory.TwistAbove.twGL_val, Matrix.smul_mulVec, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_smul] at this
  · intro h g v hv
    rw [GlobalTheory.TwistAbove.twGL_val, Matrix.smul_mulVec]
    exact W.smul_mem _ (h g v hv)

theorem isSSRep_twGL {Γ K : Type} [Group Γ] [Field K] {a : ℕ} (χ : Γ →* Kˣ) (r : Γ →* GL (Fin a) K)
    (h : IsSSRep r) : IsSSRep (twGL χ r) := fun W hW =>
  let ⟨W', h1, h2⟩ := h W ((isInv_twGL_iff χ r W).1 hW)
  ⟨W', (isInv_twGL_iff χ r W').2 h1, h2⟩

variable {D : D7} {C : CharFrame D} {art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om}

end GlobalTheory.TripInhab

namespace GlobalTheory.TripInhab

open GlobalTheory.Triple GlobalTheory.EigTie
open GlobalTheory.GalChar (IsGal toQ inQ)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf GalE)
open GlobalTheory.TwistAbove (twGL)

end GlobalTheory.TripInhab

end
