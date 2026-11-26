module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.QuotRepMk
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompIne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PlacesOfRationals.PlacesQ
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LengthEqLengthInvariantsOfTorsionLevels

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoBkMap
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato

theorem UpperTheory.V.X.Kato.bkMap :
    ∀ (l : ℕ) [Fact l.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (C V : Type) [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V] (C' V' : Type) [CommRing C'] [Algebra ℚ_[l] C'] [AddCommGroup V'] [Module C' V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] C' V'] [TopologicalSpace V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul C' V'] (ρ : Representation C (G F Ω) V) (ρ' : Representation C' (G F Ω) V') (f : V →ₗ[ℚ_[l]] V'), (∀ g x, f (ρ g x) = ρ' g (f x)) → ∀ c : G F Ω → V, Continuous (fun g => f (c g)) → IsBK l ρ c → IsBK l ρ' (fun g => f (c g)) := by
  intro l _ F Ω _ _ _ _ C V _ _ _ _ _ _ _ _ _ C' V' _ _ _ _ _ _ _ _ _ ρ ρ' f hf c hfc hc
  refine ⟨fun w hw => ?_, fun τ => ?_⟩
  · obtain ⟨A, hA, x, hx⟩ := hc.away w hw
    exact ⟨A, hA, f x, fun s hs => by rw [hx s hs, map_sub, hf]⟩
  · obtain ⟨j, hj, ⟨_, hcc⟩, x, hx⟩ := hc.above τ
    refine ⟨j, hj, ⟨?_, fun g h => ?_⟩, LinearMap.rTensor (UpperTheory.V.Loc.Bcr l) f x, fun g => ?_⟩
    · exact hfc.comp (continuous_fst.comp continuous_subtype_val)
    · have h1 := congrArg f (hcc g h)
      simpa only [map_add (f := _), hf, MonoidHom.comp_apply] using h1
    · have key : ∀ y : TensorProduct ℚ_[l] V (UpperTheory.V.Loc.Bcr l),
          LinearMap.rTensor (UpperTheory.V.Loc.Bcr l) f
            (UpperTheory.V.Loc.actC ((MonoidHom.snd _ _).comp (decJ F j).subtype)
              (ρ.comp ((MonoidHom.fst _ _).comp (decJ F j).subtype)) g y) =
          UpperTheory.V.Loc.actC ((MonoidHom.snd _ _).comp (decJ F j).subtype)
            (ρ'.comp ((MonoidHom.fst _ _).comp (decJ F j).subtype)) g
            (LinearMap.rTensor (UpperTheory.V.Loc.Bcr l) f y) := by
        intro y
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul a b => simp [UpperTheory.V.Loc.actC, hf]
        | add a b ha hb => simp only [map_add (f := _), ha, hb]
      rw [← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoTwCont
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato

private theorem cont_units {Γ R : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Monoid R]
    [TopologicalSpace R] (f : Γ →* Rˣ) (h : Continuous fun s => (f s : R)) : Continuous f := by
  rw [Units.continuous_iff]
  refine ⟨h, ?_⟩
  have : (fun x => ((f x)⁻¹ : Rˣ).val) = (fun s => (f s : R)) ∘ (fun x => x⁻¹) := by
    funext x
    simp [map_inv]
  rw [this]
  exact h.comp continuous_inv

private theorem cont_of_ker {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (f : Γ →* H) (U : Set Γ) (hU : IsOpen U) (h1 : 1 ∈ U)
    (h : ∀ s ∈ U, f s = 1) : Continuous f := by
  apply continuous_of_continuousAt_one
  have hev : (fun _ : Γ => (1 : H)) =ᶠ[nhds 1] f :=
    Filter.eventually_of_mem (hU.mem_nhds h1) fun s hs => (h s hs).symm
  exact (continuousAt_const (y := (1 : H))).congr hev

private theorem cont_kills {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (M : ℕ) (hM : 1 ≤ M) (φ : G ℚ Ω →* (Qbar l)ˣ) (hφ : KillsMu M φ) : Continuous φ := by
  classical
  have hS : {ζ : Ω | ζ ^ M = 1} = ((Polynomial.nthRoots M (1 : Ω)).toFinset : Set Ω) := by
    ext ζ
    simp [Polynomial.mem_nthRoots (by omega : 0 < M)]
  haveI : Finite ↥{ζ : Ω | ζ ^ M = 1} := by
    rw [hS]
    infer_instance
  let E := IntermediateField.adjoin ℚ {ζ : Ω | ζ ^ M = 1}
  haveI : FiniteDimensional ℚ E :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine cont_of_ker φ (E.fixingSubgroup : Set (G ℚ Ω)) E.fixingSubgroup_isOpen E.fixingSubgroup.one_mem ?_
  intro s hs
  apply hφ
  intro ζ hζ
  exact (IntermediateField.mem_fixingSubgroup_iff E s).mp hs ζ (IntermediateField.subset_adjoin ℚ _ hζ)

theorem UpperTheory.V.X.Kato.twCont :
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (W : G ℚ Ω →* GL (Fin n) (Qbar l)), Continuous W → ∀ (M : ℕ), 1 ≤ M → ∀ φ : G ℚ Ω →* (Qbar l)ˣ, KillsMu M φ → ∀ j : ℤ, Continuous (tw W (cycBar ℚ Ω l ^ j * φ)) := by
  intro l _ Ω _ _ _ n W hW M hM φ hφ j
  have hc1 : Continuous fun s : G ℚ Ω => ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) :=
    (Units.continuous_val (M := ℤ_[l])).comp (continuous_cycZ ℚ Ω l)
  have hc2 : Continuous fun x : ℤ_[l] => (x : ℚ_[l]) := continuous_subtype_val
  have hcyc : Continuous (cycBar ℚ Ω l) := by
    apply cont_units
    exact (continuous_algebraMap ℚ_[l] (Qbar l)).comp (hc2.comp hc1)
  have hχ : Continuous (cycBar ℚ Ω l ^ j * φ) := by
    have e : ⇑(cycBar ℚ Ω l ^ j * φ) = fun s => (cycBar ℚ Ω l s) ^ j * φ s := by
      funext s
      simp
    rw [e]
    exact (hcyc.zpow j).mul (cont_kills M hM φ hφ)
  apply cont_units
  have e2 : (fun s => (((tw W (cycBar ℚ Ω l ^ j * φ)) s : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))) =
      fun s => ((cycBar ℚ Ω l ^ j * φ) s : Qbar l) • (W s : Matrix (Fin n) (Fin n) (Qbar l)) :=
    funext (tw_val W _)
  rw [e2]
  exact (Units.continuous_val.comp hχ).smul (Units.continuous_val.comp hW)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcCycKFacts
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

private theorem hom_eq {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] (f : ℤ_[l] →+* k) (x : ℤ_[l]) :
    ZMod.castHom (dvd_pow_self l one_ne_zero) k (PadicInt.toZModPow 1 x) = f x := by
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective (PadicInt.toZModPow 1 x)
  have h : x - n ∈ RingHom.ker (PadicInt.toZModPow (p := l) 1) := by
    rw [RingHom.mem_ker, map_sub, map_intCast, hn, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h
  obtain ⟨y, hy⟩ := h
  rw [← hn, map_intCast, sub_eq_iff_eq_add.1 hy, map_add (f := _), map_mul, map_pow, map_natCast, CharP.cast_eq_zero, map_intCast]
  simp

theorem UpperTheory.V.X.cycKFacts :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l], (∀ σ : G ℚ Ω, IsCC σ → cycK Ω l k σ = -1) ∧ ∀ (c : Coef l) (red : c.O →+* k) (g : G ℚ Ω), (cycK Ω l k g : k) = red (chiO ℚ Ω l c.O g : c.O) := by
  intro Ω _ _ _ l hl k _ _
  refine ⟨fun σ hσ => ?_, fun c red g => hom_eq (red.comp (algebraMap ℤ_[l] c.O)) (cycZ ℚ Ω l g : ℤ_[l]ˣ)⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.out.ne_zero⟩
  have h1 : Chr.cls ℚ Ω (l ^ 1) σ = cycMod ℚ Ω l 1 σ := (Chr.clsFacts ℚ Ω (l ^ 1)).2.2.1 σ _ fun ζ hζ =>
      cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[ℚ] Ω) Ω σ) ζ hζ
  have h2 : Chr.cls ℚ Ω (l ^ 1) σ = -1 := (Chr.clsFacts ℚ Ω (l ^ 1)).2.2.2.1 σ hσ
  refine Units.ext ?_
  show ZMod.castHom (dvd_pow_self l one_ne_zero) k (cycMod ℚ Ω l 1 σ : (ZMod (l ^ 1))ˣ) = _
  rw [← h1, h2]
  simp only [Units.val_neg, Units.val_one, map_neg, map_one]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Th1Facts
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

private theorem arith (l n : ℕ) (hl : l.Prime) (hl2 : l ≠ 2) (hn : 0 < n) (hnd : ¬ l ∣ n) :
    0 < orderOf (l : ZMod (Nat.lcm 4 n)) ∧ Nat.lcm 4 n ∣ l ^ orderOf (l : ZMod (Nat.lcm 4 n)) - 1 := by
  have hm0 : Nat.lcm 4 n ≠ 0 := Nat.lcm_ne_zero (by norm_num) hn.ne'
  haveI : NeZero (Nat.lcm 4 n) := ⟨hm0⟩
  have h2 : Nat.Coprime l 2 := (Nat.coprime_primes hl Nat.prime_two).mpr hl2
  have h4 : Nat.Coprime l 4 := by
    have e := Nat.Coprime.pow_right 2 h2
    norm_num at e
    exact e
  have hn' : Nat.Coprime l n := (Nat.Prime.coprime_iff_not_dvd hl).mpr hnd
  have hc : Nat.Coprime l (Nat.lcm 4 n) :=
    Nat.Coprime.coprime_dvd_right (Nat.lcm_dvd_mul 4 n) (Nat.Coprime.mul_right h4 hn')
  have hue : ((ZMod.unitOfCoprime l hc : (ZMod (Nat.lcm 4 n))ˣ) : ZMod (Nat.lcm 4 n)) = (l : ZMod (Nat.lcm 4 n)) :=
    ZMod.coe_unitOfCoprime l hc
  have hord : orderOf (l : ZMod (Nat.lcm 4 n)) = orderOf (ZMod.unitOfCoprime l hc) := by
    rw [← hue, orderOf_units]
  refine ⟨by rw [hord]; exact orderOf_pos _, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hl.pos), Nat.cast_pow,
    pow_orderOf_eq_one, Nat.cast_one, sub_self]

theorem UpperTheory.V.X.th1Facts :
    ∀ (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N] (ψ : DirichletCharacter O N) (l : ℕ), l.Prime → l ≠ 2 → ψ = psi2 ψ * th1 l ψ * kap l ψ ∧ (∃ s, kap l ψ ^ l ^ s = 1) ∧ Odd (th1 l ψ ^ 2).conductor ∧ 0 < f0 l ψ ∧ 4 ∣ l ^ f0 l ψ - 1 ∧ th1 l ψ ^ (l ^ f0 l ψ - 1) = 1 ∧ l - 1 ∣ l ^ f0 l ψ - 1 := by
  intro O _ _ N _ ψ l hl hl2
  obtain ⟨-, hmul, hone, hinv, hpow, hidem, -, -⟩ := compAlg O N 2 Nat.prime_two
  have hfin : 0 < orderOf ψ := orderOf_pos ψ
  obtain ⟨hoK, -, hndvd, -, -, -, -⟩ := partOrd _ l hl ψ hfin
  have hkapOrd : orderOf (kap l ψ) = l ^ (orderOf ψ).factorization l := hoK
  have hc2k : comp 2 (kap l ψ) = 1 := by
    obtain ⟨k, hk⟩ := (compOrd O N (kap l ψ) 2 Nat.prime_two).2.1
    have hd : orderOf (comp 2 (kap l ψ)) ∣ orderOf (kap l ψ) := (hidem (kap l ψ)).2.1
    rw [hk, hkapOrd] at hd
    have hk0 : k = 0 := by
      by_contra hk0
      have h2 : 2 ∣ l ^ (orderOf ψ).factorization l := dvd_trans (dvd_pow_self 2 hk0) hd
      have e := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hl).mp (Nat.prime_two.dvd_of_dvd_pow h2)
      exact hl2 e.symm
    rw [hk0, pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  have hψ : th0 l ψ * kap l ψ = ψ := dirichletPrimeToLPart_mul_lPowerPart l ψ
  have hc2 : comp 2 ψ = comp 2 (th0 l ψ) := by
    conv_lhs => rw [← hψ]
    rw [hmul, hc2k, mul_one]
  have hth1c : comp 2 (th1 l ψ) = 1 := by
    show comp 2 (th0 l ψ * (comp 2 (th0 l ψ))⁻¹) = 1
    rw [hmul, hinv, (hidem _).1, mul_inv_cancel]
  have hth1pow : th1 l ψ ^ orderOf (th0 l ψ) = 1 := by
    show (th0 l ψ * (comp 2 (th0 l ψ))⁻¹) ^ orderOf (th0 l ψ) = 1
    rw [mul_pow, inv_pow, ← hpow, pow_orderOf_eq_one, hone, inv_one, mul_one]
  have hdvd1 : orderOf (th1 l ψ) ∣ orderOf (th0 l ψ) := orderOf_dvd_of_pow_eq_one hth1pow
  have hnd1 : ¬ l ∣ orderOf (th1 l ψ) := fun h => hndvd (dvd_trans h hdvd1)
  have hpos1 : 0 < orderOf (th1 l ψ) := orderOf_pos _
  obtain ⟨hf0, hdiv⟩ := arith l (orderOf (th1 l ψ)) hl hl2 hpos1 hnd1
  have hf : f0 l ψ = orderOf ((l : ZMod (Nat.lcm 4 (orderOf (th1 l ψ))))) := rfl
  refine ⟨?_, ⟨(orderOf ψ).factorization l, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · show ψ = comp 2 ψ * (th0 l ψ * (comp 2 (th0 l ψ))⁻¹) * kap l ψ
    rw [hc2, mul_comm (comp 2 (th0 l ψ)) (th0 l ψ * _), inv_mul_cancel_right]
    exact hψ.symm
  · rw [← hkapOrd]
    exact pow_orderOf_eq_one _
  · have h1 : comp 2 (th1 l ψ ^ 2) = 1 := by
      rw [hpow, hth1c, one_pow]
    have h := ((compCond O N (th1 l ψ ^ 2) 2 Nat.prime_two).2.1).mp h1
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h)
  · rw [hf]
    exact hf0
  · rw [hf]
    exact dvd_trans (Nat.dvd_lcm_left 4 _) hdiv
  · rw [hf]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_trans (Nat.dvd_lcm_right 4 _) hdiv)
  · have e := Nat.sub_dvd_pow_sub_pow l 1 (f0 l ψ)
    rwa [one_pow] at e
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcGalIdx
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

namespace UpperTheory.V.X.GaloisIndexPlaces

private theorem prime_p {l : ℕ} (hl : l.Prime) : Prime ((l : ℕ) : 𝓞 ℚ) := by
  have h : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  rw [← MulEquiv.prime_iff Rat.ringOfIntegersEquiv, map_natCast]
  exact h

private noncomputable def vQ (l : ℕ) (hl : l.Prime) : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_p hl).ne_zero).mpr (prime_p hl)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_p hl).ne_zero

private theorem mem_vQ (l : ℕ) (hl : l.Prime) : ((l : ℕ) : 𝓞 ℚ) ∈ (vQ l hl).asIdeal :=
  Ideal.mem_span_singleton_self _

private theorem eq_vQ (l : ℕ) (hl : l.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (h : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    vQ l hl = v := by
  apply HeightOneSpectrum.ext
  have hle : (vQ l hl).asIdeal ≤ v.asIdeal := by
    show Ideal.span {((l : ℕ) : 𝓞 ℚ)} ≤ v.asIdeal
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact h
  exact (vQ l hl).isMaximal.eq_of_le v.isPrime.ne_top hle

private theorem vQ_inj {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : vQ p hp = vQ q hq) : p = q := by
  have h1 : ((p : ℕ) : 𝓞 ℚ) ∈ (vQ q hq).asIdeal := h ▸ mem_vQ p hp
  have h2 : ((q : ℕ) : 𝓞 ℚ) ∣ ((p : ℕ) : 𝓞 ℚ) := Ideal.mem_span_singleton.1 h1
  have h3 := map_dvd Rat.ringOfIntegersEquiv h2
  simp only [map_natCast] at h3
  exact ((Nat.prime_dvd_prime_iff_eq hq hp).1 (Int.natCast_dvd_natCast.1 h3)).symm

private theorem isPlaceOver_vQ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) (hl : l.Prime)
    (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) : IsPlaceOver (F := ℚ) A (vQ l hl) := by
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨hne, htop, hab, -⟩ := UpperTheory.V.Base.places ℚ Ω l A
  have hAT : A ≠ ⊤ := by
    intro hT
    exact (htop hT).2 hA
  obtain ⟨v, hv⟩ := hne hAT
  have hlv : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := (hab v hv).mp hA
  rw [eq_vQ l hl v hlv]
  exact hv

end UpperTheory.V.X.GaloisIndexPlaces

open UpperTheory.V.X.GaloisIndexPlaces in
theorem UpperTheory.V.X.galIdx :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) {SP : Set (HeightOneSpectrum (𝓞 ℚ))} {T Q : Finset ℕ} (v0 : T) {pl : ℕ → ValuationSubring Ω} {K : Subgroup (G ℚ Ω)}, GalData l SP T Q pl K → ∃ (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (e : T ⊕ Q ≃ S), SP = S ∧ (∀ v : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → v ∈ S) ∧ (∀ v : T, IsPlaceOver (pl v) (e (.inl v)).1) ∧ ∀ q : Q, IsPlaceOver (pl q) (e (.inr q)).1 := by
  classical
  intro Ω _ _ _ l SP T Q v0 pl K hD
  have hex : ∃ f : ℕ → HeightOneSpectrum (𝓞 ℚ), ∀ (p : ℕ) (hp : Nat.Prime p), f p = vQ p hp :=
    ⟨fun p => if hp : Nat.Prime p then vQ p hp else vQ 2 Nat.prime_two, fun p hp => dif_pos hp⟩
  obtain ⟨f, hf⟩ := hex
  have hpr : ∀ p, p ∈ T ∨ p ∈ Q → p.Prime := hD.prime
  have hmemS : ∀ p, p ∈ T ∨ p ∈ Q → f p ∈ (T ∪ Q).image f := by
    intro p hp
    exact Finset.mem_image_of_mem f (Finset.mem_union.mpr hp)
  have hfinj : ∀ p q, (p ∈ T ∨ p ∈ Q) → (q ∈ T ∨ q ∈ Q) → f p = f q → p = q := by
    intro p q hp hq he
    rw [hf p (hpr p hp), hf q (hpr q hq)] at he
    exact vQ_inj _ _ he
  let g : T ⊕ Q → (T ∪ Q).image f := fun x => match x with
    | .inl p => ⟨f p, hmemS p (Or.inl p.2)⟩
    | .inr q => ⟨f q, hmemS q (Or.inr q.2)⟩
  have hg : Function.Bijective g := by
    constructor
    · rintro (⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩) he <;> simp only [g, Subtype.mk.injEq] at he
      · have := hfinj a b (Or.inl ha) (Or.inl hb) he
        subst this
        rfl
      · have := hfinj a b (Or.inl ha) (Or.inr hb) he
        subst this
        exact absurd hb (Finset.disjoint_left.mp hD.disj ha)
      · have := hfinj a b (Or.inr ha) (Or.inl hb) he
        subst this
        exact absurd ha (Finset.disjoint_left.mp hD.disj hb)
      · have := hfinj a b (Or.inr ha) (Or.inr hb) he
        subst this
        rfl
    · rintro ⟨s, hs⟩
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hs
      rcases Finset.mem_union.mp hp with hp | hp
      · exact ⟨.inl ⟨p, hp⟩, rfl⟩
      · exact ⟨.inr ⟨p, hp⟩, rfl⟩
  refine ⟨(T ∪ Q).image f, Equiv.ofBijective g hg, ?_, ?_, ?_, ?_⟩
  · ext v
    rw [hD.mem v, Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro ⟨p, hp, hpv⟩
      refine ⟨p, Finset.mem_union.mpr hp, ?_⟩
      rw [hf p (hpr p hp)]
      exact eq_vQ p _ v hpv
    · rintro ⟨p, hp, rfl⟩
      have hp' := Finset.mem_union.mp hp
      refine ⟨p, hp', ?_⟩
      rw [hf p (hpr p hp')]
      exact mem_vQ p _
  · intro v hv
    have hl : l ∈ T ∨ l ∈ Q := Or.inl hD.l_mem
    have : f l = v := by
      rw [hf l (hpr l hl)]
      exact eq_vQ l _ v hv
    rw [← this]
    exact hmemS l hl
  · intro p
    have hp : (p : ℕ) ∈ T ∨ (p : ℕ) ∈ Q := Or.inl p.2
    show IsPlaceOver (pl p) (f p)
    rw [hf p (hpr p hp)]
    exact isPlaceOver_vQ p _ (pl p) (hD.isOver p hp)
  · intro q
    have hq : (q : ℕ) ∈ T ∨ (q : ℕ) ∈ Q := Or.inr q.2
    show IsPlaceOver (pl q) (f q)
    rw [hf q (hpr q hq)]
    exact isPlaceOver_vQ q _ (pl q) (hD.isOver q hq)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDirVal
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

theorem UpperTheory.V.X.dirVal :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M : ℕ) [NeZero M] (g : G ℚ Ω), ∃ a : ℤ, IsCoprime a M ∧ ∀ (N : ℕ) [NeZero N], N ∣ M → ∀ (O : Type) [CommRing O] (χ : DirichletCharacter O N), (Chr.dirG ℚ Ω χ g : O) = χ a := by
  intro Ω _ _ _ M _ g
  refine ⟨(((Chr.cls ℚ Ω M g : (ZMod M)ˣ) : ZMod M).val : ℕ), ?_, fun N _ h O _ χ => ?_⟩
  · exact Nat.isCoprime_iff_coprime.2 (ZMod.val_coe_unit_coprime _)
  · have h1 := DFunLike.congr_fun ((Chr.clsFacts ℚ Ω M).2.1 N h) g
    have h2 : ((Chr.cls ℚ Ω N g : (ZMod N)ˣ) : ZMod N) = ((((Chr.cls ℚ Ω M g : (ZMod M)ˣ) : ZMod M).val : ℕ) : ZMod N) := by
      rw [← h1, MonoidHom.comp_apply, ZMod.unitsMap_val, ZMod.natCast_val]
    rw [Int.cast_natCast, ← h2]
    exact MulChar.coe_toUnitHom χ _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcVanOf
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

theorem UpperTheory.V.X.vanOf :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (k : Type) [Field k] (γ : G ℚ Ω →* kˣ), (∀ z : G ℚ Ω → k, ML.IsCoc γ z → UnrEv l γ z → ∃ m : k, ∀ g, z g = (γ g : k) * m - m) → ∀ (T : Finset ℕ) (pl : ℕ → ValuationSubring Ω) (K : Subgroup (G ℚ Ω)), (∀ p ∈ T, p.Prime ∧ (pl p).valuation (p : Ω) < 1) → K.Normal → ¬ l ∣ K.index → Van T pl K γ := by
  intro Ω _ _ _ l _ k _ γ hL T pl K hT hKn hKl z hzlc hzc hzI hzD
  have hlp : l.Prime := Fact.out
  have hz1 : z 1 = 0 := by
    have h := hzc 1 1
    simp only [mul_one, map_one, Units.val_one, one_mul] at h
    simpa using h
  have hconj : ∀ g x, (γ x : k) = 1 → z (g⁻¹ * x * g) = (γ g⁻¹ : k) * z x := by
    intro g x hx
    have h0 : z g⁻¹ + (γ g⁻¹ : k) * z g = 0 := by rw [← hzc, inv_mul_cancel, hz1]
    rw [mul_assoc, hzc, hzc, hx]
    linear_combination h0
  apply hL z ⟨hzlc, fun g h => by rw [hzc, smul_eq_mul]⟩
  intro A
  by_cases hA : ∀ p ∈ T, ¬ A.valuation (p : Ω) < 1
  · refine ⟨K, fun h => hKl (dvd_trans h (Subgroup.relIndex_dvd_index_of_normal _ _)), ?_⟩
    intro g hgK hgA _
    exact hzI A hA g hgA hgK
  · push_neg at hA
    obtain ⟨p, hpT, hAp⟩ := hA
    obtain ⟨hpp, hplp⟩ := hT p hpT
    obtain ⟨m, hm⟩ := hzD p hpT
    obtain ⟨g, hg⟩ := (B3.placesQ Ω).2.2 p (pl p) A hpp hplp hAp
    refine ⟨⊤, by rw [Subgroup.relIndex_top_left]; exact hlp.not_dvd_one, ?_⟩
    intro x _ hxA hγx
    have hγx' : (γ x : k) = 1 := by rw [hγx, Units.val_one]
    have hγc : (γ (g⁻¹ * x * g) : k) = 1 := by simp [map_mul, hγx]
    have hin : g⁻¹ * x * g ∈ Dec (pl p) := Ine_le_Dec (pl p) (hg x hxA)
    have h1 := hm _ hin
    rw [hconj g x hγx', hγc, one_mul, sub_self] at h1
    exact (mul_eq_zero.mp h1).resolve_left (Units.ne_zero _)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcPrimProd
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

theorem UpperTheory.V.X.primProd :
    ∀ (O : Type) [CommRing O] [IsDomain O] (M N : ℕ) [NeZero M] [NeZero N] (χ : DirichletCharacter O M) (θ : DirichletCharacter O N), ∃ (f : ℕ) (φ : DirichletCharacter O f), φ.IsPrimitive ∧ f ∣ M * θ.conductor ∧ (∀ t : ℕ, χ ^ t = 1 → θ ^ t = 1 → φ ^ t = 1) ∧ ∀ a : ℤ, IsCoprime a (M * N : ℕ) → φ a = χ a * θ a := by
  intro O _ _ M N _ _ χ θ
  have hc0 : θ.conductor ≠ 0 := θ.conductor_ne_zero
  haveI : NeZero θ.conductor := ⟨hc0⟩
  haveI : NeZero (M * θ.conductor) := ⟨mul_ne_zero (NeZero.ne M) hc0⟩
  set θ' := θ.primitiveCharacter with hθe
  have hM : M ∣ M * θ.conductor := dvd_mul_right M _
  have hC : θ.conductor ∣ M * θ.conductor := dvd_mul_left _ M
  set ψ : DirichletCharacter O (M * θ.conductor) :=
    DirichletCharacter.changeLevel hM χ * DirichletCharacter.changeLevel hC θ' with hψe
  refine ⟨ψ.conductor, ψ.primitiveCharacter, ψ.primitiveCharacter_isPrimitive, ψ.conductor_dvd_level, ?_, ?_⟩
  · intro t hχ hθ
    have hθ1 : θ' ^ t = 1 := by
      rw [← DirichletCharacter.changeLevel_eq_one_iff θ.conductor_dvd_level, map_pow,
        DirichletCharacter.changeLevel_primitiveCharacter]
      exact hθ
    have hψ1 : ψ ^ t = 1 := by
      rw [hψe, mul_pow, ← map_pow, ← map_pow, hχ, hθ1, map_one, map_one, mul_one]
    rw [← DirichletCharacter.changeLevel_eq_one_iff ψ.conductor_dvd_level, map_pow,
      DirichletCharacter.changeLevel_primitiveCharacter]
    exact hψ1
  · intro a ha
    rw [Nat.cast_mul] at ha
    have haM : IsCoprime a (M : ℤ) := ha.of_mul_right_left
    have haN : IsCoprime a (N : ℤ) := ha.of_mul_right_right
    have haC : IsCoprime a (θ.conductor : ℤ) :=
      haN.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr θ.conductor_dvd_level)
    have haMC : IsCoprime a ((M * θ.conductor : ℕ) : ℤ) := by
      rw [Nat.cast_mul]
      exact haM.mul_right haC
    rw [ψ.primitiveCharacter_apply_of_isCoprime haMC, hψe, MulChar.mul_apply,
      DirichletCharacter.changeLevel_eq_cast_of_dvd' χ hM haMC,
      DirichletCharacter.changeLevel_eq_cast_of_dvd' θ' hC haMC,
      θ.primitiveCharacter_apply_of_isCoprime haN]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcUnrOf
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

theorem UpperTheory.V.X.unrOf :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (k : Type) [Field k] (γ : G ℚ Ω →* kˣ) (K : Subgroup (G ℚ Ω)) [K.Normal], K ≤ γ.ker → ∀ (SP : Set (HeightOneSpectrum (𝓞 ℚ))) (T : Finset ℕ) (z : GS Ω SP → k), (∀ g h, z (toGS Ω SP (g * h)) = z (toGS Ω SP g) + (γ g : k) * z (toGS Ω SP h)) → (∀ v ∈ SP, (∃ p ∈ T, ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) ∨ ∃ A, IsPlaceOver A v ∧ ∀ g ∈ Ine (F := ℚ) A, g ∈ K → z (toGS Ω SP g) = 0) → ∀ A : ValuationSubring Ω, (∀ p ∈ T, ¬ A.valuation (p : Ω) < 1) → ∀ g ∈ Ine (F := ℚ) A, g ∈ K → z (toGS Ω SP g) = 0 := by
  intro Ω _ _ _ k _ γ K hKn hK SP T z hz hS A hA g hg hgK
  have h1 : z (toGS Ω SP 1) = 0 := by
    have e := hz 1 1
    rw [mul_one, map_one γ, Units.val_one, one_mul] at e
    linear_combination (-1 : k) * e
  obtain ⟨hTop, hPl, -, hAb⟩ := UpperTheory.V.Kum.placeDict ℚ Ω
  by_cases hAT : A = ⊤
  · subst hAT
    rw [hTop, Subgroup.mem_bot] at hg
    subst hg
    exact h1
  obtain ⟨v, hv⟩ := hPl A hAT
  by_cases hvS : v ∈ SP
  · rcases hS v hvS with ⟨p, hpT, hp⟩ | ⟨A', hA', hz0⟩
    · exact absurd ((hAb A v p hv).mpr hp) (hA p hpT)
    · obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hA' hv
      subst hσ
      have hc : σ⁻¹ * g * σ ∈ Ine (F := ℚ) A' := GlobalTheory.Cut.ShaBound.conj_mem_Ine' hg
      have hcK : σ⁻¹ * g * σ ∈ K := by
        have e := hKn.conj_mem g hgK σ⁻¹
        simpa only [inv_inv] using e
      have e0 := hz0 _ hc hcK
      have e1 := hz g σ
      have e2 := hz σ (σ⁻¹ * g * σ)
      have hγ : γ g = 1 := hK hgK
      have hm : σ * (σ⁻¹ * g * σ) = g * σ := by group
      rw [hγ, Units.val_one, one_mul] at e1
      rw [hm, e0, mul_zero, add_zero] at e2
      linear_combination e2 - e1
  · have hN : g ∈ NS Ω SP := by
      unfold NS
      apply Subgroup.le_topologicalClosure
      apply Subgroup.subset_normalClosure
      simp only [Set.mem_iUnion]
      exact ⟨v, hvS, A, hv, hg⟩
    have e : toGS Ω SP g = toGS Ω SP 1 := by
      rw [map_one]
      exact (QuotientGroup.eq_one_iff g).mpr hN
    rw [e]
    exact h1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLocCard
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

private theorem card_linearMap_zmod_eq_card (n : ℕ) [NeZero n] (N : Type) [AddCommGroup N] [Module (ZMod n) N]
    [Finite N] : Nat.card (N →ₗ[ZMod n] ZMod n) = Nat.card N := by
  classical
  have : Fintype N := Fintype.ofFinite N
  have hfinD : Finite (N →ₗ[ZMod n] ZMod n) :=
    Finite.of_injective (fun f : N →ₗ[ZMod n] ZMod n => (f : N → ZMod n)) DFunLike.coe_injective
  have hcard : Nat.card (AddChar N ℂ) = Nat.card N := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]
  apply le_antisymm
  · have hinj : Function.Injective
        (fun f : N →ₗ[ZMod n] ZMod n => ZMod.stdAddChar.compAddMonoidHom f.toAddMonoidHom) := by
      intro f g h
      have := AddChar.compAddMonoidHom_injective_right _ ZMod.injective_stdAddChar h
      ext x
      exact DFunLike.congr_fun this x
    rw [← hcard]
    exact Nat.card_le_card_of_injective _ hinj
  · let φ : AddChar N ℂ → N → AddChar (ZMod n) ℂ := fun ψ x =>
      ψ.compAddMonoidHom (LinearMap.toSpanSingleton (ZMod n) N x).toAddMonoidHom
    have hφ : ∀ ψ x y, φ ψ (x + y) = φ ψ x + φ ψ y := by
      intro ψ x y
      ext k
      simp [φ, smul_add, AddChar.map_add_eq_mul]
    let g : AddChar N ℂ → (N →ₗ[ZMod n] ZMod n) := fun ψ =>
      AddMonoidHom.toZModLinearMap n (AddMonoidHom.mk' (fun x => AddChar.zmodAddEquiv.symm (φ ψ x))
        (fun x y => by rw [hφ, map_add (f := _)]))
    have hg : Function.Injective g := by
      intro ψ ψ' h
      ext x
      have h1 : φ ψ x = φ ψ' x := by
        have := LinearMap.congr_fun h x
        simpa [g] using this
      have := DFunLike.congr_fun h1 1
      simpa [φ] using this
    rw [← hcard]
    exact Nat.card_le_card_of_injective g hg

theorem UpperTheory.V.X.So.locCard :
    LocalFiniteness → LocalTateDuality → ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ (v : HeightOneSpectrum (𝓞 k)) (A : ValuationSubring Ω), IsPlaceOver A v → ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation (ZMod (l ^ r)) (Dec (F := k) A) M), ContAction ρ → ∀ (τ : Representation (ZMod (l ^ r)) (Dec (F := k) A) (TDual (ZMod (l ^ r)) M)), (∀ g φ m, τ g φ m = (cycMod k Ω l r g : ZMod (l ^ r)) * φ (ρ g⁻¹ m)) → Finite (H1 ρ) ∧ Finite (H2 ρ) ∧ Nat.card (H2 ρ) = Nat.card (H0 τ) := by
  intro hfin hdual k Ω _ _ _ _ _ l _ r hr v A hA M _ _ _ _ _ ρ hcont τ hτ
  obtain ⟨-, h1, h2, -⟩ := hfin k Ω l r M A ρ v hr hA hcont
  obtain ⟨⟨e⟩, -, -, -, hb⟩ := hdual k Ω l r M A ρ v hr hA hcont
  refine ⟨h1, h2, ?_⟩
  have hτ' : τ = twDual ((cycMod k Ω l r).comp (Dec (F := k) A).subtype) ρ := by
    ext g φ
    apply DFunLike.ext
    intro m
    rw [hτ]
    rfl
  subst hτ'
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hfinD : Finite (TDual (ZMod (l ^ r)) M) :=
    Finite.of_injective (fun f : Module.Dual (ZMod (l ^ r)) M => (f : M → ZMod (l ^ r))) DFunLike.coe_injective
  have hA1 := Nat.card_congr (Equiv.ofBijective _ hb)
  have hA2 := Nat.card_congr (LinearEquiv.congrRight (M := ↥(H0 (MonoidHom.comp
    (twDual ((cycMod k Ω l r).comp (Dec (F := k) A).subtype) ρ) (MonoidHom.id ↥(Dec (F := k) A))))) e).toEquiv
  have hA3 := card_linearMap_zmod_eq_card (l ^ r) ↥(H0 (MonoidHom.comp
    (twDual ((cycMod k Ω l r).comp (Dec (F := k) A).subtype) ρ) (MonoidHom.id ↥(Dec (F := k) A))))
  exact hA1.trans (hA2.trans hA3)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcUrIndex
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

private theorem urIndex_mem {k D M : Type} [Field k] [Group D] [TopologicalSpace D] [AddCommGroup M] [Module k M]
    [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k D M) (J : Subgroup D) (f : Z1 ρ) :
    (Submodule.Quotient.mk f : H1 ρ) ∈ H1ur ρ J ↔ ∃ m, ∀ j ∈ J, f.1 j = ρ j m - m := by
  have hJc : Continuous J.subtype := continuous_subtype_val
  show resH1 ρ J.subtype hJc (Submodule.Quotient.mk f) = 0 ↔ _
  unfold resH1
  rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
  show ((restrictCocycles1 ρ J.subtype hJc f : Z1 (ρ.comp J.subtype)) : J → M) ∈ B1 (ρ.comp J.subtype) ↔ _
  rw [mem_coboundaries1]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, fun j hj => ?_⟩
    have h := hm ⟨j, hj⟩
    rw [restrictCocycles1_apply ρ J.subtype hJc] at h
    simpa using h
  · rintro ⟨m, hm⟩
    refine ⟨m, fun j => ?_⟩
    rw [restrictCocycles1_apply ρ J.subtype hJc]
    simpa using hm j j.2

private theorem urIndex_avg {k Γ M : Type} [Field k] [Group Γ] [AddCommGroup M] [Module k M]
    (ρ : Representation k Γ M) (N : Subgroup Γ) (hN : (N.index : k) ≠ 0) (c : Γ → M)
    (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) (h0 : ∀ n ∈ N, c n = 0) :
    ∃ m, ∀ g, c g = ρ g m - m := by
  classical
  have hNi : N.index ≠ 0 := fun h => hN (by rw [h, Nat.cast_zero])
  haveI : N.FiniteIndex := ⟨hNi⟩
  haveI : Fintype (Γ ⧸ N) := Fintype.ofFinite _
  have hconst : ∀ g n, n ∈ N → c (g * n) = c g := fun g n hn => by
    rw [hc, h0 n hn, map_zero, add_zero]
  let c' : Γ ⧸ N → M := Quotient.lift (s := QuotientGroup.leftRel N) c (fun a b hab => by
    have hab' : a⁻¹ * b ∈ N := QuotientGroup.leftRel_apply.1 hab
    have h := hconst a (a⁻¹ * b) hab'
    rw [mul_inv_cancel_left] at h
    exact h.symm)
  have hc' : ∀ (h : Γ) (x : Γ ⧸ N), c' (h • x) = c h + ρ h (c' x) := by
    intro h x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    show c (h * g) = c h + ρ h (c g)
    exact hc h g
  let S := ∑ x : Γ ⧸ N, c' x
  have hS : ∀ h, S = Fintype.card (Γ ⧸ N) • c h + ρ h S := by
    intro h
    calc S = ∑ x, c' (h • x) := (Equiv.sum_comp (MulAction.toPerm h) c').symm
      _ = ∑ x, (c h + ρ h (c' x)) := Finset.sum_congr rfl fun x _ => hc' h x
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, map_sum]
  have hcard : (Fintype.card (Γ ⧸ N) : k) = N.index := by
    rw [Fintype.card_eq_nat_card]
    rfl
  refine ⟨-((N.index : k)⁻¹ • S), fun g => ?_⟩
  have h1 := hS g
  have h2 : S - ρ g S = (N.index : k) • c g := by
    rw [← hcard, Nat.cast_smul_eq_nsmul]
    nth_rewrite 1 [h1]
    rw [add_sub_cancel_right]
  rw [map_neg, map_smul, neg_sub_neg, ← smul_sub, h2, smul_smul, inv_mul_cancel₀ hN, one_smul]

theorem UpperTheory.V.X.urIndex :
    ∀ (l : ℕ) [Fact l.Prime] {k D M : Type} [Field k] [CharP k l] [Group D] [TopologicalSpace D] [AddCommGroup M] [Module k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k D M), ContAction ρ → ∀ (I N : Subgroup D), N ≤ I → ¬ l ∣ N.relIndex I → H1ur ρ N = H1ur ρ I := by
  intro l _ k D M _ _ _ _ _ _ _ _ ρ hρ I N hNI hl
  ext c
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (Submodule.comap (Z1 ρ).subtype (B1 ρ)) c
  refine (urIndex_mem ρ N f).trans (Iff.trans ?_ (urIndex_mem ρ I f).symm)
  constructor
  · rintro ⟨m, hm⟩
    have hf := ((mem_Z1_iff_cocycle ρ _).1 f.2).2
    let cI : I → M := fun j => f.1 j - (ρ j m - m)
    have hcI : ∀ g h : I, cI (g * h) = cI g + (ρ.comp I.subtype) g (cI h) := by
      intro g h
      simp only [cI, MonoidHom.comp_apply, Subgroup.coe_subtype, Subgroup.coe_mul, hf, map_mul,
        Module.End.mul_apply, map_sub]
      abel
    have h0 : ∀ n ∈ N.subgroupOf I, cI n = 0 := fun n hn => by
      simp only [cI]
      rw [hm n (Subgroup.mem_subgroupOf.1 hn), sub_self]
    have hidx : ((N.subgroupOf I).index : k) ≠ 0 := by
      have e : (N.subgroupOf I).index = N.relIndex I := rfl
      rw [e]
      intro h
      exact hl ((CharP.cast_eq_zero_iff k l _).1 h)
    obtain ⟨m', hm'⟩ := urIndex_avg (ρ.comp I.subtype) (N.subgroupOf I) hidx cI hcI h0
    refine ⟨m + m', fun j hj => ?_⟩
    have h := hm' ⟨j, hj⟩
    simp only [cI, MonoidHom.comp_apply, Subgroup.coe_subtype] at h
    rw [sub_eq_iff_eq_add] at h
    rw [h, map_add (f := _)]
    abel
  · rintro ⟨m, hm⟩
    exact ⟨m, fun j hj => hm j (hNI hj)⟩
end
