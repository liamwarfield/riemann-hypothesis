module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.RankCard

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.Strict
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem exists_natCard_eq_pow_and_separating_zmod_forms (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod l) M]
    [Finite M] : ∃ (d : ℕ) (c : Fin d → M →+ ZMod l), Nat.card M = l ^ d ∧
      ∀ x y : M, (∀ i, c i x = c i y) → x = y := by
  refine ⟨Module.finrank (ZMod l) M,
    fun i => ((Module.finBasis (ZMod l) M).coord i).toAddMonoidHom, ?_, ?_⟩
  · letI : Fintype M := Fintype.ofFinite M
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod l), ZMod.card]
  · intro x y h
    apply (Module.finBasis (ZMod l) M).ext_elem
    intro i
    simpa [Module.Basis.coord_apply] using h i

private theorem eq_zero_of_nsmul_eq_zero_of_coprime_torsion (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M]
    (htor : ∀ m : M, l • m = 0) (n : ℕ) (hn : ¬ l ∣ n) (x : M) (hx : n • x = 0) : x = 0 := by
  have hcop : Nat.Coprime n l :=
    Nat.coprime_comm.mp ((Fact.out : l.Prime).coprime_iff_not_dvd.mpr hn)
  have h := Nat.gcd_eq_gcd_ab n l
  rw [hcop.gcd_eq_one, Nat.cast_one] at h
  calc x = (1 : ℤ) • x := (one_zsmul x).symm
    _ = ((n : ℤ) * Nat.gcdA n l + (l : ℤ) * Nat.gcdB n l) • x := by rw [h]
    _ = Nat.gcdA n l • (n • x) + Nat.gcdB n l • (l • x) := by
      rw [add_smul, mul_comm (n : ℤ), mul_comm (l : ℤ), mul_smul, mul_smul, natCast_zsmul,
        natCast_zsmul]
    _ = 0 := by rw [hx, htor, smul_zero, smul_zero, add_zero]

theorem UpperTheory.V.Ws.card_cocycles_vanishing_on_inertia_le_pow :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M], (∀ m : M, l • m = 0) → ∀ (ρ : Representation R (G F Ω) M) (K : Subgroup (G F Ω)) (r : ℕ), ¬ l ∣ K.index → (∀ g ∈ K, ∀ m, ρ g m = m) → XRk l 1 K r → CardLe (cocOff ρ (ineOff F Ω 1 ∩ K)) (Nat.card M ^ (r + 1)) := by
  intro F Ω _ _ _ _ _ l _ R M _ _ _ _ htor ρ K r hdvd hK hX
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hidx : K.index ≠ 0 := fun h => hdvd (h ▸ dvd_zero l)
  haveI : K.FiniteIndex := ⟨hidx⟩
  letI : Fintype (G F Ω ⧸ K) := Fintype.ofFinite _
  have hn : ¬ l ∣ Fintype.card (G F Ω ⧸ K) := by
    rw [← Nat.card_eq_fintype_card]
    exact hdvd
  have key : ∀ w : G F Ω → M, (∀ g h, w (g * h) = w g + ρ g (w h)) → (∀ k ∈ K, w k = 0) →
      (∑ q : G F Ω ⧸ K, w q.out) = 0 → w = 0 := by
    intro w hw hwK hS
    funext h
    show w h = 0
    have e1 : ∀ q : G F Ω ⧸ K, w (h * q.out) = w (h • q).out := by
      intro q
      have hq : ((h * q.out : G F Ω) : G F Ω ⧸ K) = h • q := by
        show ((h • q.out : G F Ω) : G F Ω ⧸ K) = h • q
        rw [← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
      have hk : (h * q.out)⁻¹ * (h • q).out ∈ K :=
        QuotientGroup.eq.mp (hq.trans (QuotientGroup.out_eq' _).symm)
      have := hw (h * q.out) ((h * q.out)⁻¹ * (h • q).out)
      rw [mul_inv_cancel_left, hwK _ hk, map_zero, add_zero] at this
      exact this.symm
    have hsum : ∑ q : G F Ω ⧸ K, w (h * q.out) = ∑ q : G F Ω ⧸ K, w q.out := by
      rw [Finset.sum_congr rfl (fun q _ => e1 q)]
      exact Equiv.sum_comp (MulAction.toPerm h) (fun q : G F Ω ⧸ K => w q.out)
    have hexp : ∑ q : G F Ω ⧸ K, w (h * q.out) =
        Fintype.card (G F Ω ⧸ K) • w h + ρ h (∑ q : G F Ω ⧸ K, w q.out) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hw, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, map_sum]
    rw [hsum, hS, map_zero, add_zero] at hexp
    exact eq_zero_of_nsmul_eq_zero_of_coprime_torsion l M htor _ hn (w h) hexp.symm
  obtain ⟨hXfin, hXcard⟩ := hX
  obtain ⟨d, c, hM, hc⟩ := @exists_natCard_eq_pow_and_separating_zmod_forms l _ M _ (AddCommGroup.zmodModule htor) _
  have mem : ∀ z : ↥(cocOff ρ (ineOff F Ω 1 ∩ (K : Set (G F Ω)))),
      IsLocallyConstant z.1 ∧ (∀ g h, z.1 (g * h) = z.1 g + ρ g (z.1 h)) ∧
        ∀ g ∈ ineOff F Ω 1 ∩ (K : Set (G F Ω)), z.1 g = 0 := fun z => z.2
  have hone : ∀ A : ValuationSubring Ω, ¬ A.valuation ((1 : ℕ) : Ω) < 1 := by
    intro A
    simp
  have coordMem : ∀ (z : ↥(cocOff ρ (ineOff F Ω 1 ∩ (K : Set (G F Ω))))) (i : Fin d),
      (fun u : K => c i (z.1 u)) ∈ UpperTheory.V.Kum.XDual (F := F) (Ω := Ω) 1 K (ZMod l) (ZMod l) := by
    intro z i
    obtain ⟨hlc, hcoc, hvan⟩ := mem z
    have hφ : IsLocallyConstant (fun u : K => c i (z.1 u)) ∧
        (∀ a e : K, c i (z.1 ↑(a * e)) = c i (z.1 a) + c i (z.1 e)) ∧
        (∀ (A : ValuationSubring Ω) (u : K), (u : G F Ω) ∈ Ine A → c i (z.1 u) = 0) ∧
        ∀ (A : ValuationSubring Ω), A.valuation ((1 : ℕ) : Ω) < 1 → ∀ u : K, (u : G F Ω) ∈ Dec A →
          c i (z.1 u) = 0 := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact (hlc.comp_continuous continuous_subtype_val).comp (fun m => c i m)
      · intro a e
        rw [Subgroup.coe_mul, hcoc, hK a a.2, map_add (f := _)]
      · intro A u hu
        have hin : (u : G F Ω) ∈ ineOff F Ω 1 := by
          show ∃ A, _
          exact ⟨A, hone A, hu⟩
        rw [hvan u ⟨hin, u.2⟩, map_zero]
      · intro A hA
        exact absurd hA (hone A)
    exact hφ
  let Φ : ↥(cocOff ρ (ineOff F Ω 1 ∩ (K : Set (G F Ω)))) →
      (Fin d → ↥(UpperTheory.V.Kum.XDual (F := F) (Ω := Ω) 1 K (ZMod l) (ZMod l))) × M :=
    fun z => (fun i => ⟨_, coordMem z i⟩, ∑ q : G F Ω ⧸ K, z.1 q.out)
  have hinj : Function.Injective Φ := by
    intro z z' hzz
    have h2 : (∑ q : G F Ω ⧸ K, z.1 q.out) = ∑ q : G F Ω ⧸ K, z'.1 q.out :=
      congrArg Prod.snd hzz
    have hKeq : ∀ k ∈ K, z.1 k = z'.1 k := by
      intro k hk
      exact hc _ _ (fun i => congrArg (fun p => (p.1 i).1 ⟨k, hk⟩) hzz)
    obtain ⟨_, hcoc, -⟩ := mem z
    obtain ⟨_, hcoc', -⟩ := mem z'
    have hw := key (fun g => z.1 g - z'.1 g)
      (by
        intro g h
        simp only [hcoc, hcoc', map_sub]
        abel)
      (by
        intro k hk
        simp [hKeq k hk])
      (by simp only [Finset.sum_sub_distrib, h2, sub_self])
    apply Subtype.ext
    funext g
    exact sub_eq_zero.mp (congrFun hw g)
  haveI : Finite ↥(UpperTheory.V.Kum.XDual (F := F) (Ω := Ω) 1 K (ZMod l) (ZMod l)) := hXfin
  refine (show Finite _ ∧ Nat.card _ ≤ _ from ⟨Finite.of_injective Φ hinj, ?_⟩)
  calc Nat.card ↥(cocOff ρ (ineOff F Ω 1 ∩ (K : Set (G F Ω))))
      ≤ Nat.card ((Fin d → ↥(UpperTheory.V.Kum.XDual (F := F) (Ω := Ω) 1 K (ZMod l) (ZMod l))) × M) :=
        Nat.card_le_card_of_injective Φ hinj
    _ = Nat.card ↥(UpperTheory.V.Kum.XDual (F := F) (Ω := Ω) 1 K (ZMod l) (ZMod l)) ^ d * Nat.card M := by
        rw [Nat.card_prod, Nat.card_fun, Nat.card_fin]
    _ ≤ (l ^ r) ^ d * Nat.card M :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hXcard _)
    _ = Nat.card M ^ (r + 1) := by
        rw [hM]
        ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.StrResidueLeCocyclesVanishingOnInertiaKernel
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical Pointwise

theorem UpperTheory.V.Ws.str_residue_le_cocycles_vanishing_on_inertia_kernel :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (T : Tower D) (w : ℤ × ℤ), (T.fr ∅).Str (residue c.O) w ≤ cocOff (charRep (T.rbU w)) (ineOff T.F Ω 1 ∩ T.Kr) := by
  intro Ω _ _ _ l _ c D hG T w z hz
  rw [Fr.Str, Submodule.mem_inf] at hz
  obtain ⟨⟨hlc, hcoc, hN, -⟩, n, hn⟩ := hz
  have hK := residualKernel_properties D hG T
  refine ⟨hlc, ?_, ?_⟩
  · intro g h
    rw [hcoc]
    simp [charRep, Tower.rbU]
  · rintro g ⟨⟨A, -, hgA⟩, hgK⟩
    have hrb : D.rbar (resQ T.F g) = 1 := hK.2.2.2.2.1 g hgK
    have hrt : residue c.O ((T.fr ∅).rt w g : c.O) = 1 := by
      have := congrArg Units.val (hK.2.2.2.2.2.1 w g hrb)
      simpa [Tower.rbU] using this
    by_cases hA : A.valuation (l : Ω) < 1
    · obtain ⟨v, ⟨σ, hσ⟩, -⟩ := T.cover A hA
      have hσA : σ⁻¹ • A = T.pl v := by
        ext x
        rw [ValuationSubring.mem_inv_pointwise_smul_iff]
        exact hσ x
      have hgA' : g • A = A := MulAction.mem_stabilizer_iff.1 hgA.1
      have hdec : σ⁻¹ * g * σ ∈ (T.fr ∅).Gv v := by
        show (σ⁻¹ * g * σ) • T.pl v = T.pl v
        rw [← hσA, mul_smul, mul_smul, smul_inv_smul, hgA']
      have hconj : (T.fr ∅).rt w (σ⁻¹ * g * σ) = (T.fr ∅).rt w g := by
        rw [map_mul, map_mul, map_inv, mul_comm ((T.fr ∅).rt w σ)⁻¹, mul_assoc, inv_mul_cancel, mul_one]
      have hz0 : z (σ⁻¹ * g * σ) = 0 := by
        rw [hn v _ hdec, hconj, hrt, one_mul, sub_self]
      have hz1 : z 1 = 0 := by
        have := hcoc 1 1
        simpa using this
      have e1 := hcoc (σ⁻¹ * g) σ
      have e2 := hcoc σ⁻¹ g
      have e3 := hcoc σ⁻¹ σ
      rw [inv_mul_cancel, hz1] at e3
      have hmul : residue c.O ((T.fr ∅).rt w (σ⁻¹ * g) : c.O) = residue c.O ((T.fr ∅).rt w σ⁻¹ : c.O) := by
        rw [map_mul, Units.val_mul, map_mul, hrt, mul_one]
      rw [hmul, e2, hz0] at e1
      have hu : IsUnit (residue c.O ((T.fr ∅).rt w σ⁻¹ : c.O)) := ((T.fr ∅).rt w σ⁻¹).isUnit.map _
      have key : residue c.O ((T.fr ∅).rt w σ⁻¹ : c.O) * z g = 0 := by
        linear_combination e3 - e1
      exact (mul_eq_zero.1 key).resolve_left hu.ne_zero
    · refine hN g ?_
      refine ⟨A, ?_, hgA, hrb⟩
      intro p hp
      rw [Finset.mem_insert] at hp
      rcases hp with rfl | hp
      · exact hA
      · simp at hp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.CardGlobalCocyclesLeOfIwasawaRank
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.GwCount
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.ShaCard
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical
open scoped Pointwise

theorem UpperTheory.V.Ws.tate_shafarevich_card_mod_l :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (Av : S → ValuationSubring Ω) (K : Subgroup (G F Ω)) (r : ℕ), (∀ v, IsPlaceOver (Av v) v.1) → K.Normal → ¬ l ∣ K.index → (∀ g ∈ K, ∀ m, ρ (toGS Ω _ g) m = m) → XRk l 1 K r → CardLe (Sha1 ρ (locFam S Av) (continuous_locFam S Av)) (Nat.card M ^ (r + 1)) := by
  intro F Ω _ _ _ _ _ l hl M _ _ _ _ _ S ρ Av K r hA hN hK hρ hX
  have hM : ∀ m : M, l • m = 0 := by
    intro m
    rw [← Nat.cast_smul_eq_nsmul (ZMod (l ^ 1)) l m]
    have h0 : ((l : ℕ) : ZMod (l ^ 1)) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 (by rw [pow_one])
    rw [h0, zero_smul]
  have hB := UpperTheory.V.Ws.card_cocycles_vanishing_on_inertia_le_pow F Ω l (ZMod (l ^ 1)) M hM (ρ.comp (toGS Ω _)) K r hK hρ hX
  obtain ⟨p1, p2, -, -⟩ := UpperTheory.V.Kum.placeDict F Ω
  have hmem : ∀ z : Z1 ρ, (Submodule.Quotient.mk z : H1 ρ) ∈ Sha1 ρ (locFam S Av) (continuous_locFam S Av) →
      (fun g => z.1 (toGS Ω _ g)) ∈ cocOff (ρ.comp (toGS Ω _)) (ineOff F Ω 1 ∩ K) := by
    intro z hz
    have hz1 : z.1 1 = 0 := by
      have := z.2.2 1 1
      rw [one_mul, map_one, Module.End.one_apply] at this
      exact left_eq_add.1 this
    have hc : ∀ a b : G F Ω, z.1 (toGS Ω _ (a * b)) = z.1 (toGS Ω _ a) + ρ (toGS Ω _ a) (z.1 (toGS Ω _ b)) :=
      fun a b => by rw [map_mul, z.2.2]
    refine ⟨(IsLocallyConstant.iff_continuous _).2 (z.2.1.comp (continuous_toGS Ω _)), hc, ?_⟩
    rintro u ⟨⟨A, -, hu⟩, huK⟩
    show z.1 (toGS Ω _ u) = 0
    by_cases hT : A = ⊤
    · subst hT
      rw [p1, Subgroup.mem_bot] at hu
      rw [hu, map_one, hz1]
    obtain ⟨v, hv⟩ := p2 A hT
    by_cases hvS : v ∈ S
    · obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) (hA ⟨v, hvS⟩) hv
      have hd : g⁻¹ * u * g ∈ Dec (F := F) (Av ⟨v, hvS⟩) := by
        have h : u • g • Av ⟨v, hvS⟩ = g • Av ⟨v, hvS⟩ := Ine_le_Dec _ hu
        show (g⁻¹ * u * g) • Av ⟨v, hvS⟩ = Av ⟨v, hvS⟩
        rw [mul_smul, mul_smul, h, inv_smul_smul]
      have hk : g⁻¹ * u * g ∈ K := by simpa using hN.conj_mem u huK g⁻¹
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 ((Submodule.mem_iInf _).1 hz ⟨v, hvS⟩))
      have h0 : z.1 (toGS Ω _ (g⁻¹ * u * g)) = 0 := (hm ⟨_, hd⟩).trans (sub_eq_zero.2 (hρ _ hk m))
      have h1 := hc g (g⁻¹ * u * g)
      rw [h0, map_zero, add_zero, mul_assoc, mul_inv_cancel_left, hc, hρ u huK] at h1
      exact add_eq_right.1 h1
    · have hn : u ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 F))) := by
        apply Subgroup.le_topologicalClosure
        apply Subgroup.subset_normalClosure
        simp only [Set.mem_iUnion]
        exact ⟨v, hvS, A, hv, hu⟩
      have : toGS Ω (S : Set (HeightOneSpectrum (𝓞 F))) u = 1 := (QuotientGroup.eq_one_iff _).2 hn
      rw [this, hz1]
  choose s hs using Submodule.Quotient.mk_surjective ((B1 ρ).comap (Z1 ρ).subtype)
  refine hB.of_injective (fun x => ⟨_, hmem (s x.1) ((hs x.1).symm ▸ x.2)⟩) fun x y h => ?_
  apply Subtype.ext
  rw [← hs x.1, ← hs y.1]
  congr 1
  apply Subtype.ext
  funext a
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
  exact congrFun (congrArg Subtype.val h) g
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.PerpTop
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem cup_product_injective_comp {R Γ D M : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    [Group Γ] [Group D] [TopologicalSpace D] [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [DiscreteTopology M] (χ : Γ →* Rˣ) (ρ : Representation R Γ M) (φ : D →* Γ)
    (hρ : ContAction (ρ.comp φ)) (χ' : D →* Rˣ) (e : χ' = χ.comp φ)
    (h : Function.Injective (cupH1H1TwistedDual χ' (ρ.comp φ) (MonoidHom.id D) (hρ.comp' continuous_id))) :
    Function.Injective (cupH1H1TwistedDual χ ρ φ hρ) := by
  subst e
  have e1 : (twDual χ ρ).comp φ = (twDual (χ.comp φ) (ρ.comp φ)).comp (MonoidHom.id D) := by
    refine MonoidHom.ext fun g => LinearMap.ext fun y => LinearMap.ext fun m => ?_
    change ((χ (φ g) : Rˣ) : R) * y (ρ ((φ g)⁻¹) m) =
      ((χ (φ g) : Rˣ) : R) * y (ρ (φ g⁻¹) m)
    rw [map_inv φ g]
  have gen : ∀ (σ σ' : Representation R D (TDual R M)) (_ : σ = σ') h1 h2,
      Function.Injective (cupProductH1H1 σ' (ρ.comp φ) ((charRep χ).comp φ) evalPair.flip
        continuous_of_discreteTopology h2 hρ) →
      Function.Injective (cupProductH1H1 σ (ρ.comp φ) ((charRep χ).comp φ) evalPair.flip
        continuous_of_discreteTopology h1 hρ) := by
    intro σ σ' e h1 h2 h
    subst e
    exact h
  exact gen _ _ e1 _ (fun g y x => evalPair_equiv (χ.comp φ) (ρ.comp φ) g x y) h

theorem UpperTheory.V.Ws.dualSelmer_orthogonalComplement_conditions :
    LocalTateDuality → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ 1))ˣ) (Av : S → ValuationSubring Ω), μ.comp (toGS Ω _) = cycMod F Ω l 1 → (∀ v, IsPlaceOver (Av v) v.1) → Sel (twDual μ ρ) (locFam S Av) (continuous_locFam S Av) (perpCond μ ρ (locFam S Av) (fun v => hρ.comp' (continuous_locFam S Av v)) fun _ => ⊤) = Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av) := by
  intro hT F Ω _ _ _ _ _ l _ M _ _ _ _ _ S ρ hρ μ Av hμ hA
  have key : ∀ v : S, Function.Injective
      (cupH1H1TwistedDual μ ρ (locFam S Av v) (hρ.comp' (continuous_locFam S Av v))) := fun v => by
    have h := (hT F Ω l 1 M (Av v) (ρ.comp (locFam S Av v)) v.1 one_pos (hA v)
      (hρ.comp' (continuous_locFam S Av v))).2.2.1.1
    exact cup_product_injective_comp μ ρ _ _ _ (by rw [← hμ]; rfl) h
  ext y
  rw [mem_Sel, Sha1, Submodule.mem_iInf]
  refine forall_congr' fun v => ?_
  rw [mem_perpCond, LinearMap.mem_ker]
  constructor
  · intro h
    apply key v
    rw [map_zero]
    exact LinearMap.ext fun x => h x trivial
  · intro h x _
    rw [h, map_zero, LinearMap.zero_apply]
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

theorem UpperTheory.V.Ws.greenberg_wiles_count_mod_l :
    CohomologyHyp → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (K : Subgroup (G F Ω)) (r : ℕ) (c : InfinitePlace F → G F Ω), l ≠ 2 → ContainsAbove S l → ContAction ρ → K.Normal → ¬ l ∣ K.index → (∀ g ∈ K, ∀ m, ρ (toGS Ω _ g) m = m) → K ≤ (cycMod F Ω l 1).ker → XRk l 1 K r → (∀ w, w.IsReal → IsCCAt w (c w)) → Finite (Z1 ρ) ∧ Nat.card (Z1 ρ) * archH0Card S ρ c ≤ Nat.card M ^ (r + 2 + S.card + Module.finrank ℚ F) := by
  intro P F Ω _ _ _ _ _ l hp M _ _ _ _ _ S ρ K r c hl hS hρ hN hK hρK hKc hX hc
  obtain ⟨μ, hμ⟩ := GlobalTheory.Published.PoitouTate.exists_lift_cycMod (F := F) (Ω := Ω) (l := l) (r := 1) (S := S) hS
  choose Av hA using fun v : S => (exists_isPlaceOver Ω v.1 : ∃ A : ValuationSubring Ω, IsPlaceOver A v.1)
  have e := P.gw F Ω l 1 M S ρ one_pos hl hS hρ μ hμ Av hA c hc (fun _ => ⊤)
  haveI : Fact (l ^ 1).Prime := ⟨by rw [pow_one]; exact hp.out⟩
  haveI hfd : Finite (TDual (ZMod (l ^ 1)) M) := DFunLike.finite _
  have hf1 : Finite (H1 ρ) := (P.gf F Ω l 1 M S ρ one_pos hS hρ).2.1
  obtain ⟨hZ, eZ⟩ := cocycle_card_euler_formula _ _ M ρ hρ hf1
  refine ⟨hZ, ?_⟩
  have hM : 0 < Nat.card M := Nat.card_pos
  have hD : Nat.card (TDual (ZMod (l ^ 1)) M) = Nat.card M := by
    show Nat.card (Module.Dual (ZMod (l ^ 1)) M) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod (l ^ 1)) (V := Module.Dual (ZMod (l ^ 1)) M),
      Subspace.dual_finrank_eq, ← Module.natCard_eq_pow_finrank]
  have hsha := (tate_shafarevich_card_mod_l F Ω l (TDual (ZMod (l ^ 1)) M) S (twDual μ ρ) Av K r hA hN hK (fun g hg y => by
    refine DFunLike.ext _ _ fun m => ?_
    have h1 : μ (toGS Ω _ g) = 1 := by
      have := hKc hg
      rw [← hμ] at this
      exact this
    rw [twDual_apply, h1, ← map_inv, hρK _ (K.inv_mem hg), Units.val_one, one_mul]) hX).2
  rw [hD, ← dualSelmer_orthogonalComplement_conditions P.loc.lt F Ω l M S ρ hρ μ Av hμ hA] at hsha
  have hsel : Sel ρ (locFam S Av) (continuous_locFam S Av) (fun _ => ⊤) = ⊤ :=
    eq_top_iff.2 fun x _ => (mem_Sel _ _ _ _ _).2 fun _ => trivial
  have htop : ∀ (N : Type) [AddCommGroup N] [Module (ZMod (l ^ 1)) N],
      Nat.card (⊤ : Submodule (ZMod (l ^ 1)) N) = Nat.card N :=
    fun N _ _ => Nat.card_congr Submodule.topEquiv.toEquiv
  rw [hsel, htop] at e
  simp only [htop] at e
  have hloc : (∏ v : S, Nat.card (H1 (ρ.comp (locFam S Av v)))) ≤
      (∏ v : S, Nat.card (H0 (ρ.comp (locFam S Av v)))) * Nat.card M ^ (S.card + Module.finrank ℚ F) := by
    refine (Finset.prod_le_prod' fun v _ => (local_h1_finite_mod_l P.loc.lf P.loc.lt P.loc.le F Ω l M (Av v) v.1
      (ρ.comp (locFam S Av v)) (hA v) (hρ.comp' (continuous_locFam S Av v))).2).trans ?_
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hM ?_)
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Fintype.card_coe,
      Finset.sum_coe_sort S (fun v => if ((l : ℕ) : 𝓞 F) ∈ v.asIdeal then locDeg v else 0)]
    exact Nat.add_le_add_left (sum_local_degree_above_l_le_finrank F l S) _
  have p1 : 0 < Nat.card (H0 ρ) := Nat.card_pos
  have p2 : 0 < Nat.card (H0 (twDual μ ρ)) := Nat.card_pos
  have p3 : 0 < ∏ v : S, Nat.card (H0 (ρ.comp (locFam S Av v))) :=
    Finset.prod_pos fun v _ => Nat.card_pos
  have key := e.le.trans (Nat.mul_le_mul (Nat.mul_le_mul_right _ hsha) hloc)
  generalize (∏ v : S, Nat.card (H0 (ρ.comp (locFam S Av v)))) = q at p3 key
  generalize Nat.card (H0 (twDual μ ρ)) = b at p2 key
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.mul_pos p1 p3)
  calc _ = (Nat.card (Z1 ρ) * Nat.card (H0 ρ)) * 1 * q * archH0Card S ρ c := by ring
    _ ≤ (Nat.card (Z1 ρ) * Nat.card (H0 ρ)) * b * q * archH0Card S ρ c := by gcongr; exact p2
    _ = Nat.card M * (Nat.card (H1 ρ) * b * q * archH0Card S ρ c) := by rw [eZ]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ key
    _ = _ := by ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.ExistsComplexConjugationAtRealPlace
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

theorem UpperTheory.V.Ws.exists_complexConjugation_at_realPlace :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (w : InfinitePlace F), w.IsReal → ∃ c : G F Ω, IsCCAt w c := by
  intro F Ω _ _ _ _ _ w hw
  let φ : F →+* ℂ := w.embedding
  have hreal : ∀ x : F, starRingEnd ℂ (φ x) = φ x := by
    intro x
    have h := congrArg (fun ψ : F →+* ℂ => ψ x)
      (NumberField.ComplexEmbedding.isReal_iff.mp (NumberField.InfinitePlace.isReal_iff.mp hw))
    simpa using h
  letI : Algebra F ℂ := φ.toAlgebra
  have halg : ∀ x : F, algebraMap F ℂ x = φ x := fun x => rfl
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : Normal F Ω := IsAlgClosure.normal F Ω
  let j : Ω →ₐ[F] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let E : IntermediateField F ℂ := j.fieldRange
  let e : Ω ≃ₐ[F] E := AlgEquiv.ofInjectiveField j
  haveI : Normal F E := Normal.of_algEquiv e
  let cj : ℂ →ₐ[F] ℂ :=
    { (starRingEnd ℂ : ℂ →+* ℂ) with
      commutes' := fun x => by
        show starRingEnd ℂ (algebraMap F ℂ x) = algebraMap F ℂ x
        rw [halg]; exact hreal x }
  have hrange : (cj.comp E.val).fieldRange = E := AlgHom.fieldRange_of_normal _
  have hmem : ∀ y : Ω, starRingEnd ℂ (j y) ∈ E := by
    intro y
    have h1 : (cj.comp E.val) (e y) ∈ (cj.comp E.val).fieldRange := AlgHom.mem_fieldRange.mpr ⟨e y, rfl⟩
    rw [hrange] at h1
    have h2 : ((e y : E) : ℂ) = j y := rfl
    simpa [cj, h2] using h1
  let f' : Ω →ₐ[F] E := (cj.comp j).codRestrict E.toSubalgebra (fun y => hmem y)
  let σ0 : Ω →ₐ[F] Ω := e.symm.toAlgHom.comp f'
  have hbij : Function.Bijective σ0 := Algebra.IsAlgebraic.algHom_bijective σ0
  let c : Ω ≃ₐ[F] Ω := AlgEquiv.ofBijective σ0 hbij
  refine ⟨c, (j : Ω →+* ℂ), ?_, ?_⟩
  · intro x
    have h3 : ((e (e.symm (f' x)) : E) : ℂ) = j (e.symm (f' x)) := rfl
    rw [AlgEquiv.apply_symm_apply] at h3
    show j (e.symm (f' x)) = starRingEnd ℂ (j x)
    rw [← h3]
    rfl
  · have h4 : (j : Ω →+* ℂ).comp (algebraMap F Ω) = φ := by
      ext x
      simp [halg]
    rw [h4]
    exact NumberField.InfinitePlace.mk_embedding w
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.DescGS
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem continuous_of_right_invariant_open_subgroup {Γ X : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [TopologicalSpace X] (H : Subgroup Γ) (hH : IsOpen (H : Set Γ)) (f : Γ → X)
    (hf : ∀ g, ∀ h ∈ H, f (g * h) = f g) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have ht : Filter.Tendsto (fun x => g⁻¹ * x) (nhds g) (nhds 1) := by
    have := (continuous_const_mul g⁻¹).tendsto g
    simpa using this
  have hev : ∀ᶠ x in nhds g, f x = f g := by
    filter_upwards [ht (hH.mem_nhds H.one_mem)] with x hx
    have := hf g _ hx
    simpa using this
  exact tendsto_const_nhds.congr' (hev.mono fun x hx => hx.symm)

theorem UpperTheory.V.Ws.exists_descent_to_galoisGroupUnramifiedOutside :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation R (G F Ω) M) (K : Subgroup (G F Ω)) (N : ℕ), (∀ v, v ∈ plDvd F N → v ∈ S) → (∀ σ ∈ ineOff F Ω N, ∀ m, ρ σ m = m) → IsOpen (K : Set (G F Ω)) → (∀ σ ∈ K, ∀ m, ρ σ m = m) → ∃ ρS : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M, (∀ g m, ρS (toGS Ω _ g) m = ρ g m) ∧ ContAction ρS ∧ ∀ z ∈ cocOff ρ (ineOff F Ω N), ∃ y ∈ Z1 ρS, ∀ g, y (toGS Ω _ g) = z g := by
  intro F Ω _ _ _ _ _ R M _ _ _ _ _ _ S ρ K N hS hine hK hKρ
  have hN : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ (S : Set (HeightOneSpectrum (𝓞 F))) →
      ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Inertia A, σ ∈ ineOff F Ω N := by
    intro v hv A hA σ hσ
    refine ⟨A, ?_, hσ⟩
    intro hlt
    apply hv
    apply hS
    have h1 := (hA (N : 𝓞 F)).1
    simp only [plDvd, Set.mem_setOf_eq]
    apply h1
    simpa using hlt
  have hNS : NS Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≤ ρ.ker := by
    have hker : ∀ g, g ∈ ρ.ker ↔ ∀ m, ρ g m = m := by
      intro g
      rw [MonoidHom.mem_ker]
      constructor
      · intro h m
        rw [h]
        rfl
      · intro h
        exact LinearMap.ext h
    have hopen : IsOpen (ρ.ker : Set (G F Ω)) := by
      apply Subgroup.isOpen_of_mem_nhds (g := 1)
      apply Filter.mem_of_superset (hK.mem_nhds K.one_mem)
      intro σ hσ
      exact (hker σ).2 (hKρ σ hσ)
    apply Subgroup.topologicalClosure_minimal _ _ (Subgroup.isClosed_of_isOpen _ hopen)
    apply Subgroup.normalClosure_le_normal
    intro σ hσ
    simp only [Set.mem_iUnion] at hσ
    obtain ⟨v, hv, A, hA, hσ⟩ := hσ
    exact (hker σ).2 (hine σ (hN v hv A hA σ hσ))
  let ρS : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M :=
    QuotientGroup.lift _ ρ hNS
  have hρS : ∀ g m, ρS (toGS Ω _ g) m = ρ g m := by
    intro g m
    rfl
  refine ⟨ρS, hρS, ?_, ?_⟩
  · show Continuous fun p : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) × M => ρS p.1 p.2
    rw [continuous_prod_of_discrete_right]
    intro m
    rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
    apply continuous_of_right_invariant_open_subgroup K hK
    intro g h hh
    show ρ (g * h) m = ρ g m
    rw [map_mul, Module.End.mul_apply, hKρ h hh]
  · intro z hz
    obtain ⟨hzlc, hzc, hz0⟩ := hz
    have hz1 : z 1 = 0 := by
      have := hzc 1 1
      simp only [mul_one, map_one, Module.End.one_apply] at this
      simpa using this
    let φ : G F Ω →* Function.End M :=
      { toFun := fun g m => ρ g m + z g
        map_one' := by
          funext m
          show ρ 1 m + z 1 = m
          rw [hz1, map_one]
          simp
        map_mul' := by
          intro g h
          funext m
          show ρ (g * h) m + z (g * h) = ρ g (ρ h m + z h) + z g
          rw [hzc, map_mul, Module.End.mul_apply, map_add (f := _)]
          abel }
    have hkerφ : ∀ g, g ∈ φ.ker ↔ z g = 0 ∧ ∀ m, ρ g m = m := by
      intro g
      rw [MonoidHom.mem_ker]
      constructor
      · intro h
        have h' : ∀ m, ρ g m + z g = m := fun m => congrFun h m
        have h0 : z g = 0 := by simpa using h' 0
        refine ⟨h0, fun m => ?_⟩
        simpa [h0] using h' m
      · rintro ⟨h0, h1⟩
        funext m
        show ρ g m + z g = m
        rw [h0, h1, add_zero]
    have hopen : IsOpen (φ.ker : Set (G F Ω)) := by
      apply Subgroup.isOpen_of_mem_nhds (g := 1)
      have hU : z ⁻¹' {0} ∈ nhds (1 : G F Ω) :=
        (hzlc.isOpen_fiber 0).mem_nhds (by simpa using hz1)
      apply Filter.mem_of_superset (Filter.inter_mem (hK.mem_nhds K.one_mem) hU)
      rintro σ ⟨hσK, hσz⟩
      exact (hkerφ σ).2 ⟨hσz, hKρ σ hσK⟩
    have hNSφ : NS Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≤ φ.ker := by
      apply Subgroup.topologicalClosure_minimal _ _ (Subgroup.isClosed_of_isOpen _ hopen)
      apply Subgroup.normalClosure_le_normal
      intro σ hσ
      simp only [Set.mem_iUnion] at hσ
      obtain ⟨v, hv, A, hA, hσ⟩ := hσ
      have hm := hN v hv A hA σ hσ
      exact (hkerφ σ).2 ⟨hz0 σ hm, hine σ hm⟩
    let φS := QuotientGroup.lift _ φ hNSφ
    let y : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) → M := fun q => φS q 0
    have hy : ∀ g, y (toGS Ω _ g) = z g := by
      intro g
      show ρ g 0 + z g = z g
      simp
    refine ⟨y, ⟨?_, ?_⟩, hy⟩
    · rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
      have : (y ∘ QuotientGroup.mk) = z := funext hy
      rw [this]
      exact hzlc.continuous
    · intro q₁ q₂
      induction q₁ using QuotientGroup.induction_on with
      | H g =>
        induction q₂ using QuotientGroup.induction_on with
        | H h =>
          have e := hy (g * h)
          rw [map_mul] at e
          show y (toGS Ω _ g * toGS Ω _ h) = y (toGS Ω _ g) + ρS (toGS Ω _ g) (y (toGS Ω _ h))
          rw [e, hy, hy, hρS, hzc]
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem plDvd_fin (F : Type) [Field F] [NumberField F] (N : ℕ) (hN : N ≠ 0) : (plDvd F N).Finite := by
  have h : Ideal.span {((N : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hN
  refine (Ideal.finite_factors h).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

theorem UpperTheory.V.Ws.card_globalCocycles_le_of_iwasawaRank :
    CohomologyHyp → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M], (∀ m : M, l • m = 0) → ∀ (ρ : Representation R (G F Ω) M) (K : Subgroup (G F Ω)) (N r g : ℕ), l ≠ 2 → N ≠ 0 → l ∣ N → (plDvd F N).ncard ≤ g → (∀ σ ∈ ineOff F Ω N, ∀ m, ρ σ m = m) → K.Normal → IsOpen (K : Set (G F Ω)) → ¬ l ∣ K.index → (∀ σ ∈ K, ∀ m, ρ σ m = m) → K ≤ (cycMod F Ω l 1).ker → XRk l 1 K r → CardLe (cocOff ρ (ineOff F Ω N)) (Nat.card M ^ (r + 2 + g + Module.finrank ℚ F)) ∧ (IsTotallyReal F → (∀ σ : G F Ω, IsCC σ → ∀ m, ρ σ m = m) → CardLe (cocOff ρ (ineOff F Ω N)) (Nat.card M ^ (r + 2 + g))) := by
  intro P F Ω _ _ _ _ _ l _ R M _ _ _ _ hlM ρ K N r g hl hN hlN hg hI hKn hKo hKi hKρ hKc hX
  obtain ⟨inst, ρ', hρ'⟩ := exists_zmod_prime_representation_of_torsion l (G F Ω) R M hlM ρ
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  have hfin := plDvd_fin F N hN
  have hcard : hfin.toFinset.card ≤ g := by rwa [← Set.ncard_eq_toFinset_card _ hfin]
  have hmem : ∀ v, v ∈ plDvd F N → v ∈ hfin.toFinset := fun v hv => hfin.mem_toFinset.2 hv
  generalize hfin.toFinset = S at hcard hmem
  have hS : ContainsAbove S l := fun v hv => hmem v (by
    obtain ⟨k, rfl⟩ := hlN
    show ((l * k : ℕ) : 𝓞 F) ∈ v.asIdeal
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hv)
  obtain ⟨ρS, h1, h2, h3⟩ := exists_descent_to_galoisGroupUnramifiedOutside F Ω (ZMod (l ^ 1)) M S ρ' K N hmem
    (fun σ h m => by rw [hρ', hI σ h]) hKo (fun σ h m => by rw [hρ', hKρ σ h])
  have hc : ∀ w : InfinitePlace F, ∃ c : G F Ω, w.IsReal → IsCCAt w c := fun w => by
    by_cases hw : w.IsReal
    · obtain ⟨c, hc⟩ := exists_complexConjugation_at_realPlace F Ω w hw
      exact ⟨c, fun _ => hc⟩
    · exact ⟨1, fun h => absurd h hw⟩
  choose c hc using hc
  obtain ⟨hZ, hb⟩ := greenberg_wiles_count_mod_l P F Ω l M S ρS K r c hl hS h2 hKn hKi
    (fun σ h m => by rw [h1, hρ', hKρ σ h]) hKc hX hc
  have hM : 0 < Nat.card M := Nat.card_pos
  have hex : ∀ z : cocOff ρ (ineOff F Ω N), ∃ y : Z1 ρS, ∀ g, y.1 (toGS Ω _ g) = z.1 g := fun z => by
    obtain ⟨y, hy, e⟩ := h3 z.1 ⟨z.2.1, fun a b => by rw [hρ']; exact z.2.2.1 a b, z.2.2.2⟩
    exact ⟨⟨y, hy⟩, e⟩
  choose f hf using hex
  have hinj : Function.Injective f := fun a b h => Subtype.ext (funext fun x => by rw [← hf, ← hf, h])
  have hb' : Nat.card (Z1 ρS) * archH0Card S ρS c ≤ Nat.card M ^ (r + 2 + g + Module.finrank ℚ F) :=
    hb.trans (Nat.pow_le_pow_right hM (by omega))
  refine ⟨CardLe.of_injective ⟨hZ, le_trans (Nat.le_mul_of_pos_right _ ?_) hb'⟩ f hinj, fun hF hcc => ?_⟩
  · unfold archH0Card
    refine Nat.mul_pos (Finset.prod_pos fun w _ => ?_) (pow_pos hM _)
    haveI : Nonempty {m : M // ρS (toGS Ω _ (c w)) m = m} := ⟨⟨0, map_zero _⟩⟩
    exact Nat.card_pos
  · have ha : archH0Card S ρS c = Nat.card M ^ Module.finrank ℚ F := by
      rw [archH0Card, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, mul_one,
        Finset.filter_true_of_mem fun w _ => IsTotallyReal.isReal w]
      have hw : ∀ w, Nat.card {m : M // ρS (toGS Ω _ (c w)) m = m} = Nat.card M := fun w => by
        obtain ⟨j, hj, -⟩ := hc w (IsTotallyReal.isReal w)
        exact Nat.card_congr (Equiv.subtypeUnivEquiv fun m => by rw [h1, hρ', hcc _ ⟨j, hj⟩])
      rw [Finset.prod_congr rfl fun w _ => hw w, Finset.prod_const, Finset.card_univ,
        IsTotallyReal.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
        IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
    rw [ha, pow_add _ (r + 2 + g)] at hb'
    exact CardLe.of_injective ⟨hZ, Nat.le_of_mul_le_mul_right hb' (pow_pos hM _)⟩ f hinj
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.EvenRt
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.CcConj
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem emb_twist {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (i j : Ω →+* ℂ) :
    ∃ g : Ω ≃ₐ[ℚ] Ω, ∀ x, j (g x) = i x := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  let jA : Ω →ₐ[ℚ] ℂ := j.toRatAlgHom
  let iA : Ω →ₐ[ℚ] ℂ := i.toRatAlgHom
  let K : IntermediateField ℚ ℂ := jA.fieldRange
  let r : Ω →+* K :=
    { toFun := fun x => ⟨jA x, jA.mem_fieldRange.2 ⟨x, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  have hr : Function.Bijective r := by
    constructor
    · intro x y hxy
      have : jA x = jA y := congrArg Subtype.val hxy
      exact jA.toRingHom.injective this
    · rintro ⟨z, hz⟩
      obtain ⟨x, rfl⟩ := jA.mem_fieldRange.1 hz
      exact ⟨x, rfl⟩
  haveI : IsAlgClosed K := IsAlgClosed.of_ringEquiv Ω K (RingEquiv.ofBijective r hr)
  have hi : ∀ x, ∃ y, j y = i x := by
    intro x
    have h1 : IsIntegral ℚ (iA x) := (Algebra.IsIntegral.isIntegral x).map iA
    have h2 : IsIntegral K (iA x) := h1.tower_top
    have h3 := minpoly.mem_range_of_degree_eq_one K (iA x)
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible h2))
    obtain ⟨k, hk⟩ := h3
    obtain ⟨y, hy⟩ := jA.mem_fieldRange.1 k.2
    refine ⟨y, ?_⟩
    have : jA y = iA x := by rw [hy]; exact hk
    exact this
  choose φ hφ using hi
  let h0 : Ω →+* Ω :=
    { toFun := φ
      map_one' := j.injective (by rw [hφ, map_one, map_one])
      map_mul' := fun x y => j.injective (by rw [hφ, map_mul, map_mul, hφ, hφ])
      map_zero' := j.injective (by rw [hφ, map_zero, map_zero])
      map_add' := fun x y => j.injective (by rw [hφ, map_add (f := _), map_add (f := _), hφ, hφ]) }
  let hA : Ω →ₐ[ℚ] Ω := h0.toRatAlgHom
  have hb : Function.Bijective hA := Algebra.IsAlgebraic.algHom_bijective hA
  exact ⟨AlgEquiv.ofBijective hA hb, fun x => hφ x⟩

theorem UpperTheory.V.Ws.isConj_of_isComplexConjugation :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (σ τ : G ℚ Ω), IsCC σ → IsCC τ → IsConj σ τ := by
  intro Ω _ _ _ σ τ hσ hτ
  obtain ⟨jσ, hjσ⟩ := hσ
  obtain ⟨jτ, hjτ⟩ := hτ
  obtain ⟨g, hg⟩ := emb_twist jσ jτ
  rw [isConj_iff]
  refine ⟨g, AlgEquiv.ext fun y => jτ.injective ?_⟩
  have e1 : jσ (g⁻¹ y) = jτ y := by
    rw [← hg]
    congr 1
    exact AlgEquiv.apply_symm_apply g y
  show jτ (g (σ (g⁻¹ y))) = jτ (τ y)
  rw [hg, hjσ, e1, hjτ]
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

theorem UpperTheory.V.Ws.residualCharacter_complexConjugation_eq_one :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (T : Tower D) (σ : G T.F Ω), IsCC σ → ∀ w ∈ [0, wPs, -wPs], T.rbU w σ = 1 := by
  intro Ω _ _ _ l _ c D hD T σ hσ w hw
  have hτ : IsCC (resQ T.F σ) := by
    unfold IsCC at *
    exact hσ
  have hconj := isConj_of_isComplexConjugation Ω (resQ T.F σ) D.cc hτ hD.isCC
  have hP : D.Psi (resQ T.F σ) = 1 := by
    obtain ⟨u, hu⟩ := isConj_iff.mp hconj
    rw [← hD.Psi_even, ← hu]
    simp only [map_mul, map_inv]
    rw [mul_comm, inv_mul_cancel_left]
  have hth : D.th (AlgEquiv.restrictScalars ℚ σ) = D.al (AlgEquiv.restrictScalars ℚ σ) := by
    have : D.th (resQ T.F σ) = (D.al * D.Psi) (resQ T.F σ) := by
      unfold Raw.th
      rfl
    rw [MonoidHom.mul_apply, hP, mul_one] at this
    exact this
  have hrt : (T.fr ∅).rt w σ = 1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · simp only [Fr.rt, Tower.fr, MonoidHom.coe_mk, OneHom.coe_mk, Prod.fst_zero, Prod.snd_zero, zpow_zero, mul_one]
    · simp only [Fr.rt, Tower.fr, wPs, MonoidHom.coe_mk, OneHom.coe_mk, zpow_zero, one_mul, zpow_one,
        MonoidHom.coe_comp, Function.comp_apply]
      unfold chi
      cases T.pr <;> simp [lab, Raw.ps, hth]
    · simp only [Fr.rt, Tower.fr, wPs, MonoidHom.coe_mk, OneHom.coe_mk, Prod.fst_neg, Prod.snd_neg, neg_zero, zpow_zero, one_mul, zpow_neg, zpow_one,
        MonoidHom.coe_comp, Function.comp_apply]
      unfold chi
      cases T.pr <;> simp [lab, Raw.ps, hth]
  show (Units.map _) ((T.fr ∅).rt w σ) = 1
  rw [hrt, map_one]
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem isLocalHom_algebraMap_padicInt_coef_O {l : ℕ} [Fact l.Prime] (c : Coef l) :
    IsLocalHom (algebraMap ℤ_[l] c.O) := by
  haveI := c.fin
  apply RingHom.IsIntegral.isLocalHom
  · exact (Algebra.IsIntegral.of_finite ℤ_[l] c.O).isIntegral
  · intro a b h
    have h' := congrArg (fun x : c.O => (x : PadicAlgCl l)) h
    simp only [Subalgebra.coe_algebraMap] at h'
    have hinj : Function.Injective (algebraMap ℤ_[l] (PadicAlgCl l)) := by
      rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (PadicAlgCl l)]
      exact (algebraMap ℚ_[l] (PadicAlgCl l)).injective.comp (fun a b h => Subtype.ext h)
    exact hinj h'

private theorem finite_residueField_coef {l : ℕ} [Fact l.Prime] (c : Coef l) :
    Finite (ResidueField c.O) := by
  haveI := c.fin
  haveI := isLocalHom_algebraMap_padicInt_coef_O c
  exact IsLocalRing.ResidueField.finite_of_finite (R := ℤ_[l]) inferInstance

private theorem prime_nsmul_residueField_coef_eq_zero {l : ℕ} [Fact l.Prime] (c : Coef l) (m : ResidueField c.O) :
    l • m = 0 := by
  haveI := isLocalHom_algebraMap_padicInt_coef_O c
  have h0 : IsLocalRing.residue c.O (algebraMap ℤ_[l] c.O (l : ℤ_[l])) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact (IsLocalRing.mem_maximalIdeal _).2
      (fun hu => PadicInt.p_nonunit (isUnit_of_map_unit (algebraMap ℤ_[l] c.O) _ hu))
  have h1 : ((l : ResidueField c.O)) = 0 := by
    rw [map_natCast] at h0
    rw [← map_natCast (IsLocalRing.residue c.O)]
    exact h0
  rw [nsmul_eq_mul, h1, zero_mul]

theorem UpperTheory.V.Ws.rank_cocycleSpaces_le_of_towerIwasawaRank :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (T : Tower D) (r g : ℕ), (plDvd T.F (prodS D)).ncard ≤ g → XRk l 1 T.Kr r → (∀ w, Module.rank (ResidueField c.O) ((T.fr ∅).Str (residue c.O) w) ≤ (r + 1 : ℕ)) ∧ (∀ w ∈ [0, wPs, -wPs], Module.rank (ResidueField c.O) ((T.fr ∅).Zgl (residue c.O) w) ≤ (r + 2 + g : ℕ)) ∧ ∀ w, Module.rank (ResidueField c.O) ((T.fr ∅).Zgl (residue c.O) w) ≤ T.d + (r + 2 + g : ℕ) := by
  intro hP Ω _ _ _ l _ c D hD T r g hg hX
  obtain ⟨hN, hO, hI, hC, hK, hU, ⟨hS0, hSl⟩, hIne, -⟩ := residualKernel_properties D hD T
  haveI := finite_residueField_coef c
  have tor := prime_nsmul_residueField_coef_eq_zero c
  have triv : ∀ (w : ℤ × ℤ), ∀ σ ∈ T.Kr, ∀ m : ResidueField c.O, (charRep (T.rbU w)) σ m = m := by
    intro w σ hσ m
    simp [charRep, hU w σ (hK σ hσ)]
  have hinf : ∀ (w : ℤ × ℤ), ∀ σ ∈ ineOff (↥T.F) Ω (prodS D), ∀ m : ResidueField c.O,
      (charRep (T.rbU w)) σ m = m := by
    intro w σ hσ m
    simp [charRep, hU w σ (hIne σ hσ).2]
  have sub : ∀ (w : ℤ × ℤ), (T.fr ∅).Zgl (residue c.O) w ≤
      cocOff (charRep (T.rbU w)) (ineOff (↥T.F) Ω (prodS D)) := by
    intro w z hz
    obtain ⟨h1, h2, h3, -⟩ := hz
    refine ⟨h1, ?_, ?_⟩
    · intro a b
      rw [h2 a b]
      simp [charRep, Tower.rbU]
    · intro a ha
      exact h3 a (hIne a ha).1
  refine ⟨?_, ?_, ?_⟩
  · intro w
    have h := card_cocycles_vanishing_on_inertia_le_pow T.F Ω l (ResidueField c.O) (ResidueField c.O) tor (charRep (T.rbU w)) T.Kr r hI
      (triv w) hX
    refine le_trans (Submodule.rank_mono (str_residue_le_cocycles_vanishing_on_inertia_kernel D hD T w)) ?_
    haveI := h.1
    exact rank_le_of_card_le_pow_card_field _ _ _ h
  · intro w hw
    have h := (card_globalCocycles_le_of_iwasawaRank hP T.F Ω l _ _ tor (charRep (T.rbU w)) T.Kr (prodS D) r g hD.l_odd hS0 hSl hg
      (hinf w) hN hO hI (triv w) hC hX).2 T.realF
      (fun σ hσ m => by simp [charRep, residualCharacter_complexConjugation_eq_one D hD T σ hσ w hw])
    refine le_trans (Submodule.rank_mono (sub w)) ?_
    haveI := h.1
    exact rank_le_of_card_le_pow_card_field _ _ _ h
  · intro w
    have h := (card_globalCocycles_le_of_iwasawaRank hP T.F Ω l _ _ tor (charRep (T.rbU w)) T.Kr (prodS D) r g hD.l_odd hS0 hSl hg
      (hinf w) hN hO hI (triv w) hC hX).1
    refine le_trans (Submodule.rank_mono (sub w)) ?_
    haveI := h.1
    have h2 := rank_le_of_card_le_pow_card_field _ _ _ h
    refine le_trans h2 (le_of_eq ?_)
    simp only [Tower.d]
    push_cast
    ring
