module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.KillPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.CardSel
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealCounting.ClassC
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CondDisc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.AtPrime
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.compsup

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CocycleCoboundaryFiniteIndex
theorem UpperTheory.Reformulated.B.CocycleCoboundaryFiniteIndex.coboundary_of_vanishing_on_finite_index :
    ∀ {R Q M : Type} [inst : CommRing R] [inst_1 : Group Q]
    [inst_2 : AddCommGroup M] [inst_3 : _root_.Module R M] (π : Representation R Q M) (H : Subgroup Q) (f : Q → M),
    (∀ (g h : Q), f (g * h) = f g + ((π : Q → M →ₗ[R] M) g : M → M) (f h)) →
      (∀ u ∈ H, f u = (0 : M)) →
        IsUnit (↑H.index : R) →
          H.index ≠ (0 : ℕ) → ∃ (m : M), ∀ (g : Q), f g = ((π : Q → M →ₗ[R] M) g : M → M) m - m := by
  intro R Q M _ _ _ _ π H f hf hH hu hn
  classical
  haveI : Fintype (Q ⧸ H) := Subgroup.fintypeOfIndexNeZero hn
  have hconst : ∀ a b : Q, (a : Q ⧸ H) = (b : Q ⧸ H) → f a = f b := by
    intro a b hab
    have hmem : a⁻¹ * b ∈ H := QuotientGroup.eq.mp hab
    have h1 := hf a (a⁻¹ * b)
    rw [mul_inv_cancel_left, hH _ hmem, map_zero, add_zero] at h1
    exact h1.symm
  let F : Q ⧸ H → M := fun x => f x.out
  have hF : ∀ a : Q, F (a : Q ⧸ H) = f a := fun a =>
    hconst _ _ (QuotientGroup.out_eq' _)
  have hstep : ∀ (g : Q) (x : Q ⧸ H), F (g • x) = f g + π g (F x) := by
    intro g x
    induction x using QuotientGroup.induction_on with
    | H a =>
      have h2 : g • (a : Q ⧸ H) = ((g * a : Q) : Q ⧸ H) := rfl
      rw [h2, hF, hF, hf]
  have hcard : Fintype.card (Q ⧸ H) = H.index := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  have hsum : ∀ g : Q, ∑ x, F x = (H.index : R) • f g + π g (∑ x, F x) := by
    intro g
    calc ∑ x, F x = ∑ x, F (g • x) := (Equiv.sum_comp (MulAction.toPerm g) F).symm
      _ = ∑ x : Q ⧸ H, (f g + π g (F x)) := Finset.sum_congr rfl fun x _ => hstep g x
      _ = _ := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcard, map_sum,
          Nat.cast_smul_eq_nsmul]
  obtain ⟨c, hc⟩ := hu.exists_left_inv
  refine ⟨-(c • ∑ x, F x), fun g => ?_⟩
  have h3 : (H.index : R) • f g = ∑ x, F x - π g (∑ x, F x) := eq_sub_of_add_eq (hsum g).symm
  calc f g = c • ((H.index : R) • f g) := by rw [smul_smul, hc, one_smul]
    _ = _ := by
      rw [h3, map_neg, map_smul, smul_sub]
      abel
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.Imports
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.UnrInj
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.TorsRep
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.torsRep :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ) (x : H1 (qzTw D e)), (l : ℤ_[l]) • x = 0 → ∃ z : Z1 (qzTw D e), x = Submodule.Quotient.mk z ∧ ∀ g, (l : ℤ_[l]) • z.1 g = 0 := by
  intro E Ω _ _ _ _ _ l hl D e x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨m, hm⟩ := Submodule.mem_comap.1 hx
  have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  obtain ⟨m', hm'⟩ := (UpperTheory.V.Kum.qzBasic l).1 (l : ℤ_[l]) hl0 m
  have hb : d0 (qzTw D e) m' ∈ B1 (qzTw D e) := ⟨m', rfl⟩
  refine ⟨z - ⟨d0 (qzTw D e) m', coboundaries_le_cocycles _ (UpperTheory.V.LDataCardLeFinrank.contTw E Ω l D e).1 hb⟩, ?_, fun g => ?_⟩
  · rw [Submodule.Quotient.eq, sub_sub_cancel]
    exact Submodule.mem_comap.2 hb
  · have h1 : (l : ℤ_[l]) • d0 (qzTw D e) m' = (l : ℤ_[l]) • z.1 := by
      rw [← map_smul]
      exact (congrArg _ hm').trans hm
    have h2 := congrFun h1 g
    show (l : ℤ_[l]) • (z.1 g - d0 (qzTw D e) m' g) = 0
    rw [smul_sub]
    exact sub_eq_zero.2 h2.symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.CobOne
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem coboundary_of_vanishing_on_finite_index {R Q M : Type} [CommRing R] [Group Q] [AddCommGroup M] [Module R M]
    (π : Representation R Q M) (H : Subgroup Q) (f : Q → M) (hf : ∀ g h, f (g * h) = f g + π g (f h))
    (h0 : ∀ u ∈ H, f u = 0) (hn : IsUnit (H.index : R)) (hn' : H.index ≠ 0) : ∃ m, ∀ g, f g = π g m - m :=
  _root_.UpperTheory.Reformulated.B.CocycleCoboundaryFiniteIndex.coboundary_of_vanishing_on_finite_index π H f hf h0 hn hn'

theorem UpperTheory.V.Odd.cobOne :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ) (z : Z1 (qzTw D e)), (∀ g ∈ galOf E (Fn E Ω l 1) Ω, z.1 (toGS Ω _ g) = 0) → (Submodule.Quotient.mk z : H1 (qzTw D e)) = 0 := by
  intro E Ω _ _ _ _ _ l hl D e z hz
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  have h0 := (fnCyc E Ω l 1).1
  rw [pow_one] at h0
  haveI : FiniteDimensional E (Fn E Ω l 1) := IsCyclotomicExtension.finiteDimensional {l} E _
  haveI : NumberField (Fn E Ω l 1) := NumberField.of_module_finite E _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : IsAlgClosure (Fn E Ω l 1) Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := E) _⟩
  have hi : (galOf E (Fn E Ω l 1) Ω).index ∣ l - 1 := by
    rw [(galEmbTop E (Fn E Ω l 1) Ω).2.2]
    exact (fnOne E Ω l).1
  have h2 := hl.out.two_le
  have hle := Nat.le_of_dvd (by omega) hi
  have hne : (galOf E (Fn E Ω l 1) Ω).index ≠ 0 := fun h => by
    rw [h, zero_dvd_iff] at hi
    omega
  have hu : IsUnit ((galOf E (Fn E Ω l 1) Ω).index : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff, hl.out.coprime_iff_not_dvd]
    exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hne) (by omega)
  obtain ⟨m, hm⟩ := coboundary_of_vanishing_on_finite_index ((qzTw D e).comp (toGS Ω _)) (galOf E (Fn E Ω l 1) Ω) (fun g => z.1 (toGS Ω _ g))
    (fun g h => by rw [map_mul]; exact z.2.2 _ _) hz hu hne
  rw [Submodule.Quotient.mk_eq_zero]
  refine (mem_coboundaries1 _ _).2 ⟨m, fun g => ?_⟩
  obtain ⟨σ, rfl⟩ : ∃ σ, toGS Ω _ σ = g := QuotientGroup.mk_surjective g
  exact hm σ
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem unrInj_smul {l : ℕ} [Fact l.Prime] {u : ℤ_[l]ˣ} (hu : u ∈ KStar.TotallyRealRoots.princ l 1) {x : QZ l}
    (hx : (l : ℤ_[l]) • x = 0) : (u : ℤ_[l]) • x = x := by
  obtain ⟨ι, hinj, hrange, hsmul⟩ := UpperTheory.V.Kum.zmodToQZ l 1
  have hmem : x ∈ Set.range ι := (hrange x).2 (by simpa using hx)
  obtain ⟨a, rfl⟩ := hmem
  have hu' : PadicInt.toZModPow 1 (u : ℤ_[l]) = 1 := by
    have h := hu
    rw [KStar.TotallyRealRoots.princ, MonoidHom.mem_ker] at h
    exact congrArg Units.val h
  rw [← hsmul, hu', one_mul]


set_option maxHeartbeats 400000 in
theorem UpperTheory.V.Odd.unrInj :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ), ∃ f : Submodule.torsionBy ℤ_[l] (H1 (qzTw D e)) (l : ℤ_[l]) → UnrHom (Fn E Ω l 1) Ω l, Function.Injective f := by
  intro E Ω _ _ _ _ _ l _ D e
  classical
  obtain ⟨ι, hinj, hrange, -⟩ := UpperTheory.V.Kum.zmodToQZ l 1
  let eq1 := ZMod.ringEquivCongr (pow_one l)
  haveI hcyc := (UpperTheory.V.Kum.fnCyc E Ω l 1).1
  have hgal : galOf E (Fn E Ω l 1) Ω = levU l (galOf E E Ω) 1 :=
    UpperTheory.V.Kum.galOfCyc E Ω l 1 E (Fn E Ω l 1)
  have key : ∀ z : Z1 (qzTw D e), (∀ g, (l : ℤ_[l]) • (z : GS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) g = 0) →
      ∃ φ : UnrHom (Fn E Ω l 1) Ω l, ∀ σ,
        ι (eq1.symm (φ.1 σ)) = (z : GS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) (toGS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) (galEmb E (Fn E Ω l 1) Ω σ)) := by
    intro z hz
    have hzc : Continuous (z : GS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) := z.2.1
    have hzco : ∀ g h, (z : GS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) (g * h) = (z : GS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) g + (qzTw D e g) ((z : GS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) h) := z.2.2
    let w : G (Fn E Ω l 1) Ω → QZ l := fun σ => (z : GS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) (toGS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) (galEmb E (Fn E Ω l 1) Ω σ))
    have hwt : ∀ σ, w σ ∈ Set.range ι := fun σ => (hrange _).2 (by simpa using hz _)
    let φ : G (Fn E Ω l 1) Ω → ZMod l := fun σ => eq1 (Function.invFun ι (w σ))
    have hφ : ∀ σ, ι (eq1.symm (φ σ)) = w σ := by
      intro σ
      simp only [φ, RingEquiv.symm_apply_apply]
      exact Function.invFun_eq (hwt σ)
    have hdet : ∀ σ (c : ZMod l), ι (eq1.symm c) = w σ → φ σ = c := by
      intro σ c h
      have h2 := hφ σ
      rw [← h] at h2
      have h3 := hinj h2
      simpa using congrArg eq1 h3
    have hmul : ∀ a b, w (a * b) = w a + w b := by
      intro a b
      have hg := hzco (toGS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) (galEmb E (Fn E Ω l 1) Ω a)) (toGS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) (galEmb E (Fn E Ω l 1) Ω b))
      have h1 : (qzTw D e) (toGS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) (galEmb E (Fn E Ω l 1) Ω a)) = qzG E Ω l e (galEmb E (Fn E Ω l 1) Ω a) := by
        rw [← qzTw_comp_toGS D e]
        rfl
      have hm := galEmb_mem E (Fn E Ω l 1) Ω a
      rw [hgal] at hm
      have hu : (cycZ E Ω l (galEmb E (Fn E Ω l 1) Ω a)) ^ (-e) ∈ KStar.TotallyRealRoots.princ l 1 :=
        Subgroup.zpow_mem (KStar.TotallyRealRoots.princ l 1) (Subgroup.mem_comap.1 hm.2) _
      rw [h1, qzG_apply, unrInj_smul hu (by simpa using hz _), ← map_mul, ← map_mul] at hg
      exact hg
    have hz1 : (z : GS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) 1 = 0 := by
      have h := hzco 1 1
      rw [map_one, mul_one, Module.End.one_apply] at h
      simpa using h
    have hwc : Continuous w :=
      hzc.comp ((continuous_toGS Ω _).comp (galEmbTop E (Fn E Ω l 1) Ω).1.continuous)
    refine ⟨⟨φ, ?_, ?_, ?_⟩, hφ⟩
    · exact ((IsLocallyConstant.iff_continuous w).2 hwc).comp (fun y => eq1 (Function.invFun ι y))
    · intro a b
      apply hdet
      rw [map_add (f := _), map_add (f := _), hφ, hφ, hmul]
    · intro A hA g hg
      have hg' : galEmb E (Fn E Ω l 1) Ω g ∈ Ine A := by
        have h := ((galEmbFam E (Fn E Ω l 1) Ω l).1 A).2
        rw [← h] at hg
        exact hg
      have h1 : toGS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) (galEmb E (Fn E Ω l 1) Ω g) = 1 := by
        by_cases htop : A = ⊤
        · have h := ((places E Ω l A).2.1 htop).1
          rw [h, Subgroup.mem_bot] at hg'
          rw [hg', map_one]
        · obtain ⟨v, hv⟩ := (places E Ω l A).1 htop
          rw [toGS, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          apply Subgroup.le_topologicalClosure
          apply Subgroup.subset_normalClosure
          have hvS : v ∈ (↑D.S : Set (HeightOneSpectrum (𝓞 E)))ᶜ := by
            intro h
            rw [D.hS] at h
            exact hA (((places E Ω l A).2.2.1 v hv).2 h)
          exact Set.mem_iUnion₂.2 ⟨v, hvS, Set.mem_iUnion₂.2 ⟨A, hv, hg'⟩⟩
      apply hdet
      simp only [w, h1, hz1, map_zero]
  choose zf hzf using fun x : Submodule.torsionBy ℤ_[l] (H1 (qzTw D e)) (l : ℤ_[l]) =>
    UpperTheory.V.Odd.torsRep E Ω l D e x.1 ((Submodule.mem_torsionBy_iff _ _).1 x.2)
  choose φf hφf using fun x => key (zf x) (hzf x).2
  refine ⟨φf, ?_⟩
  intro x y hxy
  have hv : ∀ σ, (zf x : GS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) (toGS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) (galEmb E (Fn E Ω l 1) Ω σ)) =
      (zf y : GS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) (toGS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 E))) (galEmb E (Fn E Ω l 1) Ω σ)) := by
    intro σ
    rw [← hφf x σ, ← hφf y σ, hxy]
  apply Subtype.ext
  rw [(hzf x).1, (hzf y).1, ← sub_eq_zero, ← Submodule.Quotient.mk_sub]
  apply UpperTheory.V.Odd.cobOne E Ω l D e
  intro g hg
  rw [← range_galEmb E (Fn E Ω l 1) Ω] at hg
  obtain ⟨σ, rfl⟩ := hg
  simp only [Submodule.coe_sub, Pi.sub_apply]
  rw [hv σ, sub_self]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.SelCard
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem above_card (F : Type) [Field F] [NumberField F] (l : ℕ) [hl : Fact l.Prime] :
    (Above F l).Finite ∧ Nat.card (Above F l) ≤ Module.finrank ℚ F := by
  classical
  have hn : l.Prime := hl.out
  have hp0 : (Ideal.span {(l : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn.ne_zero
  have hmax : (Ideal.span {(l : ℤ)} : Ideal ℤ).IsMaximal := inferInstance
  have hm : ∀ p : Above F l, p.1.asIdeal ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(l : ℤ)}) (𝓞 F) := by
    rintro ⟨p, hp⟩
    have hp' : ((l : ℕ) : 𝓞 F) ∈ p.asIdeal := hp
    rw [IsDedekindDomain.mem_primesOverFinset_iff hp0]
    have := p.isPrime
    refine ⟨p.isPrime, ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact hp'
  let f : Above F l → IsDedekindDomain.primesOverFinset (Ideal.span {(l : ℤ)}) (𝓞 F) := fun p => ⟨_, hm p⟩
  have hf : Function.Injective f := fun p q h =>
    Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))
  refine ⟨Finite.of_injective f hf, (Nat.card_le_card_of_injective f hf).trans ?_⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  exact Ideal.card_primesOverFinset_le_finrank (𝓞 F) ℚ F hp0

theorem UpperTheory.V.Odd.selCard :
    ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime], Finite (SelK (Above E l) l ⧸ (powK E l).subgroupOf (SelK (Above E l) l)) ∧ Nat.card (SelK (Above E l) l ⧸ (powK E l).subgroupOf (SelK (Above E l) l)) ≤ l ^ (2 * Module.finrank ℚ E) * classNumber E := by
  intro E _ _ l hl
  have hn : l.Prime := hl.out
  haveI : NeZero l := ⟨hn.ne_zero⟩
  obtain ⟨hfin, hcard⟩ := above_card E l
  have h := cardSel E (Above E l) l hn.ne_zero
  rw [cardSUnit E (Above E l) l hfin] at h
  have hsurj : Function.Surjective (QuotientGroup.mk : ClassGroup (𝓞 E) → ClS (Above E l)) :=
    QuotientGroup.mk_surjective
  haveI : Finite (ClS (Above E l)) := Finite.of_surjective _ hsurj
  haveI : Nonempty {c : ClS (Above E l) // c ^ l = 1} := ⟨⟨1, one_pow _⟩⟩
  have h1 : Nat.card {c : ClS (Above E l) // c ^ l = 1} ≤ classNumber E := by
    refine (Nat.card_le_card_of_injective _ Subtype.val_injective).trans ?_
    refine (Nat.card_le_card_of_surjective _ hsurj).trans ?_
    rw [classNumber, Nat.card_eq_fintype_card]
  have h2 : Nat.card (rootsOfUnity l E) ≤ l := card_rootsOfUnity E l
  have h3 := InfinitePlace.card_add_two_mul_card_eq_rank E
  have h4 : 0 < Module.finrank ℚ E := Module.finrank_pos
  refine ⟨Nat.finite_of_card_ne_zero ?_, ?_⟩
  · rw [h]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hn.ne_zero) Nat.card_pos.ne') Nat.card_pos.ne'
  · rw [h]
    refine Nat.mul_le_mul ?_ h1
    refine (Nat.mul_le_mul_left _ h2).trans ?_
    rw [← pow_succ]
    exact Nat.pow_le_pow_right hn.pos (by omega)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.LogH
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.LogDisc
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.logDisc :
    ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 0 < N → Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) → (discr E).natAbs ≤ N ^ Module.finrank ℚ E ∧ Module.finrank ℚ E ≤ N := by
  intro E _ _ N hN ⟨φ⟩
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero (N : ℚ) := ⟨by exact_mod_cast hN.ne'⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  let F := φ.fieldRange
  have e : E ≃ₐ[ℚ] F := AlgEquiv.ofInjectiveField φ
  have hrank : Module.finrank ℚ E = Module.finrank ℚ F := e.toLinearEquiv.finrank_eq
  have hdisc : discr E = discr F := NumberField.discr_eq_discr_of_algEquiv E e
  obtain ⟨hprod, -, -⟩ := KStar.Ram.natAbs_discr_eq_finprod_conductor (N := N) (K := CyclotomicField N ℚ) F
  obtain ⟨hcard, -⟩ := KStar.Ram.card_fieldChars (N := N) (K := CyclotomicField N ℚ) F
  constructor
  · rw [hdisc, hprod, hrank, ← hcard]
    haveI : Fintype (KStar.Ram.fieldChars N F) := Fintype.ofFinite _
    rw [finprod_eq_prod_of_fintype, Nat.card_eq_fintype_card, ← Finset.card_univ]
    exact Finset.prod_le_pow_card _ _ _
      (fun ψ _ => Nat.le_of_dvd hN (DirichletCharacter.conductor_dvd_level _))
  · have hinj : Function.Injective φ.toLinearMap := (φ : E →+* CyclotomicField N ℚ).injective
    have h := LinearMap.finrank_le_finrank_of_injective hinj
    rw [IsCyclotomicExtension.finrank (CyclotomicField N ℚ)
      (Polynomial.cyclotomic.irreducible_rat hN)] at h
    exact h.trans (Nat.totient_le N)
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.logH :
    ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 2 ≤ N → Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) → Real.log (classNumber E) ≤ 3 * Module.finrank ℚ E * Real.log N := by
  intro E _ _ N hN hE
  obtain ⟨hd, hn⟩ := UpperTheory.V.Odd.logDisc E N (by omega) hE
  have hc := KStar.IdealCounting.log_classNumber_le E
  have hd1 : (1 : ℝ) ≤ |(discr E : ℝ)| := by
    exact_mod_cast Int.one_le_abs (discr_ne_zero E)
  have hd2 : |(discr E : ℝ)| ≤ (N : ℝ) ^ Module.finrank ℚ E := by
    have h : (((discr E).natAbs : ℕ) : ℝ) ≤ (N : ℝ) ^ Module.finrank ℚ E := by exact_mod_cast hd
    rwa [Nat.cast_natAbs, Int.cast_abs] at h
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn' : (Module.finrank ℚ E : ℝ) ≤ N := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ (Module.finrank ℚ E : ℝ) := Nat.cast_nonneg _
  generalize Module.finrank ℚ E = n at *
  have hL0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hL1 : Real.log N ≤ N - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hD0 : 0 ≤ Real.log |(discr E : ℝ)| := Real.log_nonneg hd1
  have hD : Real.log |(discr E : ℝ)| ≤ n * Real.log N := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by linarith) hd2
  have hnL : (n : ℝ) * Real.log N ≤ N * (N - 1) := mul_le_mul hn' hL1 hL0 (by linarith)
  have h2 : Real.log (1 + Real.log |(discr E : ℝ)| / 2) ≤ 2 * Real.log N := by
    have e : 2 * Real.log N = Real.log ((N : ℝ) ^ 2) := by rw [Real.log_pow]; norm_num
    rw [e]
    apply Real.log_le_log (by linarith)
    nlinarith
  have h3 := mul_le_mul_of_nonneg_left h2 hn0
  have h4 := mul_nonneg hn0 hL0
  nlinarith
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.UnrSel
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.unrSel :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], (∃ ζ : E, IsPrimitiveRoot ζ l) → ∃ f : UnrHom E Ω l → SelK (Above E l) l ⧸ (powK E l).subgroupOf (SelK (Above E l) l), Function.Injective f := by
  intro E Ω _ _ _ _ _ l _ hζE
  obtain ⟨ζ₀, hζ₀⟩ := hζE
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  haveI : Fact (1 < l) := ⟨(Fact.out : l.Prime).one_lt⟩
  have hζ : IsPrimitiveRoot (algebraMap E Ω ζ₀) l := hζ₀.map_of_injective (algebraMap E Ω).injective
  have hgζ : ∀ g : G E Ω, g (algebraMap E Ω ζ₀) = algebraMap E Ω ζ₀ := fun g => g.commutes ζ₀
  have hdata : ∀ φ : UnrHom E Ω l, ∃ β : Ω, ∃ a : Eˣ, β ^ l = algebraMap E Ω a ∧
      ∀ g : G E Ω, g β = algebraMap E Ω ζ₀ ^ (φ.1 g).val * β := by
    intro φ
    obtain ⟨hlc, hadd, -⟩ := φ.2
    exact radExists E Ω l (algebraMap E Ω ζ₀) (fun _ => 1) φ.1 hζ
      (fun g => by rw [hgζ, ZMod.val_one, pow_one]) hlc (fun g h => by rw [hadd, one_mul])
  choose β a hβa hgβ using hdata
  have hsel : ∀ φ, a φ ∈ SelK (Above E l) l := by
    intro φ
    show ∀ v ∉ Above E l, _
    intro v hv
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    refine dvdOfIne E Ω l A v (β φ) (a φ) hA (hβa φ) ?_
    intro g hg
    have hnot : ¬ A.valuation (l : Ω) < 1 := by
      intro h
      apply hv
      have hp := hA (l : 𝓞 E)
      have he : algebraMap E Ω (((l : 𝓞 E) : E)) = (l : Ω) := by simp
      exact hp.mp (he ▸ h)
    have h0 : φ.1 g = 0 := φ.2.2.2 A hnot g hg
    rw [hgβ, h0, ZMod.val_zero, pow_zero, one_mul]
  refine ⟨fun φ => QuotientGroup.mk ⟨a φ, hsel φ⟩, fun φ ψ hfe => ?_⟩
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hfe
  obtain ⟨c, hc⟩ := hfe
  have hc' : a ψ = a φ * c ^ l := by
    have h : c ^ l = (a φ)⁻¹ * a ψ := by simpa using hc
    rw [h, mul_inv_cancel_left]
  have hβne : ∀ φ, β φ ≠ 0 := by
    intro φ h
    have h' := hβa φ
    rw [h, zero_pow (NeZero.ne l)] at h'
    exact (a φ).ne_zero ((map_eq_zero_iff _ (algebraMap E Ω).injective).mp h'.symm)
  have hcΩ : algebraMap E Ω (c : E) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap E Ω).injective).mpr c.ne_zero
  apply Subtype.ext
  funext g
  have hγl : (β ψ / (β φ * algebraMap E Ω c)) ^ l = 1 := by
    rw [div_pow, mul_pow, hβa ψ, hβa φ, ← map_pow, ← map_mul, hc', Units.val_mul, Units.val_pow_eq_pow_val]
    exact div_self ((map_ne_zero_iff _ (algebraMap E Ω).injective).mpr
      (mul_ne_zero (a φ).ne_zero (pow_ne_zero _ c.ne_zero)))
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hγl
  have hgγ : g (β ψ / (β φ * algebraMap E Ω c)) = β ψ / (β φ * algebraMap E Ω c) := by
    rw [← hi, map_pow, hgζ]
  have hγ0 : β ψ / (β φ * algebraMap E Ω c) ≠ 0 := div_ne_zero (hβne ψ) (mul_ne_zero (hβne φ) hcΩ)
  have hgγ' : g (β ψ / (β φ * algebraMap E Ω c)) =
      algebraMap E Ω ζ₀ ^ (ψ.1 g).val / algebraMap E Ω ζ₀ ^ (φ.1 g).val *
        (β ψ / (β φ * algebraMap E Ω c)) := by
    rw [map_div₀, map_mul, hgβ, hgβ, AlgEquiv.commutes, mul_assoc, mul_div_mul_comm]
  have hζb : algebraMap E Ω ζ₀ ^ (φ.1 g).val ≠ 0 := pow_ne_zero _ (hζ.ne_zero (NeZero.ne l))
  have hq : algebraMap E Ω ζ₀ ^ (ψ.1 g).val / algebraMap E Ω ζ₀ ^ (φ.1 g).val = 1 := by
    apply mul_right_cancel₀ hγ0
    rw [one_mul, ← hgγ', hgγ]
  have hpow := ((div_eq_one_iff_eq hζb).mp hq).symm
  exact ZMod.val_injective l (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hpow)
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.gen :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ), 0 < N → Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) → ∀ (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ), ∃ g : ℕ, Module.length ℤ_[l] (Submodule.torsionBy ℤ_[l] (H1 (qzTw D e)) (l : ℤ_[l])) ≤ g ∧ (g : ℝ) ≤ 8 * l * Module.finrank ℚ E * Real.log ((l : ℝ) * N) := by
  intro E Ω _ _ _ _ _ N hN hE l hl D e
  have hl2 : 2 ≤ l := hl.out.two_le
  obtain ⟨hdeg, hζ, hemb⟩ := fnOne E Ω l
  obtain ⟨f, hf⟩ := unrInj E Ω l D e
  obtain ⟨f', hf'⟩ := unrSel (Fn E Ω l 1) Ω l hζ
  obtain ⟨hfin, hcard⟩ := selCard (Fn E Ω l 1) l
  have hH := logH (Fn E Ω l 1) (l * N) (by nlinarith) (hemb N hN hE)
  haveI := Finite.of_injective _ (hf'.comp hf)
  obtain ⟨k, hk, hc⟩ := lenOfCard l (Submodule.torsionBy ℤ_[l] (H1 (qzTw D e)) (l : ℤ_[l]))
  have h1 := (Nat.card_le_card_of_injective _ (hf'.comp hf)).trans hcard
  rw [hc] at h1
  have hn : Module.finrank ℚ (Fn E Ω l 1) ≤ l * Module.finrank ℚ E := by
    rw [← Module.finrank_mul_finrank ℚ E (Fn E Ω l 1), mul_comm]
    exact Nat.mul_le_mul_right _ ((Nat.le_of_dvd (by omega) hdeg).trans (by omega))
  refine ⟨k, hk.le, ?_⟩
  have hh : (0 : ℝ) < classNumber (Fn E Ω l 1) := by exact_mod_cast classNumber_pos _
  generalize Module.finrank ℚ (Fn E Ω l 1) = m at *
  generalize classNumber (Fn E Ω l 1) = h at *
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl2
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h2 : (l : ℝ) ^ k ≤ (l : ℝ) ^ (2 * m) * h := by exact_mod_cast h1
  have h3 := Real.log_le_log (by positivity) h2
  rw [Real.log_mul (by positivity) hh.ne', Real.log_pow, Real.log_pow] at h3
  push_cast at h3 hH
  have ha : Real.log 2 ≤ Real.log l := Real.log_le_log (by norm_num) hl'
  have hb : Real.log l ≤ Real.log ((l : ℝ) * N) := Real.log_le_log (by positivity) (by nlinarith)
  have h2' := Real.log_two_gt_d9
  have hn' : (m : ℝ) ≤ l * Module.finrank ℚ E := by exact_mod_cast hn
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have h4 := mul_le_mul_of_nonneg_left hb hm
  have h5 : (k : ℝ) * (5 / 8) ≤ k * Real.log l := mul_le_mul_of_nonneg_left (by linarith) hk0
  have h6 := mul_le_mul_of_nonneg_right hn' (show 0 ≤ Real.log ((l : ℝ) * N) by linarith)
  nlinarith
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ProdVal
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.prodVal :
    ∀ (N : ℕ) [NeZero N] (k : ℕ) (P : Set (Subgroup (ZMod N)ˣ)), 1 ≤ k → P ⊆ parKer N k → ∃ w : ℕ → ℕ, (∀ T : Finset ℕ, (∀ l ∈ T, l.Prime) → ∑ l ∈ T, (w l : ℝ) * Real.log l ≤ (charSet ℂ P).ncard * Real.log (bnd N k)) ∧ ∀ (l : ℕ) [Fact l.Prime] (T : Finset (DirichletCharacter (PadicAlgCl l) N)), (T : Set _) ⊆ charSet (PadicAlgCl l) P → ∑ χ ∈ T, -Real.log ‖alN k χ‖ ≤ (w l : ℝ) * Real.log l := by
  intro N _ k P hk hP
  obtain ⟨M, hM0, hlog, hprod⟩ := b_prodint k P hk hP
  refine ⟨fun l => padicValInt l M, fun T hT => (b_sumval M hM0 T hT).trans hlog, ?_⟩
  intro l _ T hTS
  have hnorm : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]
  have hS : (charSet (PadicAlgCl l) P).Finite := Set.toFinite _
  have hint : ∀ χ ∈ charSet (PadicAlgCl l) P, IsIntegral ℤ (((1 : ℕ) : PadicAlgCl l) * alN k χ) := by
    intro χ _
    rw [Nat.cast_one, one_mul]
    exact (b_primmem k χ).2.2.1
  have hpr : ∏ᶠ (χ : DirichletCharacter (PadicAlgCl l) N) (_ : χ ∈ charSet (PadicAlgCl l) P),
      ((1 : ℕ) : PadicAlgCl l) * alN k χ = (M : PadicAlgCl l) := by
    simp only [Nat.cast_one, one_mul]
    exact hprod (PadicAlgCl l)
  have hu := b_ultra l hnorm (charSet (PadicAlgCl l) P) (fun χ => alN k χ) 1 M hS hM0 hint hpr
  rw [finsum_mem_eq_finite_toFinset_sum _ hS] at hu
  calc ∑ χ ∈ T, -Real.log ‖alN k χ‖ ≤ ∑ χ ∈ T, max 0 (-Real.log ‖alN k χ‖) :=
        Finset.sum_le_sum fun χ _ => le_max_right _ _
    _ ≤ ∑ χ ∈ hS.toFinset, max 0 (-Real.log ‖alN k χ‖) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun χ hχ => hS.mem_toFinset.mpr (hTS (Finset.mem_coe.mpr hχ))) (fun _ _ _ => le_max_left _ _)
    _ ≤ _ := hu
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.LenPow
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem length_ker_pow_le (R X : Type) [CommRing R] [AddCommGroup X] [Module R X]
    (f : Module.End R X) (r : ℕ) :
    Module.length R (LinearMap.ker (f ^ r)) ≤ r * Module.length R (LinearMap.ker f) := by
  induction r with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, nonpos_iff_eq_zero]
    rw [Module.length_eq_zero_iff]
    refine ⟨fun x y => Subtype.ext ?_⟩
    have hx := LinearMap.mem_ker.mp x.2
    have hy := LinearMap.mem_ker.mp y.2
    simp only [pow_zero, Module.End.one_apply] at hx hy
    rw [hx, hy]
  | succ n ih =>
    rw [pow_succ]
    refine ((UpperTheory.V.Base.lenComp R X (f ^ n) f).1).trans ?_
    calc Module.length R (LinearMap.ker (f ^ n)) + Module.length R (LinearMap.ker f)
        ≤ n * Module.length R (LinearMap.ker f) + Module.length R (LinearMap.ker f) := by
          gcongr
      _ = ((n + 1 : ℕ) : ℕ∞) * Module.length R (LinearMap.ker f) := by
          push_cast; rw [add_mul, one_mul]

theorem UpperTheory.V.Odd.lenPow :
    ∀ (R X : Type) [CommRing R] [AddCommGroup X] [Module R X] (P : Submodule R X) (a : R) (r : ℕ), (∀ x ∈ P, a ^ r • x = 0) → Module.length R P ≤ r * Module.length R (Submodule.torsionBy R X a) := by
  intro R X _ _ _ P a r hP
  let f : Module.End R X := a • (1 : Module.End R X)
  have hker : LinearMap.ker f = Submodule.torsionBy R X a := by
    ext x
    simp [f, Submodule.mem_torsionBy_iff]
  have hpow : ∀ x : X, (f ^ r) x = a ^ r • x := by
    intro x
    simp [f, smul_pow]
  have hle : P ≤ LinearMap.ker (f ^ r) := by
    intro x hx
    rw [LinearMap.mem_ker, hpow]
    exact hP x hx
  calc Module.length R P ≤ Module.length R (LinearMap.ker (f ^ r)) :=
        Module.length_le_of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
    _ ≤ r * Module.length R (LinearMap.ker f) := length_ker_pow_le R X f r
    _ = r * Module.length R (Submodule.torsionBy R X a) := by rw [hker]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.DegExistsLift
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem deg_jac {a p n : ℕ} (h : a.Coprime p) : jacobiSym ((a ^ (2 * n) : ℕ) : ℤ) p = 1 := by
  have hc : Int.gcd ((a ^ n : ℕ) : ℤ) (p : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact Nat.Coprime.pow_left n h
  have he : ((a ^ (2 * n) : ℕ) : ℤ) = ((a ^ n : ℕ) : ℤ) ^ 2 := by
    push_cast
    ring
  rw [he]
  exact jacobiSym.sq_one' hc

private theorem deg_ker (A : AbF) {a : ℕ} (n : ℕ) (h : a.Coprime A.m) : A.ker (a ^ (A.deg * n)) := by
  haveI : NeZero A.m := ⟨A.pos.ne'⟩
  let u : (ZMod A.m)ˣ := ZMod.unitOfCoprime a h
  refine ⟨u ^ (A.deg * n), ?_, ?_⟩
  · rw [pow_mul]
    exact Subgroup.pow_mem _ (Subgroup.pow_index_mem A.H u) n
  · push_cast
    simp [u, ZMod.coe_unitOfCoprime]

private theorem deg_two {a e : ℕ} (n : ℕ) (h : a.Coprime (2 ^ (e + 2))) :
    a ^ (2 ^ (e + 1) * n) ≡ 1 [MOD 2 ^ (e + 2)] := by
  have ht := Nat.ModEq.pow_totient h
  rw [Nat.totient_prime_pow Nat.prime_two (by omega)] at ht
  simp only [Nat.add_sub_cancel, show (2 : ℕ) - 1 = 1 from rfl, mul_one] at ht
  rw [pow_mul]
  simpa using ht.pow n

theorem UpperTheory.V.Odd.deg :
    ∀ (M : AbF) (e q d : ℕ), PrimePair M.m q d → ∀ (E : Type) [Field E] [NumberField E], IsCompField M e q d E → ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ Module.finrank ℚ E → l ∣ M.deg := by
  intro M e q d _ E _ _ hE l hl hl2 hldvd
  obtain ⟨N, hN, j, ζ, h1, h2, h3, h4, hζ, hfix⟩ := hE
  haveI : NeZero (N : ℚ) := ⟨by exact_mod_cast hN.ne⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  haveI : IsGalois ℚ (CyclotomicField N ℚ) := IsCyclotomicExtension.isGalois {N} ℚ _
  have hpowζ : ∀ (τ : Gal(CyclotomicField N ℚ/ℚ)) (a n : ℕ), τ ζ = ζ ^ a → (τ ^ n) ζ = ζ ^ (a ^ n) := by
    intro τ a n hτ
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ τ n, AlgEquiv.mul_apply, hτ, map_pow, ih, ← pow_mul, pow_succ a n]
  have hmem : ∀ (τ : Gal(CyclotomicField N ℚ/ℚ)) (x : E),
      (τ ^ (2 ^ (e + 1) * M.deg)) (j x) = j x := by
    intro τ
    have hτ : τ ζ = ζ ^ ((hζ.autToPow ℚ τ : (ZMod N)ˣ) : ZMod N).val := (hζ.autToPow_spec ℚ τ).symm
    have hcop : (((hζ.autToPow ℚ τ : (ZMod N)ˣ) : ZMod N).val).Coprime N := ZMod.val_coe_unit_coprime _
    refine (hfix _ _ (hpowζ τ _ (2 ^ (e + 1) * M.deg) hτ)).mpr ⟨Or.inl ?_, ?_, ?_, ?_⟩
    · exact deg_two M.deg (hcop.coprime_dvd_right h1)
    · have hk := deg_ker M (2 ^ (e + 1)) (hcop.coprime_dvd_right h2)
      rwa [mul_comm M.deg] at hk
    · have hk := deg_jac (n := 2 ^ e * M.deg) (hcop.coprime_dvd_right h3)
      rwa [show 2 * (2 ^ e * M.deg) = 2 ^ (e + 1) * M.deg by ring] at hk
    · have hk := deg_jac (n := 2 ^ e * M.deg) (hcop.coprime_dvd_right h4)
      rwa [show 2 * (2 ^ e * M.deg) = 2 ^ (e + 1) * M.deg by ring] at hk
  obtain ⟨F, hF⟩ : ∃ F : IntermediateField ℚ (CyclotomicField N ℚ), F = j.fieldRange := ⟨_, rfl⟩
  have hcomm : ∀ σ τ : Gal(CyclotomicField N ℚ/ℚ), σ * τ = τ * σ := by
    intro σ τ
    apply IsPrimitiveRoot.autToPow_injective ℚ hζ
    rw [map_mul, map_mul, mul_comm]
  haveI hKn : F.fixingSubgroup.Normal :=
    ⟨fun n hn g => by rw [hcomm g n, mul_assoc, mul_inv_cancel, mul_one]; exact hn⟩
  have hKmem : ∀ τ : Gal(CyclotomicField N ℚ/ℚ), τ ^ (2 ^ (e + 1) * M.deg) ∈ F.fixingSubgroup := by
    intro τ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [hF] at hx
    obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.mp hx
    exact hmem τ y
  have hindex : F.fixingSubgroup.index = Module.finrank ℚ E := by
    have e1 : Module.finrank ℚ E = Module.finrank ℚ F := by
      rw [hF]
      exact (AlgEquiv.ofInjectiveField j).toLinearEquiv.finrank_eq
    have e2 := Module.finrank_mul_finrank ℚ F (CyclotomicField N ℚ)
    have e3 := IsGalois.card_fixingSubgroup_eq_finrank F
    have e4 := IsGalois.card_aut_eq_finrank ℚ (CyclotomicField N ℚ)
    have e5 := F.fixingSubgroup.card_mul_index
    have hpos : 0 < Module.finrank F (CyclotomicField N ℚ) := Module.finrank_pos
    rw [e1]
    rw [e3, e4, ← e2, mul_comm (Module.finrank ℚ F)] at e5
    exact Nat.eq_of_mul_eq_mul_left hpos e5
  haveI : Fact l.Prime := ⟨hl⟩
  have hcard : l ∣ Nat.card (Gal(CyclotomicField N ℚ/ℚ) ⧸ F.fixingSubgroup) := by
    show l ∣ F.fixingSubgroup.index
    rw [hindex]
    exact hldvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' l hcard
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hxk : ((g : Gal(CyclotomicField N ℚ/ℚ) ⧸ F.fixingSubgroup)) ^ (2 ^ (e + 1) * M.deg) = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hKmem g
  have hdk := orderOf_dvd_of_pow_eq_one hxk
  rw [hx] at hdk
  have hcop : l.Coprime (2 ^ (e + 1)) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hl Nat.prime_two).mpr hl2)
  exact hcop.dvd_of_dvd_mul_left hdk
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

namespace UpperTheory.V.Odd

private theorem stick_of (hK : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ), 0 < N → Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) → ∀ (l : ℕ) [Fact l.Prime] (D : LData E Ω l), Procyc E Ω l → ∀ e : ℕ, 1 ≤ e → ∃ r : ℕ, (r : ℝ) * Real.log l ≤ C * Module.finrank ℚ E * (e + 1) * Real.log ((e : ℝ) * l * N) ∧ ∀ x ∈ ShaMinus D e, (l : ℤ_[l]) ^ r • x = 0) (hL : ∀ (R X : Type) [CommRing R] [AddCommGroup X] [Module R X] (P : Submodule R X) (a : R) (r : ℕ), (∀ x ∈ P, a ^ r • x = 0) → Module.length R P ≤ r * Module.length R (Submodule.torsionBy R X a)) (hG : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ), 0 < N → Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) → ∀ (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ), ∃ g : ℕ, Module.length ℤ_[l] (Submodule.torsionBy ℤ_[l] (H1 (qzTw D e)) (l : ℤ_[l])) ≤ g ∧ (g : ℝ) ≤ 8 * l * Module.finrank ℚ E * Real.log ((l : ℝ) * N)) : ∃ C : ℝ, 0 ≤ C ∧ StickBound C := by
  obtain ⟨C, hC, hK⟩ := hK
  refine ⟨8 * C, by positivity, fun E Ω _ _ _ _ _ _ N hN hE l _ D hP e he => ?_⟩
  obtain ⟨r, hr, hk⟩ := hK E Ω N hN hE l D hP e he
  obtain ⟨g, hg, hg'⟩ := hG E Ω N hN hE l D e
  have h1 : minusLen D e ≤ ((r * g : ℕ) : ℕ∞) := by
    push_cast
    exact (hL _ _ (ShaMinus D e) _ r hk).trans (by gcongr)
  have h2 : minusLen D e ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) h1
  refine ⟨h2, ?_⟩
  have h3 : ((minusLen D e).toNat : ℝ) ≤ r * g := by exact_mod_cast ENat.toNat_le_of_le_coe h1
  have hl : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_le
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hlN : (1 : ℝ) ≤ l * N := one_le_mul_of_one_le_of_one_le hl hN'
  have h4 : Real.log ((l : ℝ) * N) ≤ Real.log ((e : ℝ) * l * N) :=
    Real.log_le_log (by positivity) (by rw [mul_assoc]; exact le_mul_of_one_le_left (by positivity) he')
  have h5 : 0 ≤ Real.log ((e : ℝ) * l * N) := (Real.log_nonneg hlN).trans h4
  have h6 : 0 ≤ Real.log l := Real.log_nonneg hl
  calc ((minusLen D e).toNat : ℝ) * Real.log l ≤ (r * g) * Real.log l := by gcongr
    _ = (r * Real.log l) * g := by ring
    _ ≤ (C * Module.finrank ℚ E * (e + 1) * Real.log ((e : ℝ) * l * N)) *
        (8 * l * Module.finrank ℚ E * Real.log ((e : ℝ) * l * N)) := by
      refine mul_le_mul hr (hg'.trans (by gcongr)) (by positivity) (by positivity)
    _ = _ := by ring

private theorem ncard_charSet_le_ker_index {E : Type} [Field E] [NumberField E] {N : ℕ} [NeZero N]
    (ρ : (ZMod N)ˣ →* Gal(E/ℚ)) (k : ℕ) : (charSet ℂ (parE ρ k)).ncard ≤ ρ.ker.index := by
  classical
  have hS : ∀ χ ∈ charSet ℂ (parE ρ k), ρ.ker ≤ (MulChar.toUnitHom χ).ker := by
    intro χ hχ
    simp only [charSet, Set.mem_setOf_eq, parE] at hχ
    exact hχ.1
  let f : charSet ℂ (parE ρ k) → ((ZMod N)ˣ ⧸ ρ.ker →* ℂˣ) :=
    fun χ => QuotientGroup.lift ρ.ker (MulChar.toUnitHom χ.1) (hS χ.1 χ.2)
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply MulChar.ext
    intro u
    have := congrArg (fun g => ((g (QuotientGroup.mk u) : ℂˣ) : ℂ)) hab
    simpa [f] using this
  have hQ : Nat.card ((ZMod N)ˣ ⧸ ρ.ker →* ℂˣ) = ρ.ker.index := by
    rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity]
    rfl
  have hfin : Finite ((ZMod N)ˣ ⧸ ρ.ker →* ℂˣ) :=
    Nat.finite_of_card_ne_zero (by rw [hQ]; exact Subgroup.index_ne_zero_of_finite)
  calc (charSet ℂ (parE ρ k)).ncard = Nat.card (charSet ℂ (parE ρ k)) :=
        (Nat.card_coe_set_eq _).symm
    _ ≤ Nat.card ((ZMod N)ˣ ⧸ ρ.ker →* ℂˣ) := Nat.card_le_card_of_injective f hf
    _ = _ := hQ

private theorem prime_of (hA : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ) [NeZero N], Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) → ∃ ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E), IsCycAct Ω N ρ) (hF : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ) [NeZero N] (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)), IsCycAct Ω N ρ → Function.Surjective ρ ∧ IsAbelianGalois ℚ E ∧ Nat.card (Gq ρ) = Module.finrank ℚ E ∧ ρ.ker.index = Module.finrank ℚ E ∧ ∀ (M : ℕ) [NeZero M] (h : N ∣ M), IsCycAct Ω M (ρ.comp (ZMod.unitsMap h))) (hV : ∀ (N : ℕ) [NeZero N] (k : ℕ) (P : Set (Subgroup (ZMod N)ˣ)), 1 ≤ k → P ⊆ parKer N k → ∃ w : ℕ → ℕ, (∀ T : Finset ℕ, (∀ l ∈ T, l.Prime) → ∑ l ∈ T, (w l : ℝ) * Real.log l ≤ (charSet ℂ P).ncard * Real.log (bnd N k)) ∧ ∀ (l : ℕ) [Fact l.Prime] (T : Finset (DirichletCharacter (PadicAlgCl l) N)), (T : Set _) ⊆ charSet (PadicAlgCl l) P → ∑ χ ∈ T, -Real.log ‖alN k χ‖ ≤ (w l : ℝ) * Real.log l) (hP : PsiBound → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ) [NeZero N] (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)), IsCycAct Ω N ρ → ∀ (l : ℕ) [Fact l.Prime] (D : LData E Ω l), l ≠ 2 → ¬ l ∣ Module.finrank ℚ E → ∀ e : ℕ, 1 ≤ e → minusLen D e ≠ ⊤ ∧ ∃ T : Finset (DirichletCharacter (PadicAlgCl l) N), (T : Set _) ⊆ charSet (PadicAlgCl l) (parE ρ (e + 1)) ∧ ((minusLen D e).toNat : ℝ) * Real.log l ≤ ∑ χ ∈ T, -Real.log ‖alN (e + 1) χ‖)
    (h : PsiBound) : PrimeBound := by
  intro E Ω _ _ _ _ _ _ N hN hemb ld e he
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨ρ, hρ⟩ := hA E Ω N hemb
  obtain ⟨-, -, -, hidx, -⟩ := hF E Ω N ρ hρ
  have key : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ p ∣ Module.finrank ℚ E →
      minusLen (ld p) e ≠ ⊤ ∧ ∃ T : Finset (DirichletCharacter (PadicAlgCl p) N),
        (T : Set _) ⊆ charSet (PadicAlgCl p) (parE ρ (e + 1)) ∧
        ((minusLen (ld p) e).toNat : ℝ) * Real.log p ≤ ∑ χ ∈ T, -Real.log ‖alN (e + 1) χ‖ :=
    fun p _ hp2 hpd => hP h E Ω N ρ hρ p (ld p) hp2 hpd e he
  refine ⟨fun p _ hp2 hpd => (key p hp2 hpd).1, ?_⟩
  intro S hS
  obtain ⟨w, hw1, hw2⟩ := hV N (e + 1) (parE ρ (e + 1)) (by omega) (fun H hH => hH.2)
  have hterm : ∀ l ∈ S, Real.log ((l : ℕ) : ℝ) * ((minusLen (ld (l : ℕ)) e).toNat : ℝ) ≤
      (w l : ℝ) * Real.log ((l : ℕ) : ℝ) := by
    intro l hl
    haveI : Fact (l : ℕ).Prime := ⟨l.2⟩
    obtain ⟨-, T, hT, hle⟩ := key l (hS l hl).1 (hS l hl).2
    have h2 := hw2 l T hT
    nlinarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogb : 0 ≤ Real.log (bnd N (e + 1)) := by
    apply Real.log_nonneg
    unfold bnd
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (e + 1 + 1) := one_le_pow₀ hN1
    have h2 : (1 : ℝ) ≤ ((e + 1).factorial : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    nlinarith
  calc ∑ l ∈ S, Real.log ((l : ℕ) : ℝ) * ((minusLen (ld (l : ℕ)) e).toNat : ℝ)
        ≤ ∑ l ∈ S, (w l : ℝ) * Real.log ((l : ℕ) : ℝ) := Finset.sum_le_sum hterm
    _ = ∑ m ∈ S.image (fun p : Nat.Primes => (p : ℕ)), (w m : ℝ) * Real.log (m : ℝ) :=
        (Finset.sum_image (f := fun m : ℕ => (w m : ℝ) * Real.log m) (s := S)
          (g := fun p : Nat.Primes => (p : ℕ)) (fun a _ b _ h => Nat.Primes.coe_nat_injective h)).symm
    _ ≤ (charSet ℂ (parE ρ (e + 1))).ncard * Real.log (bnd N (e + 1)) := by
        apply hw1
        intro m hm
        obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hm
        exact p.2
    _ ≤ (Module.finrank ℚ E : ℝ) * Real.log (bnd N (e + 1)) := by
        apply mul_le_mul_of_nonneg_right _ hlogb
        exact_mod_cast (ncard_charSet_le_ker_index ρ (e + 1)).trans hidx.le

private theorem log_bnd_le_mul_log (F t e : ℕ) (hF : 0 < F) (ht : 2 ≤ t) (he : e + 1 ≤ t) :
    Real.log (bnd F (e + 1)) ≤ (2 * t + 5) * Real.log (t * F) := by
  have htF : 2 ≤ t * F := le_trans ht (Nat.le_mul_of_pos_right t hF)
  have h1 : 16 ≤ (t * F) ^ 4 := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ (t * F) ^ 4 := Nat.pow_le_pow_left htF 4
  have h2 : F ^ (e + 1 + 1) ≤ (t * F) ^ (t + 1) :=
    calc F ^ (e + 1 + 1) ≤ (t * F) ^ (e + 1 + 1) :=
          Nat.pow_le_pow_left (Nat.le_mul_of_pos_left F (by omega)) _
      _ ≤ (t * F) ^ (t + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : (e + 1).factorial ≤ (t * F) ^ t :=
    calc (e + 1).factorial ≤ (e + 1) ^ (e + 1) := Nat.factorial_le_pow _
      _ ≤ t ^ (e + 1) := Nat.pow_le_pow_left he _
      _ ≤ t ^ t := Nat.pow_le_pow_right (by omega) he
      _ ≤ (t * F) ^ t := Nat.pow_le_pow_left (Nat.le_mul_of_pos_right t hF) _
  have hnat : 16 * F ^ (e + 1 + 1) * (e + 1).factorial ≤ (t * F) ^ (2 * t + 5) := by
    calc 16 * F ^ (e + 1 + 1) * (e + 1).factorial
        ≤ (t * F) ^ 4 * (t * F) ^ (t + 1) * (t * F) ^ t :=
          Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
      _ = (t * F) ^ (2 * t + 5) := by
          rw [← pow_add, ← pow_add]
          congr 1
          omega
  have hF' : (0 : ℝ) < F := by exact_mod_cast hF
  have hreal : bnd F (e + 1) ≤ ((t : ℝ) * F) ^ (2 * t + 5) := by
    unfold bnd
    exact_mod_cast hnat
  have hpos : 0 < bnd F (e + 1) := by
    unfold bnd
    positivity
  calc Real.log (bnd F (e + 1)) ≤ Real.log (((t : ℝ) * F) ^ (2 * t + 5)) :=
        Real.log_le_log hpos hreal
    _ = (2 * t + 5) * Real.log (t * F) := by
        rw [Real.log_pow]
        push_cast
        ring

private theorem thmBc_of (hD : ∀ (M : AbF) (e q d : ℕ), PrimePair M.m q d → ∀ (E : Type) [Field E] [NumberField E], IsCompField M e q d E → ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ Module.finrank ℚ E → l ∣ M.deg) (hS : ∃ C : ℝ, 0 ≤ C ∧ StickBound C) (hP : PrimeBound) : ThmBcFree := by
  obtain ⟨C, hC0, hSt⟩ := hS
  refine ⟨C, ?_⟩
  intro M e t q d he ht hpp E _ _ _ hcomp
  have hmem : condF E ∈ {N : ℕ | 0 < N ∧ Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ)} := by
    unfold condF
    apply Nat.sInf_mem
    unfold IsCompField at hcomp
    obtain ⟨N, hN0, j, -⟩ := hcomp
    exact ⟨N, Nat.pos_of_ne_zero hN0.out, ⟨j⟩⟩
  obtain ⟨hFpos, hemb⟩ := hmem
  have hdvd : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ Module.finrank ℚ E → l ∣ M.deg :=
    hD M e q d hpp E hcomp
  haveI : NeZero M.m := NeZero.of_pos M.pos
  have hdeg : M.deg ≠ 0 := by
    unfold AbF.deg
    exact Subgroup.index_ne_zero_of_finite
  unfold VVminusLe minusBound
  intro Ω _ _ _ ld
  set F := condF E with hFdef
  set dE := Module.finrank ℚ E with hdE
  refine ⟨?_, ?_⟩
  · intro p _ e' hp2 he' _
    by_cases hpd : p ∣ dE
    · have hpc : Procyc E Ω p := by
        unfold Procyc
        exact Or.inl hp2
      exact (hSt E Ω F hFpos hemb p (ld p) hpc e' he').1
    · exact (hP E Ω F hFpos hemb ld e' he').1 p hp2 hpd
  · intro S hS2
    rw [← Finset.sum_filter_add_sum_filter_not S (fun l : Nat.Primes => ¬ (l : ℕ) ∣ dE)]
    have hF1 : (1 : ℝ) ≤ F := by exact_mod_cast hFpos
    have ht1 : (2 : ℝ) ≤ t := by exact_mod_cast ht
    have hlogtF : 0 ≤ Real.log ((t : ℝ) * F) := Real.log_nonneg (by nlinarith)
    have hd0 : (0 : ℝ) ≤ dE := Nat.cast_nonneg _
    have hA : ∑ l ∈ S.filter (fun l : Nat.Primes => ¬ (l : ℕ) ∣ dE),
        Real.log ((l : ℕ) : ℝ) * ∑ e' ∈ Finset.Ico 1 t, ((minusLen (ld (l : ℕ)) e').toNat : ℝ) ≤
        3 * dE * t ^ 2 * Real.log (t * F) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      calc ∑ e' ∈ Finset.Ico 1 t, ∑ l ∈ S.filter (fun l : Nat.Primes => ¬ (l : ℕ) ∣ dE),
            Real.log ((l : ℕ) : ℝ) * ((minusLen (ld (l : ℕ)) e').toNat : ℝ)
          ≤ ∑ e' ∈ Finset.Ico 1 t, (dE : ℝ) * ((2 * t + 5) * Real.log (t * F)) := by
            apply Finset.sum_le_sum
            intro e' he'
            rw [Finset.mem_Ico] at he'
            have hb := (hP E Ω F hFpos hemb ld e' he'.1).2
              (S.filter (fun l : Nat.Primes => ¬ (l : ℕ) ∣ dE)) (by
                intro l hl
                rw [Finset.mem_filter] at hl
                exact ⟨hS2 l hl.1, hl.2⟩)
            calc _ ≤ (dE : ℝ) * Real.log (bnd F (e' + 1)) := hb
              _ ≤ _ := mul_le_mul_of_nonneg_left
                  (log_bnd_le_mul_log F t e' hFpos ht (by omega)) hd0
        _ = ((t - 1 : ℕ) : ℝ) * ((dE : ℝ) * ((2 * t + 5) * Real.log (t * F))) := by
            rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        _ ≤ 3 * dE * t ^ 2 * Real.log (t * F) := by
            rw [Nat.cast_sub (by omega : 1 ≤ t)]
            push_cast
            have key : ((t : ℝ) - 1) * (2 * t + 5) ≤ 3 * t ^ 2 := by nlinarith
            have := mul_le_mul_of_nonneg_right key (mul_nonneg hd0 hlogtF)
            nlinarith
    have hB : ∑ l ∈ S.filter (fun l : Nat.Primes => ¬ ¬ (l : ℕ) ∣ dE),
        Real.log ((l : ℕ) : ℝ) * ∑ e' ∈ Finset.Ico 1 t, ((minusLen (ld (l : ℕ)) e').toNat : ℝ) ≤
        C * ∑ l ∈ M.deg.primeFactors.erase 2,
          (l : ℝ) * (dE : ℝ) ^ 2 * (t : ℝ) ^ 2 * Real.log (t * l * F) ^ 2 := by
      have hterm : ∀ l ∈ S.filter (fun l : Nat.Primes => ¬ ¬ (l : ℕ) ∣ dE),
          Real.log ((l : ℕ) : ℝ) * ∑ e' ∈ Finset.Ico 1 t, ((minusLen (ld (l : ℕ)) e').toNat : ℝ) ≤
          C * (((l : ℕ) : ℝ) * (dE : ℝ) ^ 2 * (t : ℝ) ^ 2 *
            Real.log (t * ((l : ℕ) : ℝ) * F) ^ 2) := by
        intro l hl
        rw [Finset.mem_filter, not_not] at hl
        haveI : Fact (l : ℕ).Prime := ⟨l.2⟩
        have hp2 := hS2 l hl.1
        have hpc : Procyc E Ω (l : ℕ) := by
          unfold Procyc
          exact Or.inl hp2
        have hl1 : (1 : ℝ) ≤ ((l : ℕ) : ℝ) := by exact_mod_cast l.2.one_le
        have hK : 0 ≤ C * ((l : ℕ) : ℝ) * (dE : ℝ) ^ 2 := by positivity
        rw [Finset.mul_sum]
        calc ∑ e' ∈ Finset.Ico 1 t, Real.log ((l : ℕ) : ℝ) * ((minusLen (ld (l : ℕ)) e').toNat : ℝ)
            ≤ ∑ e' ∈ Finset.Ico 1 t, C * ((l : ℕ) : ℝ) * (dE : ℝ) ^ 2 * (t : ℝ) *
                Real.log (t * ((l : ℕ) : ℝ) * F) ^ 2 := by
              apply Finset.sum_le_sum
              intro e' he'
              rw [Finset.mem_Ico] at he'
              have h1 := (hSt E Ω F hFpos hemb (l : ℕ) (ld (l : ℕ)) hpc e' he'.1).2
              have he1 : (1 : ℝ) ≤ e' := by exact_mod_cast he'.1
              have het : (e' : ℝ) + 1 ≤ t := by exact_mod_cast he'.2
              have hge1 : (1 : ℝ) ≤ e' * ((l : ℕ) : ℝ) * F :=
                one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le he1 hl1) hF1
              have hlogle : Real.log (e' * ((l : ℕ) : ℝ) * F) ≤ Real.log (t * ((l : ℕ) : ℝ) * F) := by
                apply Real.log_le_log (by linarith)
                have : (e' : ℝ) ≤ t := by linarith
                gcongr
              have hlog0' : 0 ≤ Real.log (e' * ((l : ℕ) : ℝ) * F) := Real.log_nonneg hge1
              have hsq : Real.log (e' * ((l : ℕ) : ℝ) * F) ^ 2 ≤ Real.log (t * ((l : ℕ) : ℝ) * F) ^ 2 :=
                pow_le_pow_left₀ hlog0' hlogle 2
              have hm := mul_le_mul het hsq (sq_nonneg _) (by linarith)
              calc Real.log ((l : ℕ) : ℝ) * ((minusLen (ld (l : ℕ)) e').toNat : ℝ)
                  = ((minusLen (ld (l : ℕ)) e').toNat : ℝ) * Real.log ((l : ℕ) : ℝ) := mul_comm _ _
                _ ≤ _ := h1
                _ = (C * ((l : ℕ) : ℝ) * (dE : ℝ) ^ 2) *
                      (((e' : ℝ) + 1) * Real.log (e' * ((l : ℕ) : ℝ) * F) ^ 2) := by ring
                _ ≤ (C * ((l : ℕ) : ℝ) * (dE : ℝ) ^ 2) *
                      ((t : ℝ) * Real.log (t * ((l : ℕ) : ℝ) * F) ^ 2) :=
                    mul_le_mul_of_nonneg_left hm hK
                _ = _ := by ring
          _ = ((t - 1 : ℕ) : ℝ) * (C * ((l : ℕ) : ℝ) * (dE : ℝ) ^ 2 * (t : ℝ) *
                Real.log (t * ((l : ℕ) : ℝ) * F) ^ 2) := by
              rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
          _ ≤ ∑ e' ∈ Finset.Ico 1 t, 0 + C * (((l : ℕ) : ℝ) * (dE : ℝ) ^ 2 * (t : ℝ) ^ 2 *
                Real.log (t * ((l : ℕ) : ℝ) * F) ^ 2) := by
              rw [Finset.sum_const_zero, zero_add, Nat.cast_sub (by omega : 1 ≤ t)]
              push_cast
              have hK2 : 0 ≤ C * ((l : ℕ) : ℝ) * (dE : ℝ) ^ 2 * (t : ℝ) *
                  Real.log (t * ((l : ℕ) : ℝ) * F) ^ 2 := by positivity
              nlinarith
          _ = _ := by rw [Finset.sum_const_zero, zero_add]
      calc _ ≤ ∑ l ∈ S.filter (fun l : Nat.Primes => ¬ ¬ (l : ℕ) ∣ dE),
            C * (((l : ℕ) : ℝ) * (dE : ℝ) ^ 2 * (t : ℝ) ^ 2 * Real.log (t * ((l : ℕ) : ℝ) * F) ^ 2) :=
            Finset.sum_le_sum hterm
        _ = C * ∑ m ∈ (S.filter (fun l : Nat.Primes => ¬ ¬ (l : ℕ) ∣ dE)).image
              (fun p : Nat.Primes => (p : ℕ)),
              ((m : ℝ) * (dE : ℝ) ^ 2 * (t : ℝ) ^ 2 * Real.log (t * (m : ℝ) * F) ^ 2) := by
            rw [← Finset.mul_sum]
            congr 1
            exact (Finset.sum_image
              (f := fun m : ℕ => (m : ℝ) * (dE : ℝ) ^ 2 * (t : ℝ) ^ 2 * Real.log (t * (m : ℝ) * F) ^ 2)
              (s := S.filter (fun l : Nat.Primes => ¬ ¬ (l : ℕ) ∣ dE))
              (g := fun p : Nat.Primes => (p : ℕ))
              (fun a _ b _ h => Nat.Primes.coe_nat_injective h)).symm
        _ ≤ _ := by
            apply mul_le_mul_of_nonneg_left _ hC0
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro m hm
              obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
              rw [Finset.mem_filter, not_not] at hp
              rw [Finset.mem_erase, Nat.mem_primeFactors]
              exact ⟨hS2 p hp.1, p.2, hdvd p p.2 (hS2 p hp.1) hp.2, hdeg⟩
            · intro m _ _
              positivity
    exact add_le_add hA hB

theorem stickBound : ∃ C : ℝ, 0 ≤ C ∧ StickBound C := stick_of killPow lenPow gen

theorem primeBound_of (h : PsiBound) : PrimeBound := prime_of actEx actFacts prodVal atPrime h

theorem thmBcFree_of (h : PsiBound) : ThmBcFree := thmBc_of deg stickBound (primeBound_of h)

end UpperTheory.V.Odd
