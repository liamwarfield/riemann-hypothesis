module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.UnramifiedCocycleIsCoboundaryOfBernoulliUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Counts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwAbsRam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Control
public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.LiftEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PrimRam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PullOnto
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PlacesOfRationals.PlacesQ

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.TorsClass
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KwlOnto
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.ML UpperTheory.V.X

private theorem kwl_fix {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (g : G ℚ Ω) :
    g ∈ fixMu ℚ Ω N ↔ Chr.cls ℚ Ω N g = 1 := by
  have key : ∀ x : Ω, x ^ N = 1 → x ^ ((1 : (ZMod N)ˣ) : ZMod N).val = x := fun x hx => by
    rw [Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hx, pow_one]
  refine ⟨fun h => (Chr.clsFacts ℚ Ω N).2.2.1 g 1 fun x hx => (h x hx).trans (key x hx).symm, fun h x hx => ?_⟩
  rw [Chr.cls_spec N g x hx, h, key x hx]

private theorem kwl_onto {Ω : Type} [Field Ω] [inst : Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] :
    Function.Surjective (Chr.cls ℚ Ω N) := by
  have hch : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  exact (Chr.clsOnto Ω N).1

private theorem kwl_pow (l : ℕ) (hl : l.Prime) (h2 : l ≠ 2) (n : ℕ) (hd : l ^ 2 ∣ l ^ (n + 2)) (u : (ZMod (l ^ (n + 2)))ˣ)
    (hu : ZMod.unitsMap hd u = 1) : ∃ v, v ^ l = u := by
  haveI : NeZero (l ^ (n + 2)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : NeZero (l ^ 2) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI := ZMod.isCyclic_units_of_prime_pow l hl h2 (n + 2)
  have hl0 : 0 < l - 1 := Nat.sub_pos_of_lt hl.one_lt
  have hcard : ∀ e : ℕ, 0 < e → Nat.card (ZMod (l ^ e))ˣ = l ^ (e - 1) * (l - 1) := by
    intro e he
    haveI : NeZero (l ^ e) := ⟨pow_ne_zero _ hl.ne_zero⟩
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow hl he]
  have hG := hcard (n + 2) (by omega)
  have hH := hcard 2 (by omega)
  have e1 : n + 2 - 1 = n + 1 := by omega
  rw [e1] at hG
  simp only [show (2 - 1 : ℕ) = 1 from rfl, pow_one] at hH
  have hrange : (ZMod.unitsMap hd).range = ⊤ :=
    MonoidHom.range_eq_top.2 (ZMod.unitsMap_surjective hd)
  have hker : Nat.card (ZMod.unitsMap hd).ker = l ^ n := by
    have h1 := Subgroup.card_mul_index (ZMod.unitsMap hd).ker
    rw [Subgroup.index_ker, hrange, Subgroup.card_top, hH, hG] at h1
    have hpos : 0 < l * (l - 1) := Nat.mul_pos hl.pos hl0
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1]
    ring
  have hu1 : u ^ (l ^ n) = 1 := by
    have := pow_card_eq_one' (G := (ZMod.unitsMap hd).ker) (x := ⟨u, hu⟩)
    rw [hker] at this
    exact congrArg Subtype.val this
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := (ZMod (l ^ (n + 2)))ˣ)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hγ u)
  have hord : orderOf γ = l ^ (n + 1) * (l - 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, hG]
  rw [← zpow_natCast, ← zpow_mul, ← orderOf_dvd_iff_zpow_eq_one, hord] at hu1
  have hlk : (l : ℤ) ∣ k := by
    have h3 : ((l ^ (n + 1) : ℕ) : ℤ) ∣ k * ((l ^ n : ℕ) : ℤ) :=
      (Int.natCast_dvd_natCast.2 (Dvd.intro _ rfl)).trans hu1
    push_cast at h3
    rw [pow_succ, mul_comm ((l : ℤ) ^ n)] at h3
    exact (mul_dvd_mul_iff_right (pow_ne_zero _ (by exact_mod_cast hl.ne_zero))).1 h3
  obtain ⟨j, rfl⟩ := hlk
  refine ⟨γ ^ j, ?_⟩
  rw [← zpow_natCast, ← zpow_mul, mul_comm]

theorem UpperTheory.V.X.kwl :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ φ ∈ UnrHom ℚ Ω l, ∀ g ∈ fixMu ℚ Ω (l ^ 2), φ g = 0 := by
  intro Ω _ _ _ l hlf h2 φ hφ g hg
  have hl : l.Prime := hlf.out
  obtain ⟨hlc, hadd, hunr⟩ := hφ
  let ψ : G ℚ Ω →* Multiplicative (ZMod l) :=
    MonoidHom.mk' (fun x => Multiplicative.ofAdd (φ x)) (fun a b => by
      simp only [hadd, ofAdd_add])
  have hψ : ∀ x, ψ x = Multiplicative.ofAdd (φ x) := fun x => rfl
  have hkerset : ((ψ.ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) = {x | φ x = 0} := by
    ext x
    simp [MonoidHom.mem_ker, hψ]
  have hVo : IsOpen ((ψ.ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := by
    rw [hkerset]
    exact hlc.isOpen_fiber 0
  have hVc : commutator (G ℚ Ω) ≤ ψ.ker := Abelianization.commutator_subset_ker ψ
  have hI : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → Ine (F := ℚ) A ≤ ψ.ker := by
    intro A hA x hx
    rw [MonoidHom.mem_ker, hψ, hunr A hA x hx]
    rfl
  obtain ⟨n, hn⟩ := UpperTheory.V.CF.kwAbsRam Ω ψ.ker hVo hVc l hl.pos hI
  haveI : NeZero (l ^ (n + 2)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : NeZero (l ^ 2) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hfix : fixMu ℚ Ω (l ^ (n + 2)) ≤ ψ.ker := by
    intro x hx
    apply hn x
    exact fixMu_le ℚ Ω (pow_dvd_pow l (by omega)) hx
  have hd : l ^ 2 ∣ l ^ (n + 2) := pow_dvd_pow l (by omega)
  have hc2 : ZMod.unitsMap hd (Chr.cls ℚ Ω (l ^ (n + 2)) g) = 1 := by
    have := DFunLike.congr_fun ((Chr.clsFacts ℚ Ω (l ^ (n + 2))).2.1 (l ^ 2) hd) g
    rw [MonoidHom.comp_apply] at this
    rw [this]
    exact (kwl_fix (l ^ 2) g).1 hg
  obtain ⟨v, hv⟩ := kwl_pow l hl h2 n hd _ hc2
  obtain ⟨h, rfl⟩ := kwl_onto (Ω := Ω) (l ^ (n + 2)) v
  have hk : g * (h ^ l)⁻¹ ∈ fixMu ℚ Ω (l ^ (n + 2)) := by
    rw [kwl_fix, map_mul, map_inv, map_pow, hv, mul_inv_cancel]
  have h0 := hfix hk
  rw [MonoidHom.mem_ker] at h0
  have hg' : g = g * (h ^ l)⁻¹ * h ^ l := by group
  have : ψ g = 1 := by
    rw [hg', map_mul, h0, one_mul, map_pow, hψ, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rfl
  rw [hψ] at this
  exact this
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.ML UpperTheory.V.X

private theorem sep_tors {M : Type} [AddCommGroup M] (l : ℕ) [Fact l.Prime] (x : AddSubgroup.torsionBy M l)
    (h : ∀ φ : AddSubgroup.torsionBy M l →+ ZMod l, φ x = 0) : x = 0 := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  letI : Module (ZMod l) (AddSubgroup.torsionBy M l) := AddSubgroup.torsionBy.zmodModule
  exact (Module.forall_dual_apply_eq_zero_iff (ZMod l) x).1 fun φ => h φ.toAddMonoidHom

private theorem hom_kill (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (hl : l ≠ 2)
    {M : Type} [AddCommGroup M] (f : G ℚ Ω → M) (h1 : IsLocallyConstant f) (h2 : ∀ a b, f (a * b) = f a + f b)
    (h3 : ∀ g, l • f g = 0)
    (h4 : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := ℚ) A, f g = 0) :
    ∀ g ∈ cycU l (⊤ : Subgroup (G ℚ Ω)), f g = 0 := by
  intro g hg
  have hmu : g ∈ fixMu ℚ Ω (l ^ 2) := by
    rw [(fixLev ℚ Ω l 1 2).1]
    exact cycU_le_levU l ⊤ 2 hg
  have hx : f g ∈ AddSubgroup.torsionBy M l := AddSubgroup.torsionBy.nsmul_iff.2 (h3 g)
  have key : (⟨f g, hx⟩ : AddSubgroup.torsionBy M l) = 0 := by
    apply sep_tors l
    intro φ
    let ι : G ℚ Ω → AddSubgroup.torsionBy M l := fun a => ⟨f a, AddSubgroup.torsionBy.nsmul_iff.2 (h3 a)⟩
    have hι : IsLocallyConstant ι := by
      intro s
      have hpre : ι ⁻¹' s = f ⁻¹' (Subtype.val '' s) := by
        ext a
        simp only [ι, Set.mem_preimage, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
        exact ⟨fun h => ⟨AddSubgroup.torsionBy.nsmul_iff.2 (h3 a), h⟩, fun ⟨_, h⟩ => h⟩
      rw [hpre]
      exact h1 _
    have hψ : (fun a => φ (ι a)) ∈ UnrHom ℚ Ω l := by
      refine ⟨hι.comp φ, ?_, ?_⟩
      · intro a b
        show φ (ι (a * b)) = φ (ι a) + φ (ι b)
        rw [← map_add (f := _)]
        congr 1
        exact Subtype.ext (h2 a b)
      · intro A hA g' hg'
        show φ (ι g') = 0
        have h0 : ι g' = 0 := Subtype.ext (h4 A hA g' hg')
        rw [h0, map_zero]
    exact kwl Ω l hl _ hψ g hmu
  simpa using congrArg Subtype.val key

private theorem pow_cong (l : ℕ) [Fact l.Prime] (u : ℤ_[l]ˣ) (e : ℕ) (he : l - 1 ∣ e) :
    (l : ℤ_[l]) ∣ ((u ^ (-(e : ℤ)) : ℤ_[l]ˣ) : ℤ_[l]) - 1 := by
  have hker : ∀ x : ℤ_[l], PadicInt.toZMod x = 0 → (l : ℤ_[l]) ∣ x := by
    intro x hx
    have hmem : x ∈ RingHom.ker (PadicInt.toZMod : ℤ_[l] →+* ZMod l) := hx
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hmem
    exact hmem
  apply hker
  have hw : (Units.map (PadicInt.toZMod : ℤ_[l] →+* ZMod l).toMonoidHom u) ^ (-(e : ℤ)) = 1 := by
    obtain ⟨k, rfl⟩ := he
    rw [zpow_neg, zpow_natCast, pow_mul, ZMod.units_pow_card_sub_one_eq_one, one_pow, inv_one]
  have hmap : PadicInt.toZMod ((u ^ (-(e : ℤ)) : ℤ_[l]ˣ) : ℤ_[l]) =
      (((Units.map (PadicInt.toZMod : ℤ_[l] →+* ZMod l).toMonoidHom u) ^ (-(e : ℤ)) : (ZMod l)ˣ) : ZMod l) := by
    rw [← map_zpow]
    rfl
  rw [map_sub, hmap, hw, Units.val_one, map_one, sub_self]

private theorem tors_class {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    [DiscreteTopology M] (ρ : Representation R Γ M) (l : ℕ) (h : ∀ m : M, ∃ n : ℕ, l ^ n • m = 0) (x : H1 ρ) :
    ∃ n : ℕ, (l : R) ^ n • x = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hfin : (Set.range (z : Γ → M)).Finite := (isCompact_range z.2.1).finite_of_discrete
  choose N hN using h
  refine ⟨hfin.toFinset.sup N, ?_⟩
  have hbound : ∀ g, l ^ (hfin.toFinset.sup N) • (z : Γ → M) g = 0 := by
    intro g
    have hle : N ((z : Γ → M) g) ≤ hfin.toFinset.sup N :=
      Finset.le_sup (f := N) (by simp)
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    rw [hk, add_comm, pow_add, mul_smul, hN, smul_zero]
  have hzero : ((l : R) ^ (hfin.toFinset.sup N) • z : Z1 ρ) = 0 := by
    apply Subtype.ext
    funext g
    show ((l : R) ^ (hfin.toFinset.sup N) • (z : Γ → M)) g = 0
    rw [Pi.smul_apply, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    exact hbound g
  rw [← Submodule.Quotient.mk_smul, hzero, Submodule.Quotient.mk_zero]

set_option maxHeartbeats 1000000 in
theorem UpperTheory.V.X.zOne :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O], l ≠ 2 → ∀ e : ℕ, 1 ≤ e → l - 1 ∣ e → Chr.V l e (1 : G ℚ Ω →* Oˣ) = 0 := by
  intro Ω _ _ _ l _ O _ _ _ _ _ hl e he1 he
  classical
  show Module.length O (ShaU (twist₂ l ((1 : G ℚ Ω →* Oˣ)⁻¹ * chiO ℚ Ω l O ^ (-(e : ℤ)))) l ⊤) = 0
  rw [inv_one]
  have act : ∀ (g : G ℚ Ω) (m : QO l O), (twist₂ l (1 * chiO ℚ Ω l O ^ (-(e : ℤ)))) g m =
      algebraMap ℤ_[l] O (((cycZ ℚ Ω l g ^ (-(e : ℤ)) : ℤ_[l]ˣ) : ℤ_[l])) • m := by
    intro g m
    simp [twist₂, scalRep_apply, chiO]
  have hcontm : ∀ m₀ : QO l O, Continuous fun g : G ℚ Ω => (twist₂ l (1 * chiO ℚ Ω l O ^ (-(e : ℤ)))) g m₀ := by
    intro m₀
    have hcontρ : Continuous fun p : G ℚ Ω × QO l O => (twist₂ l (1 * chiO ℚ Ω l O ^ (-(e : ℤ)))) p.1 p.2 :=
      (contTw ℚ Ω l).2.2 O 1 (-(e : ℤ)) (by simp)
    have hpair : Continuous fun g : G ℚ Ω => ((g, m₀) : G ℚ Ω × QO l O) :=
      Continuous.prodMk continuous_id continuous_const
    have h := hcontρ.comp hpair
    exact h
  set ρ : Representation O (G ℚ Ω) (QO l O) := twist₂ l (1 * chiO ℚ Ω l O ^ (-(e : ℤ))) with hρ
  have hl0 : (l : O) ≠ 0 := by
    have hinj := (UpperTheory.V.Base.dvrFacts l O).1
    intro h
    have h' : ((l : ℤ_[l])) = 0 := hinj (by simpa using h)
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h')
  have trivl : ∀ (g : G ℚ Ω) (y : QO l O), l • y = 0 → ρ g y = y := by
    intro g y hy
    obtain ⟨c, hc⟩ := pow_cong l (cycZ ℚ Ω l g) e he
    have hA : algebraMap ℤ_[l] O (((cycZ ℚ Ω l g ^ (-(e : ℤ)) : ℤ_[l]ˣ) : ℤ_[l])) =
        1 + (l : O) * algebraMap ℤ_[l] O c := by
      rw [← map_natCast (algebraMap ℤ_[l] O), ← map_mul, ← hc, ← map_one (algebraMap ℤ_[l] O), ← map_add (f := _)]
      congr 1
      ring
    rw [act, hA, add_smul, one_smul, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul, hy, smul_zero, add_zero]
  have trivk : ∀ g ∈ (cycZ ℚ Ω l).ker, ∀ m : QO l O, ρ g m = m := by
    intro g hg m
    rw [act, (MonoidHom.mem_ker).1 hg]
    simp
  have hctrl := (control ℚ Ω l O (⊤ : Subgroup (G ℚ Ω)) (by simp) (Or.inl hl) 1 (-(e : ℤ)) (by simp)
    (by omega)).1
  have hzero : ∀ x : ShaU ρ l ⊤, (l : O) • x = 0 → x = 0 := by
    intro x hx
    apply hctrl
    rw [map_zero]
    obtain ⟨y, hyS⟩ := x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hx' : (l : O) • (Submodule.Quotient.mk z : H1U ρ ⊤) = 0 := by
      simpa only [Submodule.coe_smul, Submodule.coe_zero] using congrArg Subtype.val hx
    obtain ⟨m, hm⟩ := (mk_eq_mk ρ ⊤ ((l : O) • z) 0).1
      (by rw [Submodule.Quotient.mk_smul, Submodule.Quotient.mk_zero]; exact hx')
    simp only [Submodule.coe_smul, Submodule.coe_zero, Pi.smul_apply, Pi.zero_apply, sub_zero] at hm
    obtain ⟨m', hm'⟩ := (qoFacts l O).2.2.1 (l : O) hl0 m
    let z' : G ℚ Ω → QO l O := fun g => (z : (⊤ : Subgroup (G ℚ Ω)) → QO l O) ⟨g, trivial⟩ - (ρ g m' - m')
    have htors : ∀ g, l • z' g = 0 := by
      intro g
      rw [← Nat.cast_smul_eq_nsmul O]
      show (l : O) • ((z : (⊤ : Subgroup (G ℚ Ω)) → QO l O) ⟨g, trivial⟩ - (ρ g m' - m')) = 0
      rw [smul_sub, smul_sub, ← map_smul, hm', hm ⟨g, trivial⟩]
      exact sub_self _
    have hcz : ∀ a b : G ℚ Ω, (z : (⊤ : Subgroup (G ℚ Ω)) → QO l O) ⟨a * b, trivial⟩ =
        (z : (⊤ : Subgroup (G ℚ Ω)) → QO l O) ⟨a, trivial⟩ + ρ a ((z : (⊤ : Subgroup (G ℚ Ω)) → QO l O) ⟨b, trivial⟩) :=
      fun a b => z.2.2 ⟨a, trivial⟩ ⟨b, trivial⟩
    have hadd : ∀ a b, z' (a * b) = z' a + z' b := by
      intro a b
      have hc : z' (a * b) = z' a + ρ a (z' b) := by
        show (z : (⊤ : Subgroup (G ℚ Ω)) → QO l O) ⟨a * b, trivial⟩ - (ρ (a * b) m' - m') =
          (z : (⊤ : Subgroup (G ℚ Ω)) → QO l O) ⟨a, trivial⟩ - (ρ a m' - m') +
            ρ a ((z : (⊤ : Subgroup (G ℚ Ω)) → QO l O) ⟨b, trivial⟩ - (ρ b m' - m'))
        rw [hcz, map_mul, Module.End.mul_apply, map_sub, map_sub]
        abel
      rw [hc, trivl a _ (htors b)]
    have hlc : IsLocallyConstant z' := by
      rw [IsLocallyConstant.iff_continuous]
      have h1 : Continuous fun g : G ℚ Ω => (z : (⊤ : Subgroup (G ℚ Ω)) → QO l O) ⟨g, trivial⟩ :=
        z.2.1.comp (continuous_id.subtype_mk fun _ => trivial)
      exact h1.sub ((hcontm m').sub continuous_const)
    have hunr : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := ℚ) A, z' g = 0 := by
      intro A hA g hg
      obtain ⟨m₁, hm₁⟩ := (mk_mem_locSel.1 hyS) (Ine (F := ℚ) A) (Or.inr ⟨A, rfl⟩)
      have hgk : g ∈ (cycZ ℚ Ω l).ker := (places ℚ Ω l A).2.2.2 hA hg
      have hzg : (z : (⊤ : Subgroup (G ℚ Ω)) → QO l O) ⟨g, trivial⟩ = ρ g m₁ - m₁ := hm₁ ⟨g, trivial⟩ hg
      show (z : (⊤ : Subgroup (G ℚ Ω)) → QO l O) ⟨g, trivial⟩ - (ρ g m' - m') = 0
      rw [hzg, trivk g hgk m₁, trivk g hgk m', sub_self, sub_self, sub_self]
    have hk := hom_kill Ω l hl z' hlc hadd htors hunr
    apply Subtype.ext
    rw [selRes, LinearMap.restrict_apply]
    show resU ρ _ (Submodule.Quotient.mk z) = 0
    rw [resU_mk_eq_zero]
    refine ⟨m', fun u => ?_⟩
    have hu := hk u u.2
    exact sub_eq_zero.1 hu
  haveI : CompactSpace (⊤ : Subgroup (G ℚ Ω)) := isCompact_iff_compactSpace.mp (by simpa using isCompact_univ)
  have hgen : ∀ n : ℕ, ∀ x : ShaU ρ l ⊤, (l : O) ^ n • x = 0 → x = 0 := by
    intro n
    induction n with
    | zero =>
      intro x hx
      simpa using hx
    | succ k ih =>
      intro x hx
      apply ih
      apply hzero
      rw [smul_smul, ← pow_succ']
      exact hx
  have hall : ∀ x : ShaU ρ l ⊤, x = 0 := by
    intro x
    obtain ⟨n, hn⟩ := tors_class (ρ.comp (⊤ : Subgroup (G ℚ Ω)).subtype) l (qoFacts l O).2.1 (x : H1U ρ ⊤)
    exact hgen n x (Subtype.ext (by simpa only [Submodule.coe_smul, Submodule.coe_zero] using hn))
  rw [Module.length_eq_zero_iff]
  exact ⟨fun a b => by rw [hall a, hall b]⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.ZqField
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HQuad
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.ML UpperTheory.V.X

theorem UpperTheory.V.X.hQuad :
    ∀ (K : Type) [Field K] [NumberField K] (l : ℕ), l.Prime → 5 ≤ l → Module.finrank ℚ K = 2 → discr K = l → classNumber K < l := by
  intro K _ _ l hl h5 hn hd
  have h := GlobalTheory.classNumber_le_sqrt_discr_mul_pow_pred K
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  have habs : |((discr K : ℤ) : ℝ)| = (l : ℝ) := by
    rw [hd]
    push_cast
    exact abs_of_pos hl0
  rw [hn, habs, show (2 : ℕ) - 1 = 1 from rfl, pow_one] at h
  have hx0 : 0 < Real.sqrt (l : ℝ) := Real.sqrt_pos.mpr hl0
  have h5r : (5 : ℝ) ≤ l := by exact_mod_cast h5
  have hx1 : Real.sqrt (l : ℝ) ≠ 1 := by
    intro h1
    have hs := Real.sq_sqrt hl0.le
    rw [h1] at hs
    linarith
  have hlog := Real.log_lt_sub_one_of_pos hx0 hx1
  have hsq : Real.sqrt (l : ℝ) * Real.sqrt (l : ℝ) = l := Real.mul_self_sqrt hl0.le
  have hlt : (classNumber K : ℝ) < l := by
    calc (classNumber K : ℝ) ≤ Real.sqrt (l : ℝ) * (1 + Real.log (Real.sqrt (l : ℝ))) := h
      _ < Real.sqrt (l : ℝ) * Real.sqrt (l : ℝ) := by
        apply mul_lt_mul_of_pos_left _ hx0
        linarith
      _ = l := hsq
  exact_mod_cast hlt
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.ML UpperTheory.V.X

private theorem zq_unit {l : ℕ} [Fact l.Prime] (x : ℤ_[l]) (h : PadicInt.toZMod x ≠ 0) : IsUnit x := by
  by_contra hx
  apply h
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod]
  exact hx

private theorem zq_dvd {l : ℕ} [Fact l.Prime] (x : ℤ_[l]) (h : PadicInt.toZMod x = 0) : (l : ℤ_[l]) ∣ x := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h
  exact h

private theorem zq_cast {l : ℕ} [Fact l.Prime] (x : ℤ_[l]) :
    (((PadicInt.toZModPow 1 x).val : ℕ) : ZMod l) = PadicInt.toZMod x := by
  have h : PadicInt.toZModPow 1 (x - (((PadicInt.toZModPow 1 x).val : ℕ) : ℤ_[l])) = 0 := by
    rw [map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, pow_one, ← PadicInt.maximalIdeal_eq_span_p,
    ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_natCast, sub_eq_zero] at h
  exact h.symm

private theorem zq_four {l e : ℕ} (hl : 5 ≤ l) (he : Even e) (h1 : l - 1 ∣ 2 * e) (h2 : ¬ l - 1 ∣ e) (ho : l % 2 = 1) :
    l % 4 = 1 ∧ l / 2 ∣ e := by
  obtain ⟨n, rfl⟩ : ∃ n, l = 2 * n + 1 := ⟨l / 2, by omega⟩
  have e1 : 2 * n + 1 - 1 = 2 * n := by omega
  have e2 : (2 * n + 1) / 2 = n := by omega
  rw [e1] at h1 h2
  rw [e2]
  obtain ⟨k, rfl⟩ : n ∣ e := Nat.dvd_of_mul_dvd_mul_left two_pos h1
  refine ⟨?_, dvd_mul_right _ _⟩
  rcases Nat.even_mul.1 he with ⟨j, hj⟩ | ⟨j, hj⟩
  · omega
  · exact absurd ⟨j, by rw [hj]; ring⟩ h2

private theorem zq_gen {l e : ℕ} [Fact l.Prime] (h2 : ¬ l - 1 ∣ e) :
    ∃ u : ℤ_[l]ˣ, PadicInt.toZMod (u : ℤ_[l]) ^ e ≠ 1 := by
  obtain ⟨b, hb⟩ := IsCyclic.exists_generator (α := (ZMod l)ˣ)
  have ho : orderOf b = l - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hb, Nat.card_eq_fintype_card, ZMod.card_units]
  have h0 : PadicInt.toZMod (((b : ZMod l).val : ℕ) : ℤ_[l]) = b := by
    rw [map_natCast, ZMod.natCast_zmod_val]
  obtain ⟨u, hu⟩ := zq_unit _ (h0 ▸ b.ne_zero)
  refine ⟨u, fun h => h2 ?_⟩
  rw [hu, h0] at h
  rw [← ho, orderOf_dvd_iff_pow_eq_one]
  exact Units.ext (by simpa using h)

private theorem zq_root (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hp : Fact l.Prime]
    (h4 : l % 4 = 1) : ∃ s : Ω, s ^ 2 = (l : Ω) ∧ ∀ g : G ℚ Ω, (g s = s ∨ g s = -s) ∧
      (g s = s → PadicInt.toZMod (cycZ ℚ Ω l g : ℤ_[l]) ^ (l / 2) = 1) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero l := ⟨hp.out.ne_zero⟩
  haveI hE : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  obtain ⟨⟨s, hs⟩, h⟩ := CF.gauss Ω l ζ (by omega) hζ
  have hs2 : s ^ 2 = (l : Ω) := by
    rw [hs, CF.pStar, Even.neg_one_pow ⟨l / 4, by omega⟩]
    simp
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hp.out.ne_zero (by exact_mod_cast (hs2.symm.trans (by simp) : (l : Ω) = 0))
  refine ⟨s, hs2, fun g => ⟨?_, fun hg => ?_⟩⟩
  · refine sq_eq_sq_iff_eq_or_eq_neg.1 ?_
    rw [← map_pow, hs2, map_natCast]
  · have h1 := cyclotomicCharacter.spec l (n := 1) g.toRingEquiv ζ (by rw [pow_one, hζ.pow_eq_one])
    have h2 := (h s hs).2 g.toRingEquiv.toRingHom _ h1
    have h3 : s = _ := hg.symm.trans h2
    have h5 : legendreSym l ((PadicInt.toZModPow 1 (cycZ ℚ Ω l g : ℤ_[l])).val : ℕ) = 1 := by
      have : (1 : Ω) * s = _ := (one_mul s).trans h3
      exact_mod_cast (mul_right_cancel₀ hs0 this).symm
    have h6 := legendreSym.eq_pow l (((PadicInt.toZModPow 1 (cycZ ℚ Ω l g : ℤ_[l])).val : ℕ) : ℤ)
    rw [h5, Int.cast_natCast, zq_cast, Int.cast_one] at h6
    exact h6.symm

private theorem zq_hom (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K]
    [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ) (hp : l.Prime) (hl : 5 ≤ l) (hK : Module.finrank ℚ K = 2) (hd : discr K = l)
    (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (h2 : ∀ m : M, 2 • m = 0 → m = 0)
    (φ : galOf ℚ K Ω → M) (hφ : φ ∈ Kum.XDual l (galOf ℚ K Ω) R M) (u : galOf ℚ K Ω) (hu : l • φ u = 0) : φ u = 0 := by
  rw [← Kum.pullOnto ℚ Ω K _ le_rfl l R M hp.ne_zero le_rfl (Or.inr h2)] at hφ
  obtain ⟨θ, hθ, rfl⟩ := hφ
  rw [Kum.clPull_apply] at hu ⊢
  generalize Kum.artCl K Ω (Kum.toGal K le_rfl u) = c at hu ⊢
  let θ' : ClassGroup (𝓞 K) →* Multiplicative M := MonoidHom.mk' (fun c => Multiplicative.ofAdd (θ c)) fun a b => by
    rw [hθ.1, ofAdd_add]
  have h1 : classNumber K • θ c = 0 := by
    have : θ' (c ^ classNumber K) = 1 := by rw [classNumber, pow_card_eq_one, map_one]
    rw [map_pow] at this
    exact this
  have hc : l.Coprime (classNumber K) :=
    (Nat.coprime_of_lt_prime (classNumber_pos K).ne' (hQuad K l hp hl hK hd) hp)
  have := Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hu) (addOrderOf_dvd_of_nsmul_eq_zero h1)
  rw [hc.gcd_eq_one, Nat.dvd_one, AddMonoid.addOrderOf_eq_one_iff] at this
  exact this

open IntermediateField in
private theorem zq_field (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) (hp : l.Prime) (h4 : l % 4 = 1)
    (s : Ω) (hs : s ^ 2 = (l : Ω)) (δ : G ℚ Ω) (hδ : δ s ≠ s) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra K Ω) (_ : IsAlgClosure K Ω),
      Module.finrank ℚ K = 2 ∧ discr K = l ∧ ∀ g : G ℚ Ω, g ∈ galOf ℚ K Ω ↔ g s = s := by
  have hi : IsIntegral ℚ s := Algebra.IsIntegral.isIntegral s
  haveI : FiniteDimensional ℚ ℚ⟮s⟯ := adjoin.finiteDimensional hi
  haveI : NumberField ℚ⟮s⟯ := NumberField.of_module_finite ℚ _
  refine ⟨ℚ⟮s⟯, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_, fun g => ⟨fun h => ?_, fun h x => ?_⟩⟩
  · rw [adjoin.finrank hi]
    refine le_antisymm ?_ ((minpoly.two_le_natDegree_iff hi).2 ?_)
    · have := minpoly.min ℚ s (Polynomial.monic_X_pow_sub_C (l : ℚ) two_ne_zero) (by simp [hs])
      rw [Polynomial.degree_X_pow_sub_C two_pos] at this
      exact Polynomial.natDegree_le_of_degree_le this
    · rintro ⟨q, rfl⟩
      exact hδ (δ.commutes q)
  · refine Formalism.HF.quadDiscr _ l (AdjoinSimple.gen ℚ s) (Subtype.ext (by simpa using hs)) ?_
      (Int.squarefree_natCast.2 hp.squarefree) (by omega)
    exact lift_injective _ ((lift_adjoin_simple ℚ ℚ⟮s⟯ (AdjoinSimple.gen ℚ s)).trans (lift_top ℚ ℚ⟮s⟯).symm)
  · exact h (AdjoinSimple.gen ℚ s)
  · have : ℚ⟮s⟯ ≤ fixedField (Subgroup.zpowers g) := by
      rw [adjoin_simple_le_iff, mem_fixedField_iff]
      intro f hf
      exact (Subgroup.zpowers_le.2 (show g ∈ MulAction.stabilizer (G ℚ Ω) s from h)) hf
    exact (mem_fixedField_iff _ _).1 (this x.2) g (Subgroup.mem_zpowers g)

private theorem zq_main (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hp : Fact l.Prime] (O : Type) [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (hl : 5 ≤ l) (e : ℕ) (he : Even e)
    (h1 : l - 1 ∣ 2 * e) (h2 : ¬ l - 1 ∣ e) : Chr.V l e (1 : G ℚ Ω →* Oˣ) = 0 := by
  obtain ⟨h4, hdv⟩ := zq_four hl he h1 h2 (hp.out.eq_two_or_odd.resolve_left (by omega))
  obtain ⟨u, hu⟩ := zq_gen h2
  obtain ⟨s, hs, hG⟩ := zq_root Ω l h4
  obtain ⟨A₀, hA₀⟩ := (B3.placesQ Ω).1 l hp.out
  obtain ⟨δ, -, hδ⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A₀ hA₀ u
  have hpow : ∀ g : G ℚ Ω, g s = s → PadicInt.toZMod (cycZ ℚ Ω l g : ℤ_[l]) ^ e = 1 := fun g hg => by
    obtain ⟨k, rfl⟩ := hdv
    rw [pow_mul, (hG g).2 hg, one_pow]
  have hδs : δ s ≠ s := fun h => hu (hδ ▸ hpow δ h)
  obtain ⟨K, _, _, _, _, hK, hd, hU⟩ := zq_field Ω l hp.out h4 s hs δ hδs
  set α : G ℚ Ω →* Oˣ := (1 : G ℚ Ω →* Oˣ)⁻¹ * chiO ℚ Ω l O ^ (-(e : ℤ)) with hα
  have hαg : ∀ g, α g = Units.map (algebraMap ℤ_[l] O).toMonoidHom (cycZ ℚ Ω l g ^ e)⁻¹ := fun g => by
    simp [hα, chiO]
  have hαs : ∀ g, (α g : O) - 1 = algebraMap ℤ_[l] O (-((cycZ ℚ Ω l g ^ e)⁻¹ : ℤ_[l]ˣ) * ((cycZ ℚ Ω l g : ℤ_[l]) ^ e - 1)) :=
    fun g => by
      rw [hαg, ← Units.val_pow_eq_pow_val, mul_sub, neg_mul, Units.inv_mul, map_sub]
      simp [sub_eq_neg_add, add_comm]
  have hun : ∀ g, cycZ ℚ Ω l g = u → IsUnit ((α g : O) - 1) := fun g hg => by
    rw [hαs, hg]
    refine IsUnit.map _ ((Units.isUnit _).neg.mul (zq_unit _ ?_))
    rw [map_sub, map_pow, map_one]
    exact sub_ne_zero.2 hu
  have htr : ∀ g : G ℚ Ω, g s = s → ∀ m : QO l O, l • m = 0 → (α g : O) • m = m := fun g hg m hm => by
    obtain ⟨y, hy⟩ := zq_dvd ((cycZ ℚ Ω l g : ℤ_[l]) ^ e - 1) (by rw [map_sub, map_pow, map_one, hpow g hg, sub_self])
    have : ((α g : O) - 1) • m = 0 := by
      rw [hαs, hy, mul_left_comm, map_mul, map_natCast, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul, hm, smul_zero]
    rwa [sub_smul, one_smul, sub_eq_zero] at this
  have hin : ∀ A : ValuationSubring Ω, ¬ Over A l → ∀ g ∈ Ine (F := ℚ) A, α g = 1 := fun A hA g hg => by
    have : cycZ ℚ Ω l g = 1 := (places ℚ Ω l A).2.2.2 hA hg
    rw [hαg, this, one_pow, inv_one, map_one]
  have htwo : ∀ m : QO l O, 2 • m = 0 → m = 0 := fun m hm => by
    have h : IsUnit ((2 : ℕ) : O) := by
      rw [← map_natCast (algebraMap ℤ_[l] O)]
      refine IsUnit.map _ (zq_unit _ ?_)
      rw [map_natCast, Ne, ZMod.natCast_eq_zero_iff]
      exact fun h => absurd (Nat.le_of_dvd two_pos h) (by omega)
    exact h.smul_eq_zero.1 ((Nat.cast_smul_eq_nsmul _ _ _).trans hm)
  have key : ∀ a : O, ∀ c ∈ ShT (QO l O) α δ l a, l • c = 0 → c = 0 := by
    rintro a c ⟨⟨hlc, hc⟩, hcδ, -, hI, hD⟩ hcl
    have hcl' : ∀ g, l • c g = 0 := fun g => congrFun hcl g
    have hdec : ∀ A : ValuationSubring Ω, Over A l → ∀ g ∈ Dec (F := ℚ) A, g s = s → c g = 0 := fun A hA g hg hgs => by
      obtain ⟨m, -, hm⟩ := hD A hA
      obtain ⟨t, ht, htu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA u
      have hlm : l • m = 0 := by
        refine (hun t htu).smul_eq_zero.1 ?_
        rw [smul_comm, sub_smul, one_smul, ← hm t (Ine_le_Dec (F := ℚ) A ht), hcl']
      rw [hm g hg, htr g hgs m hlm, sub_self]
    have hX : (fun v : galOf ℚ K Ω => c v) ∈ Kum.XDual l (galOf ℚ K Ω) O (QO l O) := by
      refine ⟨hlc.comp_continuous continuous_subtype_val, fun v w => ?_, fun A v hv => ?_, fun A hA v hv => ?_⟩
      · show c (v * w) = c v + c w
        rw [hc, htr v ((hU _).1 v.2) _ (hcl' _)]
      · by_cases hA : Over A l
        · exact hdec A hA v (Ine_le_Dec (F := ℚ) A hv) ((hU _).1 v.2)
        · exact hI A hA v hv
      · exact hdec A hA v hv ((hU _).1 v.2)
    have h0 : ∀ g : G ℚ Ω, g s = s → c g = 0 := fun g hg =>
      zq_hom Ω K l hp.out hl hK hd O (QO l O) htwo _ hX ⟨g, (hU g).2 hg⟩ (hcl' g)
    funext g
    rcases (hG g).1 with hg | hg
    · exact h0 g hg
    · have : (δ⁻¹ * g) s = s := by
        rw [AlgEquiv.mul_apply, hg]
        exact δ.symm_apply_eq.2 ((hG δ).1.resolve_left hδs).symm
      rw [← mul_inv_cancel_left δ g, hc, hcδ, h0 _ this, smul_zero, add_zero, Pi.zero_apply]
  refine nonpos_iff_eq_zero.1 (shaToShT Ω l O α δ (hun δ hδ) l hp.out.ne_zero hin (fun A h h' => absurd h h') 0 fun a ha => ?_)
  have hnu : ¬ IsUnit (l : O) := fun h => by
    haveI := (dvrFacts l O).2.2.1
    rw [← map_natCast (algebraMap ℤ_[l] O), isUnit_map_iff] at h
    exact PadicInt.irreducible_p.not_isUnit h
  obtain ⟨n, hn⟩ : ∃ n : ℕ, a ∣ (l : O) ^ n := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hπ
    refine ⟨n, hn.dvd.trans (pow_dvd_pow_of_dvd ?_ n)⟩
    rw [← Ideal.mem_span_singleton, ← hπ.maximalIdeal_eq]
    exact hnu
  have hall : ∀ n : ℕ, ∀ c ∈ ShT (QO l O) α δ l a, l ^ n • c = 0 → c = 0 := by
    intro n
    induction n with
    | zero => intro c _ h; simpa using h
    | succ n ih =>
      intro c hc h
      exact ih c hc (key a _ (nsmul_mem hc _) (by rw [smul_smul, ← pow_succ', h]))
  have : ShT (QO l O) α δ l a = ⊥ := by
    refine eq_bot_iff.2 fun c hc => hall n c hc (funext fun g => ?_)
    obtain ⟨y, hy⟩ := hn
    rw [Pi.smul_apply, ← Nat.cast_smul_eq_nsmul O, Nat.cast_pow, hy, mul_comm, mul_smul, hc.2.2.1 g, smul_zero, Pi.zero_apply]
  rw [this]
  simp

theorem UpperTheory.V.X.zQuad :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O], 5 ≤ l → ∀ e : ℕ, Even e → l - 1 ∣ 2 * e → ¬ l - 1 ∣ e → Chr.V l e (1 : G ℚ Ω →* Oˣ) = 0 := by
  intro Ω _ inst _ l _ O _ _ _ _ _ hl e he h1 h2
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  exact zq_main Ω l O hl e he h1 h2
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.ML UpperTheory.V.X

theorem UpperTheory.V.X.propZ :
    HV.PropZ := by
  intro Ω _ _ _ l _ c e h5 h2 hev hd
  by_cases h : l - 1 ∣ e
  · exact UpperTheory.V.X.zOne Ω l c.O (by omega) e (by omega) h
  · exact UpperTheory.V.X.zQuad Ω l c.O h5 e hev hd h
