module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionKilledByIdealCharZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftSystemRealStructure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDividingLabelsIffClassZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemberTermsIntegralUnitShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerAffineOpenAbelianPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMoritaLatticeQuotientTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointsAdditiveParametrization

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsTypeTjPIsogeny
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerfectPairingTorsionModule
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perfect_pairing_torsion_module : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → (∃ e : ℕ, c = p ^ e) → ∀ (M : Type) [AddCommGroup M] [Module (𝓞 D.F) M] [Finite M], (∀ x : M, c • x = 0) → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (e : M → M → kˣ), (∀ x x' y, e (x + x') y = e x y * e x' y) → (∀ x y y', e x (y + y') = e x y * e x y') → (∀ (a : 𝓞 D.F) x y, e (a • x) y = e x (D.bar a • y)) → (∀ x y, e x y * e y x = 1) → (∀ x, (∀ y, e x y = 1) → x = 0) → Ideal.absNorm w ^ j ≤ Nat.card {x : M // ∀ a ∈ w, a • x = 0} → ∃ H : Submodule (𝓞 D.F) M, (∀ x ∈ H, ∀ y ∈ H, e x y = 1) ∧ (∀ x, (∀ y ∈ H, e x y = 1) → x ∈ H) ∧ (∀ x ∈ H, (∃ i : ℕ, ∀ a ∈ uIdeal D r ^ i, a • x = 0) → ∀ a ∈ w, a • x = 0) ∧ Nat.card {x : M // x ∈ H ∧ ∀ a ∈ w, a • x = 0} = Ideal.absNorm w ^ j := by
  first | (exact @GlobalTheory.UPel.HT.ES.exists_maximal_isotropic_of_type) | (exact GlobalTheory.UPel.HT.ES.exists_maximal_isotropic_of_type) | (intros; apply GlobalTheory.UPel.HT.ES.exists_maximal_isotropic_of_type  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsTypeTjPIsogeny
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.TjExists

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {S : Scheme.{0}} {N : ℕ}

theorem charZero_of_base (b : Base D R) (hp : IsUnit ((p : ℕ) : R)) {k : Type} [Field k] (s : Sp k ⟶ Sp R) :
    CharZero k := by
  let β : R →+* k := (Spec.preimage s).hom
  haveI := ringChar.charP k
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hl | hl
  · exfalso
    have h0 : ((ringChar k : ℕ) : k) = 0 := CharP.cast_eq_zero k _
    have hu : IsUnit ((ringChar k : ℕ) : R) := by
      by_cases h : ringChar k = p
      · rw [h]; exact hp
      · exact b.unit _ ((Nat.coprime_primes hl Fact.out).2 h)
    have := hu.map β
    rw [map_natCast, h0] at this
    exact not_isUnit_zero this
  · haveI : CharP k 0 := hl ▸ ringChar.charP k
    exact CharP.charP_to_charZero k

attribute [local instance] ptModuleWvs

def torsSub {s : S ⟶ Sp R} (o : Obj b N s) (T : Over S) (c : ℕ) : Submodule (𝓞 D.F) (Additive (T ⟶ o.A)) where
  carrier := {g | g.toMul ^ c = 1}
  zero_mem' := one_pow c
  add_mem' {g h} hg hh := by
    show (g.toMul * h.toMul) ^ c = 1
    rw [mul_pow, show g.toMul ^ c = 1 from hg, show h.toMul ^ c = 1 from hh, _root_.mul_one]
  smul_mem' a g hg := by
    haveI := o.act.hom (algebraMap (𝓞 D.F) D.O a)
    show (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) ^ c = 1
    rw [← MonObj.pow_comp, show g.toMul ^ c = 1 from hg, MonObj.one_comp]

theorem comp_act_natCast {s : S ⟶ Sp R} (o : Obj b N s) {T : Over S} (q : T ⟶ o.A) (n : ℕ) :
    q ≫ o.act.act (n : D.O) = q ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, act_zero_eq_one_wvs, pow_zero, MonObj.comp_one]
  | succ n ih => rw [Nat.cast_succ, o.act.add, o.act.one, MonObj.comp_mul, ih, Category.comp_id, pow_succ]

theorem exists_sub (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ) (hw : w.IsMaximal) (hu : uIdeal D r ≤ w) (hj : j ≤ D.n)
    (hc : ∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) (hm : D.m = 1) {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {s : Sp k ⟶ Sp R} (o : Obj b N s) :
    ∃ H : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.A), (∀ c' : D.O, ∀ h ∈ H, h ≫ o.act.act c' ∈ H) ∧ (∀ h ∈ H, h ^ c = 1) ∧
      (∀ h₁ ∈ H, ∀ h₂ ∈ H, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1
        (lift h₁ 1 : 𝟙_ (Over (Sp k)) ⟶ G2 o.A) (lift 1 h₂) 1) ∧
      (∀ g : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → (∀ h ∈ H, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1
        (lift g 1 : 𝟙_ (Over (Sp k)) ⟶ G2 o.A) (lift 1 h) 1) → g ∈ H) ∧
      (∀ h ∈ H, (∃ e : ℕ, KilledBy o (uIdeal D r ^ e) h) → KilledBy o w h) ∧
      Nat.card {h : 𝟙_ (Over (Sp k)) ⟶ o.A // h ∈ H ∧ KilledBy o w h} = Ideal.absNorm w ^ j := by
  obtain ⟨ex, hce, hje⟩ := hc
  have hpk : ((p : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hck : (c : k) ≠ 0 := by rw [hce, Nat.cast_pow]; exact pow_ne_zero _ hpk
  obtain ⟨e, he, hl, hr, hadj, hskew, hnd⟩ : ∃ e : (𝟙_ (Over (Sp k)) ⟶ o.A) → (𝟙_ (Over (Sp k)) ⟶ o.A) → kˣ,
      (∀ g g' : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → g' ^ c = 1 → ∀ u : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ,
        Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1 (lift g 1 : 𝟙_ (Over (Sp k)) ⟶ G2 o.A) (lift 1 g') u ↔
          u = unitOn (e g g')) ∧
      (∀ g₁ g₂ g' : 𝟙_ (Over (Sp k)) ⟶ o.A, g₁ ^ c = 1 → g₂ ^ c = 1 → g' ^ c = 1 →
        e (g₁ * g₂) g' = e g₁ g' * e g₂ g') ∧
      (∀ g g₁ g₂ : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → g₁ ^ c = 1 → g₂ ^ c = 1 →
        e g (g₁ * g₂) = e g g₁ * e g g₂) ∧
      (∀ (a : D.O) (g g' : 𝟙_ (Over (Sp k)) ⟶ o.A), g ^ c = 1 → g' ^ c = 1 →
        e (g ≫ o.act.act a) g' = e g (g' ≫ o.act.act (D.star a).unop)) ∧
      (∀ g g' : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → g' ^ c = 1 → e g g' * e g' g = 1) ∧
      (∀ g : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → (∀ g' : 𝟙_ (Over (Sp k)) ⟶ o.A, g' ^ c = 1 → e g g' = 1) → g = 1) :=
    PQuot.exists_pairing o c ⟨ex, hce⟩ k hpk (𝟙 _)
  have hinj : Function.Injective (unitOn (R := k)) := by
    refine Units.map_injective (f := (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom) ?_
    exact (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.injective
  have hone : unitOn (1 : kˣ) = 1 := map_one (Units.map _)
  have he1 : ∀ g g' : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → g' ^ c = 1 →
      (Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1 (lift g 1 : 𝟙_ (Over (Sp k)) ⟶ G2 o.A) (lift 1 g') 1 ↔
        e g g' = 1) := fun g g' hg hg' => by
    rw [he g g' hg hg']
    exact ⟨fun h => (hinj (hone.trans h)).symm, fun h => by rw [h]; exact hone.symm⟩
  let M := torsSub o (𝟙_ (Over (Sp k))) c
  haveI : Finite M := (GlobalTheory.T.finite_torsion_and_descent_abelianVariety_algClosed k o.A o.ab c hck).1
  have hM0 : ∀ x : M, x = 0 ↔ x.1.toMul = 1 := fun x => ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
  have hkill : ∀ (v : Ideal (𝓞 D.F)) (x : M), (∀ a ∈ v, a • x = 0) ↔ KilledBy o v x.1.toMul :=
    fun v x => forall₂_congr fun a _ => hM0 (a • x)
  have hwne : w ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hw (NumberField.RingOfIntegers.not_isField D.F)
  have hq : 0 < Ideal.absNorm w := Nat.pos_of_ne_zero fun h => hwne (Ideal.absNorm_eq_zero_iff.1 h)
  have hle : Ideal.absNorm w ^ j ≤ Nat.card {x : M // ∀ a ∈ w, a • x = 0} := by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [pow_zero]
      haveI : Nonempty {x : M // ∀ a ∈ w, a • x = 0} := ⟨⟨0, fun a _ => smul_zero a⟩⟩
      exact Nat.card_pos
    · have hrk : Nat.card {g : 𝟙_ (Over (Sp k)) ⟶ o.A // KilledBy o w g} = Ideal.absNorm w ^ (D.m * D.n) :=
        GlobalTheory.T.card_torsion_killed_by_ideal_char_zero p D R b N (Sp k) s o w hwne k (𝟙 _)
      have htor : ∀ g : 𝟙_ (Over (Sp k)) ⟶ o.A, KilledBy o w g → g ^ c = 1 := fun g hg => by
        have h1 := hg _ (hu (p_mem_uIdeal D r))
        rw [map_natCast, comp_act_natCast] at h1
        obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (hje hj0).ne'
        rw [hce, pow_succ', pow_mul, h1, one_pow]
      let φ : {g : 𝟙_ (Over (Sp k)) ⟶ o.A // KilledBy o w g} ≃ {x : M // ∀ a ∈ w, a • x = 0} :=
        { toFun := fun g => ⟨⟨Additive.ofMul g.1, htor g.1 g.2⟩, (hkill w _).2 g.2⟩
          invFun := fun x => ⟨x.1.1.toMul, (hkill w _).1 x.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [← Nat.card_congr φ, hrk, hm, Nat.one_mul]
      exact Nat.pow_le_pow_right hq hj
  obtain ⟨K, Kiso, Kmax, Ku, Kcard⟩ := GlobalTheory.T.perfect_pairing_torsion_module p D r w j c hw hu ⟨ex, hce⟩ M
    (fun x => (hM0 _).2 x.2) k (fun x y => e x.1.toMul y.1.toMul)
    (fun x x' y => hl _ _ _ x.2 x'.2 y.2) (fun x y y' => hr _ _ _ x.2 y.2 y'.2)
    (fun a x y => by
      have := hadj (algebraMap (𝓞 D.F) D.O a) _ _ x.2 y.2
      rw [D.star_F, MulOpposite.unop_op] at this
      exact this)
    (fun x y => hskew _ _ x.2 y.2)
    (fun x h => (hM0 x).2 (hnd _ x.2 fun g' hg' => h ⟨Additive.ofMul g', hg'⟩)) hle
  let H : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.A) :=
    { carrier := {g | ∃ x ∈ K, x.1.toMul = g}
      one_mem' := ⟨0, K.zero_mem, rfl⟩
      mul_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, K.add_mem hx hy, rfl⟩
      inv_mem' := by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨-x, K.neg_mem hx, rfl⟩ }
  refine ⟨H, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro c' _ ⟨x, hx, rfl⟩
    obtain ⟨a, rfl⟩ := GlobalTheory.T.integers_surjective_of_rank_one p D hm c'
    exact ⟨a • x, K.smul_mem a hx, rfl⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact (he1 _ _ x.2 y.2).2 (Kiso x hx y hy)
  · intro g hg h
    exact ⟨⟨Additive.ofMul g, hg⟩, Kmax _ fun y hy => (he1 _ _ hg y.2).1 (h _ ⟨y, hy, rfl⟩), rfl⟩
  · rintro _ ⟨x, hx, rfl⟩ ⟨i, hi⟩
    exact (hkill w x).1 (Ku x hx ⟨i, (hkill _ x).2 hi⟩)
  · rw [← Kcard]
    refine (Nat.card_eq_of_bijective (fun x : {x : M // x ∈ K ∧ ∀ a ∈ w, a • x = 0} =>
      (⟨x.1.1.toMul, ⟨x.1, x.2.1, rfl⟩, (hkill w _).1 x.2.2⟩ :
        {h : 𝟙_ (Over (Sp k)) ⟶ o.A // h ∈ H ∧ KilledBy o w h})) ⟨fun x y h => ?_, ?_⟩).symm
    · exact Subtype.ext (Subtype.ext (Subtype.mk.inj h))
    · rintro ⟨_, ⟨x, hx, rfl⟩, hk⟩
      exact ⟨⟨x, hx, (hkill w x).2 hk⟩, rfl⟩

theorem exists_isPIsog_isTj : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Sp k ⟶ Sp R) (o : Obj b N s), ∃ (o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ ∧ IsTj r w j o o' ψ := by
  intro p _ D R _ _ b N _ _ hp r w j c hw hu hj hc hm k _ _ s o
  haveI := charZero_of_base b hp s
  obtain ⟨H, stab, hpow, hiso, hmax, hU, hcard⟩ := exists_sub r w j c hw hu hj hc hm o
  obtain ⟨ex, hce, -⟩ := hc
  have hck : (c : k) ≠ 0 := by
    rw [hce, Nat.cast_pow]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hfin : Finite H := by
    haveI := (GlobalTheory.T.finite_torsion_and_descent_abelianVariety_algClosed k o.A o.ab c hck).1
    exact Finite.of_injective (fun h : H => (⟨h.1, hpow h.1 h.2⟩ : {g : 𝟙_ (Over (Sp k)) ⟶ o.A // g ^ c = 1}))
      fun a a' h => Subtype.ext (Subtype.mk.inj h)
  have hinj : ∀ (κ : Type) [Field κ] (x : Sp κ ⟶ Sp k) (h h' : 𝟙_ (Over (Sp k)) ⟶ o.A),
      toUnit (Over.mk x) ≫ h = toUnit (Over.mk x) ≫ h' → h = h' := fun κ _ x h h' e => by
    haveI : Nonempty (Over.mk x).left := inferInstanceAs (Nonempty (PrimeSpectrum κ))
    haveI := GlobalTheory.PointQuot.epi_toUnit (Over.mk x)
    exact (cancel_epi _).1 e
  have hfree : ∀ (κ : Type) [Field κ] (x : Sp κ ⟶ Sp k) (h : 𝟙_ (Over (Sp k)) ⟶ o.A),
      toUnit (Over.mk x) ≫ h = 1 ↔ h = 1 := fun κ _ x h =>
    ⟨fun e => hinj κ x h 1 (by rw [e, MonObj.comp_one]), fun e => by rw [e, MonObj.comp_one]⟩
  obtain ⟨o', ψ, hψ, hker⟩ := PQuot.exists_quot o c ⟨ex, hce⟩ hp H hfin (fun κ _ _ x h _ e => (hfree κ x h).1 e)
    stab hpow hiso (fun κ _ _ x g hg ho => PQuot.max_geom o c hck H hpow hmax κ x g hg ho)
  refine ⟨o', ψ, hψ, fun κ _ _ _ x => ?_⟩
  have hkb : ∀ (v : Ideal (𝓞 D.F)) (h : 𝟙_ (Over (Sp k)) ⟶ o.A),
      KilledBy o v (toUnit (Over.mk x) ≫ h) ↔ KilledBy o v h := fun v h =>
    forall₂_congr fun a _ => by rw [Category.assoc, hfree]
  refine ⟨fun g hg ⟨i, hi⟩ => ?_, ?_⟩
  · obtain ⟨h, hh, rfl⟩ := (hker κ x g).1 hg
    exact (hkb w h).2 (hU h hh ⟨i, (hkb _ h).1 hi⟩)
  · rw [hm, Nat.one_mul, ← hcard]
    refine (Nat.card_eq_of_bijective (fun h : {h : 𝟙_ (Over (Sp k)) ⟶ o.A // h ∈ H ∧ KilledBy o w h} =>
      (⟨toUnit (Over.mk x) ≫ h.1, (hker κ x _).2 ⟨h.1, h.2.1, rfl⟩, (hkb w _).2 h.2.2⟩ :
        {g : Over.mk x ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g})) ⟨fun a a' h => ?_, ?_⟩).symm
    · exact Subtype.ext (hinj κ x _ _ (congrArg Subtype.val h))
    · rintro ⟨g, hg, hk⟩
      obtain ⟨h, hh, rfl⟩ := (hker κ x g).1 hg
      exact ⟨⟨h, hh, (hkb w h).1 hk⟩, rfl⟩

end GlobalTheory.UPel.HT.ES.TjExists
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsTypeTjPIsogenyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.harrisTaylor_exists_typeTj_pIsogeny : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Sp k ⟶ Sp R) (o : Obj b N s), ∃ (o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ ∧ IsTj r w j o o' ψ := by
  first | exact @GlobalTheory.UPel.HT.ES.TjExists.exists_isPIsog_isTj | exact GlobalTheory.UPel.HT.ES.TjExists.exists_isPIsog_isTj | exact @GlobalTheory.UPel.HT.ES.TjExists.exists_sub | exact GlobalTheory.UPel.HT.ES.TjExists.exists_sub | exact @GlobalTheory.UPel.HT.ES.TjExists.comp_act_natCast | exact GlobalTheory.UPel.HT.ES.TjExists.comp_act_natCast
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberExistsIntegralTermsUnitShift
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointsFramesThetaSectionMember
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointsFramesThetaSectionMember
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep

theorem exists_points_frames_theta : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), ∃ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th : SecA 𝔪.A (FractionRing V) 1) (ρ : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A))), (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) ∧ (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' → Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' = val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) ∧ (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) ∧ ρ.IsGen ∧ ∀ a, IsTorsFrame 𝔪.A ρ (X₁.S.r * X₁.S.N) (x a) (fr a) := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪
  have hj : (TFK (R := V) (FractionRing V)).hom = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (FractionRing V))) = _
    rw [Algebra.algebraMap_self]
    exact Spec.map_id _
  have gp := 𝔪.cart
  have hsq : ∀ a, (spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) ≫ X₁.ρ.P.A.hom = (TFK (R := V) (FractionRing V)).hom ≫ spMap 𝔪.yK := by
    intro a
    rw [Category.assoc, Over.w (X₁.ρ.pt a), hj]
    simp
  let x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) := fun a =>
    Over.homMk (gp.1.lift _ _ (hsq a)) (gp.1.lift_snd _ _ _)
  have hx : ∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left := fun a => gp.1.lift_fst _ _ _
  obtain ⟨rig, fr, hrig, -, hfr⟩ := GlobalTheory.exists_frames_move_through (T := baseOver (Sp X₁.S.R))
    (T' := TFK (R := V) (FractionRing V)) (h := spMap 𝔪.yK) gp 𝔪.wl_gen X₁.ρ.rig_gen hx X₁.ρ.fr_tors
  have hτ : (spMap 𝔪.yK : (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left) ≫
      (baseOver (Sp X₁.S.R)).hom = (TFK (R := V) (FractionRing V)).hom ≫ spMap 𝔪.yK := by
    rw [hj]; simp
  obtain ⟨th, hth⟩ := GlobalTheory.ThetaPtMove.exists_secRel (T := TFK (R := V) (FractionRing V))
    (T₀ := baseOver (Sp X₁.S.R)) (τ := spMap 𝔪.yK) gp hτ (w := 𝔪.wl) 𝔪.wl_gen X₁.ρ.P.isLB 𝔪.A.isLB (a := 1) X₁.ρ.th₁
  refine ⟨x, fr, th, rig, hx, fun a => ⟨(hfr a).1.2.1, fun z J J' hJ hJ' => ?_⟩, fun a => ?_, hrig, fun a => (hfr a).1⟩
  · have e := (hfr a).2 _ (𝟙 _) z J J' hJ hJ'
    rw [Fin.prod_univ_one, zpow_one, Category.id_comp, Category.id_comp] at e
    exact e.symm
  · have hv := GlobalTheory.ThetaPtMove.isValueAt_move (T := TFK (R := V) (FractionRing V))
      (T₀ := baseOver (Sp X₁.S.R)) (τ := spMap 𝔪.yK) gp hτ (w := 𝔪.wl) X₁.ρ.P.isLB 𝔪.A.isLB (a := 1)
      (x := x a) (x₀ := X₁.ρ.pt a) (hx a).symm (ρ₀ := X₁.ρ.fr a) (ρ := fr a) (hfr a).2 (s₀ := X₁.ρ.th₁) (s := th) hth
      (X₁.ρ.th_val a)
    intro z J hJ
    have e := GlobalTheory.FrameMove.sval_valueAt hv (𝟙 _) hJ
    rw [Category.id_comp] at e
    refine e.trans ?_
    rw [GlobalTheory.FrameMove.val_powFrame, Nat.cast_one, zpow_one]
    congr 1
    exact (gs_pull (𝟙 _) (spMap 𝔪.yK) z ⊤ trivial _).trans
      ((congrArg (fun q => gs q z ⊤ _) (Category.id_comp _)).trans (GlobalTheory.FrameMove.gs_spMap 𝔪.yK z _))

end GlobalTheory.GSep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointsFramesThetaSectionMemberStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_points_frames_thetaSection_member : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), ∃ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th : SecA 𝔪.A (FractionRing V) 1) (ρ : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A))), (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) ∧ (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' → Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' = val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) ∧ (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) ∧ ρ.IsGen ∧ ∀ a, IsTorsFrame 𝔪.A ρ (X₁.S.r * X₁.S.N) (x a) (fr a) := by
  first | exact @GlobalTheory.GSep.exists_points_frames_theta | exact GlobalTheory.GSep.exists_points_frames_theta | (intros; apply GlobalTheory.GSep.exists_points_frames_theta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberExistsIntegralTermsUnitShift
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.IntTerm

namespace GlobalTheory.GSep.IntTerm

theorem mem_of_psiCoord {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} (D : DegData V I) {χ : D.toPre.X} (hχ : χ ≠ 0)
    {r : V} (h : Formalism.L2.Pj.PsiCoord D.toPre χ r) : r ∈ I := by
  obtain ⟨j, h₁, h₂, e⟩ := h
  obtain ⟨r', hr', e'⟩ := D.psi_pos χ hχ j ⊤ (isAffineOpen_top _) h₁ h₂
  have e₁ : r' = DegPre.toOpen (R := V) ⊤ r := GlobalTheory.PsiCoordLocal.jK_app_inj ⊤ (e'.trans e.symm)
  rw [e₁] at hr'
  have hb := GlobalTheory.PsiCoordLocal.toOpen_top_bijective (R := V)
  obtain ⟨s, hs, es⟩ := (Ideal.mem_map_iff_of_surjective _ hb.2).1 hr'
  rwa [← hb.1 es]

theorem isUnit_of_sub_mem {V : Type} [CommRing V] [IsLocalRing V] {a b : V} (h : a - b ∈ maximalIdeal V) :
    IsUnit a ↔ IsUnit b := by
  rw [← not_iff_not, ← mem_nonunits_iff, ← mem_nonunits_iff, ← mem_maximalIdeal, ← mem_maximalIdeal]
  exact ⟨fun ha => by simpa using sub_mem ha h, fun hb => by simpa using add_mem h hb⟩

theorem exists_terms : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), Set.range lab = X₁.S.HH X₁.M z₁ → ∃ u : X → C → V, 𝔪.Terms x₀ lab (fun mu c => u mu c * t mu) ∧ (∀ mu, ∃ c, IsUnit (u mu c)) ∧ ∀ c, lab c = x₀ → IsUnit (u 0 c) := by
  intro I X₁ z₁ act x₀ hdiv V _ _ _ ev X _ t δ 𝔪 C lab hlab
  have hV := 𝔪.cn
  haveI : IsNoetherianRing V := hV.1
  haveI : CharZero V := hV.2.2.2
  have hA := admissibleBase_of_completeNormalLocalCharZero hV
  have hL := GlobalTheory.firstFiveLaws
  have hN₂ : 2 ≤ X₁.S.r * X₁.S.N := le_trans X₁.S.N_ge (Nat.le_mul_of_pos_left _ X₁.S.r_pos)
  have hN : 1 ≤ X₁.S.r * X₁.S.N := by omega

  have ht0 : IsUnit (t 0) := by
    obtain ⟨u₀, hu₀⟩ := 𝔪.psi 0
    obtain ⟨r₀, hr₀, -, -, hu⟩ := (GlobalTheory.PsiCoordLocal.main V 𝔪.D hV.2.1 (𝔪.e₈ 0)).1
    obtain ⟨v, hv⟩ := (GlobalTheory.PsiCoordLocal.main V 𝔪.D hV.2.1 (𝔪.e₈ 0)).2.1 r₀ _ hr₀ hu₀
    have h1 : IsUnit ((u₀ : V) * t 0) := hv ▸ v.isUnit.mul (hu (map_zero _))
    exact isUnit_of_mul_isUnit_right h1
  obtain ⟨x, fr, th, ρ, hx, hfr, hth, hρ, htf⟩ := GlobalTheory.T.exists_points_frames_thetaSection_member I X₁ z₁ act V ev X t δ 𝔪
  obtain ⟨hNu, h0, hdv⟩ := GlobalTheory.T.level_isUnit_dividingThetaConstant_ne_zero_dvd I X₁ z₁ act V ev X t δ 𝔪 x₀ hdiv
  obtain ⟨w₀, hw₀⟩ := 𝔪.U.ext
  obtain ⟨s, hs, -⟩ := ((expBijF_and_expandsF_lin hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U).1 (FractionRing V) 1 le_rfl w₀ hw₀).1 th
  obtain ⟨l, hl, hlf⟩ := GlobalTheory.T.exists_torsion_frame_eq_const_mul_integral_generator V hV 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U w₀ hw₀ ρ hρ _ hN
  have hint := GlobalTheory.T.mem_dividingLabels_iff_class_zero I X₁ z₁ act x₀ hdiv V ev X t δ 𝔪

  have hxb : ∀ (a) (xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A),
      xb.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫
        (X₁.ρ.pt a).left →
      xb.left = spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ (x a).left := by
    intro a xb h
    refine 𝔪.cart.1.hom_ext ?_ ?_
    · rw [h, Category.assoc, hx a, ← Category.assoc]
      congr 1
      rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl
    · rw [Category.assoc, Over.w, Over.w]
      change _ = _ ≫ Spec.map (𝟙 _)
      rw [Spec.map_id, Category.comp_id]; rfl
  have hyy : ∀ c, 𝔪.YY (lab c) 0 := fun c => (hint _).1 (by
    have : lab c ∈ Set.range lab := ⟨c, rfl⟩
    rwa [hlab] at this)
  choose p xb hp hq hxp using hyy
  have hp0 : ∀ c, (p c).y = 0 := fun c => (hp c).trans (map_zero _)
  choose h gi hh hgt hfe hext hpull using fun c => GlobalTheory.T.rationalTorsionPoint_lift_section_torusExtension V hV 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U _ hN (x (lab c)) (xb c) (p c)
    (hxb _ _ (hxp c)) (hp0 c) (hq c)
  choose g' hg' using fun c => GlobalTheory.FieldRestrictionTest.exists_isPullF (toUnit (TF (R := V) (FractionRing V))) (gi c)
  choose w hw hif hlies using fun c => GlobalTheory.T.sectionValue_integralPoint_eq_adicSum_terms V hV 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U w₀ hw₀ (x (lab c)) (fr (lab c)) (h c) (gi c)
    (g' c) l hl (hfe c) (hext c) (hg' c) (hlf _ _ _ (htf _) (hh c) (hext c))
  have htor : ∀ c, ∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g' c) o ∧ o.IsZero := fun c => by
    obtain ⟨o, ho, hz⟩ := hgt c
    obtain ⟨o', ho'⟩ := GlobalTheory.FieldRestrictionTest.exists_isPullF (toUnit (TF (R := V) (FractionRing V))) o
    exact ⟨o', GlobalTheory.FieldRestrictionTest.isNsmul_restrict (hg' c) ho' ho,
      GlobalTheory.FieldRestrictionTest.isZero_restrict ho' hz⟩
  have hb : ∀ c, (g' c).b = toUnit _ ≫ (gi c).b := fun c =>
    ((GlobalTheory.FieldRestrictionTest.isPullF_iff _ _ _).1 (hg' c)).1
  have hex : Exhausts 𝔪.D.toPre.P (X₁.S.r * X₁.S.N) fun c => (gi c).b := by
    refine GlobalTheory.T.torsionSections_exhaust_of_generic_geometric V _ _ hN C _ (fun c => (Sep.Frames.torsion_of_nsmul (g' c) _ (hb c) (htor c)).2) fun β hβ => ?_
    obtain ⟨y, hy, ⟨q, hq0, hqy⟩, H⟩ := GlobalTheory.T.geometricTorsionPoint_abelianPart_lies_under_classZero V hV 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U _ hN β hβ
    obtain ⟨a, ha⟩ := GlobalTheory.T.geometricTorsionPoint_member_has_label I X₁ z₁ act V ev X t δ 𝔪 y hy
    have hmem : a ∈ Set.range lab := by
      rw [hlab]
      exact (hint a).2 ⟨q, y, hq0.trans (map_zero _).symm, hqy, ha⟩
    obtain ⟨c, rfl⟩ := hmem
    have e : xb c = y := Over.OverMorphism.ext ((hxb _ _ (hxp c)).trans (hxb _ _ ha).symm)
    exact ⟨c, (H (p c) (hp0 c) (e ▸ hq c)).symm.trans ((GlobalTheory.FieldRestrictionTest.isPullF_iff _ _ _).1 (hpull c)).1⟩
  obtain ⟨θ, hθ⟩ := exists_isTheta hV 𝔪.D.toPre
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.degree_one_term_eq_const_mul_psi_mul_theta V 𝔪.D.toPre θ hθ s
  choose υ hυ using 𝔪.psi
  choose a ha hau using fun mu c => hκ (gi c) (g' c) (w c) l (hg' c) (hw c) (hif c) (𝔪.e₈ mu) _ (hυ mu)
  have hunit : ∀ mu, ∃ c, IsUnit (a mu c) := fun mu =>
    (GlobalTheory.T.exists_torsionTranslate_thetaSection_unit V 𝔪.D.toPre θ hθ _ hN₂ hNu C _ hex (𝔪.D.toPre.c (𝔪.e₈ mu))).imp fun c hc => hau mu c hc
  have hco : ∀ mu c, coef s (g' c) (w c) (𝔪.e₈ mu) =
      l⁻¹ * κ * algebraMap V (FractionRing V) (υ mu * t mu * a mu c) := fun mu c => by
    rw [_root_.mul_assoc, ← ha, inv_mul_cancel_left₀ hl]
  have hsum : ∀ c, ∃ S : V, 𝔪.yK ⟨X₁.S.th (lab c), X₁.S.th_mem _⟩ = l⁻¹ * κ * algebraMap V (FractionRing V) S ∧
      (IsUnit S ↔ IsUnit (a 0 c)) := fun c => by
    obtain ⟨S, hS, hm⟩ := GlobalTheory.T.adicSum_fractionField_eq_mul_integral_congr V _ (𝔪.e₈ 0) (coef s (g' c) (w c))
      (fun χ => υ (𝔪.e₈.symm χ) * t (𝔪.e₈.symm χ) * a (𝔪.e₈.symm χ) c) (l⁻¹ * κ) _
      (fun χ => by rw [← hco, AddEquiv.apply_symm_apply])
      (fun χ hχ => Ideal.mul_mem_right _ _ (mem_of_psiCoord 𝔪.D (χ := 𝔪.e₈ (𝔪.e₈.symm χ))
        (by rwa [AddEquiv.apply_symm_apply, ← map_zero 𝔪.e₈]) (hυ _)))
      (hlies c 1 le_rfl (w c) (fun _ _ _ => (pow_one _).symm) (hw c) th s _ hs (hth _))
    refine ⟨S, hS, (isUnit_of_sub_mem hm).trans ?_⟩
    simp only [AddEquiv.symm_apply_apply]
    rw [_root_.mul_assoc, Units.isUnit_units_mul]
    exact ⟨fun h' => isUnit_of_mul_isUnit_right h', fun h' => ht0.mul h'⟩
  choose S hS hSu using hsum
  have hx₀ : x₀ ∈ Set.range lab := by
    rw [hlab]
    exact AddSubgroup.subset_closure hdiv
  obtain ⟨c₀, rfl⟩ := hx₀
  have hκ0 : l⁻¹ * κ ≠ 0 := left_ne_zero_of_mul (hS c₀ ▸ h0)
  have inj := IsFractionRing.injective V (FractionRing V)
  have hS₀ : IsUnit (S c₀) := by
    obtain ⟨c₁, hc₁⟩ := hunit 0
    obtain ⟨r, hr⟩ := hdv (lab c₁)
    rw [hS, hS, mul_left_comm, ← map_mul] at hr
    have e := inj (mul_left_cancel₀ hκ0 hr)
    exact isUnit_of_mul_isUnit_right (e ▸ (hSu c₁).2 hc₁)
  obtain ⟨σ, hσ⟩ := hS₀
  refine ⟨fun mu c => υ mu * a mu c * σ⁻¹, ⟨x, fr, th, w₀, s, g', w, hx, hfr, hth, hw₀, hs,
    fun c => ⟨htor c, hw c, hlies c⟩, fun mu c => ?_⟩, fun mu => (hunit mu).imp fun c hc => ?_, fun c hc => ?_⟩
  · rw [hco, hS, ← hσ, mul_left_comm, ← map_mul]
    congr 2
    linear_combination (υ mu * a mu c * t mu : V) * σ.inv_mul
  · exact ((υ mu).isUnit.mul hc).mul (σ⁻¹).isUnit
  · have e₁ := hS c
    have e₂ := hS c₀
    simp only [hc] at e₁
    have e := inj (mul_left_cancel₀ hκ0 (e₁.symm.trans e₂))
    exact ((υ 0).isUnit.mul ((hSu c).1 (e ▸ hσ ▸ σ.isUnit))).mul (σ⁻¹).isUnit

end GlobalTheory.GSep.IntTerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberExistsIntegralTermsUnitShiftStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaMember_exists_integral_terms_unit_shift : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), Set.range lab = X₁.S.HH X₁.M z₁ → ∃ u : X → C → V, 𝔪.Terms x₀ lab (fun mu c => u mu c * t mu) ∧ (∀ mu, ∃ c, IsUnit (u mu c)) ∧ ∀ c, lab c = x₀ → IsUnit (u 0 c) := by
  first | exact @GlobalTheory.GSep.IntTerm.exists_terms | exact GlobalTheory.GSep.IntTerm.exists_terms | (intros; apply GlobalTheory.GSep.IntTerm.exists_terms <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrExp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

namespace GlobalTheory.GSep.TransTerms

variable {I : Type}

def FrExp {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}
    (𝔪 : GMem X₁ z₁ act V ev X t δ) (a τ : X₁.S.Gam) (e : ℕ) : Prop :=
  (∃ χ, TorChar 𝔪 τ χ) ∧
  ∃ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th : SecA 𝔪.A (FractionRing V) 1)
    (w₀ : W0 𝔪.U.toUnifPre) (s : Fam 𝔪.D.toPre (FractionRing V) 1) (g' : GtPtF 𝔪.D.toPre (FractionRing V))
    (w : Frm 𝔪.D.toPre (FractionRing V) 1 g'.b),
    (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) ∧
    (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
        val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) ∧
    (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) ∧ w₀.IsGen ∧
    𝔪.U.ExpandsF (FractionRing V) 1 w₀ th s ∧
    (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g' o ∧ o.IsZero) ∧ w.IsGen ∧ 𝔪.Over' w₀ g' w (x a) (fr a) ∧
    ∀ χ, TorChar 𝔪 τ χ → ∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∀ g'' : GtPtF 𝔪.D.toPre (FractionRing V),
      g'.IsAdd g₀ g'' → ∀ w'' : Frm 𝔪.D.toPre (FractionRing V) 1 g''.b, w''.IsGen →
      (∀ z J, Good 𝔪.D.toPre.P.L z J → (val w (𝟙 _) z J).val =
        cstH (R := V) z (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e))) * (val w'' (𝟙 _) z J).val) →
      𝔪.Over' w₀ g'' w'' (x (a + τ)) (fr (a + τ))

end GlobalTheory.GSep.TransTerms
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerAbelianLocusChartRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerAbelianLocusChartRing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSAbLocus

theorem tanBasis_of_basis {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R]
    (t : SAB H (Sp R)) {n : ℕ} (b : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) {T : Type} [CommRing T]
    (φ : R →+* T) :
    (∀ i, IsTanAtG t (spMap φ ≫ 𝟙 (Sp R)) (spMap (dualMap φ) ≫ (tv (b i)).left)) ∧
      ∀ w, IsTanAtG t (spMap φ ≫ 𝟙 (Sp R)) w →
        ∃! a : Fin n → T, IsCombAtG t (spMap φ ≫ 𝟙 (Sp R)) (fun i => spMap (dualMap φ) ≫ (tv (b i)).left) a w := by
  refine GlobalTheory.LocM.FrameBase.tanBasis_baseChange t φ (𝟙 (Sp R)) n _ (fun i => GlobalTheory.LieMet.isTan_tv (b i)) ?_
  intro w hw
  refine ⟨b.repr (GlobalTheory.LieMet.tanOf hw), ?_, fun a ha => ?_⟩
  · show IsCombAtG t _ _ _ (tv (GlobalTheory.LieMet.tanOf hw)).left
    rw [GlobalTheory.LieMet.isComb_iff]
    exact (b.sum_repr _).symm
  · have h := (GlobalTheory.LieMet.isComb_iff b a (GlobalTheory.LieMet.tanOf hw)).1 ha
    rw [h]
    ext i
    simp [Finsupp.single_apply]

theorem exists_isKS_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (DV : Derivation ℤ Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1)), ∃ Θ₁, IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (fun a => spMap (dualMap (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) ≫ (tv (v' a)).left) ⇑DV Θ₁ := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam _ htt hab n v' D DV
  let U : (Sp R).affineOpens := (Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens))
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))
  let ρ : R →+* Γ(Sp R, U.1) := ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤)
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have hc : spMap ρ ≫ 𝟙 (Sp R) = chart U := by
    rw [Category.comp_id]
    show Spec.map _ = U.2.fromSpec
    rw [← (isAffineOpen_top (Sp R)).map_fromSpec U.2 (homOfLE ((Sp R).basicOpen_le (U := ⊤)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec]
    rw [show CommRingCat.ofHom ρ = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op from rfl]
    erw [Spec.map_comp]
    rfl
  obtain ⟨hv, hb⟩ := GlobalTheory.KSAbLocus.tanBasis_of_basis t v' ρ
  rw [hc] at hv hb
  obtain ⟨PP', cub, sym, adj, prim, mm, -⟩ := sabPull proved_CubePullSt (chart U) t
  have h2 : (U.1 : (Sp R).Opens) = PrimeSpectrum.basicOpen (∏ i, tt i) :=
    basicOpen_eq_of_affine (R := CommRingCat.of R) (∏ i, tt i)
  have h4 : ∀ q : Sp R, q ∈ ((U.1 : (Sp R).Opens) : Set (Sp R)) → ∏ i, tt i ∉ q.asIdeal := by
    intro q hq
    rw [h2] at hq
    exact hq
  have hx : ∀ s, ∏ i, tt i ∉ ((chart U) s).asIdeal := fun s =>
    h4 _ (by rw [← U.2.range_fromSpec]; exact ⟨s, rfl⟩)
  obtain ⟨hP, hA, hK⟩ := GlobalTheory.T.uniformisedTriple_abelianLocus_proper_relAmple E H R t P m tt htt hab _ (chart U) _ hx ⟨mm⟩
  exact GlobalTheory.T.exists_kodairaSpencer_affine_open_abelian_pullback E H (Sp R) t _ U le_rfl _ ⟨mm⟩ hP hA hK n _ hv hb DV

end GlobalTheory.KSAbLocus
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerAbelianLocusChartRingStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kodairaSpencer_abelianLocus_chartRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (DV : Derivation ℤ Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1)), ∃ Θ₁, IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (fun a => spMap (dualMap (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) ≫ (tv (v' a)).left) ⇑DV Θ₁ := by
  first | exact @GlobalTheory.KSAbLocus.exists_isKS_abLocus | exact GlobalTheory.KSAbLocus.exists_isKS_abLocus | (intros; apply GlobalTheory.KSAbLocus.exists_isKS_abLocus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleLevelStructureAtGeometricPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleLevelStructureAtGeometricPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section
namespace GlobalTheory.UPel.HT.EtLev

theorem epi_sp_field {k k' : Type} [Field k] [Field k'] (x' : Sp k' ⟶ Sp k) : Epi x' := by
  rw [← Spec.map_preimage x']
  have : Flat (Spec.map (Spec.preimage x')) := by
    rw [show Spec.preimage x' = CommRingCat.ofHom (Spec.preimage x').hom from rfl]; infer_instance
  have : Surjective (Spec.map (Spec.preimage x')) :=
    ⟨fun _ => ⟨IsLocalRing.closedPoint k', Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem pt_ext_of_pullback {S : Scheme.{0}} {A : Over S} {k k' : Type} [Field k] [Field k'] (x : Sp k ⟶ S)
    (x' : Sp k' ⟶ Sp k) (g₁ g₂ : Over.mk x ⟶ A)
    (h : (Over.homMk x' rfl : Over.mk (x' ≫ x) ⟶ Over.mk x) ≫ g₁ =
      (Over.homMk x' rfl : Over.mk (x' ≫ x) ⟶ Over.mk x) ≫ g₂) : g₁ = g₂ := by
  haveI := epi_sp_field x'
  apply Over.OverMorphism.ext
  have := congrArg CommaMorphism.left h
  simp only [Over.comp_left, Over.homMk_left] at this
  exact (cancel_epi x').1 this

theorem exists_etLevOver_geomPt : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), N.Coprime p → IsEtPlace b w0 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃ l : D.La → (Over.mk x ⟶ o.A), IsEtLevOver o w0 r l := by
  intro p _ D R _ b N w0 r _hN hw S s o k _ _ x
  have hw0 : w0 ≠ ⊥ := by
    intro h
    have hp : (p : 𝓞 D.F) ∈ w0 := hw.2.1
    rw [h, Ideal.mem_bot] at hp
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hp)
  haveI : Finite (𝓞 D.F ⧸ w0 ^ r) := Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ hw0)
  obtain ⟨f, fadd, fsm, finj, fsurj⟩ := GlobalTheory.T.torsion_points_additive_parametrization p D R b N w0 r hw S s o k x
  have hmul : ∀ (c : D.O) (g h : Over.mk x ⟶ o.A), (g * h) ≫ o.act.act c = (g ≫ o.act.act c) * (h ≫ o.act.act c) := by
    intro c g h; haveI := o.act.hom c; exact MonObj.mul_comp _ _ _
  obtain ⟨l, ladd, llin, lker, lsurj⟩ := GlobalTheory.T.exists_morita_lattice_quotient_torsion p D w0 r hw.1 hw.2.1 (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c)
    (fun c g h => hmul c g h) (fun g => by simp only [o.act.one, Category.comp_id])
    (fun b c g => by simp only [o.act.mul, Category.assoc])
    (fun b c g => by simp only [o.act.add]; exact MonObj.comp_mul _ _ _) f fadd fsm finj fsurj
  have f0 : f 0 = 1 := by
    have h := fadd 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have tor : ∀ a, ∀ c ∈ w0 ^ r, f a ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
    intro a c hc
    rw [← fsm, (Ideal.Quotient.eq_zero_iff_mem).2 hc, zero_smul, f0]
  refine ⟨l, ladd, llin, fun y hy => (lker y).2 hy, ?_⟩
  intro k' _ _ x'
  refine ⟨fun y hy => ?_, fun g hg => ?_⟩
  · apply (lker y).1
    apply pt_ext_of_pullback x x'
    rw [hy]
    exact (MonObj.comp_one _).symm
  · obtain ⟨f', -, -, -, f'surj⟩ := GlobalTheory.T.torsion_points_additive_parametrization p D R b N w0 r hw S s o k' (x' ≫ x)
    let π : Over.mk (x' ≫ x) ⟶ Over.mk x := Over.homMk x' rfl
    have tor' : ∀ a, ∀ c ∈ w0 ^ r, (π ≫ f a) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
      intro a c hc
      rw [Category.assoc, tor a c hc, MonObj.comp_one]
    let φ : (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) → (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) :=
      fun a => (f'surj _ (tor' a)).choose
    have hφ : ∀ a, f' (φ a) = π ≫ f a := fun a => (f'surj _ (tor' a)).choose_spec
    have φinj : Function.Injective φ := fun a a' h =>
      finj (pt_ext_of_pullback x x' _ _ (by rw [← hφ, ← hφ, h]))
    obtain ⟨a', rfl⟩ := f'surj g hg
    obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.1 φinj) a'
    obtain ⟨y, hy⟩ := lsurj (f a) (tor a)
    exact ⟨y, by rw [hy, ← ha, hφ]⟩
end GlobalTheory.UPel.HT.EtLev
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleLevelStructureAtGeometricPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etaleLevelStructure_at_geometricPoint : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), N.Coprime p → IsEtPlace b w0 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃ l : D.La → (Over.mk x ⟶ o.A), IsEtLevOver o w0 r l := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.exists_etLevOver_geomPt) | (exact GlobalTheory.UPel.HT.EtLev.exists_etLevOver_geomPt) | (intros; apply GlobalTheory.UPel.HT.EtLev.exists_etLevOver_geomPt  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModelMemberTermMemMaximalIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModelMemberTermMemMaximalIdeal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

namespace GlobalTheory.Poinc.Sep.HighTerms


attribute [local instance] GlobalTheory.TorusExt.gtGroup in
theorem exists_integral (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (hV : IsCN V)
    (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G]
    (U : Unif (maximalIdeal V) D A G) (N : ℕ) (hN : 1 ≤ N) (g' : GtPtF D.toPre (FractionRing V))
    (ho : ∃ o, GtPtF.IsNsmul N g' o ∧ o.IsZero) :
    ∃ g : GtPt D.toPre (𝟙_ (Over (Sp V))),
      GtPt.IsPullF (FractionRing V) (toUnit (TF (R := V) (FractionRing V))).left g g' := by
  have : CharZero V := hV.2.2.2
  haveI : IsNoetherianRing V := hV.1
  have hR : GlobalTheory.Mum.Base V := ⟨admissibleBase_of_completeNormalLocalCharZero hV, hV.2.2.2⟩
  obtain ⟨M, g₀, x₀, hfin, -, hg₀, huniv, hx₀, hform⟩ :=
    GlobalTheory.ToricTorsionUnif.exists_torsion_toG V hR G D A U N hN
  have hkg : N • g' = 0 := by
    obtain ⟨o, h₁, h₂⟩ := ho
    exact ((GlobalTheory.TorusExt.isNsmul_iff_eq N g' o).1 h₁).symm.trans ((GlobalTheory.TorusExt.isZero_iff_eq o).1 h₂)
  obtain ⟨n, hn, -⟩ := huniv _ _ (GlobalTheory.Poinc.TorsLift.gtTors_toT g' hkg)
  have hj : spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ jFK (R := V) (FractionRing V) =
      jFK (R := V) (AlgebraicClosure (FractionRing V)) := by
    rw [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let nb : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ M :=
    Over.homMk (spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ n.left) (by
      rw [Category.assoc, Over.w n]
      show _ ≫ jFK (R := V) (FractionRing V) ≫ jK V = jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V
      rw [← Category.assoc, hj])
  obtain ⟨s, hs⟩ := GlobalTheory.FinDescent.galoisFixed_point_of_finite V hV.2.1 M hfin nb (fun σ => by
    have hσ : spMap σ.toAlgHom.toRingHom ≫ spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) =
        spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) := by
      rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact RingHom.ext fun r => σ.commutes r
    show spMap σ.toAlgHom.toRingHom ≫ spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ n.left = _
    rw [reassoc_of% hσ]; rfl)
  have hns : n = toUnit _ ≫ s := by
    apply Over.OverMorphism.ext
    apply GlobalTheory.OnePoint.point_ext (spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))))
    refine (congrArg (·.left) hs).trans ?_
    rw [Over.comp_left, Over.comp_left, ← Category.assoc]
    congr 1
    have e1 : ∀ X : Over (Sp V), (toUnit X).left = X.hom := fun X => by simp
    rw [e1, e1]
    show jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V =
      spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ jFK (R := V) (FractionRing V) ≫ jK V
    rw [← Category.assoc, hj]
  obtain ⟨g, hg⟩ := GlobalTheory.ConstLie.exists_isPull s g₀
  obtain ⟨q, hq⟩ := GlobalTheory.FieldRestrictionTest.exists_isPullF (toUnit (TF (R := V) (FractionRing V))) g
  have h2 := GlobalTheory.FlatTors.TorsMapExists.isPullF_trans hg hq
  rw [← Over.comp_left, ← hns] at h2
  exact ⟨g, by rwa [GlobalTheory.FieldRestrictionTest.isPullF_unique h2 hn] at hq⟩

theorem term_mem_maximalIdeal : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (m1 : ℕ) (t1 : Fin m1 → V1) (δ1 : Fin m1 → LinearMap.BilinForm ℤ Y1) (𝔪1 : UMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → Y1) → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C) (mu : Fin 8 → Y1), mu ≠ 0 → T mu c ∈ maximalIdeal V1 := by
  intro g n F W Z i X₁ z₁ act x₀ hdiv V _ _ _ ev X _ m t δ 𝔪 C₀ lab₀ _ T hT c₁ mu₁ hmu₁
  obtain ⟨x, fr, th, w₀, s, g₀, ω₀, hx, hfr, hth, hw₀, hs, hg₀, hT⟩ := hT
  have hV := 𝔪.cn
  haveI : IsNoetherianRing V := hV.1
  haveI : IsIntegrallyClosed V := hV.2.1
  haveI : CharZero V := hV.2.2.2
  have hA := admissibleBase_of_completeNormalLocalCharZero hV
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hN₂ : 2 ≤ X₁.S.r * X₁.S.N := le_trans X₁.S.N_ge (Nat.le_mul_of_pos_left _ X₁.S.r_pos)
  have hN : 1 ≤ X₁.S.r * X₁.S.N := by omega
  obtain ⟨ρ, hρ, Hr⟩ := GlobalTheory.ConstFam.exists_gen_through (K := PUnit) (φ' := fun _ => eSec 𝔪.A.A)
    (φ := fun _ => eSec X₁.ρ.P.A) (ε := fun _ => 1) (h := spMap 𝔪.yK) 𝔪.wl_gen X₁.ρ.P.isLB 𝔪.A.isLB
    (fun _ => PolBaseChange.eSec_comm 𝔪.cart) X₁.ρ.rig X₁.ρ.rig_gen
  have htf : ∀ a, IsTorsFrame 𝔪.A ρ (X₁.S.r * X₁.S.N) (x a) (fr a) := fun a =>
    GlobalTheory.FrameMove.isTorsFrame_move (T := baseOver (Sp X₁.S.R)) (T' := TFK (R := V) (FractionRing V)) (w := 𝔪.wl)
      (h := spMap 𝔪.yK) 𝔪.cart 𝔪.wl_gen
      (fun Z r z J J' hJ hJ' =>
        (Hr Z r z J J' hJ hJ').trans (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _))))
      (hx a) (X₁.ρ.fr_tors a) (hfr a).1 (fun z J J' hJ hJ' => ((hfr a).2 z J J' hJ hJ').symm)
  obtain ⟨ρ', k, hk, hNW, hmove⟩ := GlobalTheory.T.exists_renormalization_rigidification_multiple V _ 𝔪.D 𝔪.A 𝔪.G 𝔪.U.toUnifPre w₀ hw₀ ρ hρ
  obtain ⟨hNu, h0, hdv⟩ := GlobalTheory.T.level_unit_thetaConstant_ne_zero_divides_all g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ hdiv
  obtain ⟨θ, hθ⟩ := IntTerm.exists_isTheta hV 𝔪.D.toPre
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.degree_one_term_eq_const_mul_psi_mul_theta V 𝔪.D.toPre θ hθ s
  choose υ hυ using 𝔪.psi

  have core : ∀ (a : X₁.S.Gam) (gi : GtPt 𝔪.D.toPre (𝟙_ (Over (Sp V)))) (g' : GtPtF 𝔪.D.toPre (FractionRing V))
      (w : Frm 𝔪.D.toPre (FractionRing V) 1 g'.b),
      GtPt.IsPullF (FractionRing V) (toUnit (TF (R := V) (FractionRing V))).left gi g' →
      (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g' o ∧ o.IsZero) → w.IsGen → 𝔪.Over' w₀ g' w (x a) (fr a) →
      ∀ mu, ∃ α : V, coef s g' w (𝔪.e₈ mu) = k * κ * algebraMap V (FractionRing V) (υ mu * mono W t δ mu * α) ∧
        (IntTerm.UnitAt 𝔪.D.toPre θ (𝔪.D.toPre.c (𝔪.e₈ mu) * gi.b) → IsUnit α) := by
    intro a gi g' w hP ho hw hov mu
    obtain ⟨w', fr', hw', hfr', hov', hco, hval⟩ := Tors.liesOver_scale V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.U.toUnifPre (FractionRing V) w₀
      g' w (x a) (fr a) hw (hfr _).1 hov k hk
    have hb : g'.b = toUnit _ ≫ gi.b := ((GlobalTheory.FieldRestrictionTest.isPullF_iff _ _ _).1 hP).1
    obtain ⟨τ, hτ⟩ := exists_gen_of_local (V := V) 𝔪.D.toPre.P.L 𝔪.D.toPre.P.isLB
      ![(η[𝔪.D.toPre.P.A]).left, gi.b.left] (DegPre.lineε 1)
    obtain ⟨u, hu⟩ := Sep.Frames.frame_unit_core hN gi.b (Sep.Frames.torsion_of_nsmul g' _ hb ho).2 hb w' hw' (by
      obtain ⟨o, h₁, h₂⟩ := ho
      exact GlobalTheory.T.torsion_frame_abelian_part_torsion_frame hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U _ w₀ ρ' hNW _ hN _ o h₁ h₂ _ _ _ hw' hov'
        (hmove _ _ _ _ _ (htf _) hfr' hval)) τ hτ
    have hif : IntTerm.IntFrm 𝔪.D.toPre gi.b w' (algebraMap V (FractionRing V) (u⁻¹ : Vˣ)) :=
      ⟨τ, hτ, fun z J hJ => by
        rw [hu z J hJ, ← _root_.mul_assoc, GlobalTheory.UT.CoefBasic.cst_eq, GlobalTheory.UT.CoefBasic.cst_eq, ← map_mul, ← map_mul,
          Units.inv_mul, map_one, map_one, _root_.one_mul]⟩
    obtain ⟨α, hα, hαu⟩ := hκ gi g' w' _ hP hw' hif (𝔪.e₈ mu) _ (hυ mu)
    refine ⟨u * α, ?_, fun h => u.isUnit.mul (hαu h)⟩
    have e : algebraMap V (FractionRing V) u * algebraMap V (FractionRing V) (u⁻¹ : Vˣ) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [← hco]
    simp only [map_mul] at hα ⊢
    linear_combination k * algebraMap V (FractionRing V) u * hα - k * coef s g' w' (𝔪.e₈ mu) * e

  let C := ↥(X₁.S.HH X₁.M z₁)
  let lab : C → X₁.S.Gam := Subtype.val
  obtain ⟨l, hl, hlf⟩ := GlobalTheory.T.exists_torsion_frame_eq_const_mul_integral_generator V hV 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U w₀ hw₀ ρ hρ _ hN
  have hint := GlobalTheory.T.dividingThetaConstants_generate_integral_torsion_labels g n F W Z i X₁ z₁ act x₀ hdiv V ev X m t δ 𝔪
  have hxb : ∀ (a) (xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A),
      xb.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫
        (X₁.ρ.pt a).left →
      xb.left = spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ (x a).left := by
    intro a xb h
    refine 𝔪.cart.1.hom_ext ?_ ?_
    · rw [h, Category.assoc, hx a, ← Category.assoc]
      congr 1
      rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl
    · rw [Category.assoc, Over.w, Over.w]
      change _ = _ ≫ Spec.map (𝟙 _)
      rw [Spec.map_id, Category.comp_id]; rfl
  have hyy : ∀ c, 𝔪.YY (lab c) 0 := fun c => (hint _).1 c.2
  choose p xb hp hq hxp using hyy
  have hp0 : ∀ c, (p c).y = 0 := fun c => (hp c).trans (map_zero _)
  choose h gi hh hgt hfe hext hpull using fun c => GlobalTheory.T.rationalTorsionPoint_lift_section_torusExtension V hV 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U _ hN (x (lab c)) (xb c) (p c)
    (hxb _ _ (hxp c)) (hp0 c) (hq c)
  choose g' hg' using fun c => GlobalTheory.FieldRestrictionTest.exists_isPullF (toUnit (TF (R := V) (FractionRing V))) (gi c)
  choose w hw hif hlies using fun c => GlobalTheory.T.sectionValue_integralPoint_eq_adicSum_terms V hV 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U w₀ hw₀ (x (lab c)) (fr (lab c)) (h c) (gi c)
    (g' c) l hl (hfe c) (hext c) (hg' c) (hlf _ _ _ (htf _) (hh c) (hext c))
  have htor : ∀ c, ∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g' c) o ∧ o.IsZero := fun c => by
    obtain ⟨o, ho, hz⟩ := hgt c
    obtain ⟨o', ho'⟩ := GlobalTheory.FieldRestrictionTest.exists_isPullF (toUnit (TF (R := V) (FractionRing V))) o
    exact ⟨o', GlobalTheory.FieldRestrictionTest.isNsmul_restrict (hg' c) ho' ho,
      GlobalTheory.FieldRestrictionTest.isZero_restrict ho' hz⟩
  have hb : ∀ c, (g' c).b = toUnit _ ≫ (gi c).b := fun c =>
    ((GlobalTheory.FieldRestrictionTest.isPullF_iff _ _ _).1 (hg' c)).1
  have hex : IntTerm.Exhausts 𝔪.D.toPre.P (X₁.S.r * X₁.S.N) fun c => (gi c).b := by
    refine GlobalTheory.T.torsionSections_exhaust_of_generic_geometric V _ _ hN C _ (fun c => (Sep.Frames.torsion_of_nsmul (g' c) _ (hb c) (htor c)).2) fun β hβ => ?_
    obtain ⟨y, hy, ⟨q, hq0, hqy⟩, H⟩ := GlobalTheory.T.geometricTorsionPoint_abelianPart_lies_under_classZero V hV 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U _ hN β hβ
    obtain ⟨a, ha⟩ := GlobalTheory.T.geometricTorsionPoint_genericFibre_member_has_label g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 y hy
    have hmem : a ∈ X₁.S.HH X₁.M z₁ := (hint a).2 ⟨q, y, hq0.trans (map_zero _).symm, hqy, ha⟩
    let c : C := ⟨a, hmem⟩
    have e : xb c = y := Over.OverMorphism.ext ((hxb _ _ (hxp c)).trans (hxb _ _ ha).symm)
    exact ⟨c, (H (p c) (hp0 c) (e ▸ hq c)).symm.trans ((GlobalTheory.FieldRestrictionTest.isPullF_iff _ _ _).1 (hpull c)).1⟩
  choose a hco hau using fun mu c => core (lab c) (gi c) (g' c) (w c) (hg' c) (htor c) (hw c) (hlies c) mu
  have hunit : ∃ c, IsUnit (a 0 c) :=
    (GlobalTheory.T.exists_torsionTranslate_thetaSection_unit V 𝔪.D.toPre θ hθ _ hN₂ hNu C _ hex (𝔪.D.toPre.c (𝔪.e₈ 0))).imp fun c hc => hau 0 c hc
  have hsum : ∀ c, ∃ S : V, 𝔪.yK ⟨X₁.S.th (lab c), X₁.S.th_mem _⟩ = k * κ * algebraMap V (FractionRing V) S ∧
      (IsUnit S ↔ IsUnit (a 0 c)) := fun c => by
    obtain ⟨S, hS, hm⟩ := GlobalTheory.T.adicSum_fractionField_eq_mul_integral_congr V _ (𝔪.e₈ 0) (coef s (g' c) (w c))
      (fun χ => υ (𝔪.e₈.symm χ) * mono W t δ (𝔪.e₈.symm χ) * a (𝔪.e₈.symm χ) c) (k * κ) _
      (fun χ => by rw [← hco, AddEquiv.apply_symm_apply])
      (fun χ hχ => Ideal.mul_mem_right _ _ (IntTerm.mem_of_psiCoord 𝔪.D (χ := 𝔪.e₈ (𝔪.e₈.symm χ))
        (by rwa [AddEquiv.apply_symm_apply, ← map_zero 𝔪.e₈]) (hυ _)))
      (hlies c 1 le_rfl (w c) (fun _ _ _ => (pow_one _).symm) (hw c) th s _ hs (hth _))
    refine ⟨S, hS, (IntTerm.isUnit_of_sub_mem hm).trans ?_⟩
    simp only [AddEquiv.symm_apply_apply, IntTerm.mono_zero, _root_.mul_one, Units.isUnit_units_mul]
  choose S hS hSu using hsum
  let c₀ : C := ⟨x₀, AddSubgroup.subset_closure hdiv⟩
  have hS0 : 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem _⟩ = k * κ * algebraMap V (FractionRing V) (S c₀) := hS c₀
  have hκ0 : k * κ ≠ 0 := left_ne_zero_of_mul (hS0 ▸ h0)
  have inj := IsFractionRing.injective V (FractionRing V)
  have hS₀ : IsUnit (S c₀) := by
    obtain ⟨c, hc⟩ := hunit
    obtain ⟨r, hr⟩ := hdv (lab c)
    rw [hS, hS0, mul_left_comm, ← map_mul] at hr
    have e := inj (mul_left_cancel₀ hκ0 hr)
    exact isUnit_of_mul_isUnit_right (e ▸ (hSu c).2 hc)
  obtain ⟨gi₁, hgi₁⟩ := exists_integral V hV 𝔪.D 𝔪.A 𝔪.G 𝔪.U _ hN (g₀ c₁) (hg₀ c₁).1
  obtain ⟨α, hα, -⟩ := core (lab₀ c₁) gi₁ (g₀ c₁) (ω₀ c₁) hgi₁ (hg₀ c₁).1 (hg₀ c₁).2.1 (hg₀ c₁).2.2 mu₁
  have e₁ := hT mu₁ c₁
  rw [hα, hS0, mul_left_comm, ← map_mul] at e₁
  have e₂ := inj (mul_left_cancel₀ hκ0 e₁)
  have hm : T mu₁ c₁ * S c₀ ∈ maximalIdeal V :=
    e₂ ▸ Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (𝔪.mono_mem hmu₁))
  exact (Ideal.mul_unit_mem_iff_mem _ hS₀).1 hm

end GlobalTheory.Poinc.Sep.HighTerms
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModelMemberTermMemMaximalIdealStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaModelMember_term_mem_maximalIdeal : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (m1 : ℕ) (t1 : Fin m1 → V1) (δ1 : Fin m1 → LinearMap.BilinForm ℤ Y1) (𝔪1 : UMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → Y1) → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C) (mu : Fin 8 → Y1), mu ≠ 0 → T mu c ∈ maximalIdeal V1 := by
  first | exact @GlobalTheory.Poinc.Sep.HighTerms.term_mem_maximalIdeal | exact GlobalTheory.Poinc.Sep.HighTerms.term_mem_maximalIdeal | (intros; apply GlobalTheory.Poinc.Sep.HighTerms.term_mem_maximalIdeal <;> assumption)
end
end
