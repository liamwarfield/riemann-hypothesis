module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.IdealSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemberTermsIntegralUnitShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionKilledByIdealCharZero

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MUKerW
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.uKerW_of :
    KerU → PullKer → UKerW := by
  intro hKerU _ p _ D O _ _ _ _ f b N r w _ hstd M j c T hflat X g hg
  obtain ⟨⟨k, hck⟩, hmon, hact, -, -, ψ', hmon', h1, h2⟩ := T.isog
  subst hck
  have hw : w ≠ ⊤ := Ideal.IsMaximal.ne_top inferInstance
  haveI : Smooth M.s := M.smooth.smooth
  haveI : IsLocallyNoetherian M.X := LocallyOfFiniteType.isLocallyNoetherian M.s
  haveI : IsFinite T.s := T.fin
  haveI : IsLocallyNoetherian T.Y := LocallyOfFiniteType.isLocallyNoetherian T.s
  obtain ⟨hRep, -, hTors⟩ :=
    hKerU p D O b N r w hw hstd.ule T.Y (T.s ≫ M.s) T.o T.o' T.ψ ψ' k hmon hmon' hact h1 h2
  obtain ⟨K, i, -, -, hflatK, hiff⟩ := hRep
  have hiU : UKer r T.o T.ψ K i := (hiff K i).mp ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨y, rfl⟩ := (hiff X g).mpr hg
  intro a ha
  haveI := T.o.act.hom (algebraMap (𝓞 D.F) D.O a)
  have hpO : ∀ x : O, (p : O) * x = 0 → x = 0 := by
    intro x hx
    rcases mul_eq_zero.mp hx with h | h
    · exact absurd h (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out))
    · exact h
  have hpowi : (i ≫ T.o.act.act (algebraMap (𝓞 D.F) D.O a)) ^ p ^ k = 1 := by
    have h := map_pow (IsMonHom.monoidHom (T.o.act.act (algebraMap (𝓞 D.F) D.O a)) K) i (p ^ k)
    change (i ^ p ^ k) ≫ _ = (i ≫ _) ^ p ^ k at h
    rw [← h, hTors K i hiU]
    exact map_one (IsMonHom.monoidHom (T.o.act.act (algebraMap (𝓞 D.F) D.O a)) K)
  have key : i ≫ T.o.act.act (algebraMap (𝓞 D.F) D.O a) = 1 := by
    by_cases hk0 : k = 0
    · subst hk0
      simpa using hpowi
    apply OrdCount.eq_one_of_reg T.o.A T.o.ab _ (p ^ k)
    · intro U s hs
      haveI : Flat K.hom := hflatK
      haveI : Flat (T.s ≫ M.s) := hflat
      have hreg := pReg_of_flat (p := p) (K.hom ≫ T.s ≫ M.s) hpO U
      have hregk : ∀ n (t : Γ(K.left, U)), (p : Γ(K.left, U)) ^ n * t = 0 → t = 0 := by
        intro n
        induction n with
        | zero => intro t ht; simpa using ht
        | succ n ih =>
          intro t ht
          exact hreg _ (ih _ (by rw [← _root_.mul_assoc, ← _root_.pow_succ]; exact ht))
      push_cast at hs
      exact hregk k s hs
    · exact hpowi
    · intro k' _ _ hk z g'
      have hp' : (p : k') ≠ 0 := by
        intro h0
        apply hk
        push_cast
        rw [h0, zero_pow hk0]
      let φ : O →+* k' := (Spec.preimage (z ≫ T.s ≫ M.s)).hom
      haveI : CharZero k' := by
        apply charZero_of_injective_ringHom (f := φ)
        have hker : RingHom.ker φ = ⊥ := by
          by_contra hne
          have hmax := Ideal.IsPrime.isMaximal (RingHom.ker_isPrime φ) hne
          have heq := IsLocalRing.eq_maximalIdeal hmax
          have hmem : (p : O) ∈ RingHom.ker φ := heq ▸ hstd.pmem
          rw [RingHom.mem_ker, map_natCast] at hmem
          exact hp' hmem
        exact (RingHom.injective_iff_ker_eq_bot φ).mpr hker
      have hU : UKer r T.o T.ψ (Over.mk z) (g' ≫ i) := (hiff _ _).mp ⟨g', rfl⟩
      rw [← Category.assoc]
      exact (T.tj k' z).1 _ hU.1 hU.2 a ha
  rw [Category.assoc, key]
  simp
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MRankN
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.rankN_of :
    WVal → RankN := by
  intro hW p _ D O _ _ _ _ f b N r w _ hS M V _ _ _ _ hp x W
  obtain ⟨ρ, -, -, hρ3, -⟩ := hW p D O b N M w V x
  have hpO : (p : O) ∈ IsLocalRing.maximalIdeal O := hS.pmem
  have hK : CharZero (FractionRing V) := by
    let φ : O →+* V := (Spec.preimage (x ≫ M.s)).hom
    haveI : CharP (FractionRing V) (ringChar (FractionRing V)) := ringChar.charP _
    rcases CharP.char_is_prime_or_zero (FractionRing V) (ringChar (FractionRing V)) with hq | hq
    · exfalso
      have hqK : ((ringChar (FractionRing V) : ℕ) : FractionRing V) = 0 := ringChar.Nat.cast_ringChar
      have hqV : ((ringChar (FractionRing V) : ℕ) : V) = 0 := by
        apply IsFractionRing.injective V (FractionRing V)
        rw [map_natCast, map_zero]
        exact hqK
      by_cases hpq : ringChar (FractionRing V) = p
      · exact hp (hpq ▸ hqV)
      · have hcop : Nat.Coprime p (ringChar (FractionRing V)) :=
          (Nat.coprime_primes Fact.out hq).2 (Ne.symm hpq)
        have hu : IsUnit ((ringChar (FractionRing V) : ℕ) : O) := by
          by_contra hnu
          have hm : ((ringChar (FractionRing V) : ℕ) : O) ∈ IsLocalRing.maximalIdeal O :=
            (IsLocalRing.mem_maximalIdeal _).2 hnu
          obtain ⟨a, c, hac⟩ := (Nat.isCoprime_iff_coprime.2 hcop).intCast (R := O)
          simp only [Int.cast_natCast] at hac
          have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
            rw [← hac]
            exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpO) (Ideal.mul_mem_left _ _ hm)
          exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)
        have := (hu.map φ).ne_zero
        rw [map_natCast] at this
        exact this hqV
    · haveI := ringChar.of_eq hq
      exact CharP.charP_to_charZero (FractionRing V)
  have hpf : p ^ f ≠ 0 := pow_ne_zero f (Fact.out : Nat.Prime p).ne_zero
  have hw : w ≠ ⊥ := by
    intro h
    have := hS.norm
    rw [h, Ideal.absNorm_bot] at this
    exact hpf this.symm
  have hcard := CharZeroCount.card_killedBy_charZero p D O b N M.X M.s M.univ w hw (FractionRing V)
    (spMap (algebraMap V (FractionRing V)) ≫ x)
  let Φ : {g : Over.mk x ⟶ M.univ.A // KilledBy M.univ w g} →
      {h : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ x) ⟶ M.univ.A // KilledBy M.univ w h} :=
    fun g => ⟨ρ g.1, (hρ3 g.1).1 g.2⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · rintro ⟨g₁, hg₁⟩ ⟨g₂, hg₂⟩ he
      exact Subtype.ext (ρ.injective (congrArg Subtype.val he))
    · rintro ⟨h, hh⟩
      refine ⟨⟨ρ.symm h, (hρ3 _).2 (by simpa using hh)⟩, ?_⟩
      exact Subtype.ext (by simp [Φ])
  let Ψ : W.H → {g : Over.mk x ⟶ M.univ.A // KilledBy M.univ w g} :=
    fun h => ⟨W.pt h, (W.range _).1 ⟨h, rfl⟩⟩
  have hΨ : Function.Bijective Ψ := by
    constructor
    · intro a c hac
      exact W.inj (congrArg Subtype.val hac)
    · rintro ⟨g, hg⟩
      obtain ⟨h, rfl⟩ := (W.range g).2 hg
      exact ⟨h, rfl⟩
  have hH : Nat.card W.H = Ideal.absNorm w ^ D.n := by
    rw [Nat.card_eq_of_bijective _ (hΦ.comp hΨ), hcard, hS.m1, _root_.one_mul]
  have hnz : Ideal.absNorm w ≠ 0 := by rw [hS.norm]; exact hpf
  haveI : Finite W.H := Nat.finite_of_card_ne_zero (by rw [hH]; exact pow_ne_zero _ hnz)
  have hk : Nat.card (𝓞 D.F ⧸ w) = Ideal.absNorm w := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 D.F ⧸ w) := Nat.finite_of_card_ne_zero (by rw [hk]; exact hnz)
  have h2 : 2 ≤ Ideal.absNorm w := by
    rw [← hk]
    exact Finite.one_lt_card
  refine ⟨Module.Finite.of_finite, ?_⟩
  letI := Fintype.ofFinite W.H
  letI := Fintype.ofFinite (𝓞 D.F ⧸ w)
  have := Module.card_eq_pow_finrank (K := 𝓞 D.F ⧸ w) (V := W.H)
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hH, hk] at this
  exact (Nat.pow_right_injective h2 this).symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PowSuccSubMem
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem idem_mod {A : Type} [CommRing A] {P α β : A} {J : Ideal A}
    (h1 : β * α ∈ Ideal.span {P}) (h2 : α + β - 1 ∈ Ideal.span {P}) (hJ : Ideal.span {P} ≤ J) :
    β * β - β ∈ J := by
  have : β * β - β = β * (α + β - 1) - β * α := by ring
  rw [this]
  exact J.sub_mem (J.mul_mem_left _ (hJ h2)) (hJ h1)

private theorem pow_succ_sub_mem {A : Type} [CommRing A] {β : A} {J : Ideal A} (h : β * β - β ∈ J) (k : ℕ) :
    β ^ (k + 1) - β ∈ J := by
  induction k with
  | zero => simp
  | succ k ih =>
    have : β ^ (k + 1 + 1) - β = β * (β ^ (k + 1) - β) + (β * β - β) := by ring
    rw [this]
    exact J.add_mem (J.mul_mem_left _ ih) h

private theorem mem_of_pow_le {A : Type} [CommRing A] {P α β : A} {u J : Ideal A} {n k : ℕ} (hn : n ≠ 0)
    (h1 : β * α ∈ Ideal.span {P}) (h2 : α + β - 1 ∈ Ideal.span {P}) (h3 : β ∈ u ^ n)
    (hJ : Ideal.span {P} ≤ J) (hk : u ^ k ≤ J) : β ∈ J := by
  have hp := pow_succ_sub_mem (idem_mod h1 h2 hJ) k
  have hm : β ^ (k + 1) ∈ u ^ k := by
    have h4 : β ^ (k + 1) ∈ (u ^ n) ^ (k + 1) := Ideal.pow_mem_pow h3 _
    rw [← pow_mul] at h4
    refine Ideal.pow_le_pow_right ?_ h4
    have : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hn
    nlinarith
  have : β = β ^ (k + 1) - (β ^ (k + 1) - β) := by ring
  rw [this]
  exact J.sub_mem (hk hm) hp

private theorem pow_le_of_mem {A : Type} [CommRing A] {P α β : A} {u J : Ideal A} {n : ℕ}
    (h1 : ∀ a ∈ u ^ n, a * α ∈ Ideal.span {P}) (h2 : α + β - 1 ∈ Ideal.span {P})
    (hJ : Ideal.span {P} ≤ J) (hβ : β ∈ J) : u ^ n ≤ J := fun x hx => by
  have : x = x * α - x * (α + β - 1) + x * β := by ring
  rw [this]
  exact J.add_mem (J.sub_mem (hJ (h1 x hx)) (J.mul_mem_left _ (hJ h2))) (J.mul_mem_left _ hβ)

theorem UpperTheory.Gal.crystallineComparison.Mod.kerU_of :
    UElt → KerU := by
  intro hU p _ D R _ b N r w hw hu S _ s o o' ψ ψ' e hm hm' hlin h1 h2
  obtain ⟨α, hα1, hα2, hα3⟩ := hU p D r w hw hu e
  have hc0 : p ^ e ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  obtain ⟨hfin, hflat⟩ := GlobalTheory.T.isFinite_flat_abelianSchemeHom_of_quasiInverse S o.A o'.A o.ab o'.ab ψ ψ' (p ^ e) hc0 hm hm' h1 h2
  let ρ : 𝓞 D.F → (o.A ⟶ o.A) := fun a => o.act.act (algebraMap (𝓞 D.F) D.O a)
  have ρhom : ∀ a, IsMonHom (ρ a) := fun a => o.act.hom _
  have ρmul : ∀ a a', ρ (a * a') = ρ a ≫ ρ a' := fun a a' => by
    simp only [ρ]; rw [mul_comm, map_mul, o.act.mul]
  have ρadd : ∀ a a', ρ (a + a') = ρ a * ρ a' := fun a a' => by
    simp only [ρ]; rw [map_add (f := _), o.act.add]
  have ρ0 : ρ 0 = 1 := by
    have := ρadd 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have ρc : ρ ((p : 𝓞 D.F) ^ e) = 𝟙 o.A ^ (p ^ e) := by
    have : ((p : 𝓞 D.F) ^ e) = ((p ^ e : ℕ) : 𝓞 D.F) := by push_cast; rfl
    simp only [ρ]
    rw [this, map_natCast, GlobalTheory.IwLevel.HTTorsionFF.oActN_natCast]

  let I : ∀ {T : Over S}, (T ⟶ o.A) → Ideal (𝓞 D.F) := fun {T} z =>
    { carrier := {a | z ≫ ρ a = 1}
      add_mem' := fun {a a'} ha ha' => by
        haveI := ρhom a
        show z ≫ ρ (a + a') = 1
        rw [ρadd, MonObj.comp_mul, show z ≫ ρ a = 1 from ha, show z ≫ ρ a' = 1 from ha', _root_.mul_one]
      zero_mem' := by
        show z ≫ ρ 0 = 1
        rw [ρ0, MonObj.comp_one]
      smul_mem' := fun c a ha => by
        haveI := ρhom c
        show z ≫ ρ (c * a) = 1
        rw [mul_comm, ρmul, ← Category.assoc, show z ≫ ρ a = 1 from ha, MonObj.one_comp] }
  have memI : ∀ {T : Over S} (z : T ⟶ o.A) (a), a ∈ I z ↔ z ≫ ρ a = 1 := fun _ _ => Iff.rfl
  have kerP : ∀ {T : Over S} (z : T ⟶ o.A), z ≫ ψ = 1 → z ^ p ^ e = 1 := fun {T} z hz => by
    have : z ≫ ψ ≫ ψ' = 1 := by rw [← Category.assoc, hz, MonObj.one_comp]
    rwa [h1, MonObj.comp_pow, Category.comp_id] at this
  have spanI : ∀ {T : Over S} (z : T ⟶ o.A), z ≫ ψ = 1 → Ideal.span {(p : 𝓞 D.F) ^ e} ≤ I z := fun z hz => by
    rw [Ideal.span_singleton_le_iff_mem, memI, ρc, MonObj.comp_pow, Category.comp_id]
    exact kerP z hz
  have cong : ∀ {T : Over S} (z : T ⟶ o.A) (a a'), a - a' ∈ I z → z ≫ ρ a = z ≫ ρ a' := fun z a a' h => by
    haveI := ρhom a'
    haveI := ρhom (a - a')
    have : a = a' + (a - a') := by ring
    rw [this, ρadd, MonObj.comp_mul, show z ≫ ρ (a - a') = 1 from h, _root_.mul_one]
  set β := D.bar α with hβ
  have hβα : β * α ∈ Ideal.span {(p : 𝓞 D.F) ^ e} := hα1 β hα3
  obtain ⟨K, gK, i, -, hmono, hKfin, hKflat, hK⟩ := GlobalTheory.UPel.HT.ES.OrdCount.exists_idem_kernel S o.A o'.A ψ (ρ β) hm (ρhom β)
    hfin hflat (fun T z hz => ⟨by
      haveI := o'.act.hom (algebraMap (𝓞 D.F) D.O β)
      rw [Category.assoc, hlin, ← Category.assoc, hz, MonObj.one_comp], by
      rw [Category.assoc, ← ρmul]
      exact cong z _ _ (idem_mod hβα hα2 (spanI z hz))⟩)
  have key : ∀ (T : Over S) (g : T ⟶ o.A), (g ≫ ψ = 1 ∧ g ≫ ρ β = 1) ↔ UKer r o ψ T g := fun T g => by
    refine ⟨fun ⟨ha, hb⟩ => ⟨ha, e, fun a haI => pow_le_of_mem hα1 hα2 (spanI g ha) hb haI⟩, fun ⟨ha, k, hk⟩ => ⟨ha, ?_⟩⟩
    rcases Nat.eq_zero_or_pos e with rfl | he
    · have : (1 : 𝓞 D.F) ∈ I g := spanI g ha (by simp)
      exact Ideal.mem_of_one_mem this β
    · exact mem_of_pow_le he.ne' hβα hα2 hα3 (spanI g ha) (fun a haI => hk a haI)
  refine ⟨⟨K, i, hmono, hKfin, hKflat, fun T g => (hK T g).trans (key T g)⟩, fun T => ⟨?_, fun g h hg hh => ?_⟩,
    fun T g hg => kerP g hg.1⟩
  · exact (key T 1).1 ⟨by rw [MonObj.one_comp], by haveI := ρhom β; rw [MonObj.one_comp]⟩
  · obtain ⟨g1, g2⟩ := (key T g).2 hg
    obtain ⟨h1', h2'⟩ := (key T h).2 hh
    haveI := ρhom β
    refine (key T _).1 ⟨?_, ?_⟩
    · rw [← div_eq_mul_inv, GrpObj.div_comp, g1, h1', div_one]
    · rw [← div_eq_mul_inv, GrpObj.div_comp, g2, h2', div_one]
end
