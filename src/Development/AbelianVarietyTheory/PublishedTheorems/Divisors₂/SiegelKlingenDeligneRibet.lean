module

public import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes

namespace GlobalTheory.RayZeta

variable {K : Type} [Field K] [NumberField K]

def IsRayFun {α : Type} (𝔣 : Ideal (𝓞 K)) (ε : Ideal (𝓞 K) → α) : Prop :=
  ∀ I J, CoprimeTo K 𝔣 I → CoprimeTo K 𝔣 J → RayRel K 𝔣 I J → ε I = ε J

def IsRayL (𝔣 : Ideal (𝓞 K)) (ε : Ideal (𝓞 K) → ℚ) (L : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ L {1}ᶜ ∧ ∀ s : ℂ, 1 < s.re →
    HasSum (fun I : {I : Ideal (𝓞 K) // CoprimeTo K 𝔣 I} => (ε I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) (L s)

def IsRayZeta (𝔣 𝔞 : Ideal (𝓞 K)) (Z : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ Z {1}ᶜ ∧ ∀ s : ℂ, 1 < s.re →
    HasSum (fun I : {I : Ideal (𝓞 K) // CoprimeTo K 𝔣 I ∧ RayRel K 𝔣 I 𝔞} => ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) (Z s)

def IsRayValue (𝔣 : Ideal (𝓞 K)) (ε : Ideal (𝓞 K) → ℚ) (k : ℕ) (r : ℚ) : Prop :=
  ∃ L : ℂ → ℂ, IsRayL 𝔣 ε L ∧ L (1 - (k : ℂ)) = (r : ℂ)

def translate {α : Type} (𝔠 : Ideal (𝓞 K)) (ε : Ideal (𝓞 K) → α) : Ideal (𝓞 K) → α := fun I => ε (𝔠 * I)

def InZl (l : ℕ) [Fact l.Prime] (q : ℚ) : Prop := ‖(q : ℚ_[l])‖ ≤ 1

def powMod (K : Type) [Field K] [NumberField K] (l n : ℕ) : Ideal (𝓞 K) := Ideal.span {(l : 𝓞 K) ^ n}

end GlobalTheory.RayZeta

namespace GlobalTheory.Published

open GlobalTheory.RayZeta

def SiegelKlingen : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∀ ε : Ideal (𝓞 F) → ℚ, IsRayFun 𝔣 ε →
      ∃ L : ℂ → ℂ, IsRayL 𝔣 ε L ∧ ∀ k : ℕ, 1 ≤ k → ∃ r : ℚ, L (1 - (k : ℂ)) = (r : ℂ)

def DeligneRibet : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (l : ℕ) [Fact l.Prime] (n : ℕ), 1 ≤ n →
    ∀ ε : Ideal (𝓞 F) → ℚ, IsRayFun (powMod F l n) ε → (∀ I, CoprimeTo F (powMod F l n) I → InZl l (ε I)) →
      ∀ 𝔠 : Ideal (𝓞 F), CoprimeTo F (powMod F l n) 𝔠 → ∀ k : ℕ, 1 ≤ k → ∀ r r' : ℚ,
        IsRayValue (powMod F l n) ε k r → IsRayValue (powMod F l n) (translate 𝔠 ε) k r' →
          InZl l (r - (Ideal.absNorm 𝔠 : ℚ) ^ k * r')

def SiegelKlingenDeligneRibet : Prop := SiegelKlingen ∧ DeligneRibet

end GlobalTheory.Published

namespace GlobalTheory.RayZeta

variable {K : Type} [Field K] [NumberField K] {𝔣 : Ideal (𝓞 K)}

theorem IsRayL.eqOn {ε : Ideal (𝓞 K) → ℚ} {L L' : ℂ → ℂ} (h : IsRayL 𝔣 ε L) (h' : IsRayL 𝔣 ε L') : Set.EqOn L L' {1}ᶜ := by
  have ho : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num) 1).isPreconnected
  refine (h.1.analyticOnNhd ho).eqOn_of_preconnected_of_eventuallyEq (h'.1.analyticOnNhd ho) hc (z₀ := 2) (by norm_num) ?_
  have ho' : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [ho'.mem_nhds (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by simp)] with s hs
  exact (h.2 s hs).unique (h'.2 s hs)

theorem IsRayValue.eq {ε : Ideal (𝓞 K) → ℚ} {k : ℕ} {r : ℚ} (hk : 1 ≤ k) (h : IsRayValue 𝔣 ε k r) {L : ℂ → ℂ}
    (hL : IsRayL 𝔣 ε L) : L (1 - (k : ℂ)) = (r : ℂ) := by
  obtain ⟨L', hL', e⟩ := h
  have : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  rw [← e]
  exact hL.eqOn hL' (by simpa using this)

theorem IsRayValue.unique {ε : Ideal (𝓞 K) → ℚ} {k : ℕ} {r r' : ℚ} (hk : 1 ≤ k) (h : IsRayValue 𝔣 ε k r)
    (h' : IsRayValue 𝔣 ε k r') : r = r' := by
  obtain ⟨L, hL, e⟩ := h'
  have := h.eq hk hL
  rw [e] at this
  exact_mod_cast this.symm

theorem coprimeTo_mul {I J : Ideal (𝓞 K)} (hI : CoprimeTo K 𝔣 I) (hJ : CoprimeTo K 𝔣 J) : CoprimeTo K 𝔣 (I * J) :=
  ⟨mul_ne_zero hI.1 hJ.1, Ideal.isCoprime_iff_sup_eq.1
    ((Ideal.isCoprime_iff_sup_eq.2 hI.2).mul_left (Ideal.isCoprime_iff_sup_eq.2 hJ.2))⟩

theorem coprimeTo_powMod_iff {l n : ℕ} (hn : 1 ≤ n) {I : Ideal (𝓞 K)} :
    CoprimeTo K (powMod K l n) I ↔ CoprimeTo K (Ideal.span {(l : 𝓞 K)}) I := by
  simp only [CoprimeTo, powMod, ← Ideal.span_singleton_pow, ← Ideal.isCoprime_iff_sup_eq, IsCoprime.pow_right_iff hn]

theorem powMod_ne_bot {l : ℕ} (hl : l ≠ 0) (n : ℕ) : powMod K l n ≠ ⊥ := by
  simpa [powMod] using fun h => absurd h hl

theorem rayRel_refl (I : Ideal (𝓞 K)) : RayRel K 𝔣 I I :=
  ⟨1, 1, one_ne_zero, one_ne_zero, by simp, by simp, fun σ => by simp, rfl⟩

theorem rayRel_symm {I J : Ideal (𝓞 K)} (h : RayRel K 𝔣 I J) : RayRel K 𝔣 J I := by
  obtain ⟨a, b, ha, hb, ha', hb', hp, e⟩ := h
  exact ⟨b, a, hb, ha, hb', ha', fun σ => (hp σ).symm, e.symm⟩

theorem rayRel_trans {I J M : Ideal (𝓞 K)} (h : RayRel K 𝔣 I J) (h' : RayRel K 𝔣 J M) : RayRel K 𝔣 I M := by
  obtain ⟨a, b, ha, hb, ha', hb', hp, e⟩ := h
  obtain ⟨c, d, hc, hd, hc', hd', hq, e'⟩ := h'
  have hm : ∀ x y : 𝓞 K, x - 1 ∈ 𝔣 → y - 1 ∈ 𝔣 → x * y - 1 ∈ 𝔣 := fun x y hx hy => by
    rw [show x * y - 1 = x * (y - 1) + (x - 1) by ring]
    exact 𝔣.add_mem (𝔣.mul_mem_left _ hy) hx
  refine ⟨c * a, b * d, mul_ne_zero hc ha, mul_ne_zero hb hd, hm _ _ hc' ha', hm _ _ hb' hd', fun σ => ?_, ?_⟩
  · have e1 : ((c * a : 𝓞 K) : K) = (c : K) * (a : K) := rfl
    have e2 : ((b * d : 𝓞 K) : K) = (b : K) * (d : K) := rfl
    rw [e1, e2, map_mul, map_mul]
    exact ⟨mul_pos (hq σ).1 (hp σ).1, mul_pos (hp σ).2 (hq σ).2⟩
  · rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
      mul_assoc, e, mul_left_comm, e', mul_assoc]

theorem rayRel_mul_left (𝔠 : Ideal (𝓞 K)) {I J : Ideal (𝓞 K)} (h : RayRel K 𝔣 I J) : RayRel K 𝔣 (𝔠 * I) (𝔠 * J) := by
  obtain ⟨a, b, ha, hb, ha', hb', hp, e⟩ := h
  exact ⟨a, b, ha, hb, ha', hb', hp, by rw [mul_left_comm, e, mul_left_comm]⟩

theorem IsRayFun.translate {α : Type} {ε : Ideal (𝓞 K) → α} (h : IsRayFun 𝔣 ε) {𝔠 : Ideal (𝓞 K)} (hc : CoprimeTo K 𝔣 𝔠) :
    IsRayFun 𝔣 (translate 𝔠 ε) :=
  fun _ _ hI hJ e => h _ _ (coprimeTo_mul hc hI) (coprimeTo_mul hc hJ) (rayRel_mul_left 𝔠 e)


open Classical in
def rayIndicator (𝔣 𝔞 : Ideal (𝓞 K)) : Ideal (𝓞 K) → ℚ := fun I => if RayRel K 𝔣 I 𝔞 then 1 else 0

theorem isRayZeta_iff {𝔞 : Ideal (𝓞 K)} {Z : ℂ → ℂ} : IsRayZeta 𝔣 𝔞 Z ↔ IsRayL 𝔣 (rayIndicator 𝔣 𝔞) Z := by
  refine and_congr_right fun _ => forall₂_congr fun s _ => ?_
  let g : {I : Ideal (𝓞 K) // CoprimeTo K 𝔣 I ∧ RayRel K 𝔣 I 𝔞} → {I : Ideal (𝓞 K) // CoprimeTo K 𝔣 I} :=
    fun I => ⟨I.1, I.2.1⟩
  have hg : Function.Injective g := fun I J h => Subtype.ext (congrArg (fun x : {I : Ideal (𝓞 K) // CoprimeTo K 𝔣 I} => x.1) h)
  rw [← hg.hasSum_iff (f := fun I : {I : Ideal (𝓞 K) // CoprimeTo K 𝔣 I} =>
    (rayIndicator 𝔣 𝔞 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) fun I hI => by
      have : ¬ RayRel K 𝔣 I.1 𝔞 := fun h => hI ⟨⟨I.1, I.2, h⟩, rfl⟩
      simp [rayIndicator, this]]
  refine iff_of_eq (congrArg (HasSum · (Z s)) (funext fun I => ?_))
  simp [g, rayIndicator, I.2.2]

theorem inZl_iff {l : ℕ} [Fact l.Prime] {q : ℚ} : InZl l q ↔ 0 ≤ padicValRat l q := by
  rw [InZl, Padic.norm_le_one_iff_val_nonneg, Padic.valuation_ratCast]

end GlobalTheory.RayZeta

namespace GlobalTheory.Published

open GlobalTheory.RayZeta

end GlobalTheory.Published

namespace GlobalTheory.RayZeta

theorem absNorm_span_rat (n : ℕ) : Ideal.absNorm (Ideal.span {(n : 𝓞 ℚ)}) = n := by
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  simp

theorem exists_span_rat (I : Ideal (𝓞 ℚ)) : ∃ n : ℕ, I = Ideal.span {(n : 𝓞 ℚ)} := by
  haveI : IsPrincipalIdealRing (𝓞 ℚ) :=
    IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm.toRingHom Rat.ringOfIntegersEquiv.symm.surjective
  obtain ⟨a, rfl⟩ : ∃ a, I = Ideal.span {a} := ⟨_, (IsPrincipalIdealRing.principal I).span_singleton_generator.symm⟩
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, a = (m : 𝓞 ℚ) := ⟨Rat.ringOfIntegersEquiv a, by
    apply Rat.ringOfIntegersEquiv.injective; simp⟩
  refine ⟨m.natAbs, ?_⟩
  rcases Int.natAbs_eq m with h | h
  · rw [h]; simp
  · conv_lhs => rw [h]
    rw [Int.cast_neg, Ideal.span_singleton_neg, Int.cast_natCast]

theorem coprimeTo_span_rat (N n : ℕ) :
    CoprimeTo ℚ (Ideal.span {(N : 𝓞 ℚ)}) (Ideal.span {(n : 𝓞 ℚ)}) ↔ n ≠ 0 ∧ n.Coprime N := by
  rw [CoprimeTo, ← Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_span_singleton_iff, ← Nat.isCoprime_iff_coprime]
  refine and_congr (by simp) ⟨fun h => ?_, fun h => ?_⟩
  · simpa using h.map Rat.ringOfIntegersEquiv.toRingHom
  · simpa using h.map (Int.castRingHom (𝓞 ℚ))

theorem isRayL_rat_one (N : ℕ) [NeZero N] :
    IsRayL (Ideal.span {(N : 𝓞 ℚ)}) (fun _ => 1) (DirichletCharacter.LFunctionTrivChar N) := by
  refine ⟨fun s hs => (DirichletCharacter.differentiableAt_LFunction _ s (.inl hs)).differentiableWithinAt, fun s hs => ?_⟩
  let g : {I : Ideal (𝓞 ℚ) // CoprimeTo ℚ (Ideal.span {(N : 𝓞 ℚ)}) I} → ℕ := fun I => Ideal.absNorm I.1
  have hg : Function.Injective g := fun I J h => by
    obtain ⟨n, hn⟩ := exists_span_rat I.1
    obtain ⟨m, hm⟩ := exists_span_rat J.1
    simp only [g, hn, hm, absNorm_span_rat] at h
    exact Subtype.ext (by rw [hn, hm, h])
  have hr : ∀ n ∉ Set.range g, LSeries.term (fun n : ℕ => (1 : DirichletCharacter ℂ N) n) s n = 0 := fun n hn => by
    by_cases h0 : n = 0
    · simp [h0]
    · have : ¬ n.Coprime N := fun hc => hn ⟨⟨_, (coprimeTo_span_rat N n).2 ⟨h0, hc⟩⟩, absNorm_span_rat n⟩
      rw [LSeries.term_of_ne_zero h0, MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime]), zero_div]
  have := (hg.hasSum_iff hr).2 (DirichletCharacter.LSeriesSummable_of_one_lt_re (1 : DirichletCharacter ℂ N) hs).hasSum
  rw [DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_eq_LSeries _ hs, LSeries]
  convert this using 2 with I
  obtain ⟨I, hI⟩ := I
  obtain ⟨n, rfl⟩ := exists_span_rat I
  have h := (coprimeTo_span_rat N n).1 hI
  simp only [g, Function.comp, absNorm_span_rat]
  rw [LSeries.term_of_ne_zero h.1, MulChar.one_apply ((ZMod.isUnit_iff_coprime _ _).2 h.2), Complex.cpow_neg]
  simp

end GlobalTheory.RayZeta
end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

namespace GrothendieckMessing

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R}

theorem redMor {π : R →+* R₀} {A₀ : Over (Sp R₀)} [GrpObj A₀] {A : Over (Sp R)} [GrpObj A]
    {i : A₀.left ⟶ A.left} (h : IsGrpPullback A₀ A (spMap π) i) :
    GrpMor (dp0 R) (𝟙 _) A (dp0 R₀) (𝟙 _) A₀ π (spMap π) i :=
  GrpMor.of_isGrpPullback (isDPMorphism_of_eq_bot _ rfl _ _)
    ((Category.comp_id _).trans (Category.id_comp _).symm) h

def IsAdmissible {π : R →+* R₀} {A₀ : Over (Sp R₀)} [GrpObj A₀] {A : Over (Sp R)} [GrpObj A]
    {i : A₀.left ⟶ A.left} (h : IsGrpPullback A₀ A (spMap π) i) (F : Submodule R (HdR A)) : Prop :=
  (∃ N : Submodule R (HdR A), IsCompl F N) ∧
    ∀ y : HdR A₀, y ∈ Fil A₀ ↔ ∃ x ∈ F, (redMor h).Corr x y

variable (κ : DividedPowers I) (π : R →+* R₀)

def Canonical : Prop :=
  ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left)
    (h : IsGrpPullback A₀ A (spMap π) i), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    Function.Bijective (liftMor κ h).pull ∧ IsAdmissible h (Fil A)

def LiftObj : Prop :=
  ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left)
    (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' →
    SmoothOfRelativeDimension g A'.hom →
    ∀ F : Submodule R (HdR A'), IsAdmissible h' F →
      ∃ (A : Over (Sp R)) (_ : GrpObj A) (i : A₀.left ⟶ A.left)
        (h : IsGrpPullback A₀ A (spMap π) i), IsAbelianScheme A ∧
        SmoothOfRelativeDimension g A.hom ∧ liftFil κ h = F.comap (crysToDR κ h')

def LiftHom : Prop :=
  ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left)
    (h : IsGrpPullback A₀ A (spMap π) i), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
  ∀ (g' : ℕ) (B₀ : Over (Sp R₀)) [GrpObj B₀] (B : Over (Sp R)) [GrpObj B] (j : B₀.left ⟶ B.left)
    (k : IsGrpPullback B₀ B (spMap π) j), IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom →
  ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀], (∀ d ∈ liftFil κ h, push κ (spMap π) f₀ d ∈ liftFil κ k) →
    ∃! f : A ⟶ B, IsMonHom f ∧ i ≫ f.left = f₀.left ≫ j

def At : Prop := Canonical κ π ∧ LiftObj κ π ∧ LiftHom κ π

end GrothendieckMessing

def GrothendieckMessing : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (R : Type) [CommRing R], IsNilpotent (p : R) →
    ∀ (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (R₀ : Type) [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
      GrothendieckMessing.At κ π

namespace GrothendieckMessing

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {κ : DividedPowers I}
  {π : R →+* R₀} {g g' : ℕ} {A₀ B₀ : Over (Sp R₀)} [GrpObj A₀] [GrpObj B₀]
  {A A' B : Over (Sp R)} [GrpObj A] [GrpObj A'] [GrpObj B]
  {i : A₀.left ⟶ A.left} {i' : A₀.left ⟶ A'.left} {j : B₀.left ⟶ B.left}

theorem Canonical.crysToDR_bijective (H : Canonical κ π) (h : IsGrpPullback A₀ A (spMap π) i)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    Function.Bijective (crysToDR κ h) :=
  (LinearEquiv.ofBijective _ (H g A₀ A i h hA hg).1).dualMap.bijective

theorem LiftHom.exists_iff (H : LiftHom κ π) (h : IsGrpPullback A₀ A (spMap π) i)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (k : IsGrpPullback B₀ B (spMap π) j) (hB : IsAbelianScheme B)
    (hg' : SmoothOfRelativeDimension g' B.hom) (f₀ : A₀ ⟶ B₀) [IsMonHom f₀] :
    (∃ f : A ⟶ B, IsMonHom f ∧ i ≫ f.left = f₀.left ≫ j) ↔
      ∀ d ∈ liftFil κ h, push κ (spMap π) f₀ d ∈ liftFil κ k :=
  ⟨fun ⟨f, _, e⟩ _ hd ↦ push_mem_liftFil κ h k f₀ f e hd,
    fun e ↦ (H g A₀ A i h hA hg g' B₀ B j k hB hg' f₀ e).exists⟩

theorem LiftHom.unique (H : LiftHom κ π) (h : IsGrpPullback A₀ A (spMap π) i)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (k : IsGrpPullback B₀ B (spMap π) j) (hB : IsAbelianScheme B)
    (hg' : SmoothOfRelativeDimension g' B.hom) (f₀ : A₀ ⟶ B₀) [IsMonHom f₀] {f f' : A ⟶ B}
    [IsMonHom f] [IsMonHom f'] (e : i ≫ f.left = f₀.left ≫ j) (e' : i ≫ f'.left = f₀.left ≫ j) :
    f = f' :=
  (H g A₀ A i h hA hg g' B₀ B j k hB hg' f₀ fun _ hd ↦ push_mem_liftFil κ h k f₀ f e hd).unique
    ⟨inferInstance, e⟩ ⟨inferInstance, e'⟩

theorem LiftHom.exists_iso_iff (H : LiftHom κ π) (h : IsGrpPullback A₀ A (spMap π) i)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (h' : IsGrpPullback A₀ A' (spMap π) i') (hA' : IsAbelianScheme A')
    (hg' : SmoothOfRelativeDimension g' A'.hom) :
    (∃ e : A ≅ A', IsMonHom e.hom ∧ i ≫ e.hom.left = i') ↔ liftFil κ h = liftFil κ h' := by
  have hid : ∀ d : Crys κ (spMap π) A₀, push κ (spMap π) (𝟙 A₀) d = d := fun d ↦ by
    rw [push_id]; rfl
  constructor
  · rintro ⟨e, _, he⟩
    have he' : i' ≫ e.inv.left = i := by
      rw [← he, Category.assoc, ← Over.comp_left, e.hom_inv_id, Over.id_left, Category.comp_id]
    refine le_antisymm (fun d hd ↦ ?_) fun d hd ↦ ?_
    · exact hid d ▸ push_mem_liftFil κ h h' (𝟙 A₀) e.hom (by simpa using he) hd
    · exact hid d ▸ push_mem_liftFil κ h' h (𝟙 A₀) e.inv (by simpa using he') hd
  · intro e
    obtain ⟨f, _, ef⟩ := (H.exists_iff h hA hg h' hA' hg' (𝟙 A₀)).2 fun d hd ↦ by
      rw [hid, ← e]; exact hd
    obtain ⟨f', _, ef'⟩ := (H.exists_iff h' hA' hg' h hA hg (𝟙 A₀)).2 fun d hd ↦ by
      rw [hid, e]; exact hd
    rw [Over.id_left, Category.id_comp] at ef ef'
    refine ⟨⟨f, f', H.unique h hA hg h hA hg (𝟙 A₀) ?_ (by simp),
      H.unique h' hA' hg' h' hA' hg' (𝟙 A₀) ?_ (by simp)⟩, inferInstance, ef⟩
    · rw [Over.comp_left, ← Category.assoc, ef, ef', Over.id_left, Category.id_comp]
    · rw [Over.comp_left, ← Category.assoc, ef', ef, Over.id_left, Category.id_comp]

theorem crysRedMor (κ : DividedPowers I) (hI : RingHom.ker π = I) (A₀ : Over (Sp R₀)) [GrpObj A₀] :
    GrpMor κ (spMap π) A₀ (dp0 R₀) (𝟙 _) A₀ π (𝟙 _) (Over.Hom.left (𝟙 A₀)) := by
  apply GrpMor.of_hom _ (Category.id_comp _).symm (𝟙 A₀)
  have z : ∀ a ∈ I, π a = 0 := fun a ha ↦ RingHom.mem_ker.1 (hI ▸ ha)
  refine (isDPMorphism_iff _ _ _).2 ⟨Ideal.map_le_iff_le_comap.2 fun a ha ↦ z a ha, fun n hn a ha ↦ ?_⟩
  rw [z a ha, z _ (κ.dpow_mem hn ha), dpow_eval_zero _ hn]

theorem corr_crysToDR_iff (hI : RingHom.ker π = I) (h : IsGrpPullback A₀ A (spMap π) i)
    (hs : Function.Surjective (liftMor κ h).pull) (d : Crys κ (spMap π) A₀) (y : HdR A₀) :
    (redMor h).Corr (crysToDR κ h d) y ↔ (crysRedMor κ hI A₀).Corr d y := by
  have e : ∀ c, (crysRedMor κ hI A₀).pull ((liftMor κ h).pull c) = (redMor h).pull c := fun c ↦
    GrpMor.pull_pull _ _ _ (fun _ ↦ rfl) (by simp) c
  refine ⟨fun H c ↦ ?_, fun H c ↦ ?_⟩
  · obtain ⟨c, rfl⟩ := hs c
    rw [e]; exact H c
  · rw [← e]; exact H _

theorem canonical_of_abelianDeRham (P : AbelianDeRham) (hκ : IsNilDP κ)
    (hπ : Function.Surjective π) (hI : RingHom.ker π = I) : Canonical κ π := by
  intro g A₀ _ A _ i h hA hg
  obtain ⟨PF, PH, PB, PR, -⟩ := P
  letI : Algebra R R₀ := π.toAlgebra
  obtain ⟨-, ⟨N, hN⟩, -⟩ := PH R A g hA hg
  have hF : PrimitiveSubmodule A₀ = Submodule.span R₀ ((redMor h).pull '' (PrimitiveSubmodule A)) :=
    (PB R A g hA hg R₀ A₀ i h).2
  have := (PF.prim hA hg).2.1
  refine ⟨PR R A g hA hg I κ hκ R₀ π hπ hI A₀ i h, ⟨N.dualAnnihilator, ?_, ?_⟩, fun y ↦ ⟨?_, ?_⟩⟩
  · rw [disjoint_iff, Fil, ← Submodule.dualAnnihilator_sup_eq, hN.sup_eq_top,
      Submodule.dualAnnihilator_top]
  · refine codisjoint_iff_le_sup.2 fun x _ ↦ Submodule.mem_sup.2
      ⟨x ∘ₗ Submodule.projection _ _ hN.symm, ?_, x ∘ₗ Submodule.projection _ _ hN, ?_, ?_⟩
    · exact (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ by
        rw [LinearMap.comp_apply, (Submodule.projection_apply_eq_zero_iff hN.symm).2 hc, map_zero]
    · exact (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ by
        rw [LinearMap.comp_apply, (Submodule.projection_apply_eq_zero_iff hN).2 hc, map_zero]
    · ext c
      rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, ← map_add (f := _), add_comm,
        Submodule.projection_add_projection_eq_self hN]
  · intro hy
    let l : primDR A →ₗ[R] R₀ :=
      { toFun c := y ((redMor h).pull c)
        map_add' := by simp
        map_smul' r c := by rw [LinearMap.map_smulₛₗ, map_smul]; rfl }
    obtain ⟨x, hx⟩ := Module.projective_lifting_property (Algebra.linearMap R R₀) l hπ
    refine ⟨x ∘ₗ Submodule.projection _ _ hN.symm, (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ by
        rw [LinearMap.comp_apply, (Submodule.projection_apply_eq_zero_iff hN.symm).2 hc, map_zero], fun c ↦ ?_⟩
    have z : l (Submodule.projection _ _ hN c) = 0 := (Submodule.mem_dualAnnihilator _).1 hy _
      (hF ▸ Submodule.subset_span ⟨_, Submodule.projection_apply_mem hN c, rfl⟩)
    change l c = π (x _)
    conv_lhs => rw [← Submodule.projection_add_projection_eq_self hN c, map_add (f := _), z, zero_add, ← hx]
    rfl
  · rintro ⟨x, hx, e⟩
    rw [Fil, hF, Submodule.mem_dualAnnihilator]
    intro c hc
    refine (Submodule.span_le (p := LinearMap.ker y)).2 (fun c hc ↦ ?_) hc
    obtain ⟨c, hc, rfl⟩ := hc
    exact (e c).trans (by rw [(Submodule.mem_dualAnnihilator _).1 hx c hc, map_zero])

end GrothendieckMessing

end GlobalTheory.Published
end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDeRhamStructure
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def AbelianDeRhamFree : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom →
    Module.Finite R (FirstDeRham (A.hom ≫ 𝟙 _)) ∧ Module.Projective R (FirstDeRham (A.hom ≫ 𝟙 _)) ∧
    (∀ p : PrimeSpectrum R, Module.rankAtStalk (FirstDeRham (A.hom ≫ 𝟙 _)) p = 2 * g) ∧
    ∃ e : ⋀[R]^2 (FirstDeRham (A.hom ≫ 𝟙 _)) ≃ₗ[R] SecondDeRham (A.hom ≫ 𝟙 _),
      ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cup _ a b

def AbelianDeRhamStructure : Prop :=
  AbelianDeRhamFree ∧ AbelianDeRham.Hodge ∧ AbelianDeRham.BaseChange

end GlobalTheory.Published
end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DeRhamVectorExtension
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme)
open GlobalTheory.Cris (dp0)
open GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

namespace DeRhamVectorExtension

abbrev Family (p : ℕ) : Type 1 :=
  ∀ ⦃R : Type⦄ [CommRing R], IsNilpotent (p : R) → ∀ ⦃A : Over (Sp R)⦄ [GrpObj A],
    IsAbelianScheme A → ∀ ⦃G : PDivGroup p R⦄, G.TorsionTower A → (primDR A ≃ₗ[R] G.RigExt)

variable {p : ℕ} (e : Family p)

def Family.Natural : Prop :=
  ∀ ⦃R R' : Type⦄ [CommRing R] [CommRing R'] (hR : IsNilpotent (p : R)) (hR' : IsNilpotent (p : R'))
    ⦃A : Over (Sp R)⦄ [GrpObj A] ⦃A' : Over (Sp R')⦄ [GrpObj A']
    (hA : IsAbelianScheme A) (hA' : IsAbelianScheme A')
    ⦃G : PDivGroup p R⦄ ⦃G' : PDivGroup p R'⦄ (t : G.TorsionTower A) (t' : G'.TorsionTower A')
    ⦃σ : R →+* R'⦄ ⦃φ : A'.left ⟶ A.left⦄
    (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ) (c : primDR A),
    e hR' hA' t' (m.pull c) = (t'.semiHom t m).rig (e hR hA t c)

def Family.Filtered : Prop :=
  ∀ ⦃R : Type⦄ [CommRing R] (hR : IsNilpotent (p : R)) ⦃A : Over (Sp R)⦄ [GrpObj A]
    (hA : IsAbelianScheme A) ⦃G : PDivGroup p R⦄ (t : G.TorsionTower A),
    (PrimitiveSubmodule A).map (e hR hA t).toLinearMap = LinearMap.range G.rigOfOmega

def Family.Tangent : Prop :=
  ∀ ⦃R : Type⦄ [CommRing R] (hR : IsNilpotent (p : R)) ⦃A : Over (Sp R)⦄ [GrpObj A]
    (hA : IsAbelianScheme A) ⦃G : PDivGroup p R⦄ (t : G.TorsionTower A)
    (h : HdR A) (v : epsR R ⟶ A),
    IsLieImage h v ↔ t.LieCorr (G.lieUnivToLie ((e hR hA t).symm.dualMap h)) v

end DeRhamVectorExtension

def DeRhamVectorExtension : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∃ e : DeRhamVectorExtension.Family p, e.Natural ∧ e.Filtered ∧ e.Tangent

namespace DeRhamVectorExtension

variable {p : ℕ} {e : Family p} {R : Type} [CommRing R] (hR : IsNilpotent (p : R))
  {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (hA : IsAbelianScheme A) (hB : IsAbelianScheme B)
  {G H : PDivGroup p R} (t : G.TorsionTower A) (u : H.TorsionTower B)


variable [Fact p.Prime]

theorem Family.Natural.primPull (he : e.Natural) (f : A ⟶ B) [IsMonHom f] (c : primDR B) :
    e hR hA t (primPull (dp0 R) (𝟙 _) f c) = PDivGroup.rigExtMap (t.map u f) (e hR hB u c) := by
  have k := he hR hR hB hA u t (PDiv.grpMor_of_hom f) c
  rw [← PDivGroup.SemiHom.ofHom_rig]
  exact k

end DeRhamVectorExtension

end GlobalTheory.Published
end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDieudonne
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def AbelianDieudonne : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p],
    ∃ (M : ∀ (A : Over (Sp k)) [GrpObj A], ModuleCat.{0} (WittVector p k))
      (map : ∀ {A B : Over (Sp k)} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f],
        M A →ₗ[WittVector p k] M B)
      (F : ∀ (A : Over (Sp k)) [GrpObj A],
        M A →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] M A)
      (V : ∀ (A : Over (Sp k)) [GrpObj A],
        M A →ₛₗ[((WittVector.frobeniusEquiv p k).symm : WittVector p k →+* WittVector p k)] M A)
      (red : ∀ (A : Over (Sp k)) [GrpObj A],
        M A →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] HdR A),
      (∀ (A : Over (Sp k)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
        SmoothOfRelativeDimension g A.hom →
        Module.Free (WittVector p k) (M A) ∧ Module.Finite (WittVector p k) (M A) ∧
        Module.finrank (WittVector p k) (M A) = 2 * g ∧
        (∀ m, F A (V A m) = p • m) ∧ (∀ m, V A (F A m) = p • m) ∧
        Function.Surjective (red A) ∧ (∀ m, red A m = 0 ↔ ∃ n, m = p • n) ∧
        (∀ h, h ∈ Fil A ↔ ∃ m, h = red A (V A m)) ∧
        map (𝟙 A) = LinearMap.id) ∧
      (∀ (A B : Over (Sp k)) [GrpObj A] [GrpObj B], IsAbelianScheme A → IsAbelianScheme B →
        (∀ (f : A ⟶ B) [IsMonHom f] (m : M A),
          map f (F A m) = F B (map f m) ∧ map f (V A m) = V B (map f m) ∧
          red B (map f m) = push (dp0 k) (𝟙 _) f (red A m)) ∧
        ∀ (f g : A ⟶ B) [IsMonHom f] [IsMonHom g] [IsMonHom (f * g)],
          map (f * g) = map f + map g) ∧
      ∀ (A B C : Over (Sp k)) [GrpObj A] [GrpObj B] [GrpObj C], IsAbelianScheme A →
        IsAbelianScheme B → IsAbelianScheme C →
        ∀ (f : A ⟶ B) (g : B ⟶ C) [IsMonHom f] [IsMonHom g], map (f ≫ g) = map g ∘ₗ map f

namespace AbelianDieudonne

end AbelianDieudonne

end GlobalTheory.Published
end
end
