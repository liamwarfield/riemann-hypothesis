module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmallIdealNeBot
namespace GlobalTheory.SmallPrimeIdeal

open NumberField

theorem norm_le_one_of_isIntegral {K : Type} [NormedField K] [IsUltrametricDist K] {y : K}
    (hy : IsIntegral ℤ y) : ‖y‖ ≤ 1 := by
  obtain ⟨p, hp, hpy⟩ := hy
  by_contra hlt
  rw [not_le] at hlt

  have heq : y ^ p.natDegree + ∑ i ∈ Finset.range p.natDegree, (p.coeff i : K) * y ^ i = 0 := by
    rw [hp.as_sum] at hpy
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X_pow] at hpy
    simp only [algebraMap_int_eq, eq_intCast] at hpy
    exact hpy
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
  · rw [h0] at heq
    simp at heq
  obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
    (Finset.nonempty_range_iff.mpr hpos.ne') (fun i => (p.coeff i : K) * y ^ i)
  have hnorm : ‖y‖ ^ p.natDegree = ‖∑ i ∈ Finset.range p.natDegree, (p.coeff i : K) * y ^ i‖ := by
    rw [← norm_pow, eq_neg_of_add_eq_zero_left heq, norm_neg]
  have hterm : ‖(p.coeff i : K) * y ^ i‖ < ‖y‖ ^ p.natDegree := by
    rw [norm_mul, norm_pow]
    calc ‖(p.coeff i : K)‖ * ‖y‖ ^ i ≤ 1 * ‖y‖ ^ i :=
          mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_intCast_le_one K _) (by positivity)
      _ = ‖y‖ ^ i := one_mul _
      _ < ‖y‖ ^ p.natDegree := pow_lt_pow_right₀ hlt (Finset.mem_range.mp hi)
  linarith

theorem norm_int_le_one {L K : Type} [Field L] [NormedField K] [IsUltrametricDist K]
    (a : L →+* K) (x : 𝓞 L) : ‖a (x : L)‖ ≤ 1 := by

  exact norm_le_one_of_isIntegral ((NumberField.RingOfIntegers.isIntegral_coe x).map a.toIntAlgHom)

def smallIdeal {L K : Type} [Field L] [NormedField K] [IsUltrametricDist K]
    (a : L →+* K) : Ideal (𝓞 L) where
  carrier := {x | ‖a (x : L)‖ < 1}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    have h : ‖a (x : L) + a (y : L)‖ ≤ max ‖a (x : L)‖ ‖a (y : L)‖ :=
      IsUltrametricDist.norm_add_le_max _ _
    have e : a ((x + y : 𝓞 L) : L) = a (x : L) + a (y : L) := by simp
    change ‖a ((x + y : 𝓞 L) : L)‖ < 1
    rw [e]
    exact lt_of_le_of_lt h (max_lt hx hy)
  smul_mem' := by
    intro c x hx
    have e : a ((c • x : 𝓞 L) : L) = a (c : L) * a (x : L) := by simp
    change ‖a ((c • x : 𝓞 L) : L)‖ < 1
    rw [e, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right (norm_int_le_one a c) (norm_nonneg _) hx

theorem mem_smallIdeal {L K : Type} [Field L] [NormedField K] [IsUltrametricDist K]
    (a : L →+* K) (x : 𝓞 L) : x ∈ smallIdeal a ↔ ‖a (x : L)‖ < 1 := by
  exact Iff.rfl

theorem norm_eq_one {L K : Type} [Field L] [NormedField K] [IsUltrametricDist K]
    (a : L →+* K) (x : 𝓞 L) (h : ¬ ‖a (x : L)‖ < 1) : ‖a (x : L)‖ = 1 := by
  exact le_antisymm (norm_int_le_one a x) (not_lt.mp h)

theorem smallIdeal_isPrime {L K : Type} [Field L] [NormedField K] [IsUltrametricDist K]
    (a : L →+* K) : (smallIdeal a).IsPrime := by
  refine ⟨?_, ?_⟩
  ·
    rw [Ideal.ne_top_iff_one, mem_smallIdeal]
    simp
  · intro x y hxy
    rw [mem_smallIdeal] at hxy
    rw [mem_smallIdeal, mem_smallIdeal]
    by_contra hc
    push Not at hc
    obtain ⟨hx, hy⟩ := hc
    have e : a ((x * y : 𝓞 L) : L) = a (x : L) * a (y : L) := by simp
    rw [e, norm_mul, norm_eq_one a x (not_lt.mpr hx), norm_eq_one a y (not_lt.mpr hy)] at hxy
    norm_num at hxy

theorem exists_local_dvd {L : Type} [Field L] [NumberField L] (P : Ideal (𝓞 L)) [P.IsPrime]
    (hP : P ≠ ⊥) (u v : 𝓞 L) :
    ∃ r s : 𝓞 L, s ∉ P ∧ (u * r = v * s ∨ v * r = u * s) := by

  let Rp := Localization.AtPrime P
  have : IsDiscreteValuationRing Rp :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) hP Rp
  have hinj : Function.Injective (algebraMap (𝓞 L) Rp) :=
    IsLocalization.injective Rp P.primeCompl_le_nonZeroDivisors
  rcases ValuationRing.dvd_total (algebraMap (𝓞 L) Rp u) (algebraMap (𝓞 L) Rp v) with ⟨c, hc⟩ | ⟨c, hc⟩
  · obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
    refine ⟨r, s, s.2, Or.inl (hinj ?_)⟩
    rw [map_mul, map_mul, hc, mul_assoc, IsLocalization.mk'_spec]
  · obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
    refine ⟨r, s, s.2, Or.inr (hinj ?_)⟩
    rw [map_mul, map_mul, hc, mul_assoc, IsLocalization.mk'_spec]

theorem smallIdeal_ne_bot {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime]
    (a : L →+* PadicAlgCl l) : smallIdeal a ≠ ⊥ := by

  intro hbot
  have hl : ((l : 𝓞 L)) ∈ smallIdeal a := by
    rw [mem_smallIdeal]
    have e : a ((l : 𝓞 L) : L) = (l : PadicAlgCl l) := by simp
    have hext := PadicAlgCl.norm_extends (p := l) (l : ℚ_[l])
    rw [map_natCast] at hext
    rw [e, hext, Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  rw [hbot, Ideal.mem_bot] at hl
  have h0 : ((l : 𝓞 L) : L) = 0 := by rw [hl]; simp
  exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h0)

theorem le_one_of_le_one {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime]
    (a b : L →+* PadicAlgCl l)
    (h : ∀ x : 𝓞 L, ‖a (x : L)‖ < 1 ↔ ‖b (x : L)‖ < 1) (x : L) (hx : ‖a x‖ ≤ 1) :
    ‖b x‖ ≤ 1 := by
  classical
  have hb : ∀ y : 𝓞 L, y ∈ smallIdeal a ↔ ‖b (y : L)‖ < 1 := fun y => (mem_smallIdeal a y).trans (h y)
  have := smallIdeal_isPrime a

  obtain ⟨u, w, hw, rfl⟩ := IsFractionRing.div_surjective (𝓞 L) x
  change ‖a ((u : L) / (w : L))‖ ≤ 1 at hx
  change ‖b ((u : L) / (w : L))‖ ≤ 1
  have hw0 : (w : L) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hw
    exact_mod_cast this

  obtain ⟨r, s, hs, hrs⟩ := exists_local_dvd (smallIdeal a) (smallIdeal_ne_bot a) u w
  have hs0 : (s : L) ≠ 0 := by
    intro h0
    apply hs
    have : s = 0 := by exact_mod_cast h0
    rw [this]
    exact (smallIdeal a).zero_mem
  have hbs : ‖b (s : L)‖ = 1 := norm_eq_one b s (fun hlt => hs ((hb s).mpr hlt))
  have has : ‖a (s : L)‖ = 1 := norm_eq_one a s (fun hlt => hs ((mem_smallIdeal a s).mpr hlt))
  rcases hrs with h1 | h1
  ·
    have h1' : (u : L) * r = w * s := by exact_mod_cast congrArg (fun z : 𝓞 L => (z : L)) h1
    have hr0 : (r : L) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h1'
      exact mul_ne_zero hw0 hs0 h1'.symm
    have e : (u : L) / w = s / r := by
      rw [div_eq_div_iff hw0 hr0]
      linear_combination h1'
    rw [e] at hx ⊢
    rw [map_div₀, norm_div, has] at hx
    have hpos : 0 < ‖a (r : L)‖ := norm_pos_iff.mpr ((map_ne_zero a).mpr hr0)
    have har : ¬ ‖a (r : L)‖ < 1 := by
      intro hlt
      rw [div_le_iff₀ hpos] at hx
      linarith
    have hbr : ‖b (r : L)‖ = 1 := norm_eq_one b r (fun hlt => har ((h r).mpr hlt))
    rw [map_div₀, norm_div, hbs, hbr, div_one]
  ·
    have h1' : (w : L) * r = u * s := by exact_mod_cast congrArg (fun z : 𝓞 L => (z : L)) h1
    have e : (u : L) / w = r / s := by
      rw [div_eq_div_iff hw0 hs0]
      linear_combination -h1'
    rw [e, map_div₀, norm_div, hbs, div_one]
    exact norm_int_le_one b r

theorem norm_le_one_iff {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact (Nat.Prime l)]
    (a b : L →+* Formalism.ConjugateSelfDual.Qbar l)
    (h : ∀ x : 𝓞 L, ‖a (x : L)‖ < (1 : ℝ) ↔ ‖b (x : L)‖ < (1 : ℝ)) (x : L) :
    ‖a x‖ ≤ (1 : ℝ) ↔ ‖b x‖ ≤ (1 : ℝ) := by
  exact ⟨le_one_of_le_one a b h x, le_one_of_le_one b a (fun y => (h y).symm) x⟩

end GlobalTheory.SmallPrimeIdeal
end

noncomputable section

namespace GlobalTheory.EigTie

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open Formalism.MainNotions.IntegralHeckeForms (HkIdx V0 Fm0 eG Eigsp)
open Formalism.MainNotions.BlochKatoReduction.Gen (goodE Tmat eps0 chiS)
open Formalism.L2.Host (HChar CharFrame embLL0)
open GlobalTheory.Triple (Reading embSide muBase heckeVal IsParam IsResidual FbAt jIdx)
open GlobalTheory.TripleGal (HkFrob)
open GlobalTheory.HeightCounting (RowSide)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE OnW)
open scoped TensorProduct

variable {D : D7}

section Sys

variable {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

def IsEigVec (i : X.Tw) (j : ℕ) (b : Bool) (ev : ℕ → PlE D.host → FractionRing (X.O i)) (x : Y.Fm i j b) : Prop :=
  x ∈ V0 Y i j b ∧ x ≠ 0 ∧ ∀ k P, HkIdx i k P → Y.hkF i j b k P x = ev k P • x

def IsEigSys (i : X.Tw) (j : ℕ) (b : Bool) (ev : ℕ → PlE D.host → FractionRing (X.O i)) : Prop :=
  ∃ x, IsEigVec Y i j b ev x

def sigEv {i : X.Tw} (s : X.Sig i) (k : ℕ) (P : PlE D.host) : FractionRing (X.O i) :=
  algebraMap (X.O i) (FractionRing (X.O i)) (X.hEig i s k P)

variable {Y} {i : X.Tw} {j : ℕ} {b : Bool}

end Sys

section Read

variable (X : NTw D.R D.host D.what₂ D.LL0 D.nd)

def fracMap (i : X.Tw) : FractionRing (X.O0 i) →+* FractionRing (X.O i) :=
  IsFractionRing.map (A := X.O0 i) (B := X.O i) (K := FractionRing (X.O0 i)) (L := FractionRing (X.O i)) (X.O_inj i)

def embO (i : X.Tw) (b : Bool) : ↥D.LL0 →+* FractionRing (X.O i) := (fracMap X i).comp (embSide X i b)

theorem fracMap_algebraMap (i : X.Tw) (x : X.O0 i) :
    fracMap X i (algebraMap (X.O0 i) (FractionRing (X.O0 i)) x) =
      algebraMap (X.O i) (FractionRing (X.O i)) (algebraMap (X.O0 i) (X.O i) x) :=
  by simp [fracMap, IsFractionRing.map]

structure CoefRead (i : X.Tw) (b : Bool) where

  F : Type
  [fld : Field F]

  e : ↥D.LL0 →+* F

  u : F →+* FractionRing (X.O i)

  toC : F →+* ℂ
  u_e : ∀ x, u (e x) = embO X i b x
  toC_e : ∀ x, toC (e x) = embLL0 D x

attribute [instance] CoefRead.fld

variable {X} {i : X.Tw} {b : Bool}

end Read

section Par

def IsRowPar (Rw : RowSide D) (σ : D.what₂.FT) (π : D.naut.CG D.R.r) : Prop :=
  IsParam σ π ∧ ∀ w, IsSplitPl D.host w → D.naut.locG π w = Rw.locR σ w

variable (C : CharFrame D) (Rw : RowSide D) {X : NTw D.R D.host D.what₂ D.LL0 D.nd}
  (Y : NExp D.R D.host D.what₂ D.LL0 D.nd X)

variable {C Rw Y} {i : X.Tw} {b : Bool}

end Par

section Res

variable (Rw : RowSide D)

def IsoInduces {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : D.what₂.places.Pl) : Prop :=
  ∀ x : D.what₂.LL, 0 ≤ D.what₂.places.val w x ↔ ‖ι.symm (D.what₂.embLL x)‖ ≤ 1

def TeichAt {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : D.what₂.places.Pl) (red : Zbar l →+* FbAt D w) : Prop :=
  ∀ k, l ≠ D.host.g k → ∀ (v : D.nd.PlG k) x, x ≠ 0 → ∀ z : Zbar l,
    (z : Qbar l) = ι.symm (D.ntypes.teichC k x) → red z = D.ntypes.iota k v w x

def ResAt {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : D.what₂.places.Pl) (red : Zbar l →+* FbAt D w) : Prop :=
  IsoInduces ι w ∧ TeichAt ι w red ∧
    ∀ σ π (r : GalE D →* GL (Fin D.R.r) (Qbar l)), D.nd.goodRow σ → OnW D σ → IsRowPar Rw σ π →
      IsGaloisRepOf D π l ι r → IsResidual ι r σ w red

end Res

def ResTied (D : D7) (Rw : RowSide D) : Prop :=
  ∀ w : D.what₂.places.Pl, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ (l : ℕ) [Fact l.Prime], D.what₂.places.resChar w = l →
    ∃ (ι : Qbar l ≃+* ℂ) (red : Zbar l →+* FbAt D w), ResAt Rw ι w red

section Bridge

theorem ball_of_int {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime] (a b : L →+* Qbar l)
    (h : ∀ x : 𝓞 L, ‖a x‖ < 1 ↔ ‖b x‖ < 1) (x : L) : ‖a x‖ ≤ 1 ↔ ‖b x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.SmallPrimeIdeal.norm_le_one_iff
  | exact _root_.GlobalTheory.SmallPrimeIdeal.norm_le_one_iff
  | (apply _root_.GlobalTheory.SmallPrimeIdeal.norm_le_one_iff <;> assumption)
  | (intros; apply _root_.GlobalTheory.SmallPrimeIdeal.norm_le_one_iff <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SmallPrimeIdeal.norm_le_one_iff <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SmallPrimeIdeal.norm_le_one_iff ..)

theorem val_pos_iff (w : D.what₂.places.Pl) {x : D.what₂.LL} (hx : x ≠ 0) :
    0 < D.what₂.places.val w x ↔ ¬ 0 ≤ D.what₂.places.val w x⁻¹ := by
  have h := (D.what₂.places.val w).map_mul x x⁻¹
  rw [mul_inv_cancel₀ hx, AddValuation.map_one, D.val_eq w x hx, D.val_eq w _ (inv_ne_zero hx)] at h
  rw [D.val_eq w x hx, D.val_eq w _ (inv_ne_zero hx)]
  norm_cast at h ⊢
  omega

theorem IsoInduces.lt_iff {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {w : D.what₂.places.Pl} (h : IsoInduces ι w)
    (x : D.what₂.LL) : 0 < D.what₂.places.val w x ↔ ‖ι.symm (D.what₂.embLL x)‖ < 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h0 : 0 < ‖ι.symm (D.what₂.embLL x)‖ := by simpa using hx
    rw [val_pos_iff w hx, h, map_inv₀, map_inv₀, norm_inv, inv_le_one₀ h0, not_le]

theorem resChar_eq {w : D.what₂.places.Pl} {l : ℕ} (hl : l.Prime) (h : 0 < D.what₂.places.val w (l : D.what₂.LL)) :
    D.what₂.places.resChar w = l := by
  by_contra hne
  have hp := D.what₂.places.resChar_prime w
  have h1 : 0 < D.what₂.places.val w ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by
    rw [D.what₂.places.val_resChar]
    exact_mod_cast D.what₂.places.ramIdx_pos w
  have hint : ∀ n : ℤ, 0 ≤ D.what₂.places.val w (n : D.what₂.LL) := fun n => by
    have hn : ∀ n : ℕ, 0 ≤ D.what₂.places.val w (n : D.what₂.LL) := fun n => by
      induction n with
      | zero => simp
      | succ n ih => rw [Nat.cast_succ]; exact (D.what₂.places.val w).map_le_add ih (by simp)
    obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
    · simpa using hn n
    · rw [Int.cast_neg, AddValuation.map_neg]; simpa using hn n
  obtain ⟨a, b, e⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hl).2 hne)
  have e' : (a : D.what₂.LL) * (D.what₂.places.resChar w : ℕ) + (b : D.what₂.LL) * l = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → D.what₂.LL) e
  have := (D.what₂.places.val w).map_lt_add (g := 0) (x := (a : D.what₂.LL) * (D.what₂.places.resChar w : ℕ))
    (y := (b : D.what₂.LL) * l) (by rw [AddValuation.map_mul]; exact h1.trans_le (le_add_of_nonneg_left (hint a)))
    (by rw [AddValuation.map_mul]; exact h.trans_le (le_add_of_nonneg_left (hint b)))
  rw [e', AddValuation.map_one] at this
  exact lt_irrefl _ this

variable {X : NTw D.R D.host D.what₂ D.LL0 D.nd} {i : X.Tw} {b : Bool}

theorem norm_lt_iff (ρ : Reading X i b) (z : FractionRing (X.O0 i)) :
    (∃ y ∈ IsLocalRing.maximalIdeal (X.O0 i), algebraMap (X.O0 i) (FractionRing (X.O0 i)) y = z) ↔ ‖ρ.κ z‖ < 1 := by
  obtain ⟨h1, h2, -⟩ := GlobalTheory.padicAlgCl_embedding_bounded_continuous (X.l i) (X.twistBaseCoefficientRing_isAdic i) (GlobalTheory.GalChar.toQ ρ.κ) ρ.κ_alg
  refine ⟨fun ⟨y, hy, e⟩ => e ▸ h2 y hy, fun h => ?_⟩
  rcases eq_or_ne z 0 with rfl | hz
  · exact ⟨0, zero_mem _, map_zero _⟩
  have h0 : 0 < ‖ρ.κ z‖ := by simpa using hz
  rcases ValuationRing.isInteger_or_isInteger (X.O0 i) z with ⟨y, e⟩ | ⟨y, e⟩
  · refine ⟨y, ?_, e⟩
    by_contra hy
    obtain ⟨u, rfl⟩ := IsLocalRing.notMem_maximalIdeal.1 hy
    have e1 : ‖GlobalTheory.GalChar.toQ ρ.κ u‖ * ‖GlobalTheory.GalChar.toQ ρ.κ (u⁻¹ : (X.O0 i)ˣ)‖ = 1 := by
      rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
    have e2 : ‖GlobalTheory.GalChar.toQ ρ.κ u‖ < 1 := by rw [← e] at h; exact h
    exact (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) e2 (h1 _)).ne e1
  · have := h1 y
    change ‖ρ.κ (algebraMap _ _ y)‖ ≤ 1 at this
    rw [e, map_inv₀, norm_inv, inv_le_one₀ h0] at this
    exact absurd h (not_lt.2 this)

theorem exists_reading_of_induces {b' : Bool} (ρ : Reading X i b') {ι : Qbar (X.l i) ≃+* ℂ} {w : D.what₂.places.Pl}
    (h : IsoInduces ι w) (hw : ∀ x : ↥D.LL0, 0 ≤ D.what₂.places.val w x ↔ ‖ρ.κ (embSide X i b x)‖ ≤ 1) :
    ∃ ρ' : Reading X i b, ρ'.ι = ι := by
  obtain ⟨g, hg⟩ := GlobalTheory.EmbUnitBallConj.exists_conj (X.l i) ↥D.LL0 (ρ.κ.comp (embSide X i b))
    (ι.symm.toRingHom.comp (embLL0 D)) fun x => (hw x).symm.trans (h x)
  refine ⟨⟨(g : Qbar (X.l i) →+* Qbar (X.l i)).comp ρ.κ, ι, fun z => ?_, fun x => ?_⟩, rfl⟩
  · rw [RingHom.comp_apply, ρ.κ_alg]
    exact g.commutes _
  · exact (congrArg ι (hg x)).trans (ι.apply_symm_apply _)

end Bridge

namespace Model

open Formalism.MainNotions.BlochKatoReduction (scalGL)

variable (D)


variable {D}

end Model

end GlobalTheory.EigTie

end
