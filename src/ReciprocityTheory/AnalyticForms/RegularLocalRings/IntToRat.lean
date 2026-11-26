module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChart

@[expose] public section

section -- merged from ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRat
section -- merged from ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatB
namespace ReciprocityTheory.AnForm.R.IntegerToRational

open MvPolynomial

variable {σ : Type} [Fintype σ]

noncomputable def eQ (x : PrimeSpectrum (MvPolynomial σ ℤ)) (h : ChZero x.asIdeal) :
    PrimeSpectrum (MvPolynomial σ ℚ) :=
  ⟨Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) x.asIdeal, map_isPrime x.asIdeal h⟩

lemma eQ_lt {x y : PrimeSpectrum (MvPolynomial σ ℤ)} (hx : ChZero x.asIdeal)
    (hy : ChZero y.asIdeal) (hxy : x < y) : eQ x hx < eQ y hy := by
  have hle : (eQ x hx).asIdeal ≤ (eQ y hy).asIdeal := by
    show Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) x.asIdeal ≤
      Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) y.asIdeal
    exact Ideal.map_mono (show x.asIdeal ≤ y.asIdeal from hxy.le)
  show (eQ x hx).asIdeal < (eQ y hy).asIdeal
  refine lt_of_le_of_ne hle ?_
  intro heq
  have h2 : (Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) x.asIdeal).comap
      (MvPolynomial.map (Int.castRingHom ℚ)) =
      (Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) y.asIdeal).comap
      (MvPolynomial.map (Int.castRingHom ℚ)) := congrArg (Ideal.comap _) heq
  rw [comap_map_eq x.asIdeal hx, comap_map_eq y.asIdeal hy] at h2
  exact (show x.asIdeal ≠ y.asIdeal from ne_of_lt hxy) h2

lemma length_le_coheight_eQ (s : LTSeries (PrimeSpectrum (MvPolynomial σ ℤ))) :
    ∀ z, s.head = z → ∀ h0 : ChZero z.asIdeal,
      (s.length : ℕ∞) ≤ Order.coheight (eQ z h0) + 1 := by
  induction s using RelSeries.inductionOn with
  | singleton x => intros; simp
  | cons t x hx ih =>
    intro z hz h0
    rw [RelSeries.head_cons] at hz
    subst hz
    simp only [RelSeries.cons_length, Nat.cast_add, Nat.cast_one]
    by_cases h1 : ChZero t.head.asIdeal
    · have h2 := ih t.head rfl h1
      have h3 := Order.coheight_add_one_le (eQ_lt h0 h1 hx)
      calc (t.length : ℕ∞) + 1 ≤ Order.coheight (eQ t.head h1) + 1 + 1 := add_le_add_left h2 1
        _ ≤ Order.coheight (eQ x h0) + 1 := add_le_add_left h3 1
    · have h2 : (t.length : ℕ∞) ≤ Order.coheight t.head := Order.length_le_coheight_head
      have h3 := dim_le_of_charP x.asIdeal t.head.asIdeal hx.le h0 h1
      rw [ringKrullDim_quotient_eq_coheight,
        ringKrullDim_quotient_eq_coheight (hI := map_isPrime _ h0)] at h3
      have h4 : Order.coheight t.head ≤ Order.coheight (eQ x h0) := WithBot.coe_le_coe.mp h3
      calc (t.length : ℕ∞) + 1 ≤ Order.coheight t.head + 1 := add_le_add_left h2 1
        _ ≤ Order.coheight (eQ x h0) + 1 := add_le_add_left h4 1

private lemma isJacobsonRing_int_regular_local_rings : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  refine le_antisymm ?_ Ideal.le_jacobson
  by_cases hb : P = ⊥
  · subst hb
    intro m hm
    rw [Ideal.mem_jacobson_bot] at hm
    rw [Ideal.mem_bot]
    have h1 := Int.isUnit_iff.mp (hm 1)
    have h2 := Int.isUnit_iff.mp (hm 2)
    omega
  · have hmax : P.IsMaximal := by
      first
        | exact Ideal.IsPrime.isMaximal hP hb
        | exact hP.isMaximal hb
        | exact Ideal.IsPrime.to_maximal_ideal hb
        | exact Ring.DimensionLEOne.maximalOfPrime hb hP
    exact sInf_le ⟨le_rfl, hmax⟩

private lemma not_isMaximal_of_chZero (Q : Ideal (MvPolynomial σ ℤ)) (hQ : ChZero Q) :
    ¬ Q.IsMaximal := by
  intro hmax
  haveI := hmax
  haveI := isJacobsonRing_int_regular_local_rings
  letI : Field (MvPolynomial σ ℤ ⧸ Q) := Ideal.Quotient.field Q
  have hint := MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing
    (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective
  have hfe : (Ideal.Quotient.mk Q).comp (MvPolynomial.C) =
      algebraMap ℤ (MvPolynomial σ ℤ ⧸ Q) := RingHom.ext_int _ _
  haveI : Algebra.IsIntegral ℤ (MvPolynomial σ ℤ ⧸ Q) := by
    constructor
    intro x
    have hx := hint x
    rw [hfe] at hx
    exact hx
  have hinj : Function.Injective (algebraMap ℤ (MvPolynomial σ ℤ ⧸ Q)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro m hm
    rw [← hfe, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] at hm
    exact hQ m hm
  have hF : IsField ℤ := isField_of_isIntegral_of_isField hinj
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient Q).mp hmax)
  obtain ⟨b, hb⟩ := hF.mul_inv_cancel (two_ne_zero : (2 : ℤ) ≠ 0)
  omega

lemma coheight_eQ_add_one_le (P : PrimeSpectrum (MvPolynomial σ ℤ)) (hP : ChZero P.asIdeal) :
    Order.coheight (eQ P hP) + 1 ≤ Order.coheight P := by
  let φ : MvPolynomial σ ℤ →+* MvPolynomial σ ℚ := MvPolynomial.map (Int.castRingHom ℚ)
  let g : PrimeSpectrum (MvPolynomial σ ℚ) → PrimeSpectrum (MvPolynomial σ ℤ) :=
    fun Q => ⟨Q.asIdeal.comap φ, inferInstance⟩
  have hg : StrictMono g := by
    intro a b hab
    show a.asIdeal.comap φ < b.asIdeal.comap φ
    exact comap_strictMono (show a.asIdeal < b.asIdeal from hab)
  have hg0 : g (eQ P hP) = P := PrimeSpectrum.ext (comap_map_eq P.asIdeal hP)
  have hup : ∀ L : PrimeSpectrum (MvPolynomial σ ℚ), ∃ M, g L < M := by
    intro L
    have hQ : ChZero (g L).asIdeal := chZero_comap L.asIdeal
    have hnm := not_isMaximal_of_chZero (g L).asIdeal hQ
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (g L).asIdeal (g L).isPrime.ne_top
    refine ⟨⟨M, hM.isPrime⟩, ?_⟩
    show (g L).asIdeal < M
    refine lt_of_le_of_ne hle ?_
    intro heq
    apply hnm
    rw [heq]
    exact hM
  have key : ∀ n : ℕ, (n : ℕ∞) ≤ Order.coheight (eQ P hP) →
      ((n + 1 : ℕ) : ℕ∞) ≤ Order.coheight P := by
    intro n hn
    obtain ⟨p, hph, hpl⟩ := Order.exists_series_of_le_coheight (eQ P hP) hn
    obtain ⟨M, hM⟩ := hup p.last
    have hlast : (p.map g hg).last < M := hM
    let q := (p.map g hg).snoc M hlast
    have hqh : q.head = P := by
      rw [RelSeries.head_snoc]
      show g p.head = P
      rw [hph]
      exact hg0
    have hql : q.length = n + 1 := by
      rw [← hpl]
      rfl
    rw [← hql, ← hqh]
    exact Order.length_le_coheight_head
  rcases eq_or_ne (Order.coheight (eQ P hP)) ⊤ with h | h
  · have htop : Order.coheight P = ⊤ := by
      by_contra hne
      have h1 := key (Order.coheight P).toNat (by rw [h]; exact le_top)
      have h2 : (((Order.coheight P).toNat + 1 : ℕ) : ℕ∞) ≤ ((Order.coheight P).toNat : ℕ∞) := by
        rw [ENat.coe_toNat hne]
        exact h1
      have h3 := (Nat.cast_le (α := ℕ∞)).mp h2
      omega
    rw [htop]
    exact le_top
  · have h1 := key (Order.coheight (eQ P hP)).toNat (by rw [ENat.coe_toNat h])
    rw [← ENat.coe_toNat h]
    exact_mod_cast h1

end ReciprocityTheory.AnForm.R.IntegerToRational
end

namespace ReciprocityTheory.AnForm.R

open MvPolynomial IntegerToRational

variable {σ : Type} [Fintype σ]

noncomputable def extQ (P : Ideal (MvPolynomial σ ℤ)) : Ideal (MvPolynomial σ ℚ) :=
  Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) P

theorem extQ_spec (P : Ideal (MvPolynomial σ ℤ)) [P.IsPrime]
    (hP : ∀ m : ℤ, (C m : MvPolynomial σ ℤ) ∈ P → m = 0) :
    (extQ P).IsPrime ∧ (extQ P).comap (MvPolynomial.map (Int.castRingHom ℚ)) = P ∧
      ringKrullDim (MvPolynomial σ ℚ ⧸ extQ P) + 1 = ringKrullDim (MvPolynomial σ ℤ ⧸ P) := by
  have hP' : ChZero P := hP
  haveI hI : (extQ P).IsPrime := map_isPrime P hP'
  refine ⟨hI, comap_map_eq P hP', ?_⟩
  have h1 := coheight_eQ_add_one_le (⟨P, inferInstance⟩ : PrimeSpectrum (MvPolynomial σ ℤ)) hP'
  have h2 : Order.coheight (⟨P, inferInstance⟩ : PrimeSpectrum (MvPolynomial σ ℤ)) ≤
      Order.coheight (eQ ⟨P, inferInstance⟩ hP') + 1 :=
    Order.coheight_le fun s hs => length_le_coheight_eQ s _ hs hP'
  have heq : Order.coheight (eQ ⟨P, inferInstance⟩ hP') + 1 =
      Order.coheight (⟨P, inferInstance⟩ : PrimeSpectrum (MvPolynomial σ ℤ)) :=
    le_antisymm h1 h2
  have hE : (⟨extQ P, hI⟩ : PrimeSpectrum (MvPolynomial σ ℚ)) = eQ ⟨P, inferInstance⟩ hP' := rfl
  rw [ringKrullDim_quotient_eq_coheight (extQ P), ringKrullDim_quotient_eq_coheight P, hE, ← heq]
  norm_cast

end ReciprocityTheory.AnForm.R
end

section -- merged from ReciprocityTheory.AnalyticForms.RegularLocalRings.IsOpenAlt
namespace ReciprocityTheory.AnForm.R

open MvPolynomial

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def conePts (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) : Set ((Σ k, ι k) → ℂ) :=
  {z | (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ ∀ f ∈ P, eval z f = 0}

def SameOrbit (z z' : (Σ k, ι k) → ℂ) : Prop :=
  ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = fun q => c q.1 * z' q

def affCoord (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun q => z q / z ⟨q.1, p q.1⟩

def IsMultiHomog (s : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ) : Prop :=
  ∀ m ∈ s.support, ∀ k, ∑ i, m ⟨k, i⟩ = a k

structure SncData {m : ℕ} (I bd : Ideal (MvPolynomial (Fin m) ℂ)) (p : Fin m → ℂ) (e rc : ℕ) where

  r : Fin e → MvPolynomial (Fin m) ℂ

  J : Finset (Fin e)

  h : MvPolynomial (Fin m) ℂ

  σ : Fin e → Option (Fin rc)
  σ_injOn : Set.InjOn σ J
  σ_eq_none : ∀ l, σ l = none ↔ l ∉ J
  span_eq : Ideal.span (Set.range fun l => algebraMap _ (locRing I p) (r l)) =
    Ideal.map (algebraMap _ (locRing I p)) (ptIdeal p)
  eval_h : eval p h ≠ 0
  mem_bd : h * ∏ l ∈ J, r l ∈ bd
  le_span : ∀ g ∈ bd, h * g ∈ Ideal.span {∏ l ∈ J, r l} ⊔ I


variable (ι) in
structure AlgRes (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ) where

  M : Type
  [top : TopologicalSpace M]
  [compact : CompactSpace M]
  [t2 : T2Space M]

  n : ℕ

  amb : Fin n → ℕ

  ideal : ∀ i, Ideal (MvPolynomial (Fin (amb i)) ℂ)

  src : Fin n → Set M
  isOpen_alt_bis : ∀ i, IsOpen (src i)
  cover : ∀ x, ∃ i, x ∈ src i

  coord : ∀ i, M → Fin (amb i) → ℂ
  isEmbedding : ∀ i, Topology.IsEmbedding fun y : src i => coord i y
  image : ∀ i, coord i '' src i = {y | ∀ h ∈ ideal i, eval y h = 0}

  trans : ∀ i j, ∀ x ∈ src i ∩ src j, ∃ (q : MvPolynomial (Fin (amb i)) ℂ)
    (F : Fin (amb j) → MvPolynomial (Fin (amb i)) ℂ), eval (coord i x) q ≠ 0 ∧
      ∀ y ∈ src i ∩ src j, eval (coord i y) q ≠ 0 →
        ∀ l, coord j y l * eval (coord i y) q = eval (coord i y) (F l)
  regular : ∀ i, ∀ x ∈ src i, IsRegularLocalRing (locRing (ideal i) (coord i x))
  dim : ∀ i, ∀ x ∈ src i, ringKrullDim (locRing (ideal i) (coord i x)) = e

  lift : ∀ i, (Σ k, ι k) → MvPolynomial (Fin (amb i)) ℂ
  lift_one : ∀ i, ∃ p : (k : K) → ι k, ∀ k, lift i ⟨k, p k⟩ = 1
  lift_mem : ∀ i, ∀ x ∈ src i, (fun q => eval (coord i x) (lift i q)) ∈ conePts P
  compat : ∀ i j, ∀ x ∈ src i ∩ src j,
    SameOrbit (fun q => eval (coord i x) (lift i q)) (fun q => eval (coord j x) (lift j q))
  surj : ∀ z ∈ conePts P, z ∉ conePts D →
    ∃ i, ∃ x ∈ src i, SameOrbit (fun q => eval (coord i x) (lift i q)) z
  inj : ∀ i j, ∀ x ∈ src i, ∀ x' ∈ src j, (fun q => eval (coord i x) (lift i q)) ∉ conePts D →
    SameOrbit (fun q => eval (coord i x) (lift i q)) (fun q => eval (coord j x') (lift j q)) →
      x = x'

  inv : ∀ i, ∀ x ∈ src i, (fun q => eval (coord i x) (lift i q)) ∉ conePts D →
    ∀ p : (k : K) → ι k, (∀ k, eval (coord i x) (lift i ⟨k, p k⟩) ≠ 0) →
      ∃ O : Set M, IsOpen O ∧ x ∈ O ∧ O ⊆ src i ∧ ∃ (q : MvPolynomial (Σ k, ι k) ℂ)
        (F : Fin (amb i) → MvPolynomial (Σ k, ι k) ℂ), ∀ y ∈ O,
          (∀ k, eval (coord i y) (lift i ⟨k, p k⟩) ≠ 0) ∧
          eval (affCoord p fun q => eval (coord i y) (lift i q)) q ≠ 0 ∧
          ∀ l, coord i y l * eval (affCoord p fun q => eval (coord i y) (lift i q)) q =
            eval (affCoord p fun q => eval (coord i y) (lift i q)) (F l)

  bd : ∀ i, Ideal (MvPolynomial (Fin (amb i)) ℂ)
  le_bd : ∀ i, ideal i ≤ bd i
  zero_bd : ∀ i, ∀ x ∈ src i,
    (∀ h ∈ bd i, eval (coord i x) h = 0) ↔ (fun q => eval (coord i x) (lift i q)) ∈ conePts D

  rc : ℕ

  comp : Fin rc → Set M

  sncAt : ∀ i, ∀ x ∈ src i, SncData (ideal i) (bd i) (coord i x) e rc

  comp_eq : ∀ i x (hx : x ∈ src i), ∃ O : Set M, IsOpen O ∧ x ∈ O ∧ O ⊆ src i ∧ ∀ k,
    comp k ∩ O = {y ∈ O | ∃ l, (sncAt i x hx).σ l = some k ∧ eval (coord i y) ((sncAt i x hx).r l) = 0}

  mult : ∀ (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ), IsMultiHomog f a → f ∉ P →
    (∀ z ∈ conePts P, eval z f = 0 → z ∈ conePts D) → ∃ m : Fin rc → ℕ, ∀ i x (hx : x ∈ src i),
      ∃ u : locRing (ideal i) (coord i x), IsUnit u ∧
        algebraMap _ (locRing (ideal i) (coord i x)) (bind₁ (lift i) f) =
          u * ∏ l ∈ (sncAt i x hx).J,
            algebraMap _ (locRing (ideal i) (coord i x)) ((sncAt i x hx).r l) ^ ((sncAt i x hx).σ l).elim 0 m

attribute [instance] AlgRes.top AlgRes.compact AlgRes.t2

end

end ReciprocityTheory.AnForm.R
end

section -- merged from ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeC
namespace ReciprocityTheory.AnForm.R

open MvPolynomial

variable {σ : Type} [Fintype σ]

noncomputable def extC (𝔭 : Ideal (MvPolynomial σ ℚ)) : Ideal (MvPolynomial σ ℂ) :=
  Ideal.map (MvPolynomial.map (algebraMap ℚ ℂ)) 𝔭

theorem comap_of_mem_minimalPrimes_extC (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ ℂ)) (hQ : Q ∈ (extC 𝔭).minimalPrimes) :
    Q.comap (MvPolynomial.map (algebraMap ℚ ℂ)) = 𝔭 := by
  let _ : Algebra (MvPolynomial σ ℚ) (MvPolynomial σ ℂ) := MvPolynomial.algebraMvPolynomial
  have hflat : Module.Flat (MvPolynomial σ ℚ) (MvPolynomial σ ℂ) :=
    BaseChangeC.flat_mvPolynomial_rat_complex
  have hQp : Q.IsPrime := hQ.1.1
  have hle : 𝔭 ≤ Q.comap (MvPolynomial.map (algebraMap ℚ ℂ)) := Ideal.map_le_iff_le_comap.mp hQ.1.2
  have hPp : (Q.comap (MvPolynomial.map (algebraMap ℚ ℂ))).IsPrime := Ideal.comap_isPrime _ Q
  have hlo : Q.LiesOver (Q.comap (MvPolynomial.map (algebraMap ℚ ℂ))) := ⟨rfl⟩
  obtain ⟨Q', hQ'le, hQ'p, hQ'lo⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := 𝔭) Q hle
  have hQ'over : Q'.comap (MvPolynomial.map (algebraMap ℚ ℂ)) = 𝔭 := hQ'lo.over.symm
  have hmapQ' : extC 𝔭 ≤ Q' := by
    unfold extC
    rw [Ideal.map_le_iff_le_comap, hQ'over]
  have hEq : Q = Q' := le_antisymm (hQ.2 ⟨hQ'p, hmapQ'⟩ hQ'le) hQ'le
  subst hEq
  exact hQ'over

theorem ringKrullDim_of_mem_minimalPrimes_extC (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ ℂ)) (hQ : Q ∈ (extC 𝔭).minimalPrimes) :
    ringKrullDim (MvPolynomial σ ℂ ⧸ Q) = ringKrullDim (MvPolynomial σ ℚ ⧸ 𝔭) := by
  have hQp : Q.IsPrime := hQ.1.1
  have hh := BaseChangeC.height_eq_of_mem_minimalPrimes_map 𝔭 Q hQ
  have h1 := BaseChangeC.height_add_ringKrullDim_quotient_fintype ℂ Q
  have h2 := BaseChangeC.height_add_ringKrullDim_quotient_fintype ℚ 𝔭
  rw [hh] at h1
  exact BaseChangeC.withBot_enat_cancel h1 h2

end ReciprocityTheory.AnForm.R
end

section -- merged from ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLocA
namespace ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section

variable {n : ℕ}

def ptQ (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) : Ideal (MvPolynomial (Fin n) ℂ ⧸ K) :=
  (ptIdeal p).map (Ideal.Quotient.mk K)

theorem mk_mem_ptQ {K : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin n → ℂ} (hK : K ≤ ptIdeal p)
    (f : MvPolynomial (Fin n) ℂ) : Ideal.Quotient.mk K f ∈ ptQ K p ↔ f ∈ ptIdeal p := by
  exact Ideal.mem_quotient_iff_mem hK

theorem ptQ_isPrime {K : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin n → ℂ} (hK : K ≤ ptIdeal p) :
    (ptQ K p).IsPrime := by
  haveI : (ptIdeal p).IsPrime := RingHom.ker_isPrime _
  exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hK)

theorem algebraMap_quot_mk (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (f : MvPolynomial (Fin n) ℂ) :
    algebraMap (MvPolynomial (Fin n) ℂ ⧸ K) (locRing K p) (Ideal.Quotient.mk K f) =
      algebraMap _ (locRing K p) f := by
  rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

theorem isLocalization_locRing {K : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin n → ℂ}
    (hK : K ≤ ptIdeal p) :
    letI := ptQ_isPrime hK; IsLocalization.AtPrime (locRing K p) (ptQ K p) := by
  letI := ptQ_isPrime hK
  have hM : Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ K) (ptIdeal p).primeCompl =
      (ptQ K p).primeCompl := by
    ext x
    constructor
    · rintro ⟨f, hf, rfl⟩
      rw [Ideal.mem_primeCompl_iff, Ideal.Quotient.algebraMap_eq, mk_mem_ptQ hK]
      exact hf
    · intro hx
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Ideal.mem_primeCompl_iff, mk_mem_ptQ hK] at hx
      exact ⟨f, hx, rfl⟩
  have h := IsLocalization.instQuotientIdealAlgebraMapSubmonoidMapRingHomAlgebraMap
    (ptIdeal p).primeCompl (locPt p) K
  rw [hM] at h
  exact h

theorem isLocalRing_locRing {K : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin n → ℂ}
    (hK : K ≤ ptIdeal p) : IsLocalRing (locRing K p) := by
  letI := ptQ_isPrime hK
  haveI := isLocalization_locRing hK
  exact IsLocalization.AtPrime.isLocalRing (locRing K p) (ptQ K p)

theorem maximalIdeal_locRing {K : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin n → ℂ}
    (hK : K ≤ ptIdeal p) [IsLocalRing (locRing K p)] :
    IsLocalRing.maximalIdeal (locRing K p) = (ptIdeal p).map (algebraMap _ (locRing K p)) := by
  letI := ptQ_isPrime hK
  haveI := isLocalization_locRing hK
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (ptQ K p) (locRing K p), ptQ, Ideal.map_map]
  congr 1

theorem le_ptIdeal_iff' (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) :
    K ≤ ptIdeal p ↔ ∀ h ∈ K, eval p h = 0 := by
  simp [ptIdeal, SetLike.le_def, RingHom.mem_ker]

end
end ReciprocityTheory.AnForm.R
end
