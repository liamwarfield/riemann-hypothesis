module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SubFamilyTwistSt

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrictionLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Local

variable (k : Type u) [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} (x : Fin (N + 1) → Ω) (y : Fin (N + 1) → K')

def locAt : Set Ω :=
  {a | ∃ (f s : Poly k N) (e : ℕ), f.IsHomogeneous e ∧ s.IsHomogeneous e ∧ aeval y s ≠ 0 ∧
    a = aeval x f / aeval x s}


open Classical in
def redAt (a : Ω) : K' :=
  if h : ∃ (p : Poly k N × Poly k N) (e : ℕ), p.1.IsHomogeneous e ∧ p.2.IsHomogeneous e ∧
      aeval y p.2 ≠ 0 ∧ a = aeval x p.1 / aeval x p.2
  then aeval y h.choose.1 / aeval y h.choose.2 else 0

variable {k x y}

theorem aeval_ne_zero_of_primeOf_le (hsp : primeOf (S := k) x ≤ primeOf (S := k) y)
    {s : Poly k N} {e : ℕ} (hs : s.IsHomogeneous e) (h : aeval y s ≠ 0) : aeval x s ≠ 0 := fun h0 =>
  h ((mem_primeOf_of_isHomogeneous y hs).mp (hsp ((mem_primeOf_of_isHomogeneous x hs).mpr h0)))

theorem mem_locAt {f s : Poly k N} {e : ℕ} (hf : f.IsHomogeneous e) (hs : s.IsHomogeneous e)
    (h : aeval y s ≠ 0) : aeval x f / aeval x s ∈ locAt k x y :=
  ⟨f, s, e, hf, hs, h, rfl⟩

variable (hsp : primeOf (S := k) x ≤ primeOf (S := k) y)
include hsp

theorem redAt_eq {f s : Poly k N} {e : ℕ} (hf : f.IsHomogeneous e) (hs : s.IsHomogeneous e)
    (h : aeval y s ≠ 0) : redAt k x y (aeval x f / aeval x s) = aeval y f / aeval y s := by
  have hex : ∃ (p : Poly k N × Poly k N) (e : ℕ), p.1.IsHomogeneous e ∧ p.2.IsHomogeneous e ∧
      aeval y p.2 ≠ 0 ∧ aeval x f / aeval x s = aeval x p.1 / aeval x p.2 :=
    ⟨(f, s), e, hf, hs, h, rfl⟩
  rw [redAt, dite_eq_left hex]
  obtain ⟨e', hf', hs', h', heq⟩ := hex.choose_spec
  have hx := aeval_ne_zero_of_primeOf_le hsp hs h
  have hx' := aeval_ne_zero_of_primeOf_le hsp hs' h'
  rw [div_eq_div_iff hx hx'] at heq
  have hhom : (f * hex.choose.2 - hex.choose.1 * s).IsHomogeneous (e + e') := by
    refine (hf.mul hs').sub ?_
    rw [add_comm e e']; exact hf'.mul hs
  have hmem : f * hex.choose.2 - hex.choose.1 * s ∈ primeOf (S := k) x := by
    rw [mem_primeOf_of_isHomogeneous x hhom]
    simp only [map_sub, map_mul, heq, sub_self]
  have hy := (mem_primeOf_of_isHomogeneous y hhom).mp (hsp hmem)
  simp only [map_sub, map_mul] at hy
  rw [div_eq_div_iff h' h]
  linear_combination -hy

theorem locAt_algebraMap (c : k) :
    algebraMap k Ω c ∈ locAt k x y ∧ redAt k x y (algebraMap k Ω c) = algebraMap k K' c := by
  have h1 : aeval y (1 : Poly k N) ≠ 0 := by simp
  have hc : algebraMap k Ω c = aeval x (C c : Poly k N) / aeval x (1 : Poly k N) := by
    simp
  rw [hc]
  refine ⟨mem_locAt (isHomogeneous_C _ c) (isHomogeneous_one _ _) h1, ?_⟩
  rw [redAt_eq hsp (isHomogeneous_C _ c) (isHomogeneous_one _ _) h1]
  simp

theorem locAt_zero : (0 : Ω) ∈ locAt k x y ∧ redAt k x y (0 : Ω) = 0 := by
  simpa using locAt_algebraMap hsp (0 : k)

theorem locAt_one : (1 : Ω) ∈ locAt k x y ∧ redAt k x y (1 : Ω) = 1 := by
  simpa using locAt_algebraMap hsp (1 : k)

theorem locAt_add {a b : Ω} (ha : a ∈ locAt k x y) (hb : b ∈ locAt k x y) :
    a + b ∈ locAt k x y ∧ redAt k x y (a + b) = redAt k x y a + redAt k x y b := by
  obtain ⟨f, s, e, hf, hs, hsy, rfl⟩ := ha
  obtain ⟨f', s', e', hf', hs', hsy', rfl⟩ := hb
  have hsx := aeval_ne_zero_of_primeOf_le hsp hs hsy
  have hsx' := aeval_ne_zero_of_primeOf_le hsp hs' hsy'
  have hhom : (f * s' + s * f').IsHomogeneous (e + e') := (hf.mul hs').add (hs.mul hf')
  have hsum : aeval x f / aeval x s + aeval x f' / aeval x s' =
      aeval x (f * s' + s * f') / aeval x (s * s') := by
    rw [div_add_div _ _ hsx hsx']; simp only [map_add (f := _), map_mul]
  have hss : aeval y (s * s') ≠ 0 := by rw [map_mul]; exact mul_ne_zero hsy hsy'
  rw [hsum]
  refine ⟨mem_locAt hhom (hs.mul hs') hss, ?_⟩
  rw [redAt_eq hsp hhom (hs.mul hs') hss, redAt_eq hsp hf hs hsy, redAt_eq hsp hf' hs' hsy',
    div_add_div _ _ hsy hsy']
  simp only [map_add (f := _), map_mul]

theorem locAt_mul {a b : Ω} (ha : a ∈ locAt k x y) (hb : b ∈ locAt k x y) :
    a * b ∈ locAt k x y ∧ redAt k x y (a * b) = redAt k x y a * redAt k x y b := by
  obtain ⟨f, s, e, hf, hs, hsy, rfl⟩ := ha
  obtain ⟨f', s', e', hf', hs', hsy', rfl⟩ := hb
  have hprod : aeval x f / aeval x s * (aeval x f' / aeval x s') =
      aeval x (f * f') / aeval x (s * s') := by
    rw [div_mul_div_comm]; simp only [map_mul]
  have hss : aeval y (s * s') ≠ 0 := by rw [map_mul]; exact mul_ne_zero hsy hsy'
  rw [hprod]
  refine ⟨mem_locAt (hf.mul hf') (hs.mul hs') hss, ?_⟩
  rw [redAt_eq hsp (hf.mul hf') (hs.mul hs') hss, redAt_eq hsp hf hs hsy, redAt_eq hsp hf' hs' hsy',
    div_mul_div_comm]
  simp only [map_mul]

theorem locAt_pow {a : Ω} (ha : a ∈ locAt k x y) (n : ℕ) :
    a ^ n ∈ locAt k x y ∧ redAt k x y (a ^ n) = redAt k x y a ^ n := by
  induction n with
  | zero => simpa using locAt_one hsp
  | succ n ih =>
    obtain ⟨h1, h2⟩ := locAt_mul hsp ih.1 ha
    rw [pow_succ, pow_succ]
    exact ⟨h1, by rw [h2, ih.2]⟩

theorem locAt_sum {ι : Type*} (s : Finset ι) (a : ι → Ω) (ha : ∀ i ∈ s, a i ∈ locAt k x y) :
    ∑ i ∈ s, a i ∈ locAt k x y ∧ redAt k x y (∑ i ∈ s, a i) = ∑ i ∈ s, redAt k x y (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using locAt_zero hsp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    obtain ⟨h1, h2⟩ := ih fun j hj => ha j (Finset.mem_insert_of_mem hj)
    obtain ⟨h3, h4⟩ := locAt_add hsp (ha i (Finset.mem_insert_self i s)) h1
    exact ⟨h3, by rw [h4, h2]⟩

theorem locAt_inv {a : Ω} (ha : a ∈ locAt k x y) (hr : redAt k x y a ≠ 0) :
    a ≠ 0 ∧ a⁻¹ ∈ locAt k x y ∧ redAt k x y a⁻¹ = (redAt k x y a)⁻¹ := by
  obtain ⟨f, s, e, hf, hs, hsy, rfl⟩ := ha
  rw [redAt_eq hsp hf hs hsy] at hr
  have hfy : aeval y f ≠ 0 := fun h => hr (by rw [h, zero_div])
  have hfx := aeval_ne_zero_of_primeOf_le hsp hf hfy
  have hsx := aeval_ne_zero_of_primeOf_le hsp hs hsy
  refine ⟨div_ne_zero hfx hsx, by rw [inv_div]; exact mem_locAt hs hf hfy, ?_⟩
  rw [inv_div, redAt_eq hsp hs hf hfy, redAt_eq hsp hf hs hsy, inv_div]

theorem locAt_div {a b : Ω} (ha : a ∈ locAt k x y) (hb : b ∈ locAt k x y) (hr : redAt k x y b ≠ 0) :
    a / b ∈ locAt k x y ∧ redAt k x y (a / b) = redAt k x y a / redAt k x y b := by
  obtain ⟨-, h1, h2⟩ := locAt_inv hsp hb hr
  obtain ⟨h3, h4⟩ := locAt_mul hsp ha h1
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact ⟨h3, by rw [h4, h2]⟩

theorem chartRing_sub_locAt (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (I : Chart y) {a : Ω}
    (ha : a ∈ chartRing k x (liftChart hxy I)) :
    a ∈ locAt k x y ∧ redAt k x y a ∈ chartRing k y I := by
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := ha
  have hsy : aeval y s ≠ 0 := eval_ne_zero_of_mem_monos I hs
  exact ⟨mem_locAt hf hse hsy, by rw [redAt_eq hsp hf hse hsy]; exact ⟨f, s, e, hs, hf, hse, rfl⟩⟩

theorem exists_redAt_eq (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (I : Chart y) {c : K'}
    (hc : c ∈ chartRing k y I) :
    ∃ a ∈ chartRing k x (liftChart hxy I), redAt k x y a = c := by
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := hc
  exact ⟨aeval x f / aeval x s, ⟨f, s, e, hs, hf, hse, rfl⟩,
    redAt_eq hsp hf hse (eval_ne_zero_of_mem_monos I hs)⟩

end Local

section Specialize

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ}

theorem primeOf_le_primeOf_of_algHom {x : Fin (N + 1) → Ω} {j : Fin (N + 1)} (hj : x j ≠ 0)
    (ψ : chartRing k x (singleChart hj) →ₐ[k] K') :
    primeOf (S := k) x ≤ primeOf (S := k) (fun i => ψ (ratio hj i)) := by
  have key : ∀ {B : Type w} [CommRing B] [Algebra k B]
      (φ : chartRing k x (singleChart hj) →ₐ[k] B)
      (g : Poly k N), φ (aeval (ratio (S := k) hj) g) = aeval (fun i => φ (ratio hj i)) g := by
    intro B _ _ φ g
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  intro f hf
  have hcomp : ∀ d, homogeneousComponent d f ∈ primeOf (S := k) (fun i => ψ (ratio hj i)) := by
    intro d
    have hg := homogeneousComponent_isHomogeneous d f
    have h0 : aeval x (homogeneousComponent d f) = 0 :=
      (mem_primeOf_of_isHomogeneous x hg).mp (homogeneousComponent_mem_primeOf x hf d)
    rw [mem_primeOf_of_isHomogeneous _ hg, ← key]
    have hval : aeval (ratio (S := k) hj) (homogeneousComponent d f) = 0 := by
      apply Subtype.ext
      have := key (chartRing k x (singleChart hj)).val (homogeneousComponent d f)
      simp only [Subalgebra.coe_val] at this
      rw [this, ZeroMemClass.coe_zero]
      change aeval (fun l => x l / x j) (homogeneousComponent d f) = 0
      rw [aeval_div_of_isHomogeneous hg j, h0, zero_div]
    rw [hval, map_zero]
  rw [← sum_homogeneousComponent f]
  exact Ideal.sum_mem _ fun d _ => hcomp d

theorem algHom_ratio_self {x : Fin (N + 1) → Ω} {j : Fin (N + 1)} (hj : x j ≠ 0)
    (ψ : chartRing k x (singleChart hj) →ₐ[k] K') : ψ (ratio hj j) = 1 := by
  have : ratio (S := k) hj j = 1 := Subtype.ext (div_self hj)
  rw [this, map_one]

end Specialize

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCycleSplit
section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsCycleSplit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w


open Classical in
def CycleSplit.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (M : LineBundle S x) (𝔪 : Ideal S), 𝔪.IsMaximal →
    ∀ J : Ideal (Poly S N), (∀ p ∈ J, ∀ d : ℕ, homogeneousComponent d p ∈ J) →
    primeOf (S := S) x ≤ J → 𝔪.map (C : S →+* Poly S N) ≤ J →
    (∀ G ∈ J.minimalPrimes, ringKrullDim (Poly S N ⧸ G) ≤ 2) →
    ∀ᶠ c : ℕ in atTop,
      interSum J ![M.toSubSystem] c =
        ∑ᶠ G : Ideal (Poly S N),
          if h : G ∈ J.minimalPrimes ∧ IsSubvar x G 1 then
            haveI : G.IsPrime := h.1.1.1
            ((cutMult J G).toNat : ℤ) * interNum G ![M.toSubSystem]
          else 0

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsCycleSplitCurve
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def CycleSplit.Curve.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (M : LineBundle S x) (𝔪 : Ideal S), 𝔪.IsMaximal →
    ∀ G : Ideal (Poly S N), IsSubvar x G 1 → 𝔪.map (C : S →+* Poly S N) ≤ G →
    ∀ᶠ c : ℕ in atTop, interSum G ![M.toSubSystem] c = interNum G ![M.toSubSystem]

end

end GroundTheory.Heights₂.Heights.Kleiman
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

universe u w

section Lemmas

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem interSum_one (pp : Ideal (Poly S N)) (L : SubSystem S x Ω) (c : ℕ) :
    interSum pp ![L] c = restrLen pp (L.twist (twistSys S x (c : ℤ))) -
      restrLen pp ((twistSys S x 0).twist (twistSys S x (c : ℤ))) := by
  have h0 : tensorSub ![L] ∅ = twistSys S x 0 := by simp [tensorSub]
  have h1 : tensorSub ![L] {0} = L := by
    simp [tensorSub, List.finRange_succ, twistSys_zero_twist]
  have huniv : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
  rw [interSum, huniv, Finset.sum_pair (by decide), h0, h1]
  simp only [Finset.card_empty, Finset.card_singleton]
  norm_num
  ring

theorem restrLen_of_irrelevant (pp : Ideal (Poly S N)) (hX : ∀ i, (X i : Poly S N) ∈ pp)
    (F : SubSystem S x Ω) : restrLen pp F = 0 := by
  have hle : F.secs ≤ (F.twist (idealSys x pp)).secs := by
    intro y hy
    simp only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem] at hy ⊢
    intro I
    obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
    have h1 : (1 : Ω) ∈ (idealSys x pp).sub I :=
      Submodule.subset_span ⟨X i, X i, 1, hX i, X_mem_monos hi, isHomogeneous_X S i,
        isHomogeneous_X S i, by rw [aeval_X, div_self hxi]⟩
    exact Submodule.subset_span ⟨1, h1, y, hy I, (one_smul Ω y).symm⟩
  have hs : Subsingleton (F.secs ⧸ ((F.twist (idealSys x pp)).secs).comap F.secs.subtype) := by
    rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
    intro y _
    exact hle y.2
  unfold restrLen
  rw [Module.length_eq_zero_iff.mpr hs]
  rfl

theorem ringKrullDim_quot_succ_le {G pp : Ideal (Poly S N)} [G.IsPrime] (hle : G ≤ pp) {f : Poly S N}
    (hfp : f ∈ pp) (hfG : f ∉ G) : ringKrullDim (Poly S N ⧸ pp) + 1 ≤ ringKrullDim (Poly S N ⧸ G) := by
  refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hle)
    (Ideal.Quotient.factor_surjective hle) (r := Ideal.Quotient.mk _ f) ?_ ?_
  · apply mem_nonZeroDivisors_of_ne_zero
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hfp

theorem withBot_le_one_of_le_two {a : WithBot ℕ∞} (h2 : a ≤ 2)
    (hne : a ≠ ((1 + 1 : ℕ) : WithBot ℕ∞)) : a ≤ 1 := by
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact absurd h2 (by decide)
    | coe n =>
      have h2a : (n : ℕ∞) ≤ 2 := WithBot.coe_le_coe.mp h2
      have h2' : n ≤ 2 := by exact_mod_cast h2a
      have hne' : n ≠ 2 := fun h => hne (by rw [h]; rfl)
      have h1 : (n : ℕ∞) ≤ 1 := by exact_mod_cast (show n ≤ 1 by omega)
      exact WithBot.coe_le_coe.mpr h1

theorem withBot_not_succ_le {a b : WithBot ℕ∞} (ha : a = ((1 + 1 : ℕ) : WithBot ℕ∞)) (hab : a + 1 ≤ b)
    (hb : b ≤ 2) : False := by
  subst ha
  have := hab.trans hb
  exact absurd this (by decide)

end Lemmas


open Classical in
theorem CycleSplit.proof (hF : CycleSplit.Filt.Statement.{u, w}) (hCu : CycleSplit.Curve.Statement.{u, w})
    (hSm : CycleSplit.Small.Statement.{u, w}) : CycleSplit.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x M 𝔪 h𝔪 J hJhom hJle hJm hdim
  obtain ⟨n, pp, d, hpp, hcount, hres⟩ := hF S Ω N x 𝔪 h𝔪 J hJhom hJle hJm

  let v : Ideal (Poly S N) → ℤ := fun G => if IsSubvar x G 1 then interNum G ![M.toSubSystem] else 0

  have hdimj : ∀ j, ringKrullDim (Poly S N ⧸ pp j) ≤ 2 := by
    intro j
    have := (hpp j).1
    obtain ⟨G, hG, hGle⟩ := Ideal.exists_minimalPrimes_le (hpp j).2.2
    exact (ringKrullDim_le_of_surjective (Ideal.Quotient.factor hGle)
      (Ideal.Quotient.factor_surjective hGle)).trans (hdim G hG)

  have hmin : ∀ j, IsSubvar x (pp j) 1 → pp j ∈ J.minimalPrimes := by
    intro j hsv
    have := (hpp j).1
    obtain ⟨G, hG, hGle⟩ := Ideal.exists_minimalPrimes_le (hpp j).2.2
    by_cases hGe : G = pp j
    · rw [← hGe]; exact hG
    · exfalso
      have : G.IsPrime := hG.1.1
      obtain ⟨f, hfp, hfG⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hGle hGe)
      exact withBot_not_succ_le hsv.dim (ringKrullDim_quot_succ_le hGle hfp hfG) (hdim G hG)

  have hpiece : ∀ j, ∀ᶠ c : ℕ in atTop, interSum (pp j) ![M.toSubSystem] c = v (pp j) := by
    intro j
    obtain ⟨hjp, hjh, hJj⟩ := hpp j
    by_cases hsv : IsSubvar x (pp j) 1
    · simp only [v, if_pos hsv]
      exact hCu S Ω N x M 𝔪 h𝔪 (pp j) hsv (hJm.trans hJj)
    · simp only [v, if_neg hsv]
      by_cases hrel : ∃ i, (X i : Poly S N) ∉ pp j
      · refine hSm S Ω N x M 𝔪 h𝔪 (pp j) hjp hjh (hJle.trans hJj) (hJm.trans hJj) ?_
        exact withBot_le_one_of_le_two (hdimj j) fun h => hsv ⟨hjp, hjh, hJle.trans hJj, hrel, h⟩
      · push Not at hrel
        exact Eventually.of_forall fun c => by
          rw [interSum_one, restrLen_of_irrelevant _ hrel, restrLen_of_irrelevant _ hrel, sub_zero]

  have hshift : ∀ j, ∀ᶠ c : ℕ in atTop,
      0 ≤ (c : ℤ) + d j ∧ interSum (pp j) ![M.toSubSystem] ((c : ℤ) + d j).toNat = v (pp j) := by
    intro j
    have ht : Tendsto (fun c : ℕ => ((c : ℤ) + d j).toNat) atTop atTop := by
      refine tendsto_atTop_atTop.mpr fun b => ⟨b + (d j).natAbs, fun a ha => ?_⟩
      omega
    exact ((eventually_ge_atTop (d j).natAbs).and (ht.eventually (hpiece j))).mono
      fun c hc => ⟨by omega, hc.2⟩
  have hall := Filter.eventually_all.mpr hshift
  filter_upwards [hall, hres M, hres (twistBundle S x 0)] with c hc hM h0
  have h0' : restrLen J ((twistSys S x 0).twist (twistSys S x (c : ℤ))) =
      ∑ j, restrLen (pp j) ((twistSys S x 0).twist (twistSys S x ((c : ℤ) + d j))) := h0

  have hsum : interSum J ![M.toSubSystem] c = ∑ j, v (pp j) := by
    rw [interSum_one, hM, h0', ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← (hc j).2, interSum_one, Int.toNat_of_nonneg (hc j).1]
  rw [hsum, Finset.sum_comp (fun G => v G) pp]

  symm
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image pp) ?_]
  · refine Finset.sum_congr rfl fun G hG => ?_
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hG
    by_cases hsv : IsSubvar x (pp j) 1
    · have hm := hmin j hsv
      have : (pp j).IsPrime := (hpp j).1
      rw [dite_eq_left ⟨hm, hsv⟩, nsmul_eq_mul]
      simp only [v, if_pos hsv]
      rw [← hcount (pp j) hm, ENat.toNat_natCast]
    · rw [dite_eq_right fun h => hsv h.2]
      simp only [v, if_neg hsv, smul_zero]
  · intro G hG
    rw [Function.mem_support] at hG
    split_ifs at hG with h
    · have : G.IsPrime := h.1.1.1
      have hc0 : (cutMult J G).toNat ≠ 0 := by
        intro h0; rw [h0] at hG; simp at hG
      rw [← hcount G h.1, ENat.toNat_natCast] at hc0
      obtain ⟨j, hj⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc0)
      rw [Finset.mem_filter] at hj
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
      exact ⟨j, hj.2⟩
    · exact absurd rfl hG

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LengthQuotientEqLengthH0
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace QuotientH0Length

section CechH

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type w}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}
  {M : Type w} [AddCommGroup M] [Module R M]

def toH0OfCocycle (φ : M →ₗ[R] Cech.Cochain G 0) (hφ : ∀ m, Cech.d G ρ 0 (φ m) = 0) : M →ₗ[R] Cech.H G ρ 0 :=
  Submodule.mkQ _ ∘ₗ LinearMap.codRestrict (LinearMap.ker (Cech.d G ρ 0)) φ
    (fun m => LinearMap.mem_ker.mpr (hφ m))

theorem toH0OfCocycle_eq_zero_iff (φ : M →ₗ[R] Cech.Cochain G 0) (hφ : ∀ m, Cech.d G ρ 0 (φ m) = 0) (m : M) :
    toH0OfCocycle φ hφ m = 0 ↔ φ m = 0 := by
  have e : toH0OfCocycle φ hφ m = (Submodule.Quotient.mk (⟨φ m, LinearMap.mem_ker.mpr (hφ m)⟩ :
      LinearMap.ker (Cech.d G ρ 0)) : Cech.H G ρ 0) := rfl
  rw [e]
  exact (Submodule.Quotient.mk_eq_zero _).trans (Submodule.mem_comap.trans (Submodule.mem_bot R))

theorem toH0OfCocycle_surjective (φ : M →ₗ[R] Cech.Cochain G 0) (hφ : ∀ m, Cech.d G ρ 0 (φ m) = 0)
    (h : ∀ z : Cech.Cochain G 0, Cech.d G ρ 0 z = 0 → ∃ m, φ m = z) : Function.Surjective (toH0OfCocycle φ hφ) := by
  intro ξ
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  obtain ⟨m, hm⟩ := h z (LinearMap.mem_ker.mp z.2)
  refine ⟨m, ?_⟩
  have e : toH0OfCocycle φ hφ m = (Submodule.Quotient.mk (⟨φ m, LinearMap.mem_ker.mpr (hφ m)⟩ :
      LinearMap.ker (Cech.d G ρ 0)) : Cech.H G ρ 0) := rfl
  rw [e]
  exact congrArg Submodule.Quotient.mk (Subtype.ext hm)

theorem length_quotient_eq_length_H0 (φ : M →ₗ[R] Cech.Cochain G 0) (hφ : ∀ m, Cech.d G ρ 0 (φ m) = 0)
    (h : ∀ z : Cech.Cochain G 0, Cech.d G ρ 0 z = 0 → ∃ m, φ m = z) (K : Submodule R M)
    (hK : ∀ m, φ m = 0 ↔ m ∈ K) : Module.length R (M ⧸ K) = Module.length R (Cech.H G ρ 0) := by
  have hker : LinearMap.ker (toH0OfCocycle φ hφ) = K := by
    ext m
    rw [LinearMap.mem_ker, toH0OfCocycle_eq_zero_iff, hK]
  rw [← hker]
  exact (LinearMap.quotKerEquivOfSurjective _ (toH0OfCocycle_surjective φ hφ h)).length_eq

theorem sgn_mul_self' (L : Finset (Fin n)) (j : Fin n) : Cech.sgn L j * Cech.sgn L j = 1 := by
  rw [Cech.sgn, ← mul_pow]
  norm_num

end CechH

section Quot

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem mem_sub_of_mem_secs {F : SubSystem S x Ω} {t : Ω} (ht : t ∈ F.secs) (I : Chart x) :
    t ∈ F.sub I :=
  (Submodule.mem_iInf _).mp ht I

def secsTo (F₁ F₂ : SubSystem S x Ω) (I : Chart x) :
    F₁.secs →ₗ[S] (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) :=
  (SubSystem.quotSub F₁ F₂ I).mkQ ∘ₗ
    { toFun := fun t => ⟨t.1, mem_sub_of_mem_secs t.2 I⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

def toCochain (F₁ F₂ : SubSystem S x Ω) :
    F₁.secs →ₗ[S] Cech.Cochain (fun I => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) 0 :=
  LinearMap.pi fun I : Cech.Idx (support x) 0 => secsTo F₁ F₂ I.1

theorem d_toCochain (F₁ F₂ : SubSystem S x Ω) (t : F₁.secs) :
    Cech.d (fun I => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) (SubSystem.quotRes F₁ F₂) 0
      (toCochain F₁ F₂ t) = 0 := by
  have hv : ∀ (I J : Chart x) (h : I.1 ⊆ J.1),
      SubSystem.quotRes F₁ F₂ I J h (secsTo F₁ F₂ I t) = secsTo F₁ F₂ J t := fun _ _ _ => rfl
  exact Cech.d_zero_of_compat (fun I => secsTo F₁ F₂ I t) hv

def sing {a : Fin (N + 1)} (ha : a ∈ support x) : Cech.Idx (support x) 0 :=
  ⟨⟨{a}, Finset.singleton_nonempty a, Finset.singleton_subset_iff.mpr ha⟩, Finset.card_singleton a⟩

theorem eq_sing (I : Cech.Idx (support x) 0) : ∃ (a : Fin (N + 1)) (ha : a ∈ support x), I = sing ha := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp I.2
  have hmem : a ∈ support x := I.1.2.2 (by rw [ha]; exact Finset.mem_singleton_self a)
  exact ⟨a, hmem, Subtype.ext (Subtype.ext ha)⟩

theorem toCochain_eq_zero_iff (F₁ F₂ : SubSystem S x Ω) (t : F₁.secs) :
    toCochain F₁ F₂ t = 0 ↔ t ∈ F₂.secs.comap F₁.secs.subtype := by
  rw [Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · intro h
    rw [SubSystem.secs, Submodule.mem_iInf]
    intro T
    obtain ⟨a, haT⟩ := T.2.1
    have ha : a ∈ support x := T.2.2 haT
    have h1 : (Submodule.Quotient.mk (⟨(t : Ω), mem_sub_of_mem_secs t.2 _⟩ : F₁.sub (sing ha).1) :
        F₁.sub (sing ha).1 ⧸ SubSystem.quotSub F₁ F₂ (sing ha).1) = 0 := congrFun h (sing ha)
    have h2 : (t : Ω) ∈ F₂.sub (sing ha).1 :=
      (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁ F₂ (sing ha).1)).mp h1
    exact F₂.mono _ T (Finset.singleton_subset_iff.mpr haT) _ h2
  · intro h
    funext I
    show (Submodule.Quotient.mk (⟨(t : Ω), mem_sub_of_mem_secs t.2 _⟩ : F₁.sub I.1) :
        F₁.sub I.1 ⧸ SubSystem.quotSub F₁ F₂ I.1) = 0
    exact (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁ F₂ I.1)).mpr (mem_sub_of_mem_secs h I.1)

theorem d_mk (F₁ F₂ : SubSystem S x Ω) (u : Cech.Idx (support x) 0 → Ω) (hu : ∀ I, u I ∈ F₁.sub I.1)
    (J : Cech.Idx (support x) 1) :
    Cech.d (fun I => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) (SubSystem.quotRes F₁ F₂) 0
        (fun I => Submodule.Quotient.mk ⟨u I, hu I⟩) J =
      Submodule.Quotient.mk ⟨∑ j : J.1.1, Cech.sgn J.1.1 j • u (Cech.face J j),
        Submodule.sum_mem _ fun j _ =>
          zsmul_mem (F₁.mono _ _ (Cech.face_subset J j) _ (hu (Cech.face J j))) _⟩ := by
  rw [Cech.d_apply]
  have : (⟨∑ j : J.1.1, Cech.sgn J.1.1 j • u (Cech.face J j),
        Submodule.sum_mem _ fun j _ =>
          zsmul_mem (F₁.mono _ _ (Cech.face_subset J j) _ (hu (Cech.face J j))) _⟩ : F₁.sub J.1) =
      ∑ j : J.1.1, Cech.sgn J.1.1 j • F₁.res _ J.1 (Cech.face_subset J j) ⟨u (Cech.face J j), hu _⟩ := by
    apply Subtype.ext
    simp [SubSystem.res]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [this, ← Submodule.mkQ_apply, map_sum]
  simp only [map_zsmul]
  rfl


set_option maxHeartbeats 1000000 in
theorem exists_toCochain_eq (F₁ F₂ : SubSystem S x Ω)
    (hlift : ∀ s : Chart x → Ω, (∀ I, s I ∈ F₁.sub I) →
      (∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → s I₁ - s I₂ ∈ F₂.sub I₂) →
      ∃ t ∈ F₁.secs, ∀ I, t - s I ∈ F₂.sub I)
    (z : Cech.Cochain (fun I => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) 0)
    (hz : Cech.d (fun I => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) (SubSystem.quotRes F₁ F₂) 0 z = 0) :
    ∃ t : F₁.secs, toCochain F₁ F₂ t = z := by
  classical
  have hrep : ∀ I : Cech.Idx (support x) 0, ∃ v : Ω, ∃ hv : v ∈ F₁.sub I.1,
      (Submodule.Quotient.mk ⟨v, hv⟩ : F₁.sub I.1 ⧸ SubSystem.quotSub F₁ F₂ I.1) = z I := by
    intro I
    obtain ⟨⟨v, hv⟩, h⟩ := Submodule.Quotient.mk_surjective _ (z I)
    exact ⟨v, hv, h⟩
  choose v hv hvz using hrep
  have hz' : z = fun I => Submodule.Quotient.mk ⟨v I, hv I⟩ := funext fun I => (hvz I).symm
  have hpair : ∀ J : Cech.Idx (support x) 1,
      ∑ j : J.1.1, Cech.sgn J.1.1 j • v (Cech.face J j) ∈ F₂.sub J.1 := by
    intro J
    have e := congrFun hz J
    rw [hz', d_mk] at e
    exact (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁ F₂ J.1)).mp e
  let V : Finset (Fin (N + 1)) → Ω := fun T =>
    if h : (T.Nonempty ∧ T ⊆ support x) ∧ T.card = 0 + 1 then v ⟨⟨T, h.1⟩, h.2⟩ else 0
  have hV : ∀ I : Cech.Idx (support x) 0, V I.1.1 = v I := fun I => by
    simp only [V]
    rw [dite_eq_left ⟨I.1.2, I.2⟩]
  have hVpair : ∀ (a b : Fin (N + 1)) (ha : a ∈ support x) (hb : b ∈ support x) (T : Chart x),
      a ∈ T.1 → b ∈ T.1 → V {a} - V {b} ∈ F₂.sub T := by
    intro a b ha hb T haT hbT
    by_cases hab : a = b
    · subst hab
      rw [sub_self]
      exact Submodule.zero_mem _
    have hsupp : ({a, b} : Finset (Fin (N + 1))) ⊆ support x := by
      rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨ha, hb⟩
    let J : Cech.Idx (support x) 1 :=
      ⟨⟨{a, b}, Finset.insert_nonempty _ _, hsupp⟩, Finset.card_pair hab⟩
    have e := hpair J
    have hj : ∀ j : J.1.1, v (Cech.face J j) = V (J.1.1.erase j) := fun j => (hV (Cech.face J j)).symm
    simp only [hj] at e
    have e2 := Cech.sum_sgn_of_card_two (J := ({a, b} : Finset (Fin (N + 1)))) (Finset.card_pair hab)
    rw [Finset.sum_coe_sort ({a, b} : Finset (Fin (N + 1)))
      (fun j => Cech.sgn {a, b} j • V (({a, b} : Finset (Fin (N + 1))).erase j))] at e
    rw [Finset.sum_pair hab] at e e2
    have ea : ({a, b} : Finset (Fin (N + 1))).erase a = {b} :=
      Finset.erase_insert (by simpa using hab)
    have eb : ({a, b} : Finset (Fin (N + 1))).erase b = {a} := by
      rw [Finset.pair_comm]
      exact Finset.erase_insert (by simpa using Ne.symm hab)
    rw [ea, eb, eq_neg_of_add_eq_zero_right e2, neg_smul, ← sub_eq_add_neg, ← smul_sub] at e
    have e3 := zsmul_mem e (Cech.sgn {a, b} a)
    rw [smul_smul, sgn_mul_self', one_smul] at e3
    have e4 : V {a} - V {b} ∈ F₂.sub J.1 := by
      rw [← neg_sub]
      exact neg_mem e3
    refine F₂.mono J.1 T ?_ _ e4
    rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨haT, hbT⟩
  let s : Chart x → Ω := fun I => V {I.1.min' I.2.1}
  have hs : ∀ I, s I ∈ F₁.sub I := by
    intro I
    have hm := I.1.min'_mem I.2.1
    have h1 : V {I.1.min' I.2.1} ∈ F₁.sub (sing (I.2.2 hm)).1 := by
      rw [show V {I.1.min' I.2.1} = v (sing (I.2.2 hm)) from hV (sing (I.2.2 hm))]
      exact hv _
    exact F₁.mono _ I (Finset.singleton_subset_iff.mpr hm) _ h1
  have hcomp : ∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → s I₁ - s I₂ ∈ F₂.sub I₂ := by
    intro I₁ I₂ h
    exact hVpair _ _ (I₁.2.2 (I₁.1.min'_mem I₁.2.1)) (I₂.2.2 (I₂.1.min'_mem I₂.2.1)) I₂
      (h (I₁.1.min'_mem I₁.2.1)) (I₂.1.min'_mem I₂.2.1)
  obtain ⟨t, ht, hts⟩ := hlift s hs hcomp
  refine ⟨⟨t, ht⟩, ?_⟩
  rw [hz']
  funext I
  obtain ⟨a, ha, rfl⟩ := eq_sing I
  change (Submodule.Quotient.mk (⟨t, mem_sub_of_mem_secs ht _⟩ : F₁.sub (sing ha).1) :
      F₁.sub (sing ha).1 ⧸ SubSystem.quotSub F₁ F₂ (sing ha).1) = Submodule.Quotient.mk ⟨v (sing ha), hv _⟩
  rw [Submodule.Quotient.eq]
  change t - v (sing ha) ∈ F₂.sub (sing ha).1
  have hsa : s (sing ha).1 = v (sing ha) := by
    have hmin : ({a} : Finset (Fin (N + 1))).min' (Finset.singleton_nonempty a) = a :=
      Finset.min'_singleton a
    change V {({a} : Finset (Fin (N + 1))).min' _} = v (sing ha)
    rw [hmin]
    exact hV (sing ha)
  rw [← hsa]
  exact hts _


set_option maxHeartbeats 400000 in
theorem length_secs_eq (F₁ F₂ : SubSystem S x Ω)
    (hlift : ∀ s : Chart x → Ω, (∀ I, s I ∈ F₁.sub I) →
      (∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → s I₁ - s I₂ ∈ F₂.sub I₂) →
      ∃ t ∈ F₁.secs, ∀ I, t - s I ∈ F₂.sub I) :
    Module.length S (F₁.secs ⧸ F₂.secs.comap F₁.secs.subtype) =
      Module.length S (SubSystem.quotH F₁ F₂ 0) := by
  have hφ := d_toCochain F₁ F₂
  have hh := exists_toCochain_eq F₁ F₂ hlift
  have hK := toCochain_eq_zero_iff F₁ F₂
  have e : Module.length S (F₁.secs ⧸ F₂.secs.comap F₁.secs.subtype) =
      Module.length S (Cech.H (fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I)
        (SubSystem.quotRes F₁ F₂) 0) :=
    length_quotient_eq_length_H0 (toCochain F₁ F₂) hφ hh _ hK
  rw [e]
  rfl

end Quot

end QuotientH0Length

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleSecs
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace VeryAmpleSecs

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω]

theorem mem_secs_pow_twistSys_one_iff {r : ℕ} (h : Fin (r + 1) → Ω) (n : ℕ) (s : Ω) :
    s ∈ ((twistSys k h 1).pow n).secs ↔ ∀ j, h j ≠ 0 → s / h j ^ n ∈ ampleBase (S := k) h j := by
  constructor
  · intro hs j hj
    have hsj := (Submodule.mem_iInf _).mp hs (singleChart hj)
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp
      (pow_twistSys_one_le n (singleChart hj) (Finset.mem_singleton_self j) hsj)
    rw [chartRing_smul_def] at hb
    rw [← hb, mul_div_cancel_right₀ _ (pow_ne_zero n hj)]
    exact mem_ampleBase_of_mem_chartRing hj b.2
  · intro H
    rw [SubSystem.secs, Submodule.mem_iInf]
    intro I
    obtain ⟨i, hi⟩ := I.2.1
    have hhi : h i ≠ 0 := (mem_support h).mp (I.2.2 hi)
    have hbase : ampleBase (S := k) h i ≤ chartRing k h (singleChart hhi) := by
      rw [ampleBase, Algebra.adjoin_le_iff]
      rintro _ ⟨l, rfl⟩
      exact (ratio (S := k) hhi l).2
    have hmem : s / h i ^ n ∈ chartRing k h I :=
      chartRing_mono (Finset.singleton_subset_iff.mpr hi) (hbase (H i hhi))
    rw [Submodule.restrictScalars_mem, SubSystem.pow_sub]
    have hs : s = (⟨s / h i ^ n, hmem⟩ : chartRing k h I) • h i ^ n := by
      rw [chartRing_smul_def, div_mul_cancel₀ _ (pow_ne_zero n hhi)]
    rw [hs]
    exact Submodule.smul_mem _ _ (Submodule.pow_mem_pow _ (mem_twistMod_one I i) n)

theorem mem_pow_of_pow_mul_mem {A : Type*} [CommRing A] [Algebra A Ω] {L Q : Submodule A Ω}
    (hLQ : L * Q = 1) {r : ℕ} {h : Fin (r + 1) → Ω} (hL : Submodule.span A (Set.range h) = L)
    {s : Ω} {n : ℕ} (hs : ∀ j, ∃ e, h j ^ e * s ∈ L ^ (n + e)) : s ∈ L ^ n := by
  set C : Ideal A := (L ^ n).colon {s}
  have key : ∀ j, ∀ q ∈ Q, ∀ a : A, algebraMap A Ω a = h j * q → a ∈ C.radical := by
    intro j q hq a ha
    obtain ⟨e, he⟩ := hs j
    refine ⟨e, ?_⟩
    rw [Submodule.mem_colon_singleton, Algebra.smul_def, map_pow, ha]
    have hm := Submodule.mul_mem_mul (Submodule.pow_mem_pow Q hq e) he
    have hQL : Q ^ e * L ^ (n + e) = L ^ n := by
      calc Q ^ e * L ^ (n + e) = L ^ n * (L * Q) ^ e := by ring
        _ = L ^ n := by rw [hLQ, one_pow, mul_one]
    rw [hQL] at hm
    convert hm using 1
    ring
  have h1 : (1 : Submodule A Ω) ≤ Submodule.map (Algebra.linearMap A Ω) (C.radical : Submodule A A) := by
    rw [← hLQ, ← hL, ← Submodule.span_eq Q, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, q, hq, rfl⟩
    have hjq : h j * q ∈ L * Q := Submodule.mul_mem_mul (hL ▸ Submodule.subset_span ⟨j, rfl⟩) hq
    rw [hLQ, Submodule.mem_one] at hjq
    obtain ⟨a, ha⟩ := hjq
    exact ⟨a, key j q hq a ha, ha⟩
  obtain ⟨a, ⟨m, hm⟩, ha1⟩ := h1 (Submodule.mem_one.mpr ⟨1, map_one _⟩)
  have ha1' : algebraMap A Ω a = 1 := ha1
  rw [Submodule.mem_colon_singleton, Algebra.smul_def, map_pow, ha1', one_pow, one_mul] at hm
  exact hm

theorem exists_pow_mul_mem_pow {A : Subalgebra k Ω} {L : Submodule A Ω} {r : ℕ}
    {h : Fin (r + 1) → Ω} (hL : ∀ l, h l ∈ L) {j : Fin (r + 1)} (hj : h j ≠ 0) {t : Ω}
    (ht : t ∈ ampleBase (S := k) h j) : ∃ e, h j ^ e * t ∈ L ^ e := by
  induction ht using Algebra.adjoin_induction with
  | mem t ht =>
    obtain ⟨l, rfl⟩ := ht
    exact ⟨1, by rw [pow_one, pow_one, mul_div_cancel₀ _ hj]; exact hL l⟩
  | algebraMap c =>
    refine ⟨0, ?_⟩
    rw [pow_zero, pow_zero, one_mul, Submodule.mem_one]
    exact ⟨⟨_, Subalgebra.algebraMap_mem A c⟩, rfl⟩
  | add t₁ t₂ _ _ h₁ h₂ =>
    obtain ⟨e₁, he₁⟩ := h₁
    obtain ⟨e₂, he₂⟩ := h₂
    refine ⟨e₁ + e₂, ?_⟩
    have hs : h j ^ (e₁ + e₂) * (t₁ + t₂) = h j ^ e₂ * (h j ^ e₁ * t₁) + h j ^ e₁ * (h j ^ e₂ * t₂) := by
      ring
    rw [hs, pow_add]
    exact Submodule.add_mem _
      (by rw [mul_comm (L ^ e₁)]; exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (hL j) _) he₁)
      (Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (hL j) _) he₂)
  | mul t₁ t₂ _ _ h₁ h₂ =>
    obtain ⟨e₁, he₁⟩ := h₁
    obtain ⟨e₂, he₂⟩ := h₂
    refine ⟨e₁ + e₂, ?_⟩
    have hs : h j ^ (e₁ + e₂) * (t₁ * t₂) = (h j ^ e₁ * t₁) * (h j ^ e₂ * t₂) := by ring
    rw [hs, pow_add]
    exact Submodule.mul_mem_mul he₁ he₂

end VeryAmpleSecs


open VeryAmpleSecs in
theorem VeryAmpleSecs.proof : VeryAmpleSecs.Statement.{u, w} := by
  intro k _ Ω _ _ N x Nb r h hv n
  ext s
  rw [mem_secs_pow_twistSys_one_iff]
  have hL : ∀ I l, h l ∈ Nb.sub I := fun I l => (Submodule.mem_iInf _).mp (hv.mem_secs l) I
  constructor
  · intro hs j hj
    refine hv.closed j hj (Set.mem_iInter.mpr fun I => ⟨n, ?_⟩)
    rw [div_mul_cancel₀ _ (pow_ne_zero n hj), one_mul]
    exact (Submodule.mem_iInf _).mp hs I
  · intro H
    rw [SubSystem.secs, Submodule.mem_iInf]
    intro I
    rw [Submodule.restrictScalars_mem, SubSystem.pow_sub]
    obtain ⟨Q, hQ⟩ := Nb.invertible I
    refine mem_pow_of_pow_mul_mem hQ (hv.generates I) fun j => ?_
    by_cases hj : h j = 0
    · exact ⟨1, by rw [hj, pow_one, zero_mul]; exact Submodule.zero_mem _⟩
    obtain ⟨e, he⟩ := exists_pow_mul_mem_pow (hL I) hj (H j hj)
    refine ⟨e, ?_⟩
    have hs : h j ^ e * s = h j ^ n * (h j ^ e * (s / h j ^ n)) := by
      field_simp
    rw [hs, pow_add]
    exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (hL I j) n) he

end

end GroundTheory.Heights₂.Heights.Kleiman
end
