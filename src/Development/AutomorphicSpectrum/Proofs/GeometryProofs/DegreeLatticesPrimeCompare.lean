module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDim

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DegreeLatticePrimeScaling
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DegreeLatticePrimeScaling
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Num

noncomputable section

section LineVert

variable {K : Type} [DecidableEq K] {ι : K → Type} {Ω : Type} [Field Ω]

def lineVertMono [Fintype K] (c : ∀ k, ι k) (e : K → ℕ) : MRing ι ℤ := ∏ k, X ⟨k, c k⟩ ^ e k

theorem lineVertMono_homog [Fintype K] (c : ∀ k, ι k) (e : K → ℕ) :
    IsMultiHomog (lineVertMono c e) e := by
  have h := IsWeightedHomogeneous.prod (R := ℤ) (w := blockWeight ι) Finset.univ
    (fun k => (X ⟨k, c k⟩ : MRing ι ℤ) ^ e k) (fun k => e k • (Pi.single k 1 : K → ℕ))
    (fun k _ => (isWeightedHomogeneous_X ℤ (blockWeight ι) ⟨k, c k⟩).pow (e k))
  have he : ∑ k, e k • (Pi.single k 1 : K → ℕ) = e := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [he] at h
  exact h

theorem lineVertMono_aeval [Fintype K] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (e : K → ℕ) :
    aeval y (lineVertMono c e) = ∏ k, y ⟨k, c k⟩ ^ e k := by
  simp [lineVertMono, map_prod]

theorem lineVert_prod_weight [Fintype K] (m : (Σ k, ι k) →₀ ℕ) :
    (m.prod fun p e => (X p.1 : MvPolynomial K Ω) ^ e) =
      ∏ k, X k ^ (Finsupp.weight (blockWeight ι) m k) := by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]), hf, hg, map_add (f := _),
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  | single p e =>
    rw [Finsupp.prod_single_index (by simp), Finsupp.weight_single,
      Finset.prod_eq_single p.1]
    · simp [blockWeight]
    · intro k _ hk
      simp [blockWeight, Pi.single_apply, hk]
    · simp

theorem lineVert_cone_homog [Fintype K] (y : (Σ k, ι k) → Ω) {h : MRing ι ℤ} {b : K → ℕ}
    (hh : IsMultiHomog h b) :
    pointConeMap ℤ y h = C (aeval y h) * ∏ k, X k ^ b k := by
  have key : ∀ m ∈ h.support, pointConeMap ℤ y (monomial m (AddMonoidAlgebra.coeff h m)) =
      C (aeval y (monomial m (AddMonoidAlgebra.coeff h m) : MRing ι ℤ)) * ∏ k, X k ^ b k := by
    intro m hm
    have hw : Finsupp.weight (blockWeight ι) m = b := hh (mem_support_iff.mp hm)
    rw [pointConeMap, aeval_monomial, aeval_monomial, ← hw, ← lineVert_prod_weight]
    have e1 : (m.prod fun p e => (C (y p) * X p.1 : MvPolynomial K Ω) ^ e) =
        C (m.prod fun p e => y p ^ e) * m.prod fun p e => (X p.1 : MvPolynomial K Ω) ^ e := by
      simp only [mul_pow, Finsupp.prod, Finset.prod_mul_distrib, map_prod, map_pow]
    rw [e1]
    simp [mul_assoc]
  calc pointConeMap ℤ y h = ∑ m ∈ h.support, pointConeMap ℤ y (monomial m (AddMonoidAlgebra.coeff h m)) := by
        conv_lhs => rw [h.as_sum]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
    _ = ∑ m ∈ h.support, C (aeval y (monomial m (AddMonoidAlgebra.coeff h m) : MRing ι ℤ)) * ∏ k, X k ^ b k :=
        Finset.sum_congr rfl key
    _ = C (aeval y h) * ∏ k, X k ^ b k := by
        conv_rhs => rw [h.as_sum]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, map_sum, Finset.sum_mul]

theorem lineVert_mem_of_homog [Fintype K] (y : (Σ k, ι k) → Ω) {h : MRing ι ℤ} {b : K → ℕ}
    (hh : IsMultiHomog h b) (h0 : aeval y h = 0) : h ∈ pointIdeal ℤ y := by
  rw [pointIdeal, RingHom.mem_ker, lineVert_cone_homog y hh, h0]
  simp

theorem lineVert_chart_form [Fintype K] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k)
    (hc : segreVec y c ≠ 0) {a : Ω} (ha : a ∈ chartRing ℤ (segreVec y) c) :
    ∃ (r : ℕ) (G : MRing ι ℤ), IsMultiHomog G (fun _ => r) ∧
      a * segreVec y c ^ r = aeval y G := by
  rw [chartRing] at ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨d, rfl⟩ := hx
    refine ⟨1, lineVertMono d (fun _ => 1), lineVertMono_homog _ _, ?_⟩
    rw [lineVertMono_aeval, pow_one, div_mul_cancel₀ _ hc]
    simp [segreVec]
  | algebraMap n =>
    refine ⟨0, C n, isWeightedHomogeneous_C _ _, ?_⟩
    simp
  | add x z _ _ hx hz =>
    obtain ⟨r₁, G₁, h₁, v₁⟩ := hx
    obtain ⟨r₂, G₂, h₂, v₂⟩ := hz
    refine ⟨r₁ + r₂, G₁ * lineVertMono c (fun _ => r₂) + G₂ * lineVertMono c (fun _ => r₁), ?_, ?_⟩
    · have a₁ := IsWeightedHomogeneous.mul h₁ (lineVertMono_homog c fun _ => r₂)
      have a₂ := IsWeightedHomogeneous.mul h₂ (lineVertMono_homog c fun _ => r₁)
      have e₁ : (fun _ : K => r₁) + (fun _ : K => r₂) = fun _ => r₁ + r₂ := rfl
      have e₂ : (fun _ : K => r₂) + (fun _ : K => r₁) = fun _ => r₁ + r₂ := by
        funext k; simp [add_comm]
      rw [e₁] at a₁
      rw [e₂] at a₂
      exact a₁.add a₂
    · have hp : ∀ r : ℕ, ∏ k, y ⟨k, c k⟩ ^ r = segreVec y c ^ r := fun r => by
        rw [segreVec, Finset.prod_pow]
      rw [map_add (f := _), map_mul, map_mul, lineVertMono_aeval, lineVertMono_aeval, hp, hp, ← v₁, ← v₂]
      ring
  | mul x z _ _ hx hz =>
    obtain ⟨r₁, G₁, h₁, v₁⟩ := hx
    obtain ⟨r₂, G₂, h₂, v₂⟩ := hz
    refine ⟨r₁ + r₂, G₁ * G₂, IsWeightedHomogeneous.mul h₁ h₂, ?_⟩
    rw [map_mul, ← v₁, ← v₂]
    ring

theorem lineVert_chart_pair [Fintype K] (y : (Σ k, ι k) → Ω) (m : ℕ) (b b' : K → ℤ) (s : Ω)
    (hs : s ≠ 0) (c : ∀ k, ι k) (hc : segreVec y c ≠ 0)
    (h1 : ∀ t ∈ degLat ℤ y b c, ∃ n : ℕ, ∃ t' ∈ degLat ℤ y b' c, (m : Ω) ^ n * t = s * t')
    (h2 : ∀ t' ∈ degLat ℤ y b' c, ∃ n : ℕ, ∃ t ∈ degLat ℤ y b c, (m : Ω) ^ n * (s * t') = t) :
    ∃ (U V : MRing ι ℤ) (dU dV : K → ℕ), IsMultiHomog U dU ∧ IsMultiHomog V dV ∧
      (∀ k, (dV k : ℤ) - dU k = b k - b' k) ∧ s * aeval y U = aeval y V ∧
      ∀ W : Ideal (MRing ι ℤ), W.IsPrime → pointIdeal ℤ y ≤ W → (∀ k, (X ⟨k, c k⟩ : MRing ι ℤ) ∉ W) →
        (C (m : ℤ) : MRing ι ℤ) ∉ W → U ∉ W ∧ V ∉ W := by
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.mp hc k (Finset.mem_univ k)
  have hZ : ∀ e : K → ℤ, (∏ k, y ⟨k, c k⟩ ^ e k) ≠ 0 := fun e =>
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hy k)
  obtain ⟨n, t', ⟨a, ha, rfl⟩, e1⟩ := h1 (1 * ∏ k, y ⟨k, c k⟩ ^ b k) ⟨1, one_mem _, rfl⟩
  obtain ⟨n', t, ⟨a', ha', rfl⟩, e2⟩ := h2 (1 * ∏ k, y ⟨k, c k⟩ ^ b' k) ⟨1, one_mem _, rfl⟩
  obtain ⟨r, G, hG, hGa⟩ := lineVert_chart_form y c hc ha
  obtain ⟨r', G', hG', hGa'⟩ := lineVert_chart_form y c hc ha'
  rw [one_mul] at e1 e2
  set Yb := ∏ k, y ⟨k, c k⟩ ^ b k with hYb
  set Yb' := ∏ k, y ⟨k, c k⟩ ^ b' k with hYb'
  have hYb0 : Yb ≠ 0 := hZ b
  have hYb'0 : Yb' ≠ 0 := hZ b'
  set x := segreVec y c with hx
  have hxp : ∀ r : ℕ, ∏ k, y ⟨k, c k⟩ ^ r = x ^ r := fun r => by
    rw [hx, segreVec, Finset.prod_pow]

  let e : K → ℤ := fun k => b' k - b k + r'
  let dP : K → ℕ := fun k => (e k).toNat
  let dN : K → ℕ := fun k => (-e k).toNat
  have haa : a * a' = (m : Ω) ^ n * (m : Ω) ^ n' := by
    apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hs hYb0) hYb'0)
    linear_combination (-((m : Ω) ^ n' * s * Yb')) * e1 - (s * a * Yb') * e2
  have hGG : aeval y G * aeval y G' = (m : Ω) ^ (n + n') * x ^ (r + r') := by
    rw [← hGa, ← hGa', pow_add, pow_add]
    linear_combination (x ^ r * x ^ r') * haa
  have key : Yb' * x ^ r' * (∏ k, y ⟨k, c k⟩ ^ dN k) = Yb * ∏ k, y ⟨k, c k⟩ ^ dP k := by
    rw [← hxp, hYb, hYb', ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hy k), ← zpow_add₀ (hy k),
      ← zpow_add₀ (hy k)]
    congr 1
    simp only [dP, dN, e]
    omega
  refine ⟨C ((m : ℤ) ^ n') * lineVertMono c dP, G' * lineVertMono c dN, dP, (fun _ => r') + dN,
    ?_, IsWeightedHomogeneous.mul hG' (lineVertMono_homog c dN), ?_, ?_, ?_⟩
  · have a₀ := (isWeightedHomogeneous_C (blockWeight ι) ((m : ℤ) ^ n')).mul (lineVertMono_homog c dP)
    rw [zero_add] at a₀
    exact a₀
  · intro k
    simp only [Pi.add_apply, dP, dN, e]
    push_cast
    omega
  · apply mul_right_cancel₀ hYb0
    rw [map_mul, map_mul, lineVertMono_aeval, lineVertMono_aeval, aeval_C]
    simp only [map_pow, eq_intCast, Int.cast_natCast]
    linear_combination (-(s * (m : Ω) ^ n')) * key + (x ^ r' * ∏ k, y ⟨k, c k⟩ ^ dN k) * e2 +
      (Yb * ∏ k, y ⟨k, c k⟩ ^ dN k) * hGa'
  · intro W hW hPW hX hm
    have hmono : ∀ d : K → ℕ, lineVertMono c d ∉ W := by
      intro d hd
      obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp hd
      exact hX k (hW.mem_of_pow_mem _ hk)
    have hmpow : ∀ j : ℕ, (C ((m : ℤ) ^ j) : MRing ι ℤ) ∉ W := by
      intro j hj
      rw [map_pow] at hj
      exact hm (hW.mem_of_pow_mem _ hj)
    have hG'W : G' ∉ W := by
      intro hg
      have hH : G * G' - C ((m : ℤ) ^ (n + n')) * lineVertMono c (fun _ => r + r') ∈ W := by
        apply hPW
        apply lineVert_mem_of_homog y (b := fun _ => r + r')
        · have a₁ := IsWeightedHomogeneous.mul hG hG'
          have a₂ := (isWeightedHomogeneous_C (blockWeight ι) ((m : ℤ) ^ (n + n'))).mul
            (lineVertMono_homog (ι := ι) c fun _ => r + r')
          rw [zero_add] at a₂
          exact (weightedHomogeneousSubmodule ℤ (blockWeight ι) _).sub_mem a₁ a₂
        · rw [map_sub, map_mul, map_mul, lineVertMono_aeval, hxp, hGG, aeval_C]
          simp
      have h3 := W.sub_mem (W.mul_mem_left G hg) hH
      rw [sub_sub_cancel] at h3
      rcases hW.mem_or_mem h3 with h | h
      · exact hmpow _ h
      · exact hmono _ h
    constructor
    · intro h
      rcases hW.mem_or_mem h with h | h
      · exact hmpow _ h
      · exact hmono _ h
    · intro h
      rcases hW.mem_or_mem h with h | h
      · exact hG'W h
      · exact hmono _ h

end LineVert

theorem lineVert_of_eq_off : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω), IsMultiProjPrime (pointIdeal ℤ y) → ∀ (S : Finset Nat.Primes) (b b' : K → ℤ) (s : Ω), s ≠ 0 → (∀ c, segreVec y c ≠ 0 → (∀ t ∈ degLat ℤ y b c, ∃ n : ℕ, ∃ t' ∈ degLat ℤ y b' c, ((∏ p ∈ S, (p : ℕ) : ℕ) : Ω) ^ n * t = s * t') ∧ ∀ t' ∈ degLat ℤ y b' c, ∃ n : ℕ, ∃ t ∈ degLat ℤ y b c, ((∏ p ∈ S, (p : ℕ) : ℕ) : Ω) ^ n * (s * t') = t) → IsHorizontal (pointIdeal ℤ y) → ∃ f g : MRing ι ℤ, (⟨fun _ => b, fun _ => b', fun _ => f, fun _ => g⟩ : LocPair ι ℤ Unit).IsVertOff (pointIdeal ℤ y) S ∧ aeval y f = s * aeval y g := by
  intro K _ _ ι _ Ω _ y hP S b b' s hs hch hhor
  set m : ℕ := ∏ p ∈ S, (p : ℕ) with hm
  have hm0 : m ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p _ => p.2.ne_zero
  have hmP : (C (m : ℤ) : MRing ι ℤ) ∉ pointIdeal ℤ y := by
    intro h
    have h' : (m : ℤ) ∈ (pointIdeal ℤ y).comap (C : ℤ →+* MRing ι ℤ) := h
    rw [show (pointIdeal ℤ y).comap (C : ℤ →+* MRing ι ℤ) = ⊥ from hhor, Ideal.mem_bot] at h'
    exact hm0 (by exact_mod_cast h')
  have hseg : ∀ c : ∀ k, ι k, (∀ k, (X ⟨k, c k⟩ : MRing ι ℤ) ∉ pointIdeal ℤ y) →
      segreVec y c ≠ 0 := by
    intro c hc
    refine Finset.prod_ne_zero_iff.mpr fun k _ h0 => hc k ?_
    exact lineVert_mem_of_homog y (isWeightedHomogeneous_X ℤ (blockWeight ι) ⟨k, c k⟩) (by simpa using h0)
  choose c₀ hc₀ using hP.relevant
  obtain ⟨U₀, V₀, dU₀, dV₀, hU₀, hV₀, hd₀, hv₀, hW₀⟩ :=
    lineVert_chart_pair y m b b' s hs c₀ (hseg c₀ hc₀) (hch c₀ (hseg c₀ hc₀)).1 (hch c₀ (hseg c₀ hc₀)).2
  have hUV := hW₀ (pointIdeal ℤ y) hP.isPrime le_rfl hc₀ hmP
  refine ⟨V₀, U₀, ?_, hv₀.symm⟩
  intro i
  refine ⟨⟨dV₀, dU₀, hV₀, hU₀, ?_⟩, hUV.2, hUV.1, ?_⟩
  · funext k
    exact hd₀ k
  · intro W hWp hPW hWr hWS
    choose c hc using hWr
    have hcP : ∀ k, (X ⟨k, c k⟩ : MRing ι ℤ) ∉ pointIdeal ℤ y := fun k h => hc k (hPW h)
    have hmW : (C (m : ℤ) : MRing ι ℤ) ∉ W := by
      intro h
      have h' : (∏ p ∈ S, (C (((p : ℕ) : ℤ)) : MRing ι ℤ)) ∈ W := by
        rw [← map_prod]
        convert h using 2
        rw [hm]
        push_cast
        rfl
      obtain ⟨p, hp, hpW⟩ := Ideal.IsPrime.prod_mem_iff.mp h'
      exact hWS p hp hpW
    obtain ⟨U, V, dU, dV, hU, hV, hd, hv, hW⟩ :=
      lineVert_chart_pair y m b b' s hs c (hseg c hcP) (hch c (hseg c hcP)).1 (hch c (hseg c hcP)).2
    have hUV' := hW W hWp hPW hc hmW
    refine ⟨U, V, hUV'.1, hUV'.2, ?_⟩
    apply lineVert_mem_of_homog y (b := dU + dV₀)
    · have a₁ := IsWeightedHomogeneous.mul hU hV₀
      have a₂ := IsWeightedHomogeneous.mul hV hU₀
      have e₂ : dV + dU₀ = dU + dV₀ := by
        funext k
        have h1 := hd k
        have h2 := hd₀ k
        simp only [Pi.add_apply]
        omega
      rw [e₂] at a₂
      exact (weightedHomogeneousSubmodule ℤ (blockWeight ι) _).sub_mem a₁ a₂
    · simp only [map_sub, map_mul]
      rw [← hv, ← hv₀]
      ring

end

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DegreeLatticePrimeScalingStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_lattice_prime_scaling : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω), IsMultiProjPrime (pointIdeal ℤ y) → ∀ (S : Finset Nat.Primes) (b b' : K → ℤ) (s : Ω), s ≠ 0 → (∀ c, segreVec y c ≠ 0 → (∀ t ∈ degLat ℤ y b c, ∃ n : ℕ, ∃ t' ∈ degLat ℤ y b' c, ((∏ p ∈ S, (p : ℕ) : ℕ) : Ω) ^ n * t = s * t') ∧ ∀ t' ∈ degLat ℤ y b' c, ∃ n : ℕ, ∃ t ∈ degLat ℤ y b c, ((∏ p ∈ S, (p : ℕ) : ℕ) : Ω) ^ n * (s * t') = t) → IsHorizontal (pointIdeal ℤ y) → ∃ f g : MRing ι ℤ, (⟨fun _ => b, fun _ => b', fun _ => f, fun _ => g⟩ : LocPair ι ℤ Unit).IsVertOff (pointIdeal ℤ y) S ∧ aeval y f = s * aeval y g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.lineVert_of_eq_off | exact GlobalTheory.CompanionTheory.Ar.Num.lineVert_of_eq_off | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.lineVert_of_eq_off <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DegreeLatticesPrimeCompare
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem exists_pow_mul_mem_chart {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {κ : Type} {x : κ → Ω} (T : CoordTie ℤ ξ x) {c : κ} (hc : x c ≠ 0) (m : ℕ) (τ : Ω)
    (hτ : ∀ q : Cpt ξ, InChart ξ x c q → unitAt ξ q (m : Ω) → τ ∈ regAt ξ q) :
    ∃ n : ℕ, (m : Ω) ^ n * τ ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) := by
  let B := Algebra.adjoin ℤ (Set.range fun j => x j / x c)
  let I : Ideal B :=
    { carrier := {r | (r : Ω) * τ ∈ B}
      add_mem' := by
        intro a b ha hb
        have ha' : (a : Ω) * τ ∈ B := ha
        have hb' : (b : Ω) * τ ∈ B := hb
        have h := add_mem ha' hb'
        rw [← add_mul] at h
        exact h
      zero_mem' := by
        show ((0 : B) : Ω) * τ ∈ B
        simp
      smul_mem' := by
        intro r a ha
        have ha' : (a : Ω) * τ ∈ B := ha
        have h := mul_mem r.2 ha'
        rw [← _root_.mul_assoc] at h
        exact h }
  have hmem : (m : B) ∈ I.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro Q ⟨hIQ, hQ⟩
    by_contra hmQ
    obtain ⟨q, ⟨hqc, hq⟩, -⟩ := chart_point_of_prime X Ω ξ ℤ κ x T c hc Q hQ
    have hu : unitAt ξ q (((m : B) : B) : Ω) := (hq (m : B)).1 hmQ
    have hu' : unitAt ξ q (m : Ω) := by simpa using hu
    obtain ⟨s, hsB, hsu, hsτ⟩ :=
      (regAt_iff_exists_chart_fraction X Ω ξ ℤ κ x T c q hqc τ).1 (hτ q hqc hu')
    have hsQ : (⟨s, hsB⟩ : B) ∈ Q := hIQ hsτ
    exact (hq ⟨s, hsB⟩).2 hsu hsQ
  obtain ⟨n, hn⟩ := hmem
  refine ⟨n, ?_⟩
  have h : (((m : B) ^ n : B) : Ω) * τ ∈ B := hn
  simpa using h

theorem unitAt_natCast_of_dvd {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (q : Cpt ξ) {p m : ℕ} (hd : p ∣ m) (hm : unitAt ξ q (m : Ω)) : unitAt ξ q (p : Ω) := by
  obtain ⟨w, rfl⟩ := hd
  obtain ⟨h0, -, hinv⟩ := hm
  have hc : (((p * w : ℕ) : Ω)) = (p : Ω) * (w : Ω) := by push_cast; ring
  rw [hc] at h0 hinv
  have hp : (p : Ω) ≠ 0 := left_ne_zero_of_mul h0
  have hw : (w : Ω) ≠ 0 := right_ne_zero_of_mul h0
  refine ⟨hp, natCast_mem _ p, ?_⟩
  have he : (p : Ω)⁻¹ = (w : Ω) * ((p : Ω) * (w : Ω))⁻¹ := by field_simp
  rw [he]
  exact mul_mem (natCast_mem _ w) hinv


variable {Ω' : Type} [Field Ω'] in
theorem div_mem_of_mem_span {R : Subring Ω'} {v w : Ω'} (hw : w ≠ 0) (h : v ∈ Submodule.span R {w}) :
    v / w ∈ R := by
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 h
  have hr' : (r : Ω') * w = v := hr
  rw [← hr', mul_div_cancel_right₀ _ hw]
  exact r.2

theorem exists_pow_chart_quotients {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}
    (T : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩))
    {L L' : Lat ξ Ω} {a a' : K → ℤ} {e e' : Ω} (hL : L.IsDegOn Set.univ y a e)
    (hL' : L'.IsDegOn Set.univ y a' e') (S : Finset Nat.Primes)
    (hS : ∀ q : Cpt ξ, (∀ p ∈ S, ¬ InFibre ξ p q) → L q = L' q)
    (c : (k : K) → J k) (hc : ∏ k, y ⟨k, c k⟩ ≠ 0) :
    (∃ n : ℕ, ((∏ p ∈ S, (p : ℕ) : ℕ) : Ω) ^ n *
        (((∏ k, y ⟨k, c k⟩ ^ a' k) * e') / ((∏ k, y ⟨k, c k⟩ ^ a k) * e)) ∈
        Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩)) ∧
      ∃ n : ℕ, ((∏ p ∈ S, (p : ℕ) : ℕ) : Ω) ^ n *
        (((∏ k, y ⟨k, c k⟩ ^ a k) * e) / ((∏ k, y ⟨k, c k⟩ ^ a' k) * e')) ∈
        Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) := by
  have key : ∀ q : Cpt ξ, InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c q →
      unitAt ξ q ((∏ p ∈ S, (p : ℕ) : ℕ) : Ω) →
      Submodule.span (regAt ξ q) {(∏ k, y ⟨k, c k⟩ ^ a k) * e} =
        Submodule.span (regAt ξ q) {(∏ k, y ⟨k, c k⟩ ^ a' k) * e'} := by
    intro q hq hm
    have h1 := hL.2 q (Set.mem_univ q) c hq
    have h2 := hL'.2 q (Set.mem_univ q) c hq
    rw [smul_eq_mul] at h1 h2
    rw [← h1, ← h2]
    refine hS q fun p hp hf => hf ?_
    exact unitAt_natCast_of_dvd q (Finset.dvd_prod_of_mem (fun p : Nat.Primes => (p : ℕ)) hp) hm
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc k (Finset.mem_univ k)
  have hu : (∏ k, y ⟨k, c k⟩ ^ a k) * e ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)) hL.1
  have hu' : (∏ k, y ⟨k, c k⟩ ^ a' k) * e' ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)) hL'.1
  constructor
  · refine exists_pow_mul_mem_chart T hc _ _ fun q hq hm => div_mem_of_mem_span hu ?_
    rw [key q hq hm]
    exact Submodule.mem_span_singleton_self _
  · refine exists_pow_mul_mem_chart T hc _ _ fun q hq hm => div_mem_of_mem_span hu' ?_
    rw [← key q hq hm]
    exact Submodule.mem_span_singleton_self _

theorem lat_vertOff : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ d : ℕ, IsArithVar (mCoordIdeal y) (d + 1) → ∀ (L L' : Lat ξ Ω) (a a' : K → ℤ) (e e' : Ω), L.IsDegOn Set.univ y a e → L'.IsDegOn Set.univ y a' e' → ∀ S : Finset Nat.Primes, (∀ q : Cpt ξ, (∀ p ∈ S, ¬ InFibre ξ p q) → L q = L' q) → ∃ f g : MvPolynomial (Σ k, J k) ℤ, (⟨fun _ => a, fun _ => a', fun _ => f, fun _ => g⟩ : LocPair J ℤ Unit).IsVertOff (mCoordIdeal y) S ∧ aeval y f = e' / e * aeval y g := by
  intro X Ω _ ξ K _ _ J _ y T d hA L L' a a' e e' hL hL' S hS
  have hrel : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hA.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    rw [mCoordIdeal, RingHom.mem_ker]
    simp [mConeMap, h0]
  have hproj : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiProjPrime (pointIdeal ℤ y) :=
    GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDim.isMultiProjPrime_pointIdeal y hrel
  have he : e ≠ 0 := hL.1
  have he' : e' ≠ 0 := hL'.1
  refine GlobalTheory.T.degree_lattice_prime_scaling K J Ω y hproj S a a' (e' / e) (div_ne_zero he' he) ?_ hA.2.2.1
  intro c hc
  have hc' : ∏ k, y ⟨k, c k⟩ ≠ 0 := hc
  obtain ⟨⟨n, hn⟩, ⟨n', hn'⟩⟩ := exists_pow_chart_quotients T hL hL' S hS c hc'
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc' k (Finset.mem_univ k)
  have hY : (∏ k, y ⟨k, c k⟩ ^ a k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)
  have hY' : (∏ k, y ⟨k, c k⟩ ^ a' k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)
  constructor
  · rintro t ⟨A, hAm, rfl⟩
    have hAm' : A ∈ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k =>
        (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) := hAm
    refine ⟨n', _, ⟨_, mul_mem hn' hAm', rfl⟩, ?_⟩
    generalize (∏ k, y ⟨k, c k⟩ ^ a k) = Y at hY
    generalize (∏ k, y ⟨k, c k⟩ ^ a' k) = Y' at hY'
    field_simp
  · rintro t ⟨A, hAm, rfl⟩
    have hAm' : A ∈ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k =>
        (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) := hAm
    refine ⟨n, _, ⟨_, mul_mem hn hAm', rfl⟩, ?_⟩
    generalize (∏ k, y ⟨k, c k⟩ ^ a k) = Y at hY
    generalize (∏ k, y ⟨k, c k⟩ ^ a' k) = Y' at hY'
    field_simp

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DegreeLatticesPrimeCompareStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_lattices_prime_compare : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ d : ℕ, IsArithVar (mCoordIdeal y) (d + 1) → ∀ (L L' : Lat ξ Ω) (a a' : K → ℤ) (e e' : Ω), L.IsDegOn Set.univ y a e → L'.IsDegOn Set.univ y a' e' → ∀ S : Finset Nat.Primes, (∀ q : Cpt ξ, (∀ p ∈ S, ¬ InFibre ξ p q) → L q = L' q) → ∃ f g : MvPolynomial (Σ k, J k) ℤ, (⟨fun _ => a, fun _ => a', fun _ => f, fun _ => g⟩ : LocPair J ℤ Unit).IsVertOff (mCoordIdeal y) S ∧ aeval y f = e' / e * aeval y g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.lat_vertOff | exact GlobalTheory.CompanionTheory.Ar.Num.lat_vertOff | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.lat_vertOff <;> assumption)
end
