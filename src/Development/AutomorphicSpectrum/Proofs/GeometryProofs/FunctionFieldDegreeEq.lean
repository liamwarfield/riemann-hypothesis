module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeIsMaximalOfIsFractionRing
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LengthFormulaSumValuations

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsMultihomogPrimeOfPlace
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsMultihomogPrimeOfPlace
noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg

namespace GlobalTheory.CompanionTheory.Ar.GeoDeg.Centre

section

variable {B : Type} [Fintype B] {J : B → Type} [∀ k, Fintype (J k)]
  {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K]

theorem mem_mCoordIdeal_iff {Ω : Type} [Field Ω] (y : (Σ k, J k) → Ω) {g : MRing J} {e : B → ℕ}
    (hg : IsMultiHomog g e) : g ∈ mCoordIdeal y ↔ aeval y g = 0 := by
  have hT : (∏ k, (X k : MvPolynomial B Ω) ^ e k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k)
  rw [mCoordIdeal, RingHom.mem_ker]
  show mConeMap y g = 0 ↔ _
  rw [GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest.mConeMap_form y hg, mul_eq_zero, or_iff_right hT, C_eq_zero]

variable (v : Place (ZMod p) K) (w : (Σ k, J k) → K) (c : ∀ k, J k)

def ratio (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (hle : ∀ k i, v.valuation (w ⟨k, i⟩) ≤ v.valuation (w ⟨k, c k⟩))
    (q : Σ k, J k) : v.ring :=
  ⟨w q / w ⟨q.1, c q.1⟩, by
    rw [← v.valuation_le_one_iff, map_div₀]
    exact div_le_one_of_le₀ (hle q.1 q.2) zero_le'⟩

variable {v w c}
variable (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (hle : ∀ k i, v.valuation (w ⟨k, i⟩) ≤ v.valuation (w ⟨k, c k⟩))

include hc in
theorem prod_ne_zero (e : B → ℕ) : (∏ k, w ⟨k, c k⟩ ^ e k) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)

theorem coe_aeval_ratio {g : MRing J} {e : B → ℕ} (hg : IsMultiHomog g e) :
    ((aeval (ratio v w c hc hle) g : v.ring) : K) = aeval w g * (∏ k, w ⟨k, c k⟩ ^ e k)⁻¹ := by
  rw [← GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointResidue.aeval_div w c g e hg]
  exact MvPolynomial.comp_aeval_apply (φ := (algebraMap v.ring K).toIntAlgHom) _ g

theorem aeval_residue (g : MRing J) :
    aeval (fun q => residue v.ring (ratio v w c hc hle q)) g =
      residue v.ring (aeval (ratio v w c hc hle) g) :=
  (MvPolynomial.comp_aeval_apply (φ := (residue v.ring).toIntAlgHom) _ g).symm

theorem valuation_prod (e : B → ℕ) :
    v.valuation (∏ k, w ⟨k, c k⟩ ^ e k) = ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k := by
  rw [map_prod]
  exact Finset.prod_congr rfl fun k _ => map_pow _ _ _

include hc in
theorem prod_valuation_pos (e : B → ℕ) : 0 < ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k := by
  rw [← valuation_prod]
  exact zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (prod_ne_zero hc e))


include hc hle in
theorem valuation_aeval_le {g : MRing J} {e : B → ℕ} (hg : IsMultiHomog g e) :
    v.valuation (aeval w g) ≤ ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k := by
  have h := (v.valuation_le_one_iff _).2 (aeval (ratio v w c hc hle) g).2
  rw [coe_aeval_ratio hc hle hg, map_mul, map_inv₀, valuation_prod] at h
  rwa [mul_inv_le_iff₀ (prod_valuation_pos hc e), one_mul] at h

theorem mem_iff {g : MRing J} {e : B → ℕ} (hg : IsMultiHomog g e) :
    g ∈ mCoordIdeal (fun q => residue v.ring (ratio v w c hc hle q)) ↔
      v.valuation (aeval w g) < ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k := by
  refine (mem_mCoordIdeal_iff _ hg).trans (Iff.trans (Eq.congr_left (aeval_residue hc hle g)) ?_)
  rw [residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff, ← v.valuation_lt_one_iff,
    coe_aeval_ratio hc hle hg, map_mul, map_inv₀, valuation_prod,
    mul_inv_lt_iff₀ (prod_valuation_pos hc e), one_mul]

end

theorem exists_centre : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type)
    [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K) (v : Place (ZMod p) K)
    (c : ∀ k, J k), (∀ k, w ⟨k, c k⟩ ≠ 0) →
    (∀ k i, v.valuation (w ⟨k, i⟩) ≤ v.valuation (w ⟨k, c k⟩)) →
    ∃ W : Ideal (MRing J), W.IsPrime ∧ IsMultiHomogIdeal W ∧ mCoordIdeal w ≤ W ∧
      (∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) ∧ Dom v w W ∧
      ∀ (e : B → ℕ) (g : MRing J), IsMultiHomog g e →
        (g ∈ W ↔ v.valuation (aeval w g) < ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k) := by
  intro B _ J _ p _ K _ _ _ w v c hc hle
  refine ⟨mCoordIdeal (fun q => residue v.ring (ratio v w c hc hle q)), RingHom.ker_isPrime _,
    GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal _, ?_, ?_, ?_, fun e g hg => mem_iff hc hle hg⟩
  · obtain ⟨S, hS, hSe⟩ := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal w
    have hSV : Ideal.span S ≤ mCoordIdeal w := hSe.ge
    rw [hSe, Ideal.span_le]
    intro f hf
    obtain ⟨a, ha⟩ := hS f hf
    have hf0 : aeval w f = 0 := (mem_mCoordIdeal_iff w ha).1 (hSV (Ideal.subset_span hf))
    refine (mem_iff hc hle ha).2 ?_
    rw [hf0, map_zero]
    exact prod_valuation_pos hc a
  · intro k h
    have h1 := (X_mem_iff _ k (c k)).1 h
    have h2 : ratio v w c hc hle ⟨k, c k⟩ = 1 := Subtype.ext (div_self (hc k))
    rw [h2, map_one] at h1
    exact one_ne_zero h1
  · intro e g h hg hh hhW
    have hh' : v.valuation (aeval w h) = ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k :=
      le_antisymm (valuation_aeval_le hc hle hh) (not_lt.1 fun hlt => hhW ((mem_iff hc hle hh).2 hlt))
    rw [hh']
    exact ⟨valuation_aeval_le hc hle hg, (mem_iff hc hle hg).1⟩

end GlobalTheory.CompanionTheory.Ar.GeoDeg.Centre
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsMultihomogPrimeOfPlaceStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multihomog_prime_of_place : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K) (v : Place (ZMod p) K) (c : ∀ k, J k), (∀ k, w ⟨k, c k⟩ ≠ 0) → (∀ k i, v.valuation (w ⟨k, i⟩) ≤ v.valuation (w ⟨k, c k⟩)) → ∃ W : Ideal (MRing J), W.IsPrime ∧ IsMultiHomogIdeal W ∧ mCoordIdeal w ≤ W ∧ (∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) ∧ Dom v w W ∧ ∀ (e : B → ℕ) (g : MRing J), IsMultiHomog g e → (g ∈ W ↔ v.valuation (aeval w g) < ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GeoDeg.Centre.exists_centre | exact GlobalTheory.CompanionTheory.Ar.GeoDeg.Centre.exists_centre | (intros; apply GlobalTheory.CompanionTheory.Ar.GeoDeg.Centre.exists_centre <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricNumberZeroFinrank
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricNumberZeroFinrank
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GeoDeg.ResDeg

open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointResidue (exists_homog exists_homog_mem aeval_div)
open GroundTheory.Heights₂.Heights.HilbertSamuel.SmallSectionsNonzero (chartMono isMultiHomog_chartMono mem_mCoordIdeal_of_aeval_eq_zero)
open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointChart (chartMono_notMem)
open GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds (homog_X fracHom fracHom_apply fracHom_eq_zero_iff mem_locRing_iff div_mem_locRing)

theorem length_toNat_of_addEquiv {M κ : Type*} [AddCommGroup M] [Module ℤ M] [Field κ] (e : M ≃+ κ)
    (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) κ] :
    (Module.length ℤ M).toNat = Module.finrank (ZMod p) κ := by
  let l : M ≃ₗ[ℤ] κ := { e with map_smul' := fun n x => by simpa using map_intCast_smul e ℤ ℤ n x }
  rw [l.length_eq, Module.length_eq_of_surjective (R := ZMod p) (S := ℤ) (M := κ)
    (fun z => ⟨(z.cast : ℤ), by simp⟩), Module.length_eq_rank, Cardinal.toNat_toENat]
  rfl

attribute [local instance 2000] Ring.toIntAlgebra

variable {B : Type} [Fintype B] {J : B → Type} [∀ k, Fintype (J k)]
variable {P W : Ideal (MRing J)} [P.IsPrime] [W.IsPrime]

def dehom (hPW : P ≤ W) (c : ∀ k, J k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) : MRing J →+* locRing P W := by
  classical
  exact (aeval (R := ℤ) fun p : Σ k, J k =>
    (⟨fracHom P (X p) / fracHom P (X ⟨p.1, c p.1⟩),
      div_mem_locRing hPW (homog_X p.1 p.2) (homog_X p.1 (c p.1)) (hc p.1)⟩ : locRing P W)).toRingHom

theorem frac_chart_ne_zero (hPW : P ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) (k : B) :
    fracHom P (X ⟨k, c k⟩ : MRing J) ≠ 0 := fun h =>
  hc k (hPW (fracHom_eq_zero_iff.1 h))

theorem coe_dehom (hPW : P ≤ W) (c : ∀ k, J k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) (f : MRing J) :
    ((dehom hPW c hc f : locRing P W) : FractionRing (MRing J ⧸ P)) =
      aeval (fun p : Σ k, J k => fracHom P (X p) / fracHom P (X ⟨p.1, c p.1⟩)) f := by
  classical
  have h : (locRing P W).subtype.comp (dehom hPW c hc) =
      (aeval (R := ℤ) (fun p : Σ k, J k => fracHom P (X p) / fracHom P (X ⟨p.1, c p.1⟩))).toRingHom := by
    refine MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun p => ?_
    simp [dehom]
  exact RingHom.congr_fun h f

theorem fracHom_eq_aeval (f : MRing J) :
    fracHom P f = aeval (fun p : Σ k, J k => fracHom P (X p)) f := by
  have h : fracHom P = (aeval (R := ℤ) (fun p : Σ k, J k => fracHom P (X p))).toRingHom :=
    MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun p => by simp
  exact RingHom.congr_fun h f

theorem dehom_form (hPW : P ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) {G : MRing J} {n : B → ℕ}
    (hG : IsMultiHomog G n) :
    ((dehom hPW c hc G : locRing P W) : FractionRing (MRing J ⧸ P)) * fracHom P (chartMono c n) = fracHom P G := by
  have hD : fracHom P (chartMono c n) = ∏ k, fracHom P (X ⟨k, c k⟩ : MRing J) ^ n k := by
    simp [chartMono, map_prod, map_pow]
  have hD0 : ∏ k, fracHom P (X ⟨k, c k⟩ : MRing J) ^ n k ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (frac_chart_ne_zero hPW hc k)
  rw [coe_dehom, aeval_div (fun p : Σ k, J k => fracHom P (X p)) c G n hG, hD, ← fracHom_eq_aeval,
    mul_assoc, inv_mul_cancel₀ hD0, mul_one]

theorem dehom_X_chart (hPW : P ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) (k : B) :
    dehom hPW c hc (X ⟨k, c k⟩) = 1 := by
  apply Subtype.ext
  rw [coe_dehom, aeval_X]
  exact div_self (frac_chart_ne_zero hPW hc k)

variable [IsLocalRing (locRing P W)]

theorem dehom_mem_maximalIdeal_iff (hPW : P ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W)
    {G : MRing J} {n : B → ℕ} (hG : IsMultiHomog G n) :
    dehom hPW c hc G ∈ maximalIdeal (locRing P W) ↔ G ∈ W :=
  regularityLocalFlat_holds.mem_maximalIdeal_iff hPW _ hG (isMultiHomog_chartMono c n)
    (chartMono_notMem ‹W.IsPrime› hc n) (dehom_form hPW hc hG)

def theta (hPW : P ≤ W) (c : ∀ k, J k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) :
    MRing J →+* ResidueField (locRing P W) :=
  (residue (locRing P W)).comp (dehom hPW c hc)

theorem theta_eq_zero_iff (hPW : P ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W)
    {G : MRing J} {n : B → ℕ} (hG : IsMultiHomog G n) : theta hPW c hc G = 0 ↔ G ∈ W :=
  (residue_eq_zero_iff _).trans (dehom_mem_maximalIdeal_iff hPW hc hG)

theorem theta_X_chart (hPW : P ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) (k : B) :
    theta hPW c hc (X ⟨k, c k⟩) = 1 := by
  simp [theta, dehom_X_chart]

theorem ker_theta (hPW : P ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W)
    (hWh : IsMultiHomogIdeal W) :
    RingHom.ker (theta hPW c hc) = W ⊔ Ideal.span (Set.range fun k => (X ⟨k, c k⟩ : MRing J) - 1) := by
  set I0 := Ideal.span (Set.range fun k => (X ⟨k, c k⟩ : MRing J) - 1) with hI0
  have hIk : I0 ≤ RingHom.ker (theta hPW c hc) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    simp [SetLike.mem_coe, RingHom.mem_ker, theta_X_chart]
  apply le_antisymm
  · intro f hf
    have hχ : ∀ k, Ideal.Quotient.mk I0 (X ⟨k, c k⟩) = 1 := fun k => by
      rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
      exact Ideal.subset_span ⟨k, rfl⟩
    obtain ⟨n, G, hG, hGf⟩ := exists_homog _ c hχ f
    have hd : G - f ∈ I0 := Ideal.Quotient.eq.mp hGf
    have hG0 : G ∈ RingHom.ker (theta hPW c hc) := by simpa using add_mem (hIk hd) hf
    have hGW : G ∈ W := (theta_eq_zero_iff hPW hc hG).1 hG0
    have e : f = G - (G - f) := by ring
    rw [e]
    exact sub_mem (Ideal.mem_sup_left hGW) (Ideal.mem_sup_right hd)
  · refine sup_le ?_ hIk
    intro f hf
    obtain ⟨n, G, hGW, hG, e⟩ := exists_homog_mem (theta hPW c hc) c (theta_X_chart hPW hc) hWh hf
    rw [RingHom.mem_ker, ← e]
    exact (theta_eq_zero_iff hPW hc hG).2 hGW

theorem theta_surjective (hPW : P ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W)
    (hmax : (RingHom.ker (theta hPW c hc)).IsMaximal) : Function.Surjective (theta hPW c hc) := by
  intro z
  obtain ⟨x, rfl⟩ := residue_surjective z
  obtain ⟨u, v, a, hu, hv, hvW, hx⟩ := (mem_locRing_iff hPW).1 x.2
  have hvk : v ∉ RingHom.ker (theta hPW c hc) := fun h => hvW ((theta_eq_zero_iff hPW hc hv).1 h)
  obtain ⟨g, i, hi, hgi⟩ := hmax.exists_inv hvk
  have hD0 : fracHom P (chartMono c a) ≠ 0 := fun h =>
    chartMono_notMem ‹W.IsPrime› hc a (hPW (fracHom_eq_zero_iff.1 h))
  have h1 : dehom hPW c hc u = x * dehom hPW c hc v := by
    apply Subtype.ext
    apply mul_right_cancel₀ hD0
    rw [dehom_form hPW hc hu, ← hx, Subring.coe_mul, mul_assoc, dehom_form hPW hc hv]
  have h2 : theta hPW c hc g * theta hPW c hc v = 1 := by
    have := congrArg (theta hPW c hc) hgi
    rwa [map_add, map_mul, RingHom.mem_ker.1 hi, add_zero, map_one] at this
  refine ⟨u * g, ?_⟩
  have h3 : theta hPW c hc u = residue _ x * theta hPW c hc v := by
    simp only [theta, RingHom.comp_apply, h1, map_mul]
  rw [map_mul, h3, mul_assoc, mul_comm (theta hPW c hc v), h2, mul_one]


omit [P.IsPrime] [W.IsPrime] in
def chartHom {K : Type} [Field K] (w : (Σ k, J k) → K) (c : ∀ k, J k) : MRing J →+* chartRingZ w c :=
  (aeval (R := ℤ) fun p : Σ k, J k =>
    (⟨w p / w ⟨p.1, c p.1⟩, Algebra.subset_adjoin ⟨p, rfl⟩⟩ : chartRingZ w c)).toRingHom

theorem coe_chartHom {K : Type} [Field K] (w : (Σ k, J k) → K) (c : ∀ k, J k) (f : MRing J) :
    ((chartHom w c f : chartRingZ w c) : K) = aeval (fun p : Σ k, J k => w p / w ⟨p.1, c p.1⟩) f := by
  have h : (chartRingZ w c).val.toRingHom.comp (chartHom w c) =
      (aeval (R := ℤ) (fun p : Σ k, J k => w p / w ⟨p.1, c p.1⟩)).toRingHom := by
    refine MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun p => ?_
    simp [chartHom]
  exact RingHom.congr_fun h f

theorem chartHom_surjective {K : Type} [Field K] (w : (Σ k, J k) → K) (c : ∀ k, J k) :
    Function.Surjective (chartHom w c) := by
  rintro ⟨r, hr⟩
  rw [chartRingZ, Algebra.adjoin_range_eq_range_aeval] at hr
  obtain ⟨f, hf⟩ := (AlgHom.mem_range _).mp hr
  exact ⟨f, Subtype.ext ((coe_chartHom w c f).trans hf)⟩

theorem ker_chartHom_le {K : Type} [Field K] {w : (Σ k, J k) → K} {c : ∀ k, J k} {W : Ideal (MRing J)}
    (hPW : mCoordIdeal w ≤ W) (hwc : ∀ k, w ⟨k, c k⟩ ≠ 0) :
    RingHom.ker (chartHom w c) ≤ W ⊔ Ideal.span (Set.range fun k => (X ⟨k, c k⟩ : MRing J) - 1) := by
  set I0 := Ideal.span (Set.range fun k => (X ⟨k, c k⟩ : MRing J) - 1) with hI0
  have hspan : I0 ≤ RingHom.ker (chartHom w c) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    apply Subtype.ext
    rw [coe_chartHom]
    simp [hwc k]
  intro f hf
  have hχ : ∀ k, Ideal.Quotient.mk I0 (X ⟨k, c k⟩) = 1 := fun k => by
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
    exact Ideal.subset_span ⟨k, rfl⟩
  obtain ⟨n, G, hG, hGf⟩ := exists_homog _ c hχ f
  have hd : G - f ∈ I0 := Ideal.Quotient.eq.mp hGf
  have hG0 : chartHom w c G = 0 := by simpa using add_mem (hspan hd) hf
  have hGv : aeval w G = 0 := by
    have h1 := congrArg Subtype.val hG0
    rw [coe_chartHom, aeval_div w c G n hG] at h1
    exact (mul_eq_zero.1 h1).resolve_right
      (inv_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hwc k)))
  have hGW : G ∈ W := hPW (mem_mCoordIdeal_of_aeval_eq_zero w hG hGv)
  have e : f = G - (G - f) := by ring
  rw [e]
  exact sub_mem (Ideal.mem_sup_left hGW) (Ideal.mem_sup_right hd)

theorem ker_theta_isMaximal {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    [IsFunctionField (ZMod p) K] {w : (Σ k, J k) → K} {W : Ideal (MRing J)} [(mCoordIdeal w).IsPrime] [W.IsPrime]
    [IsLocalRing (locRing (mCoordIdeal w) W)] (hbir : Birational w) (hPW : mCoordIdeal w ≤ W)
    {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) (hWh : IsMultiHomogIdeal W)
    {k : B} {i : J k} (hw : w ⟨k, i⟩ ≠ 0) (hX : (X ⟨k, i⟩ : MRing J) ∈ W) :
    (RingHom.ker (theta hPW c hc)).IsMaximal := by
  have hwc : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k h => hc k (hPW ((X_mem_iff w k _).2 h))
  have hs := chartHom_surjective w c
  have hker := ker_theta hPW hc hWh
  have hle : RingHom.ker (chartHom w c) ≤ RingHom.ker (theta hPW c hc) := by
    rw [hker]
    exact ker_chartHom_le hPW hwc
  haveI : (RingHom.ker (theta hPW c hc)).IsPrime := RingHom.ker_isPrime _
  have hq : (Ideal.map (chartHom w c) (RingHom.ker (theta hPW c hc))).IsPrime :=
    Ideal.map_isPrime_of_surjective hs hle
  have h0 : Ideal.map (chartHom w c) (RingHom.ker (theta hPW c hc)) ≠ ⊥ := by
    intro h
    have hx : (X ⟨k, i⟩ : MRing J) ∈ RingHom.ker (theta hPW c hc) := by
      rw [hker]
      exact Ideal.mem_sup_left hX
    have h1 := Ideal.mem_map_of_mem (chartHom w c) hx
    rw [h, Ideal.mem_bot] at h1
    have h2 := congrArg Subtype.val h1
    rw [coe_chartHom, aeval_X] at h2
    exact div_ne_zero hw (hwc k) h2
  haveI := chart_prime_isMaximal (p := p) w hbir c hwc _ hq h0
  have h3 := Ideal.comap_isMaximal_of_surjective (chartHom w c) hs
    (K := Ideal.map (chartHom w c) (RingHom.ker (theta hPW c hc)))
  have hle' : Ideal.comap (chartHom w c) ⊥ ≤ RingHom.ker (theta hPW c hc) := hle
  rwa [Ideal.comap_map_of_surjective (chartHom w c) hs, sup_eq_left.2 hle'] at h3

theorem geoNum_zero_eq_finrank : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K), Birational w → ∀ (k : B) (c : J k), w ⟨k, c⟩ ≠ 0 → ∀ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), ∀ (b : Fin 0 → B → ℤ) [IsLocalRing (locRing (mCoordIdeal w) W)] [Algebra (ZMod p) (locRing (mCoordIdeal w) W)], geoNum 0 W b = (Module.finrank (ZMod p) (ResidueField (locRing (mCoordIdeal w) W)) : ℤ) := by
  intro B _ J _ p _ K _ _ _ w hbir k i hw W hW b _ _
  classical
  obtain ⟨hmin, hrel⟩ := hW
  haveI hWp : W.IsPrime := hmin.1.1
  haveI hPp : (mCoordIdeal w).IsPrime := RingHom.ker_isPrime _
  have hPW : mCoordIdeal w ≤ W := le_sup_left.trans hmin.1.2
  have hX : (X ⟨k, i⟩ : MRing J) ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
  have hWh : IsMultiHomogIdeal W :=
    isMultiHomogIdeal_of_mem_minimalPrimes (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal w)
      (homog_X k i) hmin
  have hc : ∀ k, (X ⟨k, (hrel k).choose⟩ : MRing J) ∉ W := fun k => (hrel k).choose_spec
  have hmax := ker_theta_isMaximal (p := p) hbir hPW hc hWh hw hX
  have hsurj := theta_surjective hPW hc hmax
  rw [geoNum, dite_eq_left hrel]
  congr 1
  exact length_toNat_of_addEquiv
    ((Ideal.quotEquivOfEq (ker_theta hPW hc hWh).symm).trans
      (RingHom.quotientKerEquivOfSurjective hsurj)).toAddEquiv p

end GlobalTheory.CompanionTheory.Ar.GeoDeg.ResDeg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricNumberZeroFinrankStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_number_zero_finrank : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K), Birational w → ∀ (k : B) (c : J k), w ⟨k, c⟩ ≠ 0 → ∀ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), ∀ (b : Fin 0 → B → ℤ) [IsLocalRing (locRing (mCoordIdeal w) W)] [Algebra (ZMod p) (locRing (mCoordIdeal w) W)], geoNum 0 W b = (Module.finrank (ZMod p) (ResidueField (locRing (mCoordIdeal w) W)) : ℤ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GeoDeg.ResDeg.geoNum_zero_eq_finrank | exact GlobalTheory.CompanionTheory.Ar.GeoDeg.ResDeg.geoNum_zero_eq_finrank | (intros; apply GlobalTheory.CompanionTheory.Ar.GeoDeg.ResDeg.geoNum_zero_eq_finrank <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingEssFiniteType
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingEssFiniteType
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GeoDeg

open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointChart (chartMono_notMem)
open GroundTheory.Heights₂.Heights.HilbertSamuel.SmallSectionsNonzero (chartMono isMultiHomog_chartMono aeval_chartMono)
open GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds (homog_X mem_locRing_iff div_mem_locRing fracHom fracHom_eq_zero_iff isUnit_iff)

theorem aeval_ratio_mul_chartMono {B : Type} [Fintype B] {J : B → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
    (φ : MRing J →+* Ω) (c : ∀ k, J k) (hc : ∀ k, φ (X ⟨k, c k⟩) ≠ 0) (S : Subring Ω) (x : (Σ k, J k) → S)
    (hx : ∀ q, (x q : Ω) = φ (X q) / φ (X ⟨q.1, c q.1⟩)) {g : MRing J} {e : B → ℕ} (hg : IsMultiHomog g e) :
    ((aeval x g : S) : Ω) * φ (chartMono c e) = φ g := by
  classical
  let ψ : MRing J →+* Ω := S.subtype.comp (aeval x : MRing J →ₐ[ℤ] S).toRingHom
  have hψX : ∀ q, ψ (X q) = φ (X q) / φ (X ⟨q.1, c q.1⟩) := fun q => by
    show ((aeval x (X q) : S) : Ω) = _
    rw [aeval_X]
    exact hx q
  have hψC : ∀ a : ℤ, ψ (C a) = φ (C a) := fun a =>
    RingHom.congr_fun (RingHom.ext_int (ψ.comp C) (φ.comp C)) a
  show ψ g * φ (chartMono c e) = φ g
  set_option synthInstance.maxHeartbeats 100000 in
    rw [g.as_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∀ k, ∑ i, m ⟨k, i⟩ = e k := hg m hm
  have hchart : φ (chartMono c e) = ∏ q : (Σ k, J k), φ (X ⟨q.1, c q.1⟩) ^ m q := by
    rw [Fintype.prod_sigma]
    simp only [Finset.prod_pow_eq_pow_sum, hdeg]
    show φ (∏ k, X ⟨k, c k⟩ ^ e k) = _
    rw [map_prod]
    simp only [map_pow]
  have hne : ∏ q : (Σ k, J k), φ (X ⟨q.1, c q.1⟩) ^ m q ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun q _ => pow_ne_zero _ (hc q.1)
  rw [hchart, monomial_eq, map_mul, map_mul, hψC, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [map_prod, map_pow, hψX, div_pow, Finset.prod_div_distrib]
  rw [mul_assoc, div_mul_cancel₀ _ hne]

theorem essFiniteType_locRing : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime]
    (K : Type) [Field K] (w : (Σ k, J k) → K) (W : Ideal (MRing J)) (c : ∀ k, J k),
    (mCoordIdeal w).IsPrime → W.IsPrime → mCoordIdeal w ≤ W → (∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) →
    ∀ [Algebra (ZMod p) (locRing (mCoordIdeal w) W)],
      Algebra.EssFiniteType (ZMod p) (locRing (mCoordIdeal w) W) := by
  intro B _ J _ p _ K _ w W c hP hW hle hcW _
  classical
  haveI : (mCoordIdeal w).IsPrime := hP
  haveI : W.IsPrime := hW
  have hXP : ∀ k, fracHom (mCoordIdeal w) (X ⟨k, c k⟩) ≠ 0 := fun k h =>
    hcW k (hle (fracHom_eq_zero_iff.1 h))
  have hchartP : ∀ a : B → ℕ, fracHom (mCoordIdeal w) (chartMono c a) ≠ 0 := fun a h =>
    chartMono_notMem hW hcW a (hle (fracHom_eq_zero_iff.1 h))
  let xS : (Σ k, J k) → locRing (mCoordIdeal w) W := fun q =>
    ⟨fracHom (mCoordIdeal w) (X q) / fracHom (mCoordIdeal w) (X ⟨q.1, c q.1⟩),
      div_mem_locRing hle (homog_X q.1 q.2) (homog_X q.1 (c q.1)) (hcW q.1)⟩
  let s : Finset (locRing (mCoordIdeal w) W) := Finset.univ.image xS
  have hsub : Set.range xS ⊆ (s : Set (locRing (mCoordIdeal w) W)) := by
    rintro _ ⟨q, rfl⟩
    exact Finset.mem_coe.2 (Finset.mem_image_of_mem xS (Finset.mem_univ q))
  have hmem : ∀ g : MRing J, aeval xS g ∈ Algebra.adjoin (ZMod p) (s : Set (locRing (mCoordIdeal w) W)) := by
    intro g
    refine Algebra.adjoin_mono hsub ?_
    induction g using MvPolynomial.induction_on
    next a =>
      rw [aeval_C, algebraMap_int_eq, Int.coe_castRingHom]
      exact intCast_mem _ a
    next f g hf hg =>
      rw [map_add (f := _)]
      exact add_mem hf hg
    next f q hf =>
      rw [map_mul, aeval_X]
      exact mul_mem hf (Algebra.subset_adjoin ⟨q, rfl⟩)
  refine ⟨⟨s, ?_⟩⟩
  constructor
  constructor
  · intro y
    exact y.2
  · intro z
    obtain ⟨u, v, a, hu, hv, hvW, hz⟩ := (mem_locRing_iff hle).1 z.2
    have hA := aeval_ratio_mul_chartMono (fracHom (mCoordIdeal w)) c hXP _ xS (fun q => rfl) hu
    have hB := aeval_ratio_mul_chartMono (fracHom (mCoordIdeal w)) c hXP _ xS (fun q => rfl) hv
    have hBu : IsUnit (aeval xS v) :=
      (isUnit_iff hle (aeval xS v) hv (isMultiHomog_chartMono c a) (chartMono_notMem hW hcW a) hB).2 hvW
    refine ⟨(⟨aeval xS u, hmem u⟩, ⟨⟨aeval xS v, hmem v⟩, hBu⟩), ?_⟩
    apply Subtype.ext
    apply mul_right_cancel₀ (hchartP a)
    show ((z : FractionRing (MRing J ⧸ mCoordIdeal w)) * (aeval xS v : FractionRing (MRing J ⧸ mCoordIdeal w))) *
        fracHom (mCoordIdeal w) (chartMono c a) =
      (aeval xS u : FractionRing (MRing J ⧸ mCoordIdeal w)) * fracHom (mCoordIdeal w) (chartMono c a)
    rw [mul_assoc, hB, hA, hz]
  · intro x y h
    exact ⟨1, by rw [Subtype.ext h]⟩

end GlobalTheory.CompanionTheory.Ar.GeoDeg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingEssFiniteTypeStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_ring_ess_finite_type : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (w : (Σ k, J k) → K) (W : Ideal (MRing J)) (c : ∀ k, J k), (mCoordIdeal w).IsPrime → W.IsPrime → mCoordIdeal w ≤ W → (∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) → ∀ [Algebra (ZMod p) (locRing (mCoordIdeal w) W)], Algebra.EssFiniteType (ZMod p) (locRing (mCoordIdeal w) W) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GeoDeg.essFiniteType_locRing | exact GlobalTheory.CompanionTheory.Ar.GeoDeg.essFiniteType_locRing | (intros; apply GlobalTheory.CompanionTheory.Ar.GeoDeg.essFiniteType_locRing <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogPrimeMemDivisorSupport
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogPrimeMemDivisorSupport
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GeoDeg.ChartMin

open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointChart

variable {B : Type} [Fintype B] {J : B → Type} [∀ k, Fintype (J k)] {K : Type} [Field K]

def chartIdeal (w : (Σ k, J k) → K) (c : ∀ k, J k) (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (U : Ideal (MRing J)) :
    Ideal (chartRingZ w c) where
  carrier := {r | (r : K) ∈ chartPrime w c U}
  add_mem' ha hb := chartPrime_add w ha hb
  zero_mem' := ⟨0, 0, fun m hm => by simp at hm, U.zero_mem, by simp⟩
  smul_mem' a _ hb := chartPrime_mul w hc a.2 hb

theorem mem_chartIdeal {w : (Σ k, J k) → K} {c : ∀ k, J k} {hc : ∀ k, w ⟨k, c k⟩ ≠ 0} {U : Ideal (MRing J)}
    {r : chartRingZ w c} : r ∈ chartIdeal w c hc U ↔ (r : K) ∈ chartPrime w c U :=
  Iff.rfl

theorem chartIdeal_mono {w : (Σ k, J k) → K} {c : ∀ k, J k} (hc : ∀ k, w ⟨k, c k⟩ ≠ 0)
    {U U' : Ideal (MRing J)} (h : U ≤ U') : chartIdeal w c hc U ≤ chartIdeal w c hc U' := by
  rintro r ⟨e, g, hg, hgU, hr⟩
  exact ⟨e, g, hg, h hgU, hr⟩

theorem chartIdeal_isPrime (w : (Σ k, J k) → K) {c : ∀ k, J k} (hc : ∀ k, w ⟨k, c k⟩ ≠ 0)
    {U : Ideal (MRing J)} (hVU : mCoordIdeal w ≤ U) (hU : U.IsPrime)
    (hXU : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ U) : (chartIdeal w c hc U).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one]
    intro h
    have h1 := (mem_chartPrime_iff w hVU hU hXU (r := ((1 : chartRingZ w c) : K)) (e := 0) (k := 1)
      GroundTheory.Heights₂.Heights.Inter.AvoidRing.isMultiHomog_one (by simp)).mp (mem_chartIdeal.mp h)
    exact hU.ne_top ((Ideal.eq_top_iff_one U).mpr h1)
  · intro a b hab
    obtain ⟨e, k, hk, ha⟩ := exists_rep w hc a.2
    obtain ⟨e', k', hk', hb⟩ := exists_rep w hc b.2
    have hkk : k * k' ∈ U := (mem_chartPrime_iff w hVU hU hXU (r := ((a * b : chartRingZ w c) : K))
      (GroundTheory.Heights₂.Heights.Inter.AvoidRing.isMultiHomog_mul hk hk') (by
        rw [MulMemClass.coe_mul, map_mul, prod_pow_add]
        linear_combination ((b : K) * ∏ k, w ⟨k, c k⟩ ^ e' k) * ha + (aeval w k) * hb)).mp
      (mem_chartIdeal.mp hab)
    rcases hU.mem_or_mem hkk with h | h
    · exact Or.inl ⟨e, k, hk, h, ha⟩
    · exact Or.inr ⟨e', k', hk', h, hb⟩

theorem mem_minimalPrimes_of_coord (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime]
    (K : Type) [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K)
    (hbir : Birational w) (W : Ideal (MRing J)) (c : ∀ k, J k) (hWp : W.IsPrime) (hWh : IsMultiHomogIdeal W)
    (hVW : mCoordIdeal w ≤ W) (hXc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) (k : B) (c₀ : J k)
    (hw : w ⟨k, c₀⟩ ≠ 0) (hx : (X ⟨k, c₀⟩ : MRing J) ∈ W) :
    W ∈ (mCoordIdeal w ⊔ Ideal.span {(X ⟨k, c₀⟩ : MRing J)}).minimalPrimes := by
  classical
  have hIW : mCoordIdeal w ⊔ Ideal.span {(X ⟨k, c₀⟩ : MRing J)} ≤ W :=
    sup_le hVW ((Ideal.span_singleton_le_iff_mem _).2 hx)
  refine ⟨⟨hWp, hIW⟩, ?_⟩
  rintro Q ⟨hQp, hIQ⟩ hQW
  have hwc : ∀ j, w ⟨j, c j⟩ ≠ 0 := fun j h => hXc j (hVW ((X_mem_iff w j (c j)).2 h))
  have hVQ : mCoordIdeal w ≤ Q := le_sup_left.trans hIQ
  have hxQ : (X ⟨k, c₀⟩ : MRing J) ∈ Q := hIQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hXQ : ∀ j, (X ⟨j, c j⟩ : MRing J) ∉ Q := fun j h => hXc j (hQW h)

  have hpW := chartIdeal_isPrime w hwc hVW hWp hXc
  have hpQ := chartIdeal_isPrime w hwc hVQ hQp hXQ

  let r : chartRingZ w c := ⟨w ⟨k, c₀⟩ / w ⟨k, c k⟩, Algebra.subset_adjoin ⟨⟨k, c₀⟩, rfl⟩⟩
  have hr : r ∈ chartIdeal w c hwc Q := by
    refine ⟨Pi.single k 1, X ⟨k, c₀⟩, GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds.homog_X k c₀, hxQ, ?_⟩
    have hprod : ∏ j, w ⟨j, c j⟩ ^ (Pi.single k 1 : B → ℕ) j = w ⟨k, c k⟩ := by
      rw [Fintype.prod_eq_single k (fun j hj => by simp [Pi.single_eq_of_ne hj])]
      simp
    rw [hprod, aeval_X]
    exact div_mul_cancel₀ _ (hwc k)
  have hne : chartIdeal w c hwc Q ≠ ⊥ := by
    intro h0
    have h1 : r = 0 := by simpa [h0] using hr
    exact div_ne_zero hw (hwc k) (congrArg Subtype.val h1)
  have hmax := chart_prime_isMaximal (p := p) w hbir c hwc _ hpQ hne
  have heq := hmax.eq_of_le hpW.ne_top (chartIdeal_mono hwc hQW)

  obtain ⟨S, hS, hSe⟩ := hWh
  have hSW : Ideal.span S ≤ W := hSe.ge
  rw [hSe, Ideal.span_le]
  intro g hg
  obtain ⟨e, he⟩ := hS g hg
  have hprod : (∏ j, w ⟨j, c j⟩ ^ e j) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (hwc j)
  have hrep : aeval w g * (∏ j, w ⟨j, c j⟩ ^ e j)⁻¹ * ∏ j, w ⟨j, c j⟩ ^ e j = aeval w g :=
    inv_mul_cancel_right₀ hprod _
  let t : chartRingZ w c := ⟨_, form_div_mem_chart w c he⟩
  have htW : t ∈ chartIdeal w c hwc W := ⟨e, g, he, hSW (Ideal.subset_span hg), hrep⟩
  rw [← heq] at htW
  exact (mem_chartPrime_iff w hVQ hQp hXQ he hrep).1 (mem_chartIdeal.1 htW)

end GlobalTheory.CompanionTheory.Ar.GeoDeg.ChartMin

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogPrimeMemDivisorSupportStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multihomog_prime_mem_divisor_support : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K), Birational w → ∀ (W : Ideal (MRing J)) (c : ∀ k, J k), W.IsPrime → IsMultiHomogIdeal W → mCoordIdeal w ≤ W → (∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) → ∀ (k : B) (c₀ : J k), w ⟨k, c₀⟩ ≠ 0 → (X ⟨k, c₀⟩ : MRing J) ∈ W → W ∈ (mCoordIdeal w ⊔ Ideal.span {(X ⟨k, c₀⟩ : MRing J)}).minimalPrimes := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GeoDeg.ChartMin.mem_minimalPrimes_of_coord | exact GlobalTheory.CompanionTheory.Ar.GeoDeg.ChartMin.mem_minimalPrimes_of_coord | (intros; apply GlobalTheory.CompanionTheory.Ar.GeoDeg.ChartMin.mem_minimalPrimes_of_coord <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldDegreeEq
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.GeoDeg
open MvPolynomial GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing

section
variable {B : Type} [Fintype B] {J : B → Type} [∀ k, Fintype (J k)]
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K]

theorem exists_centre (w : (Σ k, J k) → K) (hbir : Birational w) (hw : ∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) (v : Place (ZMod p) K) (k : B) (c : J k)
    (hc : w ⟨k, c⟩ ≠ 0) (hlt : v.valuation (w ⟨k, c⟩) < (Finset.univ.sup fun i => v.valuation (w ⟨k, i⟩))) :
    ∃ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), Dom v w W := by
  classical
  have hch : ∀ k', ∃ c' : J k', w ⟨k', c'⟩ ≠ 0 ∧ ∀ i, v.valuation (w ⟨k', i⟩) ≤ v.valuation (w ⟨k', c'⟩) := by
    intro k'
    obtain ⟨c0, h0⟩ := hw k'
    haveI : Nonempty (J k') := ⟨c0⟩
    obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun i => v.valuation (w ⟨k', i⟩)) Finset.univ_nonempty
    refine ⟨m, ?_, fun i => hm i (Finset.mem_univ i)⟩
    intro h
    have h1 := hm c0 (Finset.mem_univ _)
    simp only [h, map_zero] at h1
    exact ((Valuation.ne_zero_iff _).2 h0) (le_zero_iff.1 h1)
  choose c' hc1 hc2 using hch
  obtain ⟨W, hWp, hWh, hVW, hcW, hD, hiff⟩ := GlobalTheory.T.exists_multihomog_prime_of_place B J p K w v c' hc1 hc2
  have hx : (X ⟨k, c⟩ : MRing J) ∈ W := by
    rw [hiff (Pi.single k 1) _ (GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds.homog_X k c)]
    have hs : (Finset.univ.sup fun i => v.valuation (w ⟨k, i⟩)) = v.valuation (w ⟨k, c' k⟩) :=
      le_antisymm (Finset.sup_le fun i _ => hc2 k i)
        (Finset.le_sup (f := fun i => v.valuation (w ⟨k, i⟩)) (Finset.mem_univ _))
    rw [hs] at hlt
    simpa [Pi.single_apply, pow_ite, Finset.prod_ite_eq'] using hlt
  exact ⟨W, ⟨GlobalTheory.T.multihomog_prime_mem_divisor_support B J p K w hbir W c' hWp hWh hVW hcW k c hc hx, fun k' => ⟨c' k', hcW k'⟩⟩, hD⟩

open GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds (homog_X fracHom fracHom_apply fracHom_eq_zero_iff isLocalRing mem_maximalIdeal_iff isUnit_iff)

theorem local_term (w : (Σ k, J k) → K) (hbir : Birational w) (k : B) (c : J k) (hc : w ⟨k, c⟩ ≠ 0)
    (W : Ideal (MRing J)) (hWd : W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩)) (c' : ∀ k, J k)
    (hc' : ∀ k, (X ⟨k, c' k⟩ : MRing J) ∉ W) (b : Fin 0 → B → ℤ) :
    (multAt (mCoordIdeal w ⊔ Ideal.span {(X ⟨k, c⟩ : MRing J)}) W : ℤ) * geoNum 0 W b =
      ∑ᶠ v ∈ {v : Place (ZMod p) K | Dom v w W}, (v.deg : ℤ) * v.ord (w ⟨k, c⟩ / w ⟨k, c' k⟩) := by
  classical
  have hV : (mCoordIdeal w).IsPrime := RingHom.ker_isPrime _
  have hVh : IsMultiHomogIdeal (mCoordIdeal w) := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal w
  have hVW : mCoordIdeal w ≤ W := le_trans le_sup_left hWd.1.1.2
  have hWp : W.IsPrime := hWd.1.1.1
  haveI := hV
  haveI := hWp
  obtain ⟨ρ, hρ⟩ := exists_rho w W hV hWp hVW
  haveI hloc : IsLocalRing (locRing (mCoordIdeal w) W) := isLocalRing hVW
  letI : Algebra (locRing (mCoordIdeal w) W) K := ρ.toAlgebra
  haveI hfr : IsFractionRing (locRing (mCoordIdeal w) W) K := hρ.isFractionRing hbir hV hWp hVW hc'
  have hpK : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  have hpA : CharP (locRing (mCoordIdeal w) W) p :=
    (RingHom.charP_iff (algebraMap (locRing (mCoordIdeal w) W) K) (IsFractionRing.injective _ _) p).2 hpK
  letI : Algebra (ZMod p) (locRing (mCoordIdeal w) W) := ZMod.algebra _ p
  haveI : IsScalarTower (ZMod p) (locRing (mCoordIdeal w) W) K :=
    IsScalarTower.of_algebraMap_eq fun x =>
      DFunLike.congr_fun (Subsingleton.elim (algebraMap (ZMod p) K)
        ((algebraMap (locRing (mCoordIdeal w) W) K).comp (algebraMap (ZMod p) (locRing (mCoordIdeal w) W)))) x
  haveI hE : Algebra.EssFiniteType (ZMod p) (locRing (mCoordIdeal w) W) :=
    GlobalTheory.T.local_ring_ess_finite_type B J p K w W c' hV hWp hVW hc'
  haveI hN : IsNoetherianRing (locRing (mCoordIdeal w) W) := Algebra.EssFiniteType.isNoetherianRing (ZMod p) _
  have hs : IsMultiHomog (X ⟨k, c⟩ : MRing J) (Pi.single k 1) := homog_X k c
  have ht : IsMultiHomog (X ⟨k, c' k⟩ : MRing J) (Pi.single k 1) := homog_X k (c' k)
  have hsV : (X ⟨k, c⟩ : MRing J) ∉ mCoordIdeal w := fun h => hc ((X_mem_iff w k c).1 h)
  have hproj : IsMultiProjPrime (mCoordIdeal w) :=
    ⟨hV, hVh, fun k => ⟨c' k, fun h => hc' k (hVW h)⟩⟩
  have ht0 : fracHom (mCoordIdeal w) (X ⟨k, c' k⟩) ≠ 0 := fun h => hc' k (hVW (fracHom_eq_zero_iff.1 h))
  have hy : (fracHom (mCoordIdeal w) (X ⟨k, c⟩) / fracHom (mCoordIdeal w) (X ⟨k, c' k⟩)) *
      fracHom (mCoordIdeal w) (X ⟨k, c' k⟩) = fracHom (mCoordIdeal w) (X ⟨k, c⟩) := div_mul_cancel₀ _ ht0
  obtain ⟨hym, hlen⟩ := GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.regularityDehomogenization_holds B J (mCoordIdeal w) (X ⟨k, c⟩) (X ⟨k, c' k⟩)
    (Pi.single k 1) W (fracHom (mCoordIdeal w) (X ⟨k, c⟩) / fracHom (mCoordIdeal w) (X ⟨k, c' k⟩)) hproj hs hsV hWd ht (hc' k) hy
  set f : locRing (mCoordIdeal w) W := ⟨_, hym⟩ with hfdef
  have hf1 := hρ f _ _ _ hs ht (hc' k) hy
  have hne : w ⟨k, c' k⟩ ≠ 0 := fun h => hc' k (hVW ((X_mem_iff w k _).2 h))
  have hf2 : ρ f = w ⟨k, c⟩ / w ⟨k, c' k⟩ := by
    rw [eq_div_iff hne]
    simpa using hf1
  have hf0 : f ≠ 0 := by
    intro h
    rw [h, map_zero] at hf2
    exact div_ne_zero hc hne hf2.symm
  have hxW : (X ⟨k, c⟩ : MRing J) ∈ W := hWd.1.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
  have hnf : ¬ IsField (locRing (mCoordIdeal w) W) := by
    intro hF
    have hu : IsUnit f := by
      obtain ⟨g, hg⟩ := hF.mul_inv_cancel hf0
      exact IsUnit.of_mul_eq_one _ hg
    exact ((isUnit_iff hVW f hs ht (hc' k) hy).1 hu) hxW
  have key := GlobalTheory.T.length_formula_sum_valuations (ZMod p) K (locRing (mCoordIdeal w) W) hnf f hf0
  have hset : {v : Place (ZMod p) K | (∀ a : locRing (mCoordIdeal w) W, v.valuation (algebraMap _ K a) ≤ 1) ∧
      ∀ a ∈ maximalIdeal (locRing (mCoordIdeal w) W), v.valuation (algebraMap _ K a) < 1} =
      {v : Place (ZMod p) K | Dom v w W} := by
    ext v
    exact hρ.dom_iff hV hWp hVW v
  rw [hset] at key
  rw [hlen, locIdeal_eq_span hym, GlobalTheory.T.geometric_number_zero_finrank B J p K w hbir k c hc W hWd b]
  have : (algebraMap (locRing (mCoordIdeal w) W) K f) = w ⟨k, c⟩ / w ⟨k, c' k⟩ := hf2
  rw [this] at key
  rw [← key]
  push_cast
  rfl

theorem block_sum (local_term : ∀ (w : (Σ k, J k) → K), Birational w → ∀ (k : B) (c : J k), w ⟨k, c⟩ ≠ 0 →
      ∀ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), ∀ c' : ∀ k, J k, (∀ k, (X ⟨k, c' k⟩ : MRing J) ∉ W) → ∀ b : Fin 0 → B → ℤ,
      (multAt (mCoordIdeal w ⊔ Ideal.span {(X ⟨k, c⟩ : MRing J)}) W : ℤ) * geoNum 0 W b =
        ∑ᶠ v ∈ {v : Place (ZMod p) K | Dom v w W}, (v.deg : ℤ) * v.ord (w ⟨k, c⟩ / w ⟨k, c' k⟩))
    (exists_centre : ∀ (w : (Σ k, J k) → K), Birational w → (∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) → ∀ (v : Place (ZMod p) K) (k : B) (c : J k),
      w ⟨k, c⟩ ≠ 0 → v.valuation (w ⟨k, c⟩) < (Finset.univ.sup fun i => v.valuation (w ⟨k, i⟩)) →
      ∃ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), Dom v w W)
    (w : (Σ k, J k) → K) (hbir : Birational w) (hw : ∀ k, ∃ c, w ⟨k, c⟩ ≠ 0)
    (hfin : ∀ x : K, x ≠ 0 → {v : Place (ZMod p) K | v.valuation x ≠ 1}.Finite)
    (hprod : ∀ x : K, x ≠ 0 → ∑ᶠ v : Place (ZMod p) K, (v.deg : ℤ) * WithZero.log (v.valuation x) = 0)
    (k : B) (c : J k) (hc : w ⟨k, c⟩ ≠ 0) (b : Fin 0 → B → ℤ) :
    ∑ᶠ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩),
        (multAt (mCoordIdeal w ⊔ Ideal.span {(X ⟨k, c⟩ : MRing J)}) W : ℤ) * geoNum 0 W b =
      ∑ᶠ v : Place (ZMod p) K, (v.deg : ℤ) * WithZero.log (Finset.univ.sup fun i => v.valuation (w ⟨k, i⟩)) := by
  classical
  have hV : (mCoordIdeal w).IsPrime := RingHom.ker_isPrime _
  have hVh : IsMultiHomogIdeal (mCoordIdeal w) := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal w
  set S : Place (ZMod p) K → WithZero (Multiplicative ℤ) := fun v => Finset.univ.sup fun i => v.valuation (w ⟨k, i⟩) with hSdef
  set f : Place (ZMod p) K → ℤ := fun v =>
    (v.deg : ℤ) * (WithZero.log (S v) - WithZero.log (v.valuation (w ⟨k, c⟩))) with hf
  set T : Set (Place (ZMod p) K) := {v | v.valuation (w ⟨k, c⟩) < S v} with hTdef
  have hle : ∀ v : Place (ZMod p) K, v.valuation (w ⟨k, c⟩) ≤ S v := fun v =>
    Finset.le_sup (f := fun i => v.valuation (w ⟨k, i⟩)) (Finset.mem_univ c)
  set U : Set (Place (ZMod p) K) := ⋃ j ∈ {j : J k | w ⟨k, j⟩ ≠ 0}, {v | v.valuation (w ⟨k, j⟩) ≠ 1} with hUdef
  have hU : U.Finite := (Set.toFinite _).biUnion fun j hj => hfin _ hj
  have h1 : ∀ v ∉ U, ∀ j, w ⟨k, j⟩ ≠ 0 → v.valuation (w ⟨k, j⟩) = 1 := by
    intro v hv j hj
    by_contra h
    exact hv (Set.mem_biUnion (show j ∈ {j : J k | w ⟨k, j⟩ ≠ 0} from hj) h)
  have hS1 : ∀ v ∉ U, S v = 1 := by
    intro v hv
    apply le_antisymm
    · refine Finset.sup_le fun i _ => ?_
      by_cases hi : w ⟨k, i⟩ = 0
      · simp [hi]
      · exact (h1 v hv i hi).le
    · calc 1 = v.valuation (w ⟨k, c⟩) := (h1 v hv c hc).symm
        _ ≤ S v := hle v
  have hTU : T ⊆ U := by
    intro v hv
    by_contra hvU
    have h2 : S v = 1 := hS1 v hvU
    have h3 := h1 v hvU c hc
    have h4 : v.valuation (w ⟨k, c⟩) < S v := hv
    rw [h2, h3] at h4
    exact lt_irrefl _ h4
  have hTfin : T.Finite := hU.subset hTU
  have hmain : ∀ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩),
      (multAt (mCoordIdeal w ⊔ Ideal.span {(X ⟨k, c⟩ : MRing J)}) W : ℤ) * geoNum 0 W b =
        ∑ᶠ v ∈ {v : Place (ZMod p) K | Dom v w W}, f v := by
    intro W hW
    choose c' hc' using hW.2
    rw [local_term w hbir k c hc W hW c' hc' b]
    refine finsum_mem_congr rfl fun v hv => ?_
    have hVW : mCoordIdeal w ≤ W := le_trans le_sup_left hW.1.1.2
    have hne : w ⟨k, c' k⟩ ≠ 0 := fun h => hc' k (hVW ((X_mem_iff w k _).2 h))
    have hsup : S v = v.valuation (w ⟨k, c' k⟩) := Dom.sup_eq hv hc' k
    simp only [hf, hsup]
    rw [v.ord_div hc hne]
    simp only [Place.ord]
    ring
  have hset : ∀ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), {v : Place (ZMod p) K | Dom v w W} ⊆ T := by
    intro W hW v hv
    choose c' hc' using hW.2
    have hx : (X ⟨k, c⟩ : MRing J) ∈ W := hW.1.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
    have h2 : S v = v.valuation (w ⟨k, c' k⟩) := Dom.sup_eq hv hc' k
    show v.valuation (w ⟨k, c⟩) < S v
    rw [h2]
    exact Dom.lt_chart hv hc' k hx
  have hcover : T ⊆ ⋃ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), {v : Place (ZMod p) K | Dom v w W} := by
    intro v hv
    obtain ⟨W, hW, hD⟩ := exists_centre w hbir hw v k c hc hv
    exact Set.mem_biUnion hW hD
  have hdisj : (divSupp (mCoordIdeal w) (X ⟨k, c⟩)).PairwiseDisjoint
      (fun W => {v : Place (ZMod p) K | Dom v w W}) := by
    intro W hW W' hW' hne
    refine Set.disjoint_left.2 fun v hv hv' => hne (le_antisymm ?_ ?_)
    · choose c' hc' using hW.2
      exact Dom.le_of_dom hv hv' (isMultiHomogIdeal_of_mem_minimalPrimes hVh
        (GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds.homog_X k c) hW.1) hW.1.1.1 hc'
    · choose c' hc' using hW'.2
      exact Dom.le_of_dom hv' hv (isMultiHomogIdeal_of_mem_minimalPrimes hVh
        (GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds.homog_X k c) hW'.1) hW'.1.1.1 hc'
  have hsupp : T ∩ Function.support f = Set.univ ∩ Function.support f := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_univ, true_and, and_iff_right_iff_imp]
    intro hv
    by_contra hvT
    have h2 : S v = v.valuation (w ⟨k, c⟩) := le_antisymm (not_lt.1 hvT) (hle v)
    exact hv (by simp [hf, h2])
  have hF1 : (Function.support fun v : Place (ZMod p) K => (v.deg : ℤ) * WithZero.log (S v)).Finite := by
    refine hU.subset fun v hv => ?_
    by_contra hvU
    exact hv (by simp [hS1 v hvU])
  have hF2 : (Function.support fun v : Place (ZMod p) K => (v.deg : ℤ) * WithZero.log (v.valuation (w ⟨k, c⟩))).Finite := by
    refine (hfin _ hc).subset fun v hv => ?_
    intro h
    exact hv (by simp [h])
  calc _ = ∑ᶠ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), ∑ᶠ v ∈ {v : Place (ZMod p) K | Dom v w W}, f v :=
        finsum_mem_congr rfl hmain
    _ = ∑ᶠ v ∈ ⋃ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), {v : Place (ZMod p) K | Dom v w W}, f v :=
        (finsum_mem_biUnion hdisj (divSupp_finite _ _) fun W hW => hTfin.subset (hset W hW)).symm
    _ = ∑ᶠ v ∈ T, f v := by
        rw [Set.Subset.antisymm (Set.iUnion₂_subset hset) hcover]
    _ = ∑ᶠ v ∈ (Set.univ : Set (Place (ZMod p) K)), f v := finsum_mem_inter_support_eq f _ _ hsupp
    _ = ∑ᶠ v, f v := finsum_mem_univ f
    _ = ∑ᶠ v : Place (ZMod p) K, ((v.deg : ℤ) * WithZero.log (S v) - (v.deg : ℤ) * WithZero.log (v.valuation (w ⟨k, c⟩))) :=
        finsum_congr fun v => by simp only [hf]; ring
    _ = _ := by
        rw [finsum_sub_distrib hF1 hF2, hprod _ hc, sub_zero]

theorem degree_of_local (local_term : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K), Birational w → ∀ (k : B) (c : J k), w ⟨k, c⟩ ≠ 0 →
      ∀ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), ∀ c' : ∀ k, J k, (∀ k, (X ⟨k, c' k⟩ : MRing J) ∉ W) → ∀ b : Fin 0 → B → ℤ,
      (multAt (mCoordIdeal w ⊔ Ideal.span {(X ⟨k, c⟩ : MRing J)}) W : ℤ) * geoNum 0 W b =
        ∑ᶠ v ∈ {v : Place (ZMod p) K | Dom v w W}, (v.deg : ℤ) * v.ord (w ⟨k, c⟩ / w ⟨k, c' k⟩))
    (exists_centre : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K), Birational w → (∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) → ∀ (v : Place (ZMod p) K) (k : B) (c : J k),
      w ⟨k, c⟩ ≠ 0 → v.valuation (w ⟨k, c⟩) < (Finset.univ.sup fun i => v.valuation (w ⟨k, i⟩)) →
      ∃ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), Dom v w W) :
    ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [GroundTheory.FunctionField.IsFunctionField (ZMod p) K] (C : ACurve K) (w : (Σ k, J k) → K) (a : B → ℤ), IsFFCurve (ZMod p) C → Birational w → (∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) → geoNum 1 (mCoordIdeal w) (fun _ => a) = coordDeg C w a := by
  intro B _ J _ p _ K _ _ _ C w a hC hbir hw
  classical
  obtain ⟨e, he⟩ := hC
  have hfin : ∀ x : K, x ≠ 0 → {v : Place (ZMod p) K | v.valuation x ≠ 1}.Finite := by
    intro x hx
    refine ((C.fin x hx).image e).subset fun v hv => ⟨e.symm v, ?_, by simp⟩
    have := (he (e.symm v)).1
    simp only [Equiv.apply_symm_apply] at this
    simpa [this] using hv
  have hprod : ∀ x : K, x ≠ 0 → ∑ᶠ v : Place (ZMod p) K, (v.deg : ℤ) * WithZero.log (v.valuation x) = 0 := by
    intro x hx
    rw [← C.prod x hx, ← finsum_comp_equiv e]
    refine finsum_congr fun i => ?_
    rw [(he i).1, (he i).2]
  have hrel : IsRelevant (mCoordIdeal w) := fun k => by
    obtain ⟨c, hc⟩ := hw k
    exact ⟨c, fun h => hc ((X_mem_iff w k c).1 h)⟩
  show geoNum (0 + 1) (mCoordIdeal w) (fun _ => a) = _
  rw [geoNum, dite_eq_left hrel, coordDeg]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hck : w ⟨k, (hrel k).choose⟩ ≠ 0 := fun h => (hrel k).choose_spec ((X_mem_iff w k _).2 h)
  rw [block_sum (local_term B J p K) (exists_centre B J p K) w hbir hw hfin hprod k _ hck, ← finsum_comp_equiv e]
  congr 1
  refine finsum_congr fun i => ?_
  simp only [(he i).1, (he i).2]

theorem geoNum_one_eq_coordDeg : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [GroundTheory.FunctionField.IsFunctionField (ZMod p) K] (C : ACurve K) (w : (Σ k, J k) → K) (a : B → ℤ), IsFFCurve (ZMod p) C → Birational w → (∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) → geoNum 1 (mCoordIdeal w) (fun _ => a) = coordDeg C w a :=
  degree_of_local (fun _ _ _ _ _ _ _ _ _ _ w hbir k c hc W hW c' hc' b => local_term w hbir k c hc W hW c' hc' b)
    (fun _ _ _ _ _ _ _ _ _ _ w hbir hw v k c hc hlt => exists_centre w hbir hw v k c hc hlt)

end
end GlobalTheory.CompanionTheory.Ar.GeoDeg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldDegreeEqStatement
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.function_field_degree_eq : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [GroundTheory.FunctionField.IsFunctionField (ZMod p) K] (C : ACurve K) (w : (Σ k, J k) → K) (a : B → ℤ), IsFFCurve (ZMod p) C → Birational w → (∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) → geoNum 1 (mCoordIdeal w) (fun _ => a) = coordDeg C w a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GeoDeg.geoNum_one_eq_coordDeg | exact GlobalTheory.CompanionTheory.Ar.GeoDeg.geoNum_one_eq_coordDeg | (intros; apply GlobalTheory.CompanionTheory.Ar.GeoDeg.geoNum_one_eq_coordDeg <;> assumption)
end
