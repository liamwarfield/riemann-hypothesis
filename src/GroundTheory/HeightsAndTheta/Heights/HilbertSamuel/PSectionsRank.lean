module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResVolume
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRatNoetherFrame
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionsRank
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open scoped Pointwise

noncomputable section

namespace SectionsRank

theorem sec_eq_span (o : Type*) [CommRing o] {Ω : Type*} [CommRing Ω] [Algebra o Ω] {ι : Type*}
    (x : ι → Ω) (n : ℕ) : sec o x n = Submodule.span o (Set.range x ^ n) := by
  unfold sec
  rw [← MvPolynomial.homogeneousSubmodule_one_pow, Submodule.map_pow,
    MvPolynomial.homogeneousSubmodule_one_eq_span_X, Submodule.map_span, ← Set.range_comp,
    Submodule.span_pow]
  congr 3
  ext i
  simp

theorem exists_int_multiple {ι : Type*} (f : MvPolynomial ι ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∃ p : MvPolynomial ι ℤ, map (Int.castRingHom ℚ) p = (N : ℚ) • f := by
  induction f using MvPolynomial.induction_on with
  | C q =>
    refine ⟨q.den, q.pos, C q.num, ?_⟩
    rw [map_C, smul_eq_C_mul, ← C_mul, Rat.den_mul_eq_num]
    rfl
  | add f g hf hg =>
    obtain ⟨a, ha, p, hp⟩ := hf
    obtain ⟨b, hb, r, hr⟩ := hg
    refine ⟨a * b, Nat.mul_pos ha hb, (b : ℤ) • p + (a : ℤ) • r, ?_⟩
    rw [map_add (f := _), smul_eq_C_mul, smul_eq_C_mul, map_mul, map_mul, hp, hr, map_C, map_C]
    simp only [smul_eq_C_mul, eq_intCast, Int.cast_natCast, Nat.cast_mul, map_mul]
    ring
  | mul_X f i hf =>
    obtain ⟨a, ha, p, hp⟩ := hf
    refine ⟨a, ha, p * X i, ?_⟩
    rw [map_mul, hp, map_X, smul_mul_assoc]

variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type}

theorem mem_map_coordIdeal_iff [Fintype J] (x : J → Ω) {n : ℕ} {f : MvPolynomial J ℚ}
    (hf : f.IsHomogeneous n) :
    f ∈ (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)) ↔ aeval x f = 0 := by
  constructor
  · intro h
    have hle : (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)) ≤
        RingHom.ker (aeval x : MvPolynomial J ℚ →ₐ[ℚ] Ω) := by
      rw [Ideal.map_le_iff_le_comap]
      intro p hp
      rw [Ideal.mem_comap, RingHom.mem_ker, ← algebraMap_int_eq]
      change aeval x (MvPolynomial.map (algebraMap ℤ ℚ) p) = 0
      rw [aeval_map_algebraMap]
      exact aeval_eq_zero_of_mem_coordIdeal hp
    exact hle h
  · intro h
    obtain ⟨N, hN, p, hp⟩ := exists_int_multiple f
    have hpn : p.IsHomogeneous n := by
      refine IsHomogeneous.of_map (f := Int.castRingHom ℚ) (RingHom.injective_int _) ?_
      rw [hp]
      exact (mem_homogeneousSubmodule n _).mp
        (Submodule.smul_mem _ _ ((mem_homogeneousSubmodule n f).mpr hf))
    have hp0 : aeval x p = 0 := by
      rw [← aeval_map_algebraMap ℚ, algebraMap_int_eq, hp, map_smul, h, smul_zero]
    have hmem := Ideal.mem_map_of_mem (MvPolynomial.map (Int.castRingHom ℚ))
      (mem_coordIdeal_of_isHomogeneous ℤ x hpn hp0)
    rw [hp, smul_eq_C_mul] at hmem
    have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    have := Ideal.mul_mem_left _ (C (N : ℚ)⁻¹) hmem
    rwa [← mul_assoc, ← C_mul, inv_mul_cancel₀ hN', C_1, one_mul] at this

theorem finrank_map_eq {K M N N' : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [AddCommGroup N'] [Module K N'] (V : Submodule K M)
    (f : M →ₗ[K] N) (g : M →ₗ[K] N') (h : ∀ v ∈ V, f v = 0 ↔ g v = 0) :
    Module.finrank K (V.map f) = Module.finrank K (V.map g) := by
  have ef : V.map f = LinearMap.range (f ∘ₗ V.subtype) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have eg : V.map g = LinearMap.range (g ∘ₗ V.subtype) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hk : LinearMap.ker (f ∘ₗ V.subtype) = LinearMap.ker (g ∘ₗ V.subtype) := by
    ext v
    simpa using h v v.2
  rw [ef, eg]
  exact ((f ∘ₗ V.subtype).quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ hk).trans (g ∘ₗ V.subtype).quotKerEquivRange)).finrank_eq

theorem finrank_sec_int [Fintype J] (x : J → Ω) (n : ℕ) :
    Module.finrank ℤ (sec ℤ x n) = Module.finrank ℚ (sec ℚ x n) := by
  have : Module.Finite ℤ (sec ℤ x n) := Module.Finite.iff_fg.mpr (sec_fg x n)
  let b := Module.Free.chooseBasis ℤ (sec ℤ x n)
  let v : Module.Free.ChooseBasisIndex ℤ (sec ℤ x n) → Ω := fun i => (b i : Ω)
  have hli : LinearIndependent ℤ v :=
    b.linearIndependent.map' (sec ℤ x n).subtype (Submodule.ker_subtype _)
  have hliQ : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hli
  have hspanZ : Submodule.span ℤ (Set.range v) = sec ℤ x n := by
    have : Set.range v = (sec ℤ x n).subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hspanQ : Submodule.span ℚ (Set.range v) = sec ℚ x n := by
    rw [← Submodule.span_span_of_tower ℤ, hspanZ, sec_eq_span ℤ, sec_eq_span ℚ,
      Submodule.span_span_of_tower]
  rw [Module.finrank_eq_card_chooseBasisIndex, ← hspanQ, finrank_span_eq_card hliQ]

end SectionsRank


open SectionsRank in
theorem SectionsRank.proof : SectionsRank.Statement := by
  intro Ω _ _ κ _ x n
  set q := (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ))
  have hw : GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight (GlobalTheory κ) = fun _ _ => 1 := by
    funext v u
    simp [GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight]
  have hV : weightedHomogeneousSubmodule ℚ (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight (GlobalTheory κ))
      (fun _ => n) = homogeneousSubmodule (Ix κ) ℚ n := by
    ext f
    rw [mem_weightedHomogeneousSubmodule, mem_homogeneousSubmodule, hw]
    have hwt : ∀ d : Ix κ →₀ ℕ,
        Finsupp.weight (fun _ _ => (1 : ℕ) : Ix κ → Unit → ℕ) d = fun _ => Finsupp.weight 1 d := by
      intro d
      funext u
      simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
    simp only [IsHomogeneous, IsWeightedHomogeneous, hwt, funext_iff, forall_const]
  have hg : ∀ m : Unit → ℕ, m = (fun _ => n) →
      GroundTheory.Heights₂.Heights.NumbersDVR.gradedPiece q m =
        (homogeneousSubmodule (Ix κ) ℚ n).map (Ideal.Quotient.mkₐ ℚ q).toLinearMap := by
    rintro m rfl
    unfold GroundTheory.Heights₂.Heights.NumbersDVR.gradedPiece
    rw [hV]
  unfold GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn
  rw [if_pos (fun _ => Int.natCast_nonneg n), hg _ (by funext; simp), finrank_sec_int]
  congr 1
  refine finrank_map_eq _ _ _ fun f hf => ?_
  rw [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem,
    AlgHom.toLinearMap_apply]
  exact mem_map_coordIdeal_iff x ((mem_homogeneousSubmodule n f).mp hf)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefAmpleFibre
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

set_option linter.unusedSectionVars false

namespace NefAmpleFibreAlt

section Reduction

variable {K : Type} {ι : K → Type} (p : ℕ)

abbrev red : MRing ι →+* MRingOver (ZMod p) ι := MvPolynomial.map (Int.castRingHom (ZMod p))

theorem red_surjective : Function.Surjective (red (ι := ι) p) :=
  MvPolynomial.map_surjective _ (fun x => ZMod.intCast_surjective x)

theorem ker_red_le {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J) :
    RingHom.ker (red (ι := ι) p) ≤ J := by
  rw [MvPolynomial.ker_map, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton, Ideal.span_le,
    Set.singleton_subset_iff]
  simpa using hp

theorem mem_map_red_iff {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J) (g : MRing ι) :
    red p g ∈ J.map (red p) ↔ g ∈ J := by
  rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ (red_surjective p), sup_eq_left.mpr]
  rw [← RingHom.ker_eq_comap_bot]
  exact ker_red_le p hp

theorem ringKrullDim_red {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J) :
    ringKrullDim (MRingOver (ZMod p) ι ⧸ J.map (red p)) = ringKrullDim (MRing ι ⧸ J) := by
  have e : J = RingHom.ker ((Ideal.Quotient.mk (J.map (red p))).comp (red p)) := by
    ext g
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, mem_map_red_iff p hp]
  exact (ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq e).trans
    (RingHom.quotientKerEquivOfSurjective (Ideal.Quotient.mk_surjective.comp (red_surjective p))))).symm

end Reduction

section Homog

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {R S : Type} [CommRing R] [CommRing S]

theorem map_weightedHomogeneousComponent (f : R →+* S) (w : (Σ k, ι k) → K → ℕ) (b : K → ℕ)
    (g : MRingOver R ι) :
    weightedHomogeneousComponent w b (MvPolynomial.map f g) =
      MvPolynomial.map f (weightedHomogeneousComponent w b g) := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_map, coeff_map, coeff_weightedHomogeneousComponent]
  split_ifs <;> simp

theorem isMultiHomogIdeal_map (f : R →+* S) {V : Ideal (MRingOver R ι)} (hV : IsMultiHomogIdeal V) :
    IsMultiHomogIdeal (V.map (MvPolynomial.map f)) := by
  obtain ⟨T, hT, rfl⟩ := hV
  refine ⟨MvPolynomial.map f '' T, ?_, by rw [Ideal.map_span]⟩
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨a, ha⟩ := hT g hg
  exact ⟨a, fun m hm => ha m (support_map_subset _ _ hm)⟩

theorem isMultiHomogIdeal_comap (f : R →+* S) {W : Ideal (MRingOver S ι)} (hW : IsMultiHomogIdeal W) :
    IsMultiHomogIdeal (W.comap (MvPolynomial.map f)) := by
  classical
  have hW' := (Bridge.isMultiHomogIdeal_iff (R := S) W).mpr hW
  refine (Bridge.isMultiHomogIdeal_iff (R := R) _).mp fun g hg b => ?_
  rw [Ideal.mem_comap, ← map_weightedHomogeneousComponent]
  exact hW' _ hg b

end Homog

section Nef

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem nefOnF_map_red (ℓ : ℕ) [Fact ℓ.Prime] (hGeo : GeoNumStatement ι) {I : IFamily (ZMod ℓ) ι}
    (hI : IsFieldIntersection I) {P : Ideal (MRing ι)} {α : K → ℤ} (hN : NefOnFibres P α) :
    KH.NefOnF I (P.map (red ℓ)) α := by
  intro W' hW' hle
  obtain ⟨⟨hW'p, hW'h, hW'r⟩, hW'd⟩ := hW'
  set W := W'.comap (red ℓ) with hWdef
  have hmap : W.map (red ℓ) = W' := Ideal.map_comap_of_surjective _ (red_surjective ℓ) W'
  have hpW : ((ℓ : ℕ) : MRing ι) ∈ W := by
    have h0 : ((ℓ : ℕ) : MRingOver (ZMod ℓ) ι) = 0 := by
      rw [← map_natCast (C : ZMod ℓ →+* MRingOver (ZMod ℓ) ι), ZMod.natCast_self, map_zero]
    rw [hWdef, Ideal.mem_comap, map_natCast, h0]
    exact W'.zero_mem
  have hWm : IsMultiProjPrime W := by
    refine ⟨Ideal.comap_isPrime _ W', isMultiHomogIdeal_comap _ hW'h, fun k => ?_⟩
    obtain ⟨i, hi⟩ := hW'r k
    refine ⟨i, ?_⟩
    rw [hWdef, Ideal.mem_comap, map_X]
    exact hi
  have hPW : P ≤ W := Ideal.map_le_iff_le_comap.mp hle
  have hdim : ringKrullDim (MRing ι ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [← ringKrullDim_red ℓ hpW, hmap, hW'd]
  have hchar : charOf W ≠ 0 := by
    intro h0
    have hg : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι)) = 0 := Int.natAbs_eq_zero.mp h0
    have hmem : ((ℓ : ℕ) : ℤ) ∈ W.comap (C : ℤ →+* MRing ι) := by
      rw [Ideal.mem_comap, map_natCast]
      exact hpW
    rw [← Submodule.IsPrincipal.span_singleton_generator (W.comap (C : ℤ →+* MRing ι)), hg,
      Ideal.mem_span_singleton, zero_dvd_iff] at hmem
    exact (Fact.out : ℓ.Prime).ne_zero (by exact_mod_cast hmem)
  have hWp : IsProjVarF (W.map (MvPolynomial.map (Int.castRingHom (ZMod ℓ)))) 1 := by
    show IsProjVarF (W.map (red ℓ)) 1
    rw [hmap]
    exact ⟨⟨hW'p, hW'h, hW'r⟩, hW'd⟩
  have h := hN W hWm hPW hchar hdim
  rw [hGeo ℓ I hI W 1 _ hWm hpW hWp] at h
  change 0 ≤ I (W.map (red ℓ)) 1 (fun _ => α) at h
  rw [hmap] at h
  convert h using 2
  funext j
  fin_cases j
  rfl

end Nef

end NefAmpleFibreAlt


open NefAmpleFibreAlt in
theorem NefAmpleFibre.proof (hK : KleimanScheme.Statement)
    (hGeo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GeoNumStatement ι)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι) :
    NefAmpleFibre.Statement := by
  intro K _ _ ι _ _ Ω _ y D α b a ℓ hP hN hb ha hℓ
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨I, hI, -⟩ := hR4 (ZMod ℓ) K ι
  have e : ((b : ℤ) • α + fun _ => (a : ℤ)) = (b • α + fun _ => (a : ℤ)) := by
    rw [natCast_zsmul]
  rw [e]
  exact hK (ZMod ℓ) K ι I (fibreIdeal ℓ y) α b a hI (isMultiHomogIdeal_map _ hP.2.1.2.1)
    (nefOnF_map_red ℓ (hGeo K ι) hI hN) hb ha

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.WhittakerFunctional
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 Filter Topology

noncomputable section

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem G5.fderiv_fderiv_eq_of_add_const {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : E → ℝ} {y : E}
    (b : ℝ) (h : ∀ᶠ y' in 𝓝 y, f y' = g y' + b) : fderiv ℝ (fderiv ℝ f) y = fderiv ℝ (fderiv ℝ g) y := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [h.eventually_nhds] with y' hy'
  have hfg : f =ᶠ[𝓝 y'] fun x => g x + b := hy'
  rw [hfg.fderiv_eq, fderiv_add_const]

theorem G5.ptsIntegral_eq_of_add_const {e : ℕ} (P : Ideal (MRing ι)) (φ ψ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (h : ∀ j, ∃ b : ℝ, ∀ z ∈ mcPts P, φ j z = ψ j z + b) (g : ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral P φ g = ptsIntegral P ψ g := by
  have hs : ∀ Ψ y w, sheetDensity P Ψ φ g y w = sheetDensity P Ψ ψ g y w := by
    intro Ψ y w
    unfold sheetDensity
    split_ifs with hγ
    · congr 1
      have hH : ∀ j, cxHessian (fun y' => φ j (hγ.choose y')) y = cxHessian (fun y' => ψ j (hγ.choose y')) y := by
        intro j
        obtain ⟨b, hb⟩ := h j
        have hev : ∀ᶠ y' in 𝓝 y, φ j (hγ.choose y') = ψ j (hγ.choose y') + b :=
          hγ.choose_spec.2.mono fun y' hy' => hb _ hy'.2.1
        unfold cxHessian
        rw [G5.fderiv_fderiv_eq_of_add_const b hev]
      simp only [maDensity, hH]
    · rfl
  unfold ptsIntegral ptsIntegralAt
  simp only [hs]

theorem G5.ptsIntegral_const {e : ℕ} (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (c : ℝ) :
    ptsIntegral P φ (fun _ => c) = c * ptsIntegral P φ (fun _ => 1) := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext y
    rw [mul_finsum_mem]
    refine finsum_mem_congr rfl fun w _ => ?_
    unfold sheetDensity
    split_ifs <;> ring
  · simp

theorem G5.isSmoothHerm_constLine (c : ℝ) : IsSmoothHerm (constLine (ι := ι) c) := by
  show ContDiffOn ℝ _ (fun _ => Real.exp (-c)) _
  exact contDiffOn_const

theorem G5.log_tensor_constLine (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ℝ) (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log ((A.tensor (constLine c)).h z) = Real.log (A.h z) + -c := by
  show Real.log (A.h z * Real.exp (-c)) = _
  rw [Real.log_mul (A.pos z hz).ne' (Real.exp_pos _).ne', Real.log_exp]

theorem G5.top_tensor_constLine (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) (P : Ideal (MRing ι)) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ℝ)
    (hP : IsArithVar P (D + 1)) (hA : IsSmoothHerm A) :
    I P (D + 1) (fun _ => A.tensor (constLine c)) =
      I P (D + 1) (fun _ => A) - ((D + 1 : ℕ) : ℝ) * c * geomDeg P A D := by
  set A' := A.tensor (constLine (ι := ι) c) with hA'def
  have hA' : IsSmoothHerm A' := hA.mul (G5.isSmoothHerm_constLine c)
  let L : ℕ → Fin (D + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun k j => if (j : ℕ) < k then A' else A
  have hL2 : ∀ k j, L k j = A ∨ L k j = A' := fun k j => by
    by_cases h : (j : ℕ) < k
    · exact Or.inr (if_pos h)
    · exact Or.inl (if_neg h)
  have hLs : ∀ k j, IsSmoothHerm (L k j) := fun k j => (hL2 k j).elim (fun h => h ▸ hA) (fun h => h ▸ hA')

  have hint : ∀ M : Fin D → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, (∀ j, M j = A ∨ M j = A') →
      ptsIntegral P (pot M) (fun _ => c) = c * geomDeg P A D := by
    intro M hM
    rw [G5.ptsIntegral_const]
    congr 1
    refine G5.ptsIntegral_eq_of_add_const P _ _ (fun j => ?_) _
    rcases hM j with h | h
    · exact ⟨0, fun z _ => by simp [pot, h]⟩
    · exact ⟨-c, fun z hz => by simp only [pot, h]; exact G5.log_tensor_constLine A c z hz.1⟩
  have step : ∀ k, k ≤ D + 1 → I P (D + 1) (L k) = I P (D + 1) (fun _ => A) - (k : ℝ) * c * geomDeg P A D := by
    intro k
    induction k with
    | zero =>
      intro _
      have : L 0 = fun _ => A := by funext j; simp [L]
      rw [this]; simp
    | succ k ih =>
      intro hk
      have hkD : k < D + 1 := by omega
      set i : Fin (D + 1) := ⟨k, hkD⟩
      set σ := Equiv.swap i (Fin.last D)
      set M : Fin D → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun j => L (k + 1) (σ (Fin.castSucc j))
      have hne : ∀ j : Fin D, σ (Fin.castSucc j) ≠ i := by
        intro j hj
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at hj
        exact (Fin.castSucc_lt_last j).ne hj
      have hMk : ∀ j : Fin D, L k (σ (Fin.castSucc j)) = M j := by
        intro j
        have h1 : ((σ (Fin.castSucc j) : Fin (D + 1)) : ℕ) ≠ k := fun h => hne j (Fin.ext h)
        simp only [M, L]
        by_cases h2 : ((σ (Fin.castSucc j) : Fin (D + 1)) : ℕ) < k
        · rw [if_pos h2, if_pos (by omega)]
        · rw [if_neg h2, if_neg (by omega)]
      have hσi : σ (Fin.last D) = i := Equiv.swap_apply_right _ _
      have e1 : L (k + 1) ∘ σ = Fin.snoc M A' := by
        funext x
        refine Fin.lastCases ?_ (fun j => ?_) x
        · simp only [Function.comp_apply, Fin.snoc_last, hσi, L, i]
          exact if_pos (Nat.lt_succ_self k)
        · simp only [Function.comp_apply, Fin.snoc_castSucc, M]
      have e0 : L k ∘ σ = Fin.snoc M A := by
        funext x
        refine Fin.lastCases ?_ (fun j => ?_) x
        · simp only [Function.comp_apply, Fin.snoc_last, hσi, L, i]
          exact if_neg (lt_irrefl k)
        · simp only [Function.comp_apply, Fin.snoc_castSucc]
          exact hMk j
      have hM : ∀ j, M j = A ∨ M j = A' := fun j => hL2 _ _
      have hMs : ∀ j, IsSmoothHerm (M j) := fun j => hLs _ _
      have hmc := metricChange K ι I hI P D M A (fun _ => c) (fun _ _ _ => rfl) hP hMs hA contDiffOn_const
      have s1 := hI.1 P (D + 1) (L (k + 1)) σ hP (hLs _)
      have s0 := hI.1 P (D + 1) (L k) σ hP (hLs _)
      rw [e1] at s1
      rw [e0] at s0
      have hsnoc : I P (D + 1) (Fin.snoc M A') =
          I P (D + 1) (Fin.snoc M A) - ptsIntegral P (pot M) (fun _ => c) := hmc
      rw [← s1, hsnoc, s0, ih (by omega), hint M hM]
      push_cast
      ring
  have hall : L (D + 1) = fun _ => A' := by
    funext j
    exact if_pos j.isLt
  have := step (D + 1) le_rfl
  rw [hall] at this
  rw [this]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecondVeronese
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Veronese

theorem pair_eq {D : ℕ} {i j k l : Fin (D + 1)} (hij : i ≤ j) (hkl : k ≤ l)
    (h : (Finsupp.single i 1 + Finsupp.single j 1 : Fin (D + 1) →₀ ℕ) = Finsupp.single k 1 + Finsupp.single l 1) :
    i = k ∧ j = l := by
  have hm : ({i} + {j} : Multiset (Fin (D + 1))) = {k} + {l} := by
    have := congrArg Finsupp.toMultiset h
    simpa only [map_add (f := _), Finsupp.toMultiset_single, one_nsmul] using this
  have h1 : i = k ∨ i = l := by
    have : i ∈ ({k} + {l} : Multiset (Fin (D + 1))) := hm ▸ Multiset.mem_add.2 (Or.inl (Multiset.mem_singleton_self i))
    simpa using this
  have h2 : j = k ∨ j = l := by
    have : j ∈ ({k} + {l} : Multiset (Fin (D + 1))) := hm ▸ Multiset.mem_add.2 (Or.inr (Multiset.mem_singleton_self j))
    simpa using this
  have h3 : k = i ∨ k = j := by
    have : k ∈ ({i} + {j} : Multiset (Fin (D + 1))) := hm.symm ▸ Multiset.mem_add.2 (Or.inl (Multiset.mem_singleton_self k))
    simpa using this
  have h4 : l = i ∨ l = j := by
    have : l ∈ ({i} + {j} : Multiset (Fin (D + 1))) := hm.symm ▸ Multiset.mem_add.2 (Or.inr (Multiset.mem_singleton_self l))
    simpa using this
  rw [Fin.le_iff_val_le_val] at hij hkl
  simp only [Fin.ext_iff] at h1 h2 h3 h4 ⊢
  omega

theorem exponent_injective (D : ℕ) :
    Function.Injective fun q : Ix (Idx D) =>
      (Finsupp.single q.2.1.1 1 + Finsupp.single q.2.1.2 1 : Fin (D + 1) →₀ ℕ) := by
  intro q q' h
  obtain ⟨u, ⟨⟨i, j⟩, hij⟩⟩ := q
  obtain ⟨u', ⟨⟨k, l⟩, hkl⟩⟩ := q'
  obtain ⟨rfl, rfl⟩ := pair_eq hij hkl h
  cases u
  cases u'
  rfl

def polyMap (D : ℕ) : MvPolynomial (Fin (D + 1)) ℤ →+* Fld D :=
  (algebraMap (MvPolynomial (Fin (D + 1)) ℚ) (Fld D)).comp (MvPolynomial.map (Int.castRingHom ℚ))

theorem polyMap_injective (D : ℕ) : Function.Injective (polyMap D) :=
  (IsFractionRing.injective (MvPolynomial (Fin (D + 1)) ℚ) (Fld D)).comp
    (MvPolynomial.map_injective _ (RingHom.injective_int (Int.castRingHom ℚ)))

theorem x_linearIndependent (D : ℕ) : LinearIndependent ℤ (x D) := by
  have hmono : LinearIndependent ℤ fun q : Ix (Idx D) =>
      (X q.2.1.1 * X q.2.1.2 : MvPolynomial (Fin (D + 1)) ℤ) := by
    have h := (basisMonomials (Fin (D + 1)) ℤ).linearIndependent.comp _ (exponent_injective D)
    have e : (fun q : Ix (Idx D) => (X q.2.1.1 * X q.2.1.2 : MvPolynomial (Fin (D + 1)) ℤ)) =
        ⇑(basisMonomials (Fin (D + 1)) ℤ) ∘ fun q : Ix (Idx D) =>
          (Finsupp.single q.2.1.1 1 + Finsupp.single q.2.1.2 1 : Fin (D + 1) →₀ ℕ) := by
      funext q
      simp only [Function.comp_apply, coe_basisMonomials, X, monomial_mul, mul_one]
    rw [e]
    exact h
  have h2 := hmono.map' (polyMap D).toAddMonoidHom.toIntLinearMap
    (LinearMap.ker_eq_bot.mpr (polyMap_injective D))
  have e2 : x D = ⇑(polyMap D).toAddMonoidHom.toIntLinearMap ∘ fun q : Ix (Idx D) =>
      (X q.2.1.1 * X q.2.1.2 : MvPolynomial (Fin (D + 1)) ℤ) := by
    funext q
    simp [x, t, polyMap, map_mul]
  rw [e2]
  exact h2

theorem isSmoothMetric_metric (D : ℕ) : IsSmoothMetric (metric D) := by
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (scale D) :=
    contDiff_pi.2 fun q => contDiff_const.mul (contDiff_apply ℝ (fun _ => ℂ) q)
  exact (ProjLine.isSmoothMetric_fs (J := Ix (Idx D))).comp hs.contDiffOn fun z hz => scale_ne_zero hz

theorem isConjInvariant_metric (D : ℕ) : IsConjInvariant (metric D) := by
  intro z
  have h : scale D (fun q => conj (z q)) = fun q => conj (scale D z q) := by
    funext q
    simp [scale, map_mul, Complex.conj_ofReal]
  show (fsMetric (ι := Ix (Idx D))).ρ (scale D _) = (fsMetric (ι := Ix (Idx D))).ρ (scale D z)
  rw [h]
  exact ProjLine.isConjInvariant_fs (scale D z)

theorem eval_smul_homog {ι : Type*} {φ : MvPolynomial ι ℂ} {n : ℕ} (hφ : φ.IsHomogeneous n) (c : ℂ)
    (z : ι → ℂ) : eval (c • z) φ = c ^ n * eval z φ := by
  classical
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = n := by
    by_contra h
    exact (mem_support_iff.mp hd) (hφ.coeff_eq_zero h)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hs : d.degree = ∑ i ∈ d.support, d i := rfl
  rw [← hdeg, hs]
  ring

theorem pairVal_smul {D n : ℕ} {b b' : MvPolynomial (Ix (Idx D)) ℚ}
    (hb : ∃ f : MvPolynomial (Ix (Idx D)) ℤ, f.IsHomogeneous n ∧ b = MvPolynomial.map (Int.castRingHom ℚ) f)
    (hb' : ∃ f : MvPolynomial (Ix (Idx D)) ℤ, f.IsHomogeneous n ∧ b' = MvPolynomial.map (Int.castRingHom ℚ) f)
    (c : ℂ) (z : Ix (Idx D) → ℂ) (hc : c ≠ 0) :
    pairVal (metric D) n b b' (c • z) = pairVal (metric D) n b b' z := by
  obtain ⟨f, hf, rfl⟩ := hb
  obtain ⟨f', hf', rfl⟩ := hb'
  unfold pairVal
  rw [eval_smul_homog ((hf.map _).map _), eval_smul_homog ((hf'.map _).map _), (metric D).smul]
  have key : c ^ n * conj (c ^ n) = (((‖c‖ ^ (2 * n) : ℝ)) : ℂ) := by
    rw [map_pow, ← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hK : (((‖c‖ ^ (2 * n) : ℝ)) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < ‖c‖ := norm_pos_iff.mpr hc
    exact_mod_cast (pow_pos this _).ne'
  have hL : ∀ A B : ℂ, A * c ^ n * conj (B * c ^ n) = (((‖c‖ ^ (2 * n) : ℝ)) : ℂ) * (A * conj B) := by
    intro A B
    rw [← key, map_mul]
    ring
  rw [mul_comm (c ^ n), mul_comm (c ^ n), hL, mul_pow]
  push_cast
  exact mul_div_mul_left _ _ (by exact_mod_cast hK)

end Veronese

open Veronese

theorem SecondVeronese.proof (hA : VeroneseArith.Statement) (hS : VeroneseSemipos.Statement)
    (hR : VeroneseResolution.Statement) (hC : VeroneseChi.Statement) (hT : VeroneseTop.Statement)
    (hG : VeroneseGenDeg.Statement) : SecondVeronese.Statement := by
  intro D hD
  obtain ⟨J, R, meas, borel, dV, hvol, htr⟩ := hR D hD
  let d : HSMDatum D (Fld D) (Idx D) :=
    { x := x D, m := metric D, P0 := ⊥, J := J, R := R, meas := meas, borel := borel, dV := dV,
      one_le := hD, arith := hA D hD, indep := x_linearIndependent D, smooth := isSmoothMetric_metric D,
      conjInv := isConjInvariant_metric D, normalForm_baseLattice_le_dualSpan_sup_line := bot_le, semipos := hS D, vol := hvol }
  refine ⟨Fld D, inferInstance, inferInstance, Idx D, inferInstance, d, fun n => ?_,
    fun I hI => hT D hD I hI, hG D hD⟩

  have hgram : ∀ {r : ℕ} (b : Fin r → MvPolynomial (Ix (Idx D)) ℚ),
      (∀ k, ∃ f : MvPolynomial (Ix (Idx D)) ℤ, f.IsHomogeneous n ∧ b k = MvPolynomial.map (Int.castRingHom ℚ) f) →
      resGram d n b = Veronese.gram D n b := by
    intro r b hb
    ext k l
    have e1 := htr (fun z => pairVal (metric D) n (b k) (b l) z)
      (fun c z hc => pairVal_smul (hb k) (hb l) c z hc)
    have e2 := htr (fun z => pairVal (metric D) n (b k) (b l) (conjPt z)) fun c z hc => by
      have : conjPt (c • z) = conj c • conjPt z := by
        funext q
        simp [conjPt]
      simp only [this]
      exact pairVal_smul (hb k) (hb l) _ _ ((map_ne_zero _).mpr hc)
    unfold resGram Veronese.gram resPt
    rw [e1, e2]
  rw [← hC D hD n]
  unfold resChi Veronese.chi
  split_ifs with h1
  · rw [hgram _ h1.choose_spec.1]
  · rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBoundedMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SectionBoundedMul

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]


omit [Fintype K] in
theorem isMultiHomog_mul {g h : MRing ι} {a b : K → ℕ} (hg : IsMultiHomog g a)
    (hh : IsMultiHomog h b) : IsMultiHomog (g * h) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (support_mul g h hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply]
  rw [hg m₁ hm₁ k, hh m₂ hm₂ k]


omit [Fintype K] in
theorem isMultiHomog_sub {g h : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d)
    (hh : IsMultiHomog h d) : IsMultiHomog (g - h) d := by
  classical
  intro m hm
  rcases Finset.mem_union.mp (support_sub _ g h hm) with hm | hm
  · exact hg m hm
  · exact hh m hm


omit [Fintype K] in
theorem isMultiHomog_monomial (e : (Σ k, ι k) →₀ ℕ) (r : ℤ) :
    IsMultiHomog (monomial e r : MRing ι) (fun k => ∑ i, e ⟨k, i⟩) := by
  classical
  intro m hm k
  rw [Finset.mem_singleton.mp (support_monomial_subset hm)]


open Classical in
theorem sum_single_apply (k' : K) (j : ι k') (b : ℕ) (k : K) :
    ∑ i, (Finsupp.single (⟨k', j⟩ : Σ k, ι k) b) ⟨k, i⟩ = if k' = k then b else 0 := by
  classical
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro he
    exact h (Sigma.mk.inj_iff.mp he).1

def chartMono (c : ∀ k, ι k) (d : K → ℕ) : MRing ι :=
  ∏ k, X ⟨k, c k⟩ ^ d k

theorem isMultiHomog_chartMono (c : ∀ k, ι k) (d : K → ℕ) : IsMultiHomog (chartMono c d) d := by
  classical
  have h : chartMono c d = monomial (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k)) (1 : ℤ) := by
    rw [chartMono, monomial_sum_one]
    exact Finset.prod_congr rfl fun k _ => X_pow_eq_monomial
  have hd : (fun k => ∑ i, (∑ k', Finsupp.single (⟨k', c k'⟩ : Σ k, ι k) (d k')) ⟨k, i⟩) = d := by
    funext k
    simp only [Finsupp.finsetSum_apply]
    rw [Finset.sum_comm]
    simp only [sum_single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [h]
  have hm := isMultiHomog_monomial (ι := ι) (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k)) (1 : ℤ)
  rw [hd] at hm
  exact hm


omit [∀ k, Fintype (ι k)] in
theorem aeval_chartMono (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (d : K → ℕ) :
    aeval y (chartMono c d) = ∏ k, y ⟨k, c k⟩ ^ d k := by
  simp [chartMono, map_prod]


omit [∀ k, Fintype (ι k)] in
theorem eval_chartMono (z : (Σ k, ι k) → ℂ) (c : ∀ k, ι k) (d : K → ℕ) :
    eval z (map (Int.castRingHom ℂ) (chartMono c d)) = ∏ k, z ⟨k, c k⟩ ^ d k := by
  simp [chartMono, map_prod]

theorem mem_mCoordIdeal_of_aeval_eq_zero (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ}
    (hg : IsMultiHomog g d) (h0 : aeval y g = 0) : g ∈ mCoordIdeal y := by
  show g ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker, ProjLine.mConeMap_eq_of_isMultiHomog y hg, h0, map_zero, zero_mul]

theorem exists_form_of_mem_chartRingZ (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {x : Ω}
    (hx : x ∈ chartRingZ y c) :
    ∃ (δ : K → ℕ) (e : MRing ι), IsMultiHomog e δ ∧ aeval y e = x * ∏ k, y ⟨k, c k⟩ ^ δ k := by
  classical
  have hpow : ∀ δ₁ δ₂ : K → ℕ, ∏ k, y ⟨k, c k⟩ ^ (δ₁ + δ₂) k =
      (∏ k, y ⟨k, c k⟩ ^ δ₁ k) * ∏ k, y ⟨k, c k⟩ ^ δ₂ k := fun δ₁ δ₂ => by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  rw [chartRingZ] at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨k₀, j⟩ := p
    refine ⟨fun k => ∑ i, (Finsupp.single (⟨k₀, j⟩ : Σ k, ι k) 1) ⟨k, i⟩, X ⟨k₀, j⟩, ?_, ?_⟩
    · have h := isMultiHomog_monomial (ι := ι) (Finsupp.single (⟨k₀, j⟩ : Σ k, ι k) 1) 1
      rwa [← X] at h
    · have h1 : ∏ k, y ⟨k, c k⟩ ^ (∑ i, (Finsupp.single (⟨k₀, j⟩ : Σ k, ι k) 1) ⟨k, i⟩) = y ⟨k₀, c k₀⟩ := by
        simp only [sum_single_apply]
        rw [Finset.prod_eq_single k₀ (fun k _ hk => by rw [if_neg (Ne.symm hk), pow_zero])
          (fun h => absurd (Finset.mem_univ _) h)]
        simp
      rw [aeval_X, h1, div_mul_cancel₀ _ (hc k₀)]
  | algebraMap r =>
    refine ⟨fun _ => 0, C r, ?_, by simp⟩
    have h := isMultiHomog_monomial (ι := ι) 0 r
    simpa using h
  | add x w _ _ hx hw =>
    obtain ⟨δ₁, e₁, h₁, v₁⟩ := hx
    obtain ⟨δ₂, e₂, h₂, v₂⟩ := hw
    refine ⟨δ₁ + δ₂, e₁ * chartMono c δ₂ + e₂ * chartMono c δ₁, ?_, ?_⟩
    · intro m hm
      rcases Finset.mem_union.mp (support_add hm) with hm | hm
      · exact isMultiHomog_mul h₁ (isMultiHomog_chartMono c δ₂) m hm
      · rw [add_comm δ₁]
        exact isMultiHomog_mul h₂ (isMultiHomog_chartMono c δ₁) m hm
    · rw [map_add (f := _), map_mul, map_mul, v₁, v₂, aeval_chartMono, aeval_chartMono, hpow]
      ring
  | mul x w _ _ hx hw =>
    obtain ⟨δ₁, e₁, h₁, v₁⟩ := hx
    obtain ⟨δ₂, e₂, h₂, v₂⟩ := hw
    refine ⟨δ₁ + δ₂, e₁ * e₂, isMultiHomog_mul h₁ h₂, ?_⟩
    rw [map_mul, v₁, v₂, hpow]
    ring

theorem exists_chartForm (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ) {s : Ω} (hs : s ∈ chartLat y a n)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ (N dg : K → ℕ) (g : MRing ι), IsMultiHomog g dg ∧ (∀ k, (dg k : ℤ) = N k + n * a k) ∧
      aeval y g = s * aeval y (chartMono c N) := by
  have hx : s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k)) ∈ chartRingZ y c := hs c hc
  obtain ⟨δ, e, he, hv⟩ := exists_form_of_mem_chartRingZ y c hc hx
  set ex : K → ℕ := fun k => ((n : ℤ) * a k + ((n : ℤ) * a k).natAbs).toNat with hex
  have hexk : ∀ k, (ex k : ℤ) = (n : ℤ) * a k + ((n : ℤ) * a k).natAbs := fun k => by
    rw [hex]
    exact Int.toNat_of_nonneg (by omega)
  refine ⟨fun k => δ k + ((n : ℤ) * a k).natAbs, δ + ex, e * chartMono c ex,
    isMultiHomog_mul he (isMultiHomog_chartMono c ex), fun k => ?_, ?_⟩
  · simp only [Pi.add_apply, Nat.cast_add, hexk k]
    ring
  · rw [map_mul, hv, aeval_chartMono, aeval_chartMono, mul_assoc, mul_assoc, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    have h0 := hc k
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ h0, ← zpow_add₀ h0, hexk k]
    congr 1
    push_cast
    ring

end SectionBoundedMul


open SectionBoundedMul in
theorem SectionBoundedMul.proof : SectionBoundedMul.Statement := by
  intro K _ ι _ Ω _ y A n m C C' s t hs ht hbs hbt dg dh g h z hg hh hdeg he hz
  choose c hc using hz.1
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    have hX : IsMultiHomog (X ⟨k, c k⟩ : MRing ι) _ :=
      (by have h := isMultiHomog_monomial (ι := ι) (Finsupp.single (⟨k, c k⟩ : Σ k, ι k) 1) 1
          rwa [← X] at h)
    have hmem := mem_mCoordIdeal_of_aeval_eq_zero y hX (by rw [aeval_X, h0])
    have hz0 := hz.2 _ hmem
    simp only [map_X, eval_X] at hz0
    exact hc k hz0
  obtain ⟨N, dgs, gs, hgs, hdgs, hvs⟩ := exists_chartForm y A.a n hs c hy
  obtain ⟨M, dgt, gt, hgt, hdgt, hvt⟩ := exists_chartForm y A.a m ht c hy
  have bs := hbs dgs N gs (chartMono c N) z hgs (isMultiHomog_chartMono c N) hdgs hvs hz
  have bt := hbt dgt M gt (chartMono c M) z hgt (isMultiHomog_chartMono c M) hdgt hvt hz

  have hdeq : dgs + dgt + dh = dg + (N + M) := by
    funext k
    have e1 := hdgs k
    have e2 := hdgt k
    have e3 := hdeg k
    simp only [Pi.add_apply]
    have : ((dgs k + dgt k + dh k : ℕ) : ℤ) = ((dg k + (N k + M k) : ℕ) : ℤ) := by
      push_cast at e3 ⊢
      linear_combination e1 + e2 - e3
    exact_mod_cast this
  have hF : IsMultiHomog (gs * gt * h - g * chartMono c (N + M)) (dgs + dgt + dh) := by
    refine isMultiHomog_sub (isMultiHomog_mul (isMultiHomog_mul hgs hgt) hh) ?_
    rw [hdeq]
    exact isMultiHomog_mul hg (isMultiHomog_chartMono c (N + M))
  have hmono : ∀ (w : (Σ k, ι k) → Ω), aeval w (chartMono c (N + M)) =
      aeval w (chartMono c N) * aeval w (chartMono c M) := fun w => by
    rw [aeval_chartMono, aeval_chartMono, aeval_chartMono, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  have hF0 : aeval y (gs * gt * h - g * chartMono c (N + M)) = 0 := by
    rw [map_sub, map_mul, map_mul, map_mul, hvs, hvt, he, hmono]
    ring
  have hz0 := hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hF hF0)
  simp only [map_sub, map_mul] at hz0
  rw [sub_eq_zero] at hz0

  set ev : MRing ι → ℂ := fun f => eval z (map (Int.castRingHom ℂ) f) with hev
  have hmz : ev (chartMono c (N + M)) = ev (chartMono c N) * ev (chartMono c M) := by
    simp only [hev, eval_chartMono, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  have hpos : 0 < ‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖ := by
    refine mul_pos (norm_pos_iff.mpr ?_) (norm_pos_iff.mpr ?_) <;>
    · simp only [hev, eval_chartMono]
      exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have key : ‖ev g‖ * (‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖) =
      ‖ev gs‖ * ‖ev gt‖ * ‖ev h‖ := by
    rw [← norm_mul, ← hmz, ← norm_mul, ← norm_mul, ← norm_mul]
    exact congrArg norm hz0.symm
  have hprod : ‖ev gs‖ * ‖ev gt‖ ≤
      (C * ‖ev (chartMono c N)‖ * A.h z ^ n) * (C' * ‖ev (chartMono c M)‖ * A.h z ^ m) :=
    mul_le_mul bs bt (norm_nonneg _) ((norm_nonneg _).trans bs)
  refine le_of_mul_le_mul_right ?_ hpos
  rw [key]
  calc ‖ev gs‖ * ‖ev gt‖ * ‖ev h‖
      ≤ (C * ‖ev (chartMono c N)‖ * A.h z ^ n) * (C' * ‖ev (chartMono c M)‖ * A.h z ^ m) * ‖ev h‖ :=
        mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
    _ = C * C' * ‖ev h‖ * A.h z ^ (n + m) * (‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖) := by
        rw [pow_add]
        ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
