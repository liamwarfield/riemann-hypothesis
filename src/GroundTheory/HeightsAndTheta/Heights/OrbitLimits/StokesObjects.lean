module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ExistsUnique
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveResidueDegree

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StokesObjects
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

def IsDegZeroSmooth {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (u : ((Σ k, ι k) → ℂ) → ℝ) : Prop :=
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} ∧
    ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z

section

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem isDegZeroSmooth_log {B : HermLine ι} (hB : IsSmoothHerm B) (h0 : B.a = 0) :
    IsDegZeroSmooth (fun z => Real.log (B.h z)) := by
  refine ⟨ContDiffOn.log hB fun z hz => (B.pos z hz).ne', fun c z hc => ?_⟩
  simp only [B.smul c z hc, h0, Pi.zero_apply, zpow_zero, Finset.prod_const_one, one_mul]

theorem isDegZeroSmooth_const (a : ℝ) : IsDegZeroSmooth (ι := ι) (fun _ => a) :=
  ⟨contDiffOn_const, fun _ _ _ => rfl⟩

theorem IsDegZeroSmooth.mul {u v : ((Σ k, ι k) → ℂ) → ℝ} (hu : IsDegZeroSmooth u)
    (hv : IsDegZeroSmooth v) : IsDegZeroSmooth (fun z => u z * v z) :=
  ⟨hu.1.mul hv.1, fun c z hc => by simp only [hu.2 c z hc, hv.2 c z hc]⟩

end

def planeSq (z : (Σ k, PBlk 3 k) → ℂ) : ℝ := ∑ i : Fin 3, ‖z ⟨(), i⟩‖ ^ 2

def planeBump (z : (Σ k, PBlk 3 k) → ℂ) : ℝ :=
  Real.smoothTransition (4 * ‖z ⟨(), 0⟩‖ ^ 2 / planeSq z - 1)

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.BaseChangeMinimal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial

namespace BaseChangeMin

variable {σ : Type*} [Fintype σ] {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']

section GD

attribute [local instance] MvPolynomial.algebraMvPolynomial



end GD

theorem ringKrullDim_quotient_le_of_minimalPrimes {R : Type*} [CommRing R] (I : Ideal R)
    {N : WithBot ℕ∞} (h : ∀ Z ∈ I.minimalPrimes, ringKrullDim (R ⧸ Z) ≤ N) :
    ringKrullDim (R ⧸ I) ≤ N := by
  rw [ringKrullDim_quotient, Order.krullDim_eq_iSup_coheight, iSup_le_iff]
  intro a
  obtain ⟨Z, hZ, hZa⟩ :=
    Ideal.exists_minimalPrimes_le ((PrimeSpectrum.mem_zeroLocus _ _).mp a.2)
  have : Z.IsPrime := hZ.1.1
  let z : PrimeSpectrum.zeroLocus (R := R) (I : Set R) :=
    ⟨⟨Z, inferInstance⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr hZ.1.2⟩
  have hza : z ≤ a := hZa
  let e : Set.Ici z ↪o PrimeSpectrum.zeroLocus (R := R) (Z : Set R) :=
    OrderEmbedding.ofMapLEIff
      (fun x => ⟨x.1.1, (PrimeSpectrum.mem_zeroLocus _ _).mpr (show Z ≤ x.1.1.asIdeal from x.2)⟩)
      fun _ _ => Iff.rfl
  calc ((Order.coheight a : ℕ∞) : WithBot ℕ∞) ≤ ((Order.coheight z : ℕ∞) : WithBot ℕ∞) :=
        WithBot.coe_le_coe.mpr (Order.coheight_anti hza)
    _ = Order.krullDim (Set.Ici z) := Order.coheight_eq_krullDim_Ici z
    _ ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := R) (Z : Set R)) :=
        Order.krullDim_le_of_orderEmbedding e
    _ = ringKrullDim (R ⧸ Z) := (ringKrullDim_quotient Z).symm
    _ ≤ N := h Z hZ

end BaseChangeMin

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PExistsUniqueRelabel
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

namespace ExistsUniqueRelabel

section RingEquiv

variable {R R' : Type*} [CommRing R] [CommRing R'] (φ : R ≃+* R')

theorem mem_map_iff (I : Ideal R) (x : R) : φ x ∈ I.map (φ : R →+* R') ↔ x ∈ I := by
  rw [Ideal.map_comap_of_equiv, Ideal.mem_comap, RingEquiv.symm_apply_apply]

theorem map_mem_minimalPrimes {J W : Ideal R} (h : W ∈ J.minimalPrimes) :
    W.map (φ : R →+* R') ∈ (J.map (φ : R →+* R')).minimalPrimes := by
  rw [Ideal.map_comap_of_equiv, Ideal.map_comap_of_equiv]
  exact Ideal.minimalPrimes_comap_of_surjective (f := (φ.symm : R' →+* R)) φ.symm.surjective h

theorem map_mem_minimalPrimes_iff {J W : Ideal R} :
    W.map (φ : R →+* R') ∈ (J.map (φ : R →+* R')).minimalPrimes ↔ W ∈ J.minimalPrimes := by
  refine ⟨fun h => ?_, map_mem_minimalPrimes φ⟩
  have := map_mem_minimalPrimes φ.symm h
  rwa [Ideal.map_of_equiv, Ideal.map_of_equiv] at this

theorem ringKrullDim_quot_map (V : Ideal R) :
    ringKrullDim (R' ⧸ V.map (φ : R →+* R')) = ringKrullDim (R ⧸ V) :=
  (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv V _ φ rfl)).symm

theorem length_map (V W : Ideal R) [W.IsPrime] [(W.map (φ : R →+* R')).IsPrime] (hVW : V ≤ W)
    (x : R) :
    Module.length (Localization.AtPrime (W.map (φ : R →+* R')))
        (LocalizedModule (W.map (φ : R →+* R')).primeCompl
          (R' ⧸ (V.map (φ : R →+* R') ⊔ Ideal.span {φ x}))) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ (V ⊔ Ideal.span {x}))) := by
  set V' := V.map (φ : R →+* R')
  set W' := W.map (φ : R →+* R')
  have hVW' : V' ≤ W' := Ideal.map_mono hVW
  have : (W'.map (Ideal.Quotient.mk V')).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hVW')
  have h' := ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.isLocData_atPrime_quot V' W' hVW'
  letI : Algebra R (Localization.AtPrime (W'.map (Ideal.Quotient.mk V'))) :=
    ((algebraMap R' (Localization.AtPrime (W'.map (Ideal.Quotient.mk V')))).comp
      (φ : R →+* R')).toAlgebra
  have hal : ∀ r, algebraMap R (Localization.AtPrime (W'.map (Ideal.Quotient.mk V'))) r =
      algebraMap R' (Localization.AtPrime (W'.map (Ideal.Quotient.mk V'))) (φ r) := fun r => rfl
  have hS : ∀ s : R', s ∈ W'.primeCompl → φ.symm s ∈ W.primeCompl := by
    intro s hs h
    apply hs
    rw [← φ.apply_symm_apply s]
    exact (mem_map_iff φ W _).2 h
  have h : ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.IsLocData R
      (Localization.AtPrime (W'.map (Ideal.Quotient.mk V'))) W.primeCompl V := by
    refine ⟨fun s hs => ?_, fun y => ?_, fun r hr => ?_, fun v hv => ?_⟩
    · rw [hal]
      exact h'.1 _ (fun h => hs ((mem_map_iff φ W s).1 h))
    · obtain ⟨r, s, hs, e⟩ := h'.2.1 y
      refine ⟨φ.symm r, φ.symm s, hS s hs, ?_⟩
      rw [hal, hal, φ.apply_symm_apply, φ.apply_symm_apply]
      exact e
    · rw [hal] at hr
      obtain ⟨s, hs, e⟩ := h'.2.2.1 _ hr
      refine ⟨φ.symm s, hS s hs, ?_⟩
      rw [← mem_map_iff φ V, map_mul, φ.apply_symm_apply]
      exact e
    · rw [hal]
      exact h'.2.2.2 _ ((mem_map_iff φ V v).2 hv)
  exact (h'.length_eq (φ x)).trans (h.length_eq x).symm

end RingEquiv

section MRing

variable {F : Type*} [Field F] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]

variable (e : K ≃ K') (σ : (Σ k, ι k) ≃ (Σ k', ι' k')) (hσ : ∀ p, (σ p).1 = e p.1)




include hσ












end MRing

end ExistsUniqueRelabel

universe u v w v' w'

end GroundTheory.Heights₂.Heights.Targets
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLelongWeightLimit
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Filter Topology Matrix Set
open scoped ContDiff Manifold
open GroundTheory.Heights₂.Heights (varInt chartInt SmoothNear localMult linEval linForm logReg contDiff_linEval
  contDiff_logReg smoothNear_of_contDiff)

namespace LelongWeightLimit

variable {n : ℕ}

theorem exists_contDiff_eqOn {Z : Set (Fin n → ℂ)} (hZ : IsClosed Z) {f : (Fin n → ℂ) → ℝ}
    (hf : SmoothNear Z f) (hfc : HasCompactSupport f) :
    ∃ g : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ ∀ x ∈ Z, g x = f x := by
  obtain ⟨U, hU, hZU, hfU⟩ := hf
  have hK : IsCompact (Z ∩ tsupport f) := hfc.isCompact.inter_left hZ
  obtain ⟨V, hV, hKV, hVU, -⟩ :=
    exists_open_between_and_isCompact_closure hK hU (inter_subset_left.trans hZU)
  obtain ⟨θ, hθ, -, hθs, hθ1⟩ :=
    exists_contMDiff_support_eq_eq_one_iff 𝓘(ℝ, Fin n → ℂ) (n := ⊤) hV hK.isClosed hKV
  rw [contMDiff_iff_contDiff] at hθ
  refine ⟨θ * f, ?_, hfc.mul_left, fun x hx => ?_⟩
  · refine contDiff_iff_contDiffAt.mpr fun x => ?_
    by_cases hx : x ∈ U
    · exact hθ.contDiffAt.mul (hfU.contDiffAt (hU.mem_nhds hx))
    · have hev : θ * f =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds fun h => hx (hVU h)] with y hy
        have : θ y = 0 := by
          by_contra h
          exact hy (subset_closure (hθs ▸ (Function.mem_support.mpr h)))
        simp [this]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · by_cases hxf : x ∈ tsupport f
    · rw [Pi.mul_apply, (hθ1 x).1 ⟨hx, hxf⟩, one_mul]
    · rw [Pi.mul_apply, image_eq_zero_of_notMem_tsupport hxf, mul_zero]

theorem varInt_congr {J : Ideal (MvPolynomial (Fin n) ℂ)} {d : ℕ} {f g : (Fin n → ℂ) → ℝ}
    (h : ∀ x ∈ ComplexSets.zeroSet J, f x = g x) (φ : Fin d → (Fin n → ℂ) → ℝ) :
    varInt J d f φ = varInt J d g φ := by
  unfold varInt chartInt
  split_ifs
  · rw [CutOffDominated.chartDens_congr_zeroSet h]
  · rfl

theorem smoothNear_weight {Z : Set (Fin n → ℂ)} (u : Fin n → ℂ) {k : (Fin n → ℂ) → ℝ}
    (hk : SmoothNear Z k) (hk0 : ∀ x ∈ Z, 0 < k x) {ε : ℝ} (hε : 0 < ε) :
    SmoothNear Z (fun x => Real.log (‖linEval u x‖ ^ 2 + ε * k x ^ 2) / 2) := by
  obtain ⟨U, hU, hZU, hkU⟩ := hk
  refine ⟨U ∩ k ⁻¹' Ioi 0, hkU.continuousOn.isOpen_inter_preimage hU isOpen_Ioi,
    fun x hx => ⟨hZU hx, hk0 x hx⟩, ?_⟩
  refine ContDiffOn.div_const (ContDiffOn.log ?_ fun x hx => ?_) _
  · exact ((contDiff_norm_sq ℝ).comp (contDiff_linEval u)).contDiffOn.add
      (contDiffOn_const.mul ((hkU.mono inter_subset_left).pow 2))
  · have h1 : 0 < ε * k x ^ 2 := mul_pos hε (pow_pos hx.2 2)
    have h2 : 0 ≤ ‖linEval u x‖ ^ 2 := sq_nonneg _
    exact (by linarith : (0 : ℝ) < ‖linEval u x‖ ^ 2 + ε * k x ^ 2).ne'

end LelongWeightLimit


open LelongWeightLimit in
theorem LelongWeightLimit.proof (hL : GroundTheory.Heights₂.Heights.LelongLimit.Statement)
    (hS : GroundTheory.Heights₂.Heights.StokesOnVariety.Statement) (hD : LelongWeightDiff.Statement) :
    LelongWeightLimit.Statement := by
  intro n d J u f k φ hJ hdim hu hf hfc hφ hk hk0
  obtain ⟨g, hg, hgc, hgf⟩ :=
    exists_contDiff_eqOn (GroundTheory.Heights₂.Heights.SheetSumMeasurable.isClosed_zeroSet J) hf hfc
  have hsum : (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
        (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g φ) =
      ∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
        (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d f φ := by
    refine finsum_congr fun W => finsum_congr fun hW => ?_
    rw [varInt_congr (fun x hx => hgf x fun q hq => hx q (le_sup_left.trans hW.1.2 hq)) φ]
  have hlim := (hL n d J u g φ hJ hdim hu hg hgc hφ).add (hD n d J u g k φ hJ hdim hu hg hgc hφ hk hk0)
  rw [hsum, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [varInt_congr (fun x hx => (hgf x hx).symm) (vecCons _ φ),
    hS n d J g _ φ hJ hdim (smoothNear_of_contDiff hg) (smoothNear_weight u hk hk0 hε) hφ (Or.inl hgc),
    hS n d J g (logReg u ε) φ hJ hdim (smoothNear_of_contDiff hg)
      (smoothNear_of_contDiff (contDiff_logReg u hε)) hφ (Or.inl hgc)]
  ring

end GroundTheory.Heights₂.Heights.Targets
end
end
