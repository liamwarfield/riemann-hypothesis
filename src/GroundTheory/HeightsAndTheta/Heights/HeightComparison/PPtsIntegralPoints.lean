module

public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCurve
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.FiniteIntegralClosureCharZero
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightComparison.PPtsIntegralPoints
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G MeasureTheory

namespace PtsIntegralPoints

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem rel_equivalence (P : Ideal (Geo.MRing ι)) :
    Equivalence (fun z z' : Geo.mcPts P ↦
      ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ (z' : (Σ k, ι k) → ℂ) = fun p ↦ c p.1 * (z : (Σ k, ι k) → ℂ) p) := by
  constructor
  · intro z
    exact ⟨fun _ ↦ 1, fun _ ↦ one_ne_zero, by funext p; simp⟩
  · rintro z z' ⟨c, hc, h⟩
    refine ⟨fun k ↦ (c k)⁻¹, fun k ↦ inv_ne_zero (hc k), ?_⟩
    funext p
    rw [h]
    exact (inv_mul_cancel_left₀ (hc p.1) _).symm
  · rintro z z' z'' ⟨c, hc, h⟩ ⟨d, hd, h'⟩
    refine ⟨fun k ↦ d k * c k, fun k ↦ mul_ne_zero (hd k) (hc k), ?_⟩
    funext p
    rw [h', h, mul_assoc]

theorem segre_ne_zero {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : Geo.segre z ≠ 0 := by
  choose i hi using hz
  intro h
  have := congrFun h i
  simp only [Geo.segre, Pi.zero_apply] at this
  exact Finset.prod_ne_zero_iff.mpr (fun k _ ↦ hi k) this

theorem sheetDensity_eq (P : Ideal (Geo.MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ)) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (hg : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → z ∈ Geo.mcPts P →
      g (fun p ↦ c p.1 * z p) = g z)
    (y : Fin 0 → ℂ) {z : (Σ k, ι k) → ℂ} (hz : z ∈ Geo.mcPts P)
    (hΨ : Ψ (Geo.segre z) = Fin.cons 1 y) :
    Geo.sheetDensity P Ψ Fin.elim0 g y (Geo.segre z) = g z := by
  have hex : ∃ γ, Geo.IsSheet P Ψ y (Geo.segre z) γ := by
    refine ⟨fun _ ↦ z, rfl, Filter.Eventually.of_forall fun y' ↦ ⟨differentiableAt_const _, hz, ?_⟩⟩
    rw [Subsingleton.elim y' y]
    exact hΨ
  rw [Geo.sheetDensity, dite_eq_left hex]
  obtain ⟨hseg, hev⟩ := hex.choose_spec
  have hmem : hex.choose y ∈ Geo.mcPts P := hev.self_of_nhds.2.1
  obtain ⟨c, hc, hcz⟩ := Geo.sameOrbit_of_segre (z := z) hmem.1 1 one_ne_zero (by rw [one_smul, hseg])
  have hgz : g z = g (hex.choose y) := (congrArg g hcz).trans (hg c _ hc hmem)
  rw [hgz]
  simp [Geo.maDensity, Geo.mixedDisc]

theorem ptsIntegralAt_eq [Nonempty K] (P : Ideal (Geo.MRing ι)) (hP : Geo.IsMultiHomogIdeal P)
    (g : ((Σ k, ι k) → ℂ) → ℝ)
    (hg : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → z ∈ Geo.mcPts P →
      g (fun p ↦ c p.1 * z p) = g z)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ)) (hΨ : Geo.IsGoodProj P Ψ) :
    Geo.ptsIntegralAt P Ψ Fin.elim0 g = ∑ᶠ q : projPts P, g (Quot.out q : Geo.mcPts P) := by
  classical
  have hE := rel_equivalence P
  have hcons : ∀ (y : Fin 0 → ℂ) (v : Fin (0 + 1) → ℂ), v = Fin.cons 1 y ↔ v 0 = 1 := by
    intro y v
    constructor
    · rintro rfl; rfl
    · intro h; funext i; rw [show i = 0 from Fin.ext (by have := i.isLt; omega)]; exact h
  have hne : ∀ z ∈ Geo.mcPts P, Ψ (Geo.segre z) 0 ≠ 0 := fun z hz h ↦
    hΨ z hz (funext fun i ↦ by rw [show i = 0 from Fin.ext (by have := i.isLt; omega)]; exact h)
  let k₀ : K := Classical.arbitrary K
  let t : projPts P → ℂ := fun q ↦ (Ψ (Geo.segre (Quot.out q : Geo.mcPts P)) 0)⁻¹
  have ht : ∀ q, t q ≠ 0 := fun q ↦ inv_ne_zero (hne _ (Quot.out q).2)
  let c : projPts P → K → ℂ := fun q k ↦ if k = k₀ then t q else 1
  have hc : ∀ q k, c q k ≠ 0 := fun q k ↦ by
    simp only [c]
    split_ifs
    · exact ht q
    · exact one_ne_zero
  have hcprod : ∀ q, ∏ k, c q k = t q := fun q ↦ by simp [c]
  let zq : projPts P → (Σ k, ι k) → ℂ := fun q p ↦ c q p.1 * (Quot.out q).1 p
  have hzq : ∀ q, zq q ∈ Geo.mcPts P := fun q ↦ Geo.mcPts_smul hP (c q) (hc q) (Quot.out q).2
  have hseg : ∀ q, Geo.segre (zq q) = t q • Geo.segre (Quot.out q : Geo.mcPts P) := fun q ↦ by
    rw [← hcprod q]
    exact Geo.segre_smul (c q) (Quot.out q).1
  have hone : ∀ q, Ψ (Geo.segre (zq q)) 0 = 1 := fun q ↦ by
    rw [hseg, map_smul, Pi.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ (hne _ (Quot.out q).2)
  have hrep : ∀ z : Geo.mcPts P, ∃ d : K → ℂ, (∀ k, d k ≠ 0) ∧
      (z : (Σ k, ι k) → ℂ) = fun p ↦ d p.1 * (Quot.out (Quot.mk _ z : projPts P)).1 p :=
    fun z ↦ hE.eqvGen_iff.mp (Quot.eqvGen_exact (Quot.out_eq (Quot.mk _ z : projPts P)))
  have hsum : ∀ y : Fin 0 → ℂ, ∑ᶠ w ∈ Geo.fibre P Ψ y, Geo.sheetDensity P Ψ Fin.elim0 g y w =
      ∑ᶠ q : projPts P, g (Quot.out q : Geo.mcPts P) := by
    intro y
    let σ : projPts P → Geo.fibre P Ψ y := fun q ↦
      ⟨Geo.segre (zq q), zq q, hzq q, rfl, (hcons y _).mpr (hone q)⟩
    have hinj : Function.Injective σ := by
      intro q q' h
      have h' : Geo.segre (zq q) = Geo.segre (zq q') := congrArg Subtype.val h
      obtain ⟨d, hd, hdq⟩ :=
        Geo.sameOrbit_of_segre (z := zq q) (hzq q').1 1 one_ne_zero (by rw [one_smul, h'])
      have e1 : (Quot.mk _ (Quot.out q) : projPts P) = Quot.mk _ ⟨zq q, hzq q⟩ :=
        Quot.sound ⟨c q, hc q, rfl⟩
      have e2 : (Quot.mk _ ⟨zq q', hzq q'⟩ : projPts P) = Quot.mk _ ⟨zq q, hzq q⟩ :=
        Quot.sound ⟨d, hd, hdq⟩
      have e3 : (Quot.mk _ (Quot.out q') : projPts P) = Quot.mk _ ⟨zq q', hzq q'⟩ :=
        Quot.sound ⟨c q', hc q', rfl⟩
      rw [Quot.out_eq] at e1 e3
      exact e1.trans (e2.symm.trans e3.symm)
    have hsurj : Function.Surjective σ := by
      rintro ⟨w, z, hz, rfl, hw⟩
      obtain ⟨d, hd, hdz⟩ := hrep ⟨z, hz⟩
      refine ⟨Quot.mk _ ⟨z, hz⟩, Subtype.ext ?_⟩
      have hsz : Geo.segre z = (∏ k, d k) •
          Geo.segre (Quot.out (Quot.mk _ ⟨z, hz⟩ : projPts P) : Geo.mcPts P) := by
        rw [← Geo.segre_smul]
        exact congrArg Geo.segre hdz
      have h1 := (hcons y _).mp hw
      rw [hsz, map_smul, Pi.smul_apply, smul_eq_mul] at h1
      have h2 : ∏ k, d k = t (Quot.mk _ ⟨z, hz⟩) := eq_inv_of_mul_eq_one_left h1
      show Geo.segre (zq _) = Geo.segre z
      rw [hseg, hsz, h2]
    rw [← finsum_set_coe_eq_finsum_mem, ← finsum_comp_equiv (Equiv.ofBijective σ ⟨hinj, hsurj⟩)]
    refine finsum_congr fun q ↦ ?_
    show Geo.sheetDensity P Ψ Fin.elim0 g y (Geo.segre (zq q)) = _
    rw [sheetDensity_eq P Ψ g hg y (hzq q) ((hcons y _).mpr (hone q))]
    exact hg (c q) _ (hc q) (Quot.out q).2
  rw [Geo.ptsIntegralAt]
  simp only [hsum]
  rw [integral_const, MeasureTheory.volume_pi, Measure.pi_of_empty]
  simp

theorem exists_isGoodProj (P : Ideal (Geo.MRing ι)) (hfin : Finite (projPts P)) :
    ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ), Geo.IsGoodProj P Ψ := by
  have hE := rel_equivalence P
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℂ) (M := ((k : K) → ι k) → ℂ)
    (fun q : projPts P ↦ Geo.segre (Quot.out q).1)
    (fun q ↦ segre_ne_zero (z := (Quot.out q).1) (Quot.out q).2.1)
  refine ⟨LinearMap.pi fun _ ↦ f, fun z hz h ↦ ?_⟩
  obtain ⟨d, hd, hdz⟩ := hE.eqvGen_iff.mp (Quot.eqvGen_exact (Quot.out_eq (Quot.mk _ ⟨z, hz⟩ : projPts P)))
  have h0 : f (Geo.segre z) = 0 := congrFun h 0
  have hsz : Geo.segre z = (∏ k, d k) •
      Geo.segre (Quot.out (Quot.mk _ ⟨z, hz⟩ : projPts P) : Geo.mcPts P) := by
    rw [← Geo.segre_smul]
    exact congrArg Geo.segre hdz
  rw [hsz, map_smul, smul_eq_mul] at h0
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ ↦ hd k) (hf _) h0

def HomogStatement : Prop :=
  ∀ (K : Type) [Fintype K] [Nonempty K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (Geo.MRing ι)) (g : ((Σ k, ι k) → ℂ) → ℝ),
    Geo.IsMultiHomogIdeal P → Finite (projPts P) →
    (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → z ∈ Geo.mcPts P →
      g (fun p ↦ c p.1 * z p) = g z) →
    Geo.ptsIntegral P (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) g =
      ∑ᶠ q : projPts P, g (Quot.out q : Geo.mcPts P)

theorem homogProof : HomogStatement := by
  intro K _ _ ι _ P g hP hfin hg
  have hex : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ), Geo.IsGoodProj P Ψ :=
    exists_isGoodProj P hfin
  rw [Geo.ptsIntegral, dite_eq_left hex]
  exact ptsIntegralAt_eq P hP g hg _ hex.choose_spec

section Dependence

open MvPolynomial

end Dependence

end PtsIntegralPoints

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterDivSupp
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

theorem OrbitCenterDivSupp.proof (hMI : OrbitCenterMemIff.Statement)
    (hPr : OrbitCenterPrime.Statement) (hSP : SubringPrimeMaximal.Statement) :
    OrbitCenterDivSupp.Statement := by
  intro ι _ _ n x s a hx hs hsW v hsv
  obtain ⟨c, hc⟩ := exists_chart_ciSup x hx v
  have hrel : Geo.IsRelevant (ι := blockIdx n) (orbitCenter x v) := fun k ↦ ⟨c k, fun h ↦ by
    have := (hMI ι n x hx v _ _ ((geoMultiHomog_iff _ _).mpr
      (isWeightedHomogeneous_X ℤ (coordDeg n) ⟨k, c k⟩))).mp h
    simp [evalCone, coordDeg, Pi.single_apply, pow_ite, (hc k).1] at this⟩
  have hW : orbitIdeal x ≤ orbitCenter x v := by
    obtain ⟨S, hS, hspan⟩ := OrbitCurve.isMultiHomogIdeal_orbitIdeal x
    have hSW : ∀ F ∈ S, F ∈ orbitIdeal x := fun F hF ↦ by rw [hspan]; exact Ideal.subset_span hF
    rw [hspan]
    refine Ideal.span_le.mpr fun F hF ↦ ?_
    obtain ⟨d, hd⟩ := hS F hF
    refine Ideal.subset_span ⟨d, hd, ?_⟩
    rw [(mem_orbitIdeal_iff_of_isMultiHomog x F d hd).mp (hSW F hF), map_zero]
    exact Finset.prod_pos fun k _ ↦ pow_pos (hc k).2 _
  refine ⟨⟨⟨hPr ι n x hx v, sup_le hW ((Ideal.span_singleton_le_iff_mem _).mpr hsv)⟩,
    fun Q hQ hle ↦ ?_⟩, hrel⟩
  have := hQ.1
  exact orbitCenter_le_of_le hMI hSP x hx v c hc s a hs hsW Q (le_sup_left.trans hQ.2)
    (hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))) hle

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightComparison.PLocalNormalIndex
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

theorem LocalNormalIndex.proof : LocalNormalIndex.Statement := by
  intro L _ _ O hft hfr m _
  set A := Localization.subalgebra.ofField L m.primeCompl m.primeCompl_le_nonZeroDivisors
  set C := integralClosure A L
  have : Algebra.FiniteType ℤ O := hft
  have : CharZero O := ⟨fun a b h ↦ by
    have := congrArg (fun t : O ↦ (t : L)) h
    simpa using this⟩

  have hfin : Module.Finite O (integralClosure O L) :=
    Model.finite_integralClosure_fractionRing_of_charZero O L
  obtain ⟨d, hd, hdI⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors O)
    (Module.Finite.iff_fg.mp hfin : (Subalgebra.toSubmodule (integralClosure O L)).FG)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hdL : algebraMap O L d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd

  have hdC : ∀ x ∈ C, algebraMap O L d * x ∈ A := by
    intro x hx
    obtain ⟨⟨s, hs⟩, hsx⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (R := O) (M := m.primeCompl) (Rₘ := A) x hx
    obtain ⟨o, ho⟩ := hdI _ hsx
    have hs0 : algebraMap O L s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (m.primeCompl_le_nonZeroDivisors hs)
    simp only [Submonoid.smul_def, Algebra.smul_def] at ho
    refine ⟨o, s, hs, ?_⟩
    rw [ho]
    field_simp

  have hAC : A.toSubring ≤ C.toSubring := fun x hx ↦
    (isIntegral_algebraMap : IsIntegral A (algebraMap A L ⟨x, hx⟩))
  set f := algebraMap O L d
  have hinj : Function.Injective (AddMonoidHom.mulLeft f) := mul_right_injective₀ hdL
  have h1 : A.toSubring.toAddSubgroup.map (AddMonoidHom.mulLeft f) ≤
      C.toSubring.toAddSubgroup.map (AddMonoidHom.mulLeft f) := AddSubgroup.map_mono hAC
  have h2 : C.toSubring.toAddSubgroup.map (AddMonoidHom.mulLeft f) ≤ A.toSubring.toAddSubgroup := by
    rintro _ ⟨y, hy, rfl⟩
    exact hdC y hy
  have e1 := AddSubgroup.relIndex_mul_relIndex _ _ _ h1 h2
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ hinj] at e1
  have hcard : (A.toSubring.toAddSubgroup.map (AddMonoidHom.mulLeft f)).relIndex
      A.toSubring.toAddSubgroup ≠ 0 := by
    let e : Localization.AtPrime m ≃ₐ[O] A := IsLocalization.algEquiv m.primeCompl _ _
    have hq1 : Nat.card (Localization.AtPrime m ⧸ Ideal.span {algebraMap O (Localization.AtPrime m) d}) =
        Nat.card (A.toSubring ⧸ Ideal.span {(algebraMap O A d : A.toSubring)}) := by
      refine Nat.card_congr (Ideal.quotientEquiv _ _ e.toRingEquiv ?_).toEquiv
      rw [Ideal.map_span, Set.image_singleton]
      congr 2
      exact (e.commutes d).symm
    have hfL : ((algebraMap O A d : A.toSubring) : L) = f := rfl
    have hcq := card_quot_span_eq_relIndex A.toSubring (algebraMap O A d : A.toSubring)
    rw [hfL] at hcq
    have key : Nat.card (Localization.AtPrime m ⧸
        Ideal.span {algebraMap O (Localization.AtPrime m) d}) ≠ 0 := by
      rw [LocalQuotCard.proof L O hft hfr m d hd0]
      refine pow_ne_zero _ ?_
      have hq : Algebra.FiniteType ℤ (O ⧸ m) :=
        @Algebra.FiniteType.of_surjective ℤ O (O ⧸ m) _ _ _ _ _ hft (Ideal.Quotient.mkₐ ℤ m)
          (Ideal.Quotient.mkₐ_surjective ℤ m)
      let _ : Field (O ⧸ m) := Ideal.Quotient.field m
      obtain ⟨hp, hc⟩ :=
        @natCard_eq_pow_length_of_finiteType (O ⧸ m) _
          (by convert hq <;> rfl) (ringChar (O ⧸ m)) (ringChar.charP _)
      rw [hc]
      exact pow_ne_zero _ hp.ne_zero
    rw [← hcq]
    exact fun h ↦ key (hq1.trans h)
  rw [← e1] at hcard
  exact left_ne_zero_of_mul hcard

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartDehom
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

abbrev chartOneIdeal (c : (k : ι) → Fin (n k + 1)) : Ideal (MvPolynomial (Coord n) ℤ) :=
  Ideal.span (Set.range fun k ↦ (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) - 1)

theorem weightedHomogeneousComponent_mem_of_mem_divSupp (x : Cone n (AlgebraicClosure ℚ))
    {s : MvPolynomial (Coord n) ℤ} {a : ι → ℕ} (hs : IsWeightedHomogeneous (coordDeg n) s a)
    {V : Ideal (MvPolynomial (Coord n) ℤ)} (hV : V ∈ Geo.divSupp (orbitIdeal x) s)
    {f : MvPolynomial (Coord n) ℤ} (hf : f ∈ V) (b : ι → ℕ) :
    weightedHomogeneousComponent (coordDeg n) b f ∈ V := by
  have hP : NumbersDVR.IsMultiHomogIdeal (ι := blockIdx n) (R := ℤ) (orbitIdeal x) :=
    fun g hg b ↦ OrbitCurve.weightedHomogeneousComponent_mem_orbitIdeal x hg b
  have hJ := NumbersDVR.SupSpanMultiHomog.proof ℤ ι (blockIdx n) (orbitIdeal x) s a hP hs
  exact NumbersDVR.MinimalPrimeMultiHomog.proof ℤ ι (blockIdx n) _ V hJ hV.1 f hf b

variable (V : Ideal (MvPolynomial (Coord n) ℤ)) [V.IsPrime]

def classFrac : MvPolynomial (Coord n) ℤ →ₐ[ℤ] FractionRing (MvPolynomial (Coord n) ℤ ⧸ V) :=
  (IsScalarTower.toAlgHom ℤ (MvPolynomial (Coord n) ℤ ⧸ V) _).comp (Ideal.Quotient.mkₐ ℤ V)

def dehomFrac (c : (k : ι) → Fin (n k + 1)) :
    MvPolynomial (Coord n) ℤ →ₐ[ℤ] FractionRing (MvPolynomial (Coord n) ℤ ⧸ V) :=
  aeval fun p ↦ classFrac V (X p) / classFrac V (X ⟨p.1, c p.1⟩)

omit [Fintype ι] [DecidableEq ι] [V.IsPrime] in
theorem classFrac_eq_zero_iff (f : MvPolynomial (Coord n) ℤ) : classFrac V f = 0 ↔ f ∈ V := by
  change algebraMap _ (FractionRing (MvPolynomial (Coord n) ℤ ⧸ V)) (Ideal.Quotient.mk V f) = 0 ↔ _
  rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]

variable {V}

theorem dehomFrac_of_isWeightedHomogeneous (c : (k : ι) → Fin (n k + 1))
    (G : MvPolynomial (Coord n) ℤ) (d : ι → ℕ) (hG : IsWeightedHomogeneous (coordDeg n) G d) :
    dehomFrac V c G = classFrac V G * ∏ k, (classFrac V (X ⟨k, c k⟩) ^ d k)⁻¹ := by
  have e : (aeval fun p ↦ classFrac V (X p)) = classFrac V := MvPolynomial.algHom_ext fun p ↦ aeval_X _ _
  rw [dehomFrac, aeval_div_chart (fun p ↦ classFrac V (X p)) c G d hG, DFunLike.congr_fun e G]

theorem ker_dehomFrac
    (hVh : ∀ f ∈ V, ∀ b : ι → ℕ, weightedHomogeneousComponent (coordDeg n) b f ∈ V)
    {c : (k : ι) → Fin (n k + 1)} (hc : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) :
    RingHom.ker (dehomFrac V c) = V ⊔ chartOneIdeal c := by
  have hz : ∀ k, classFrac V (X ⟨k, c k⟩) ≠ 0 := fun k h ↦ hc k ((classFrac_eq_zero_iff V _).mp h)
  have hle : V ⊔ chartOneIdeal c ≤ RingHom.ker (dehomFrac V c) := by
    refine sup_le (fun f hf ↦ ?_) (Ideal.span_le.mpr ?_)
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [RingHom.mem_ker, ← sum_weightedHomogeneousComponent (w := coordDeg n) f,
        finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f), map_sum]
        refine Finset.sum_eq_zero fun b _ ↦ ?_
        rw [dehomFrac_of_isWeightedHomogeneous c _ b
            (weightedHomogeneousComponent_isWeightedHomogeneous b f),
          (classFrac_eq_zero_iff V _).mpr (hVh f hf b), zero_mul]
    · rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, dehomFrac, aeval_X]
      exact sub_eq_zero.mpr (div_self (hz k))
  refine le_antisymm (fun f hf ↦ ?_) hle
  rw [RingHom.mem_ker] at hf
  have hχ : ∀ k, Ideal.Quotient.mk (V ⊔ chartOneIdeal c) (X ⟨k, c k⟩) = 1 := fun k ↦ by
    rw [← map_one (Ideal.Quotient.mk (V ⊔ chartOneIdeal c)), Ideal.Quotient.eq]
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
  obtain ⟨D, G, hG, hGf⟩ := exists_isWeightedHomogeneous_eq_of_chart
    (Ideal.Quotient.mk (V ⊔ chartOneIdeal c)) c hχ f
  have hd : G - f ∈ V ⊔ chartOneIdeal c := Ideal.Quotient.eq.mp hGf
  have h0 : dehomFrac V c G = 0 := by
    have := hle hd
    rwa [RingHom.mem_ker, map_sub, hf, sub_zero] at this
  rw [dehomFrac_of_isWeightedHomogeneous c G D hG, mul_eq_zero] at h0
  have hGV : G ∈ V := by
    refine (classFrac_eq_zero_iff V G).mp (h0.resolve_right ?_)
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ inv_ne_zero (pow_ne_zero _ (hz k))
  simpa using sub_mem (Ideal.mem_sup_left hGV) hd

theorem comap_sup_chartOneIdeal
    (hVh : ∀ f ∈ V, ∀ b : ι → ℕ, weightedHomogeneousComponent (coordDeg n) b f ∈ V)
    {c : (k : ι) → Fin (n k + 1)} (hc : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) :
    (V ⊔ chartOneIdeal c).comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) =
      V.comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) := by
  refine le_antisymm (fun a ha ↦ ?_) (Ideal.comap_mono le_sup_left)
  rw [Ideal.mem_comap, ← ker_dehomFrac hVh hc, RingHom.mem_ker] at ha
  rw [Ideal.mem_comap, ← classFrac_eq_zero_iff V]
  rw [← ha]
  exact ((classFrac V).commutes a).trans ((dehomFrac V c).commutes a).symm

def quotEquivRange
    (hVh : ∀ f ∈ V, ∀ b : ι → ℕ, weightedHomogeneousComponent (coordDeg n) b f ∈ V)
    {c : (k : ι) → Fin (n k + 1)} (hc : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) :
    (MvPolynomial (Coord n) ℤ ⧸ (V ⊔ chartOneIdeal c)) ≃+* (dehomFrac V c).range :=
  (Ideal.quotEquivOfEq (ker_dehomFrac hVh hc).symm).trans
    (Ideal.quotientKerEquivRange (dehomFrac V c)).toRingEquiv


omit [Fintype ι] [DecidableEq ι] in
theorem range_dehomFrac_le {c c' : (k : ι) → Fin (n k + 1)}
    (hc : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V)
    (hc' : ∀ k, (X ⟨k, c' k⟩ : MvPolynomial (Coord n) ℤ) ∉ V)
    (hF : IsField (dehomFrac V c).range) : (dehomFrac V c').range ≤ (dehomFrac V c).range := by
  have hz : ∀ k, classFrac V (X ⟨k, c k⟩) ≠ 0 := fun k h ↦ hc k ((classFrac_eq_zero_iff V _).mp h)
  have hz' : ∀ k, classFrac V (X ⟨k, c' k⟩) ≠ 0 :=
    fun k h ↦ hc' k ((classFrac_eq_zero_iff V _).mp h)
  rw [dehomFrac, ← Algebra.adjoin_range_eq_range_aeval]
  refine Algebra.adjoin_le ?_
  rintro _ ⟨p, rfl⟩
  have hmem : ∀ q : Coord n, classFrac V (X q) / classFrac V (X ⟨q.1, c q.1⟩) ∈ (dehomFrac V c).range :=
    fun q ↦ (AlgHom.mem_range _).mpr ⟨X q, by rw [dehomFrac, aeval_X]⟩
  let u : (dehomFrac V c).range := ⟨_, hmem ⟨p.1, c' p.1⟩⟩
  have hu : u ≠ 0 := fun h ↦ div_ne_zero (hz' p.1) (hz p.1) (congrArg Subtype.val h)
  obtain ⟨w, hw⟩ := hF.mul_inv_cancel hu
  have hinv : (u : FractionRing (MvPolynomial (Coord n) ℤ ⧸ V))⁻¹ ∈ (dehomFrac V c).range := by
    rw [← eq_inv_of_mul_eq_one_right (congrArg Subtype.val hw)]
    exact w.2
  have e : classFrac V (X p) / classFrac V (X ⟨p.1, c' p.1⟩) =
      classFrac V (X p) / classFrac V (X ⟨p.1, c p.1⟩) * (u : FractionRing _)⁻¹ := by
    change _ = _ * (classFrac V (X ⟨p.1, c' p.1⟩) / classFrac V (X ⟨p.1, c p.1⟩))⁻¹
    field_simp [hz p.1, hz' p.1]
  change classFrac V (X p) / classFrac V (X ⟨p.1, c' p.1⟩) ∈ (dehomFrac V c).range
  rw [e]
  exact mul_mem (hmem p) hinv

theorem OrbitChartDehom.proof (hM : OrbitChartMax.Statement) (hQ : OrbitChartQuot.Statement) :
    OrbitChartDehom.Statement := by
  intro ι _ _ _ n A x s hx hs V hV c c' hc hc'
  have hPV : orbitIdeal x ≤ V := le_sup_left.trans hV.1.1.2
  have : V.IsPrime := hV.1.1.1
  obtain ⟨a, -, hsa, -⟩ := id hs
  have hVh : ∀ f ∈ V, ∀ b : ι → ℕ, weightedHomogeneousComponent (coordDeg n) b f ∈ V :=
    fun f hf b ↦ weightedHomogeneousComponent_mem_of_mem_divSupp x ((geoMultiHomog_iff s a).mp hsa)
      hV hf b
  refine ⟨comap_sup_chartOneIdeal hVh hc, ?_⟩
  have hfield : ∀ d : (k : ι) → Fin (n k + 1),
      (∀ k, (X ⟨k, d k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) → IsField (dehomFrac V d).range := by
    intro d hd
    have hxd : ∀ k, x k (d k) ≠ 0 := by
      intro k h0
      apply hd k
      apply hPV
      rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X]
      simp [flatCone, h0]
    obtain ⟨eQ⟩ := hQ ι n x d hxd V hPV
    have hmax := hM ι n A x s hx hs V hV d hd
    exact MulEquiv.isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax)
      (eQ.trans (quotEquivRange hVh hd)).symm.toMulEquiv
  have hr : (dehomFrac V c).range = (dehomFrac V c').range :=
    le_antisymm (range_dehomFrac_le hc' hc (hfield c' hc')) (range_dehomFrac_le hc hc' (hfield c hc))
  exact ⟨(quotEquivRange hVh hc).trans
    ((Subalgebra.equivOfEq _ _ hr).toRingEquiv.trans (quotEquivRange hVh hc').symm)⟩

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitDegreeRatio
section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitDegreeRatioLemmas
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {ι : Type} {n : ι → ℕ}

def chartHomogQ (c : (k : ι) → Fin (n k + 1)) (f : MvPolynomial (Coord n) ℚ)
    [Fintype ι] : MvPolynomial (Coord n) ℚ :=
  ∑ m ∈ f.support, C (AddMonoidAlgebra.coeff f m) * ∏ p : Coord n, (X p ^ m p * X ⟨p.1, c p.1⟩ ^ (f.totalDegree - m p))

theorem le_totalDegree_of_mem_support {f : MvPolynomial (Coord n) ℚ} {m : Coord n →₀ ℕ}
    (hm : m ∈ f.support) (p : Coord n) : m p ≤ f.totalDegree :=
  (monomial_le_degreeOf p hm).trans (degreeOf_le_totalDegree f p)

variable [Fintype ι]

theorem aeval_chartHomogQ {S : Type*} [CommRing S] [Algebra ℚ S] (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℚ) (y : Coord n → S) :
    aeval y (chartHomogQ c f) = ∑ m ∈ f.support, algebraMap ℚ S (AddMonoidAlgebra.coeff f m) *
      ∏ p : Coord n, (y p ^ m p * y ⟨p.1, c p.1⟩ ^ (f.totalDegree - m p)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [chartHomogQ, map_sum, map_prod]

theorem aeval_chartHomogQ_field {K : Type*} [Field K] [Algebra ℚ K] (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℚ) (y : Coord n → K) (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    aeval y (chartHomogQ c f) = (∏ p : Coord n, y ⟨p.1, c p.1⟩ ^ f.totalDegree) *
      aeval (fun p ↦ y p / y ⟨p.1, c p.1⟩) f := by
  rw [aeval_chartHomogQ, aeval_def, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have h : ∀ p : Coord n, y p ^ m p * y ⟨p.1, c p.1⟩ ^ (f.totalDegree - m p) =
      y ⟨p.1, c p.1⟩ ^ f.totalDegree * (y p / y ⟨p.1, c p.1⟩) ^ m p := by
    intro p
    obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (le_totalDegree_of_mem_support hm p)
    have hyp := hy p.1
    rw [he, Nat.add_sub_cancel_left, pow_add, div_pow]
    field_simp
  simp_rw [h, Finset.prod_mul_distrib]
  ring

theorem coneMapQ_chartHomogQ (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℚ) :
    OrbitCurve.coneMapQ x (chartHomogQ c f) =
      C (aeval (flatCone x) (chartHomogQ c f)) * ∏ p : Coord n, X p.1 ^ f.totalDegree := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [OrbitCurve.coneMapQ, aeval_chartHomogQ, aeval_chartHomogQ, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have h : ∀ p : Coord n,
      (C (flatCone x p) * X p.1 : MvPolynomial ι (AlgebraicClosure ℚ)) ^ m p *
        (C (flatCone x ⟨p.1, c p.1⟩) * X p.1) ^ (f.totalDegree - m p) =
      C (flatCone x p ^ m p * flatCone x ⟨p.1, c p.1⟩ ^ (f.totalDegree - m p)) *
        X p.1 ^ f.totalDegree := by
    intro p
    obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (le_totalDegree_of_mem_support hm p)
    rw [he, Nat.add_sub_cancel_left]
    simp only [mul_pow, map_mul, map_pow, pow_add]
    ring
  simp only [h, Finset.prod_mul_distrib, map_mul, map_prod, MvPolynomial.algebraMap_apply]
  ring

theorem aeval_ratio_eq_zero (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) {z : Coord n → ℂ} (hz : z ∈ Geo.mcPts (ι := blockIdx n) (orbitIdeal x))
    (hz0 : ∀ k, z ⟨k, c k⟩ ≠ 0) (f : MvPolynomial (Coord n) ℚ)
    (hf : aeval (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) f = 0) :
    aeval (fun p ↦ z p / z ⟨p.1, c p.1⟩) f = 0 := by
  have hx : aeval (flatCone x) (chartHomogQ c f) = 0 := by
    rw [aeval_chartHomogQ_field c f (flatCone x) hc]
    exact mul_eq_zero_of_right _ hf
  have hker : chartHomogQ c f ∈ RingHom.ker (OrbitCurve.coneMapQ x) := by
    rw [RingHom.mem_ker, coneMapQ_chartHomogQ, hx, map_zero, zero_mul]
  classical
  rw [OrbitCurve.ker_coneMapQ] at hker
  have hle : ReciprocityTheory.AnForm.R.extQ (orbitIdeal x) ≤
      RingHom.ker (aeval z : MvPolynomial (Coord n) ℚ →ₐ[ℚ] ℂ) := by
    refine Ideal.map_le_iff_le_comap.mpr fun g hg ↦ ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, ← algebraMap_int_eq, aeval_map_algebraMap, aeval_def,
      algebraMap_int_eq, ← eval_map]
    exact hz.2 g hg
  have h := hle hker
  rw [RingHom.mem_ker, aeval_chartHomogQ_field c f z hz0] at h
  exact (mul_eq_zero.mp h).resolve_left
    (Finset.prod_ne_zero_iff.mpr fun p _ ↦ pow_ne_zero _ (hz0 p.1))

variable [DecidableEq ι]

theorem chart_ne_zero_of_mem_mcPts (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) {z : Coord n → ℂ}
    (hz : z ∈ Geo.mcPts (ι := blockIdx n) (orbitIdeal x)) (k : ι) : z ⟨k, c k⟩ ≠ 0 := by
  intro h0
  obtain ⟨i, hi⟩ := hz.1 k
  obtain ⟨g, hg0, hg⟩ := exists_int_relation (flatCone x ⟨k, i⟩ / flatCone x ⟨k, c k⟩)
  have h := hz.2 _ (homogForm_mem_orbitIdeal x g ⟨k, i⟩ ⟨k, c k⟩ rfl (hc k) hg)
  rw [eval_homogForm, h0, homog_sum_zero] at h
  exact mul_ne_zero (Int.cast_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hg0))
    (pow_ne_zero _ hi) h

end

end GroundTheory.Heights₂.Heights
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {ι : Type} {n : ι → ℕ}

def ratioVec (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) :
    Coord n → ratioField x :=
  fun p ↦ ⟨x p.1 p.2 / x p.1 (c p.1), div_mem_ratioField x _ _ _⟩

theorem val_aeval_ratioVec (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℚ) :
    ((aeval (ratioVec x c) f : ratioField x) : AlgebraicClosure ℚ) =
      aeval (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) f :=
  DFunLike.congr_fun (comp_aeval (ratioVec x c) (ratioField x).val) f

theorem aeval_ratioVec_surjective (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) :
    Function.Surjective (aeval (ratioVec x c) : MvPolynomial (Coord n) ℚ →ₐ[ℚ] ratioField x) := by
  set S := Set.range fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)
  have hL : ratioField x = IntermediateField.adjoin ℚ S := by
    refine le_antisymm (IntermediateField.adjoin_le_iff.mpr ?_)
      (IntermediateField.adjoin_le_iff.mpr ?_)
    · rintro _ ⟨⟨k, i, j⟩, rfl⟩
      dsimp only
      rw [← div_div_div_cancel_right₀ (hc k) (x k i) (x k j)]
      exact div_mem (IntermediateField.subset_adjoin ℚ S ⟨⟨k, i⟩, rfl⟩)
        (IntermediateField.subset_adjoin ℚ S ⟨⟨k, j⟩, rfl⟩)
    · rintro _ ⟨p, rfl⟩
      exact div_mem_ratioField x _ _ _
  intro a
  have ha : (a : AlgebraicClosure ℚ) ∈
      (aeval (R := ℚ) fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)).range := by
    have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
    rw [aeval_range, ← IntermediateField.adjoin_toSubalgebra, ← hL]
    exact a.2
  obtain ⟨f, hf⟩ := ha
  exact ⟨f, Subtype.ext ((val_aeval_ratioVec x c f).trans hf)⟩

theorem exists_extend_embedding (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (τ : L →+* ℂ) :
    ∃ σ : AlgebraicClosure ℚ →+* ℂ, ∀ a : L, σ a = τ a := by
  let : Algebra L ℂ := τ.toAlgebra
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  have : Algebra.IsAlgebraic L (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) L
  exact ⟨(IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[L] ℂ).toRingHom, fun a ↦
    (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[L] ℂ).commutes a⟩

theorem OrbitDegreeRatio.proof : OrbitDegreeRatio.Statement := by
  intro ι _ _ _ n x hx
  obtain ⟨c, hc⟩ := exists_chart hx
  set W := orbitIdeal x
  set L := ratioField x
  set Q := Quot fun z z' : Geo.mcPts (ι := blockIdx n) W ↦
    ∃ a : ι → ℂ, (∀ k, a k ≠ 0) ∧ (z' : Coord n → ℂ) = fun p ↦ a p.1 * (z : Coord n → ℂ) p
  show Nat.card Q = _
  choose σ hσ using exists_extend_embedding L
  have hpt : ∀ τ : L →+* ℂ, (fun p ↦ σ τ (flatCone x p)) ∈ Geo.mcPts (ι := blockIdx n) W := by
    intro τ
    refine ⟨fun k ↦ ?_, fun f hf ↦ eval_conj_eq_zero x (σ τ) hf⟩
    obtain ⟨i, hi⟩ := Function.ne_iff.mp (hx k)
    exact ⟨i, (map_ne_zero _).mpr hi⟩
  let Φ : (L →+* ℂ) → Q := fun τ ↦ Quot.mk _ ⟨_, hpt τ⟩

  let R : Q → Coord n → ℂ := Quot.lift
    (fun z p ↦ (z : Coord n → ℂ) p / (z : Coord n → ℂ) ⟨p.1, c p.1⟩) (by
      rintro z z' ⟨a, ha, e⟩
      funext p
      simp only [e]
      rw [mul_div_mul_left _ _ (ha p.1)])
  have hRΦ : ∀ τ p, R (Φ τ) p = τ (ratioVec x c p) := by
    intro τ p
    show σ τ (x p.1 p.2) / σ τ (x p.1 (c p.1)) = _
    rw [← map_div₀]
    exact hσ τ (ratioVec x c p)
  have hτ : ∀ (τ : L →+* ℂ) f, τ (aeval (ratioVec x c) f) =
      aeval (fun p ↦ τ (ratioVec x c p)) f := fun τ f ↦
    DFunLike.congr_fun (comp_aeval (ratioVec x c) τ.toRatAlgHom) f
  let ψ : MvPolynomial (Coord n) ℚ →+* L :=
    (aeval (ratioVec x c) : MvPolynomial (Coord n) ℚ →ₐ[ℚ] L).toRingHom
  have hsurj : Function.Surjective ψ := aeval_ratioVec_surjective x c hc

  have hinj : Function.Injective Φ := by
    intro τ τ' h
    have e : (fun p ↦ τ (ratioVec x c p)) = fun p ↦ τ' (ratioVec x c p) := funext fun p ↦ by
      rw [← hRΦ, ← hRΦ, h]
    ext a
    obtain ⟨f, rfl⟩ := hsurj a
    show τ (aeval (ratioVec x c) f) = τ' (aeval (ratioVec x c) f)
    rw [hτ, hτ, e]

  have hΦ : Function.Surjective Φ := by
    refine Quot.ind fun z ↦ ?_
    obtain ⟨z, hz⟩ := z
    have hz0 := chart_ne_zero_of_mem_mcPts x c hc hz
    let g : {g : MvPolynomial (Coord n) ℚ →+* ℂ // RingHom.ker ψ ≤ RingHom.ker g} :=
      ⟨(aeval fun p ↦ z p / z ⟨p.1, c p.1⟩ : MvPolynomial (Coord n) ℚ →ₐ[ℚ] ℂ).toRingHom,
        fun f hf ↦ by
          rw [RingHom.mem_ker] at hf ⊢
          refine aeval_ratio_eq_zero x c hc hz hz0 f ?_
          rw [← val_aeval_ratioVec]
          exact congrArg Subtype.val hf⟩
    have hτp : ∀ p, ψ.liftOfSurjective hsurj g (ratioVec x c p) =
        z p / z ⟨p.1, c p.1⟩ := fun p ↦ by
      have h := RingHom.liftOfSurjective_comp_apply ψ hsurj g (X p)
      simp only [ψ, g, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X] at h
      exact h
    set τ := ψ.liftOfSurjective hsurj g
    refine ⟨τ, (Quot.sound ⟨fun k ↦ σ τ (x k (c k)) / z ⟨k, c k⟩,
      fun k ↦ div_ne_zero ((map_ne_zero _).mpr (hc k)) (hz0 k), ?_⟩).symm⟩
    funext p
    have h1 : σ τ (x p.1 p.2) = σ τ (x p.1 p.2 / x p.1 (c p.1)) * σ τ (x p.1 (c p.1)) := by
      rw [← map_mul, div_mul_cancel₀ _ (hc p.1)]
    have h2 : σ τ (x p.1 p.2 / x p.1 (c p.1)) = z p / z ⟨p.1, c p.1⟩ :=
      (hσ τ (ratioVec x c p)).trans (hτp p)
    show σ τ (x p.1 p.2) = σ τ (x p.1 (c p.1)) / z ⟨p.1, c p.1⟩ * z p
    rw [h1, h2]
    ring
  rw [← Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hΦ⟩), Nat.card_eq_fintype_card,
    NumberField.Embeddings.card]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitArchSum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

variable {ι : Type} [Fintype ι] {n : ι → ℕ}

theorem eval_smul_of_isMultiHomog (s : MvPolynomial (Coord n) ℤ) (a : ι → ℕ)
    (hs : Geo.IsMultiHomog (ι := blockIdx n) s a) (c : ι → ℂ) (z : Coord n → ℂ) :
    eval (fun p ↦ c p.1 * z p) (map (Int.castRingHom ℂ) s) =
      (∏ k, c k ^ a k) * eval z (map (Int.castRingHom ℂ) s) := by
  have key : ∀ f : MvPolynomial (Coord n) ℤ,
      eval c (Geo.mConeMap (ι := blockIdx n) z f) = eval (fun p ↦ c p.1 * z p) (map (Int.castRingHom ℂ) f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r => simp [Geo.mConeMap]
    | add f g hf hg => simp only [map_add (f := _), hf, hg]
    | mul_X f p hf =>
      rw [map_mul, map_mul, map_mul, hf]
      simp [Geo.mConeMap, mul_comm]
  classical
  rw [← key, mConeMap_of_isMultiHomog z s a hs, eval_map]
  simp [map_prod, mul_comm]

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightComparison.PCentredPlacesFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

theorem CentredPlacesFinite.proof : CentredPlacesFinite.Statement := by
  intro L _ _ O hft _ m _
  have hq : Algebra.FiniteType ℤ (O ⧸ m) :=
    @Algebra.FiniteType.of_surjective ℤ O (O ⧸ m) _ _ _ _ _ hft (Ideal.Quotient.mkₐ ℤ m)
      (Ideal.Quotient.mkₐ_surjective ℤ m)
  let _ : Field (O ⧸ m) := Ideal.Quotient.field m
  obtain ⟨hp, -⟩ :=
    @natCard_eq_pow_length_of_finiteType (O ⧸ m) _
      (by convert hq <;> rfl) (ringChar (O ⧸ m))
      (ringChar.charP _)
  set p := ringChar (O ⧸ m)
  have hpm : (p : O) ∈ m := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero (O ⧸ m) p
  have hp0 : (p : L) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  refine (FinitePlace.hasFiniteMulSupport hp0).subset fun w hw ↦ ?_
  have hlt := (hw.2 (p : O)).mpr hpm
  have hcoe : ((p : O) : L) = (p : L) := by simp
  rw [hcoe] at hlt
  exact hlt.ne

end GroundTheory.Heights₂.Heights
end
