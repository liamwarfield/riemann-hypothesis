module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernWeilNumbersOfDegreeEqChernIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassEqSelfIntersectionOfGenerated

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeEqIntegralTopChernFormComplex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassEqSelfIntersectionLineBundle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolynomialChernIntegralTensPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolynomialMongeAmpereMassAddZsmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolynomialMongeAmpereMassAddZsmul
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.MongeAmperePoly

variable {X : Type} [TopologicalSpace X]

theorem update_comp_swap {e : ℕ} (Φ : Fin (e + 1) → LocPot X) (i : Fin (e + 1)) (P : LocPot X) :
    Function.update Φ i P ∘ Equiv.swap 0 i =
      (Fin.cons P (fun k => Φ (Equiv.swap 0 i k.succ)) : Fin (e + 1) → LocPot X) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp
  · have h : Equiv.swap 0 i k.succ ≠ i := by
      intro h
      have h2 : Equiv.swap 0 i k.succ = Equiv.swap 0 i 0 := by rw [h, Equiv.swap_apply_left]
      exact Fin.succ_ne_zero k ((Equiv.swap 0 i).injective h2)
    simp [Function.update_of_ne h]

theorem mInt_update_add_zsmul [CompactSpace X] [T2Space X] {e : ℕ} (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (i : Fin e) (P Q : LocPot X)
    (hP : IsPotential A P) (hQ : IsPotential A Q) (m : ℤ) :
    mInt A (Function.update Φ i (P + Q.zsmul m)) (fun _ => 1) =
      mInt A (Function.update Φ i P) (fun _ => 1) +
        m * mInt A (Function.update Φ i Q) (fun _ => 1) := by
  cases e with
  | zero => exact i.elim0
  | succ e =>
    have key : ∀ R : LocPot X, mInt A (Function.update Φ i R) (fun _ => 1) =
        mInt A (Fin.cons R (fun k => Φ (Equiv.swap 0 i k.succ))) (fun _ => 1) := by
      intro R
      rw [← update_comp_swap, mIntSymm]
    have hT : ∀ k : Fin e, IsPotential A (Φ (Equiv.swap 0 i k.succ)) := fun k => hΦ _
    have hI : ∀ R : LocPot X, IsPotential A R →
        MIntegrable A (Fin.cons R (fun k => Φ (Equiv.swap 0 i k.succ))) (fun _ => 1) := by
      intro R hR
      refine mIntegrableCont A _ (fun k => ?_) _ continuous_const
      refine Fin.cases ?_ (fun k => ?_) k
      · simpa using hR
      · simpa using hT k
    have hQm := isPotentialZsmul A m Q hQ
    rw [key, key, key, mIntAdd A P _ _ hP hQm hT _ (hI _ hP) (hI _ hQm),
      mIntZsmul A m Q _ hQ hT]

theorem exists_poly_finset [CompactSpace X] [T2Space X] {e : ℕ} (A : FinHolAtlas e X)
    (Ψ : Fin e → LocPot X) (hΨ : ∀ i, IsPotential A (Ψ i)) (S : Finset (Fin e)) :
    ∀ Φ : Fin e → LocPot X, (∀ i, IsPotential A (Φ i)) → ∃ P : Polynomial ℝ, ∀ m : ℤ,
      mInt A (fun i => if i ∈ S then Φ i + (Ψ i).zsmul m else Φ i) (fun _ => 1) =
        P.eval (m : ℝ) := by
  induction S using Finset.induction_on with
  | empty =>
    intro Φ _
    exact ⟨Polynomial.C (mInt A Φ (fun _ => 1)), fun m => by simp⟩
  | insert a S ha ih =>
    intro Φ hΦ
    have hΦ' : ∀ i, IsPotential A (Function.update Φ a (Ψ a) i) := by
      intro i
      by_cases h : i = a
      · subst h; simpa using hΨ i
      · simpa [Function.update_of_ne h] using hΦ i
    obtain ⟨P₁, h₁⟩ := ih Φ hΦ
    obtain ⟨P₂, h₂⟩ := ih _ hΦ'
    refine ⟨P₁ + Polynomial.X * P₂, fun m => ?_⟩
    set F : Fin e → LocPot X := fun i => if i ∈ S then Φ i + (Ψ i).zsmul m else Φ i with hF
    have hFp : ∀ i, IsPotential A (F i) := by
      intro i
      by_cases h : i ∈ S
      · simpa [hF, h] using isPotentialAdd A _ _ (hΦ i) (isPotentialZsmul A m _ (hΨ i))
      · simpa [hF, h] using hΦ i
    have e0 : (fun i => if i ∈ insert a S then Φ i + (Ψ i).zsmul m else Φ i) =
        Function.update F a (Φ a + (Ψ a).zsmul m) := by
      funext i
      by_cases h : i = a
      · subst h; simp
      · simp [hF, Function.update_of_ne h, h]
    have e1 : Function.update F a (Φ a) = F := by
      funext i
      by_cases h : i = a
      · subst h; simp [hF, ha]
      · simp [Function.update_of_ne h]
    have e2 : Function.update F a (Ψ a) = fun i => if i ∈ S then
        Function.update Φ a (Ψ a) i + (Ψ i).zsmul m else Function.update Φ a (Ψ a) i := by
      funext i
      by_cases h : i = a
      · subst h; simp [ha]
      · simp [hF, Function.update_of_ne h]
    rw [e0, mInt_update_add_zsmul A F hFp a _ _ (hΦ a) (hΨ a), e1, e2, h₂ m]
    have := h₁ m
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
    rw [← this]

theorem mInt_add_zsmul_poly : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X]
    [T2Space X] (A : FinHolAtlas e X) (Φ Ψ : Fin e → LocPot X), (∀ i, IsPotential A (Φ i)) →
    (∀ i, IsPotential A (Ψ i)) → ∃ P : Polynomial ℝ, ∀ m : ℤ,
      mInt A (fun i => Φ i + (Ψ i).zsmul m) (fun _ => 1) = P.eval (m : ℝ) := by
  intro e X _ _ _ A Φ Ψ hΦ hΨ
  obtain ⟨P, hP⟩ := exists_poly_finset A Ψ hΨ Finset.univ Φ hΦ
  exact ⟨P, fun m => by simpa using hP m⟩

end GlobalTheory.MongeAmperePoly
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolynomialMongeAmpereMassAddZsmulStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomial_mongeAmpereMass_add_zsmul : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Φ Ψ : Fin e → LocPot X), (∀ i, IsPotential A (Φ i)) → (∀ i, IsPotential A (Ψ i)) → ∃ P : Polynomial ℝ, ∀ m : ℤ, mInt A (fun i => Φ i + (Ψ i).zsmul m) (fun _ => 1) = P.eval (m : ℝ) := by
  first | exact @GlobalTheory.MongeAmperePoly.mInt_add_zsmul_poly | exact GlobalTheory.MongeAmperePoly.mInt_add_zsmul_poly | (intros; apply GlobalTheory.MongeAmperePoly.mInt_add_zsmul_poly <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolynomialChernIntegralTensPow
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ChernPoly

theorem chernInt_tens_pow_poly : ∀ (Y : Var ℂ) (L H : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L)
    (ψ : Weight Y.str (RingHom.id ℂ) H), φ.IsCInf → ψ.IsCInf → ∃ P : Polynomial ℝ,
      P.eval 0 = Weight.chernInt φ Y.dim Set.univ (fun _ => 1) ∧ ∀ m : ℕ,
        Weight.chernInt (φ.tens (ψ.pow m)) Y.dim Set.univ (fun _ => 1) = P.eval (m : ℝ) := by
  intro Y L H φ ψ hφ hψ
  obtain ⟨hc, ht, _, A, hA⟩ := GlobalTheory.T.complexPoints_smoothProjVariety_compact_manifold Y
  have := hc
  have := ht

  have hφs : φ.IsSmooth (AnRead.all Y.str (RingHom.id ℂ) Y.dim) :=
    (Weight.isCInf_iff_isSmooth _).1 hφ
  have hψs : ψ.IsSmooth (AnRead.all Y.str (RingHom.id ℂ) Y.dim) :=
    (Weight.isCInf_iff_isSmooth _).1 hψ
  have hΦ : IsPotential A φ.locPot := hφs.isPotential hA
  have hΨ : IsPotential A ψ.locPot := hψs.isPotential hA

  obtain ⟨P, hP⟩ := GlobalTheory.T.exists_polynomial_mongeAmpereMass_add_zsmul Y.dim _ A (fun _ => φ.locPot) (fun _ => ψ.locPot)
    (fun _ => hΦ) (fun _ => hΨ)

  refine ⟨P, ?_, fun m => ?_⟩
  · rw [(GlobalTheory.T.chernIntegral_one_eq_mongeAmpereIntegral Y L φ hφ).2 A hA, ← (by simpa using hP 0 :
      mInt A (fun _ => φ.locPot + ψ.locPot.zsmul 0) (fun _ => 1) = P.eval 0)]
    refine SameForm.mInt_eq (fun _ => ?_) _
    refine (Weight.sameForm_of_eq φ hA (isPotentialAdd A _ _ hΦ (isPotentialZsmul A 0 _ hΨ))
      (fun x => ⟨pick φ.isLB x, mem_pick φ.isLB x, fun z => ?_⟩)).symm
    show φ.φ (pick φ.isLB x) z / 2 = φ.locPot.φ x z + ((0 : ℤ) : ℝ) * ψ.locPot.φ x z
    rw [Weight.locPot_φ]
    simp
  · have hT : (φ.tens (ψ.pow m)).IsCInf := hφ.tens (hψ.zpow m)
    rw [(GlobalTheory.T.chernIntegral_one_eq_mongeAmpereIntegral Y _ _ hT).2 A hA, show ((m : ℕ) : ℝ) = (((m : ℕ) : ℤ) : ℝ) by push_cast; rfl,
      ← hP m]
    refine SameForm.mInt_eq (fun _ => ?_) _
    refine Weight.sameForm_of_eq _ hA (isPotentialAdd A _ _ hΦ (isPotentialZsmul A m _ hΨ))
      (fun x => ⟨(pick φ.isLB x, fun _ => pick ψ.isLB x),
        mem_ptsIn_inf.2 ⟨mem_pick φ.isLB x, mem_pow_iff.2 (mem_pick ψ.isLB x)⟩, fun z => ?_⟩)
    show (φ.φ (pick φ.isLB x) z + (ψ.zpow m).φ (fun _ => pick ψ.isLB x) z) / 2 =
      φ.locPot.φ x z + ((m : ℤ) : ℝ) * ψ.locPot.φ x z
    rw [Weight.zpow_φ, Weight.locPot_φ, Weight.locPot_φ]
    ring

end GlobalTheory.ChernPoly
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolynomialChernIntegralTensPowStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomial_chernIntegral_tens_pow : ∀ (Y : Var ℂ) (L H : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L) (ψ : Weight Y.str (RingHom.id ℂ) H), φ.IsCInf → ψ.IsCInf → ∃ P : Polynomial ℝ, P.eval 0 = Weight.chernInt φ Y.dim Set.univ (fun _ => 1) ∧ ∀ m : ℕ, Weight.chernInt (φ.tens (ψ.pow m)) Y.dim Set.univ (fun _ => 1) = P.eval (m : ℝ) := by
  first | exact @GlobalTheory.ChernPoly.chernInt_tens_pow_poly | exact GlobalTheory.ChernPoly.chernInt_tens_pow_poly | (intros; apply GlobalTheory.ChernPoly.chernInt_tens_pow_poly <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolynomialMultilinear
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

namespace GlobalTheory.SelfInterPoly

theorem exists_polynomial_multilinear {A : Type*} {ι : Type} [AddCommGroup A] [Fintype ι]
    (f : (ι → A) →ₘₗ[ℤ] ℤ) (a b : A) :
    ∃ P : Polynomial ℝ, ∀ m : ℕ, (f (fun _ => a + m • b) : ℝ) = P.eval (m : ℝ) := by
  classical
  refine ⟨∑ S : Finset ι, Polynomial.C (f (S.piecewise (fun _ => b) (fun _ => a)) : ℝ) *
    Polynomial.X ^ S.card, fun m => ?_⟩
  have e : (fun _ : ι => a + m • b) = (fun _ : ι => (m : ℤ) • b) + (fun _ : ι => a) := by
    funext i
    simp [add_comm]
  rw [e, f.map_add_univ, Polynomial.eval_finsetSum, Int.cast_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  have e₂ : S.piecewise (fun _ : ι => (m : ℤ) • b) (fun _ : ι => a) =
      S.piecewise (fun i => (fun _ : ι => (m : ℤ)) i • S.piecewise (fun _ => b) (fun _ => a) i)
        (S.piecewise (fun _ => b) (fun _ => a)) := by
    funext i
    by_cases h : i ∈ S <;> simp [h]
  rw [e₂, f.map_piecewise_smul]
  simp [mul_comm]

theorem exists_polynomial_topSelf : ∀ (Y : Var ℂ) (L H : LB Y.X), L.IsLB → H.IsLB → ∃ P : Polynomial ℝ, P.eval 0 = (topSelfIntersection ℂ L Y.dim : ℝ) ∧ ∀ m : ℕ, (topSelfIntersection ℂ (CechPic.tens L (lbPow H m)) Y.dim : ℝ) = P.eval (m : ℝ) := by
  intro Y L H hL hH
  have hv := diffVanish_chiPic_of_isProjOver Y.algebraMap_Γ (structureModule Y.X) Y.isProjOver
    (d := Y.dim) (by rw [QCoh.suppDim_structureModule, Y.topologicalKrullDim_eq])
  have key : ∀ (M : LB Y.X) (hM : M.IsLB), topSelfIntersection ℂ M Y.dim = hv.form fun _ => cls M hM :=
    fun M hM => (interNum_eq_multiDiff ℂ _ fun _ => hM).trans (hv.form_apply _ 0).symm
  obtain ⟨P, hP⟩ := exists_polynomial_multilinear hv.form (cls L hL) (cls H hH)
  refine ⟨P, ?_, fun m => ?_⟩
  · have h0 := hP 0
    rw [zero_nsmul, add_zero, Nat.cast_zero] at h0
    rw [key L hL, h0]
  · rw [key _ (isLB_tens hL (isLB_lbPow hH m)), cls_tens hL (isLB_lbPow hH m), cls_lbPow hH, hP]

end GlobalTheory.SelfInterPoly
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassEqSelfIntersectionLineBundle
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option autoImplicit false

namespace GlobalTheory.MassDegree

theorem chernInt_eq_topSelf : ∀ (Y : Var ℂ) (L : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = (topSelfIntersection ℂ L Y.dim : ℝ) := by
  intro Y L φ hφ
  let ψ : Weight Y.str (RingHom.id ℂ) ((ProjSpace.O1 ℂ Y.N).pull Y.ι) :=
    ((ProjSpace.hermitianTwistingSheaf ℂ Y.N).φ (RingHom.id ℂ)).pull Y.ι Y.ι_str
  have hψ : ψ.IsCInf := ((ProjSpace.hermitianTwistingSheaf ℂ Y.N).cInf (RingHom.id ℂ)).pull Y.ι Y.ι_str
  obtain ⟨P, hP0, hP⟩ := GlobalTheory.T.exists_polynomial_chernIntegral_tens_pow Y L _ φ ψ hφ hψ
  obtain ⟨Q, hQ0, hQ⟩ := GlobalTheory.SelfInterPoly.exists_polynomial_topSelf Y L _ φ.isLB ψ.isLB
  obtain ⟨m₀, hm₀⟩ := GlobalTheory.T.twist_ample_globally_generated Y L φ.isLB
  have key : ∀ m : ℕ, m₀ ≤ m → P.eval (m : ℝ) = Q.eval (m : ℝ) := by
    intro m hm
    obtain ⟨n, u, hu⟩ := hm₀ m hm
    rw [← hP m, ← hQ m]
    exact GlobalTheory.T.chernMass_eq_selfIntersection_of_generated Y _ (φ.tens (ψ.pow m)) (hφ.tens (hψ.zpow m)) n u hu
  have hPQ : P = Q := by
    refine Polynomial.eq_of_infinite_eval_eq P Q ?_
    refine Set.Infinite.mono ?_ ((Set.Ici_infinite m₀).image Nat.cast_injective.injOn)
    rintro _ ⟨m, hm, rfl⟩
    exact key m hm
  rw [← hP0, ← hQ0, hPQ]

end GlobalTheory.MassDegree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassEqSelfIntersectionLineBundleStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernMass_eq_selfIntersection_lineBundle : ∀ (Y : Var ℂ) (L : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = (topSelfIntersection ℂ L Y.dim : ℝ) := by
  first | exact @GlobalTheory.MassDegree.chernInt_eq_topSelf | exact GlobalTheory.MassDegree.chernInt_eq_topSelf | (intros; apply GlobalTheory.MassDegree.chernInt_eq_topSelf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionDivisorEqSelfIntersectionPresented
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionDivisorEqSelfIntersectionPresented
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ChernDegree

theorem inter_const_eq_topSelf_of_presents :
    ∀ (Y : Var ℂ) (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ), L.IsLB → Presents Δ L r → Y.inter (fun _ => Δ) = topSelfIntersection ℂ L Y.dim :=
  fun _ _ _ _ hL h => Var.inter_eq_of_toPic_eq (fun _ => hL) fun _ => h.toPic_eq

end GlobalTheory.ChernDegree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionDivisorEqSelfIntersectionPresentedStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_divisor_eq_selfIntersection_presented : ∀ (Y : Var ℂ) (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ), L.IsLB → Presents Δ L r → Y.inter (fun _ => Δ) = topSelfIntersection ℂ L Y.dim := by
  first | exact @GlobalTheory.ChernDegree.inter_const_eq_topSelf_of_presents | exact GlobalTheory.ChernDegree.inter_const_eq_topSelf_of_presents | (intros; apply GlobalTheory.ChernDegree.inter_const_eq_topSelf_of_presents <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeEqIntegralTopChernFormComplex
namespace GlobalTheory.ChernDegree

theorem chernDegreeComplex : GlobalTheory.Published.ChernDegreeComplex := fun Y Δ L r hr φ hφ =>
  ⟨(GlobalTheory.T.chernIntegral_one_eq_mongeAmpereIntegral Y L φ hφ).1, by
    rw [GlobalTheory.T.chernMass_eq_selfIntersection_lineBundle Y L φ hφ, GlobalTheory.T.intersection_divisor_eq_selfIntersection_presented Y Δ L r φ.isLB hr]⟩

end GlobalTheory.ChernDegree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeEqIntegralTopChernFormComplexStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_eq_integral_topChernForm_complex : GlobalTheory.Published.ChernDegreeComplex := by
  first | exact @GlobalTheory.ChernDegree.chernDegreeComplex | exact GlobalTheory.ChernDegree.chernDegreeComplex | (intros; apply GlobalTheory.ChernDegree.chernDegreeComplex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernNumbersEqIntegralChernFormsSmoothMetric
namespace GlobalTheory.ChernDegree

theorem chernWeilNumbers_holds : GlobalTheory.Published.ChernWeilNumbers :=
  GlobalTheory.T.chernWeilNumbers_of_degree_eq_chernIntegral GlobalTheory.T.degree_eq_integral_topChernForm_complex

end GlobalTheory.ChernDegree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernNumbersEqIntegralChernFormsSmoothMetricStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernNumbers_eq_integral_chernForms_smoothMetric : GlobalTheory.Published.ChernWeilNumbers := by
  first | exact @GlobalTheory.ChernDegree.chernWeilNumbers_holds | exact GlobalTheory.ChernDegree.chernWeilNumbers_holds | (intros; apply GlobalTheory.ChernDegree.chernWeilNumbers_holds <;> assumption)
end
