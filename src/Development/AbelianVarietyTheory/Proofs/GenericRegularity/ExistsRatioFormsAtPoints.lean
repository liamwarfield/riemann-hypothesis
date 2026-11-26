module

public import Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.RApprox
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfRangeSubset
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsObjOfUniformisedTripleComplex
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NatCastMemMaximalIdealOfOverLa
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsOfH0EqOneClosedFields

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsRatioFormsAtPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsRatioFormsAtPoints
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj

namespace GlobalTheory.ConstRatio

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
  {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

abbrev Deg (wL : WeightFamilies.Wt D j) (m : ℕ) : Submodule B.KO X.Forms :=
  LinearMap.range (X.inc (addL (wt0 D j) wL m))

theorem deg_mul {m n : ℕ} {x y : X.Forms} (hx : x ∈ Deg X wL m) (hy : y ∈ Deg X wL n) :
    x * y ∈ Deg X wL (m + n) := by
  obtain ⟨F, rfl⟩ := hx
  obtain ⟨G, rfl⟩ := hy
  have h : X.inc _ F * X.inc _ G ∈
      LinearMap.range (X.inc (wadd (addL (wt0 D j) wL m) (addL (wt0 D j) wL n))) := by
    obtain ⟨H, hH⟩ := X.inc_mul _ _ F G
    exact ⟨H, hH.symm⟩
  rwa [wadd_addL_addL, zero_weight_add] at h

theorem deg_one (F : B.Cusp j wL) : X.inc wL F ∈ Deg X wL 1 := by
  have h : X.inc wL F ∈ LinearMap.range (X.inc wL) := ⟨F, rfl⟩
  unfold Deg
  rwa [add_zero_weight_one_eq]

theorem deg_wsmul (k : ℕ) (g : B.Cusp j (wsmul k wL)) : X.inc (wsmul k wL) g ∈ Deg X wL k := by
  have h : X.inc _ g ∈ LinearMap.range (X.inc (wsmul k wL)) := ⟨g, rfl⟩
  unfold Deg
  rwa [addL, zero_weight_add]

theorem deg_mul_pow {m : ℕ} {y x : X.Forms} (hy : y ∈ Deg X wL m) (hx : x ∈ Deg X wL 1) (e : ℕ) :
    y * x ^ e ∈ Deg X wL (m + e) := by
  induction e with
  | zero => simpa using hy
  | succ e ih =>
    rw [pow_succ, ← mul_assoc, ← add_assoc]
    exact deg_mul X ih hx

theorem deg_mul_prod (d : Fin N →₀ ℕ) {m : ℕ} {y : X.Forms} (hy : y ∈ Deg X wL m) (s : Finset (Fin N)) :
    y * ∏ i ∈ s, X.inc wL (w i) ^ d i ∈ Deg X wL (m + ∑ i ∈ s, d i) := by
  classical
  refine Finset.induction_on s (by simpa using hy) ?_
  intro a s ha ih
  rw [Finset.prod_insert ha, Finset.sum_insert ha]
  have e1 : y * (X.inc wL (w a) ^ d a * ∏ i ∈ s, X.inc wL (w i) ^ d i) =
      (y * ∏ i ∈ s, X.inc wL (w i) ^ d i) * X.inc wL (w a) ^ d a := by ring
  have e2 : m + (d a + ∑ i ∈ s, d i) = m + ∑ i ∈ s, d i + d a := by ring
  rw [e1, e2]
  exact deg_mul_pow X ih (deg_one X (w a)) (d a)

theorem deg_mul_aeval {k : ℕ} (Pw : MvPolynomial (Fin N) B.KO) (hPw : Pw.IsHomogeneous k) {m : ℕ} {y : X.Forms}
    (hy : y ∈ Deg X wL m) :
    y * MvPolynomial.aeval (fun i => X.inc wL (w i)) Pw ∈ Deg X wL (m + k) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Pw.as_sum, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [MvPolynomial.aeval_monomial, mul_left_comm, ← Algebra.smul_def]
  refine Submodule.smul_mem _ _ ?_
  have hdeg : ∑ i ∈ d.support, d i = k := by
    have := hPw (MvPolynomial.mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  have h := deg_mul_prod X w d hy d.support
  rw [hdeg] at h
  exact h

theorem ratio_large {Ω : Type} [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)
    (hB : CurveLoc.BirAt X N w gF) (k0 : Fin N) (hk0 : gF (X.inc wL (w k0)) ≠ 0) (a : Ω) :
    ∃ k : ℕ, ∀ m, k < m → ∃ n d : B.Cusp j (addL (wt0 D j) wL m),
      gF (X.inc _ d) ≠ 0 ∧ gF (X.inc _ n) = a * gF (X.inc _ d) := by
  obtain ⟨k, g, Pw, hPw, hne, he⟩ := hB a
  refine ⟨k, fun m hm => ?_⟩
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt hm
  have h1 : X.inc wL (w k0) * X.inc wL (w k0) ^ e ∈ Deg X wL (1 + e) :=
    deg_mul_pow X (deg_one X (w k0)) (deg_one X (w k0)) e
  have hd := deg_mul_aeval X w Pw hPw h1
  have hn := deg_mul X h1 (deg_wsmul X k g)
  have e1 : 1 + e + k = k + e + 1 := by ring
  rw [e1] at hd hn
  obtain ⟨d, hd⟩ := hd
  obtain ⟨n, hn⟩ := hn
  have hPv : gF (MvPolynomial.aeval (fun i => X.inc wL (w i)) Pw) =
      MvPolynomial.aeval (fun i => gF (X.inc wL (w i))) Pw :=
    MvPolynomial.comp_aeval_apply (fun i => X.inc wL (w i)) gF Pw
  refine ⟨n, d, ?_, ?_⟩
  · rw [hd, map_mul, map_mul, map_pow, hPv]
    exact mul_ne_zero (mul_ne_zero hk0 (pow_ne_zero _ hk0)) hne
  · rw [hd, hn, map_mul, map_mul gF _ (MvPolynomial.aeval _ Pw), hPv, ← he]
    ring

end GlobalTheory.ConstRatio

namespace GlobalTheory


open ConstRatio in
theorem exists_ratio_forms_at_points : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (wL : WeightFamilies.Wt D j) (w : Fin N → B.Cusp j wL) (Pt : Type) [Finite Pt] (U : Pt → Type) [∀ ζ, Field (U ζ)] (ev : ∀ ζ, Rp X la N →+* U ζ) (ι : Type) (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)] (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z) (Zc : Pt → ι) (jz : ∀ ζ, Ω (Zc ζ) →+* U ζ), (∀ ζ, ∃ k, ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc wL (w k))) ≠ 0) → (∀ ζ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), gF (Zc ζ) (X.inc u F) = 0 → ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc u F)) = 0) → (∀ ζ (u : WeightFamilies.Wt D j) (F F' : B.Cusp j u), jz ζ (gF (Zc ζ) (X.inc u F)) * ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc u F')) = jz ζ (gF (Zc ζ) (X.inc u F')) * ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc u F))) → (∀ Z, CurveLoc.BirAt X N w (gF Z)) → (∀ Z (u : WeightFamilies.Wt D j) (F : B.Cusp j u), ∃ F' : B.Cusp j u, gF Z (X.inc u F') = gF Z (X.inc u F) ∧ ∀ Z', Z' ≠ Z → gF Z' (X.inc u F') = 0) → ∀ a : ∀ Z, Ω Z, ∃ (k : ℕ) (F F' : B.Cusp j (addL (wt0 D j) wL k)), ∀ ζ, ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc _ F')) ≠ 0 ∧ ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc _ F)) = jz ζ (a (Zc ζ)) * ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc _ F')) := by
  intro D B P j X la N wL w Pt _ U _ ev ι Ω _ _ gF Zc jz h1 h2 h3 hB hs a
  classical
  haveI := Fintype.ofFinite Pt
  choose k0 hk0 using h1
  have hg0 : ∀ ζ, gF (Zc ζ) (X.inc wL (w (k0 ζ))) ≠ 0 := fun ζ h => hk0 ζ (h2 ζ wL _ h)
  choose K hK using fun ζ => ratio_large X w (gF (Zc ζ)) (hB _) (k0 ζ) (hg0 ζ) (a _)
  set M : ℕ := Finset.univ.sup K with hM
  have hlt : ∀ ζ, K ζ < 1 + M := fun ζ => by
    have : K ζ ≤ M := Finset.le_sup (f := K) (Finset.mem_univ ζ)
    omega
  have key : ∀ Z, ∃ n d : B.Cusp j (addL (wt0 D j) wL (1 + M)),
      (∀ Z', Z' ≠ Z → gF Z' (X.inc _ n) = 0 ∧ gF Z' (X.inc _ d) = 0) ∧
      (Z ∈ Set.range Zc → gF Z (X.inc _ d) ≠ 0 ∧ gF Z (X.inc _ n) = a Z * gF Z (X.inc _ d)) := by
    intro Z
    by_cases hZ : Z ∈ Set.range Zc
    · obtain ⟨ζ, rfl⟩ := hZ
      obtain ⟨n, d, hd, hn⟩ := hK ζ _ (hlt ζ)
      obtain ⟨n', hn1, hn2⟩ := hs (Zc ζ) _ n
      obtain ⟨d', hd1, hd2⟩ := hs (Zc ζ) _ d
      refine ⟨n', d', fun Z' h => ⟨hn2 Z' h, hd2 Z' h⟩, fun _ => ?_⟩
      rw [hn1, hd1]
      exact ⟨hd, hn⟩
    · exact ⟨0, 0, fun Z' _ => by simp, fun h => absurd h hZ⟩
  choose n d hoff hon using key
  have hsum : ∀ (f : ι → B.Cusp j (addL (wt0 D j) wL (1 + M))),
      (∀ Z Z', Z' ≠ Z → gF Z' (X.inc _ (f Z)) = 0) → ∀ ζ,
      gF (Zc ζ) (X.inc _ (∑ Z ∈ Finset.univ.image Zc, f Z)) = gF (Zc ζ) (X.inc _ (f (Zc ζ))) := by
    intro f hf ζ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    exact Finset.sum_eq_single_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_univ ζ))
      fun Z _ h => hf Z _ h.symm
  refine ⟨1 + M, ∑ Z ∈ Finset.univ.image Zc, n Z, ∑ Z ∈ Finset.univ.image Zc, d Z, fun ζ => ?_⟩
  have hn := hsum n (fun Z Z' h => (hoff Z Z' h).1) ζ
  have hd := hsum d (fun Z Z' h => (hoff Z Z' h).2) ζ
  obtain ⟨o1, o2⟩ := hon (Zc ζ) ⟨ζ, rfl⟩
  rw [← hd] at o1
  rw [← hd, ← hn] at o2
  generalize (∑ Z ∈ Finset.univ.image Zc, n Z) = F at o2 ⊢
  generalize (∑ Z ∈ Finset.univ.image Zc, d Z) = F' at o1 o2 ⊢
  have hj : jz ζ (gF (Zc ζ) (X.inc _ F')) ≠ 0 := (map_ne_zero _).2 o1
  constructor
  · obtain ⟨G, hG⟩ := deg_mul_pow X (deg_one X (w (k0 ζ))) (deg_one X (w (k0 ζ))) M
    have hev : ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc _ G)) ≠ 0 := by
      rw [hG, map_mul, map_mul, map_pow, map_pow]
      exact mul_ne_zero (hk0 ζ) (pow_ne_zero _ (hk0 ζ))
    intro h0
    have h := h3 ζ _ F' G
    rw [h0, mul_zero] at h
    exact mul_ne_zero hj hev h
  · have h := h3 ζ _ F F'
    rw [o2, map_mul] at h
    apply mul_left_cancel₀ hj
    rw [← h]
    ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsRatioFormsAtPointsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ratio_forms_at_points_alt : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (wL : WeightFamilies.Wt D j) (w : Fin N → B.Cusp j wL) (Pt : Type) [Finite Pt] (U : Pt → Type) [∀ ζ, Field (U ζ)] (ev : ∀ ζ, Rp X la N →+* U ζ) (ι : Type) (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)] (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z) (Zc : Pt → ι) (jz : ∀ ζ, Ω (Zc ζ) →+* U ζ), (∀ ζ, ∃ k, ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc wL (w k))) ≠ 0) → (∀ ζ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), gF (Zc ζ) (X.inc u F) = 0 → ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc u F)) = 0) → (∀ ζ (u : WeightFamilies.Wt D j) (F F' : B.Cusp j u), jz ζ (gF (Zc ζ) (X.inc u F)) * ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc u F')) = jz ζ (gF (Zc ζ) (X.inc u F')) * ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc u F))) → (∀ Z, CurveLoc.BirAt X N w (gF Z)) → (∀ Z (u : WeightFamilies.Wt D j) (F : B.Cusp j u), ∃ F' : B.Cusp j u, gF Z (X.inc u F') = gF Z (X.inc u F) ∧ ∀ Z', Z' ≠ Z → gF Z' (X.inc u F') = 0) → ∀ a : ∀ Z, Ω Z, ∃ (k : ℕ) (F F' : B.Cusp j (addL (wt0 D j) wL k)), ∀ ζ, ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc _ F')) ≠ 0 ∧ ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc _ F)) = jz ζ (a (Zc ζ)) * ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc _ F')) := by
  first | exact @GlobalTheory.exists_ratio_forms_at_points | exact GlobalTheory.exists_ratio_forms_at_points | (intros; apply GlobalTheory.exists_ratio_forms_at_points <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralSmoothChartFrameModuli
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralSmoothChartFrameModuli
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.Frames

namespace GlobalTheory.LocalFrame

theorem secBaseChange_of_secTwist (hT : Out.SecTwistSt) : Out.SecBaseChangeSt := by
  refine (GlobalTheory.AbLaw.AllLaws.laws_of_h0_eq_one fun K _ _ P => ?_).1.secBaseChange
  obtain ⟨b, hb⟩ := GlobalTheory.PowBasis.exists_basis_pow hT P 1 le_rfl K (𝟙 _)
  have : Nontrivial Γ((Over.mk (𝟙 (Spec (CommRingCat.of K)))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  exact (GlobalTheory.SecTwist.finrank_of_isSecBasis P.A P.L _ _ b hb).trans (one_pow _)

theorem exists_away_isDomain {R : Type} [CommRing R] [IsNoetherianRing R] (q : Ideal R) [q.IsPrime]
    [IsDomain (Localization.AtPrime q)] : ∃ g ∉ q, IsDomain (Localization.Away g) := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (RingHom.ker (algebraMap R (Localization.AtPrime q))))
  have h1 : ∀ a : s, ∃ m : q.primeCompl, (m : R) * a = 0 := fun a =>
    (IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q) (a : R)).1
      (by rw [← RingHom.mem_ker, ← hs]; exact Submodule.subset_span a.2)
  choose m hm using h1
  let g : q.primeCompl := ∏ a, m a
  have hg : ∀ a ∈ RingHom.ker (algebraMap R (Localization.AtPrime q)), (g : R) * a = 0 := by
    intro a ha
    rw [← hs] at ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨r, hr⟩ : (m ⟨a, ha⟩ : R) ∣ (g : R) := by
        obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ ⟨a, ha⟩)
        exact ⟨b, congrArg (fun x : q.primeCompl => (x : R)) hb⟩
      rw [hr, mul_right_comm, hm ⟨a, ha⟩, zero_mul]
    | zero => exact mul_zero _
    | add a b _ _ ha hb => rw [mul_add, ha, hb, add_zero]
    | smul r a _ ha => rw [smul_eq_mul, mul_left_comm, ha, mul_zero]
  refine ⟨g, g.2, ?_⟩
  have hu : IsUnit (algebraMap R (Localization.AtPrime q) g) := IsLocalization.map_units _ g
  let f : Localization.Away (g : R) →+* Localization.AtPrime q := IsLocalization.Away.lift (g : R) hu
  refine Function.Injective.isDomain f ((injective_iff_map_eq_zero f).2 fun x hx => ?_)
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (g : R) x
  have h2 : algebraMap R (Localization.AtPrime q) a = 0 := by
    rw [← IsLocalization.Away.lift_eq (S := Localization.Away (g : R)) (g : R) hu a, ← ha, map_mul]
    exact (congrArg (· * _) hx).trans (zero_mul _)
  have hu' : IsUnit (algebraMap R (Localization.Away (g : R)) g) := IsLocalization.Away.algebraMap_isUnit _
  have h3 : algebraMap R (Localization.Away (g : R)) a = 0 := by
    rw [← hu'.mul_right_eq_zero, ← map_mul, hg a h2, map_zero]
  rw [h3] at ha
  exact (hu'.pow n).mul_left_eq_zero.1 ha

theorem isTypeFn_fst {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) : IsTypeFn H Dw.p Dw.q (fun j => (e j).1) := by
  intro τ
  have hcard : Nat.card {i // (e i).1 = τ} = Dw.mult τ := by
    have e2 : {i // (e i).1 = τ} ≃ {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ} :=
      e.subtypeEquiv (fun _ => Iff.rfl)
    have e3 : {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ} ≃ Fin (Dw.mult τ) := Equiv.sigmaSubtype τ
    rw [Nat.card_congr (e2.trans e3), Nat.card_eq_fintype_card, Fintype.card_fin]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine hcard.trans ?_
    unfold Datum.mult
    rw [if_pos h]
  · refine hcard.trans ?_
    unfold Datum.mult
    rw [if_neg h]

theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'')
    (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem dualMap_comp_epsMul {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (a : S) :
    (dualMap ψ).comp (epsMul a) = (epsMul (ψ a)).comp (dualMap ψ) := by
  ext s <;> simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem isEigAt_pull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (ψ : S →+* T) (hψ : ∀ a, ψ (algebraMap c.F S a) = algebraMap c.F T a) (τ : E →+* ℂ)
    {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsEigAt c τ v) :
    IsEigAt c τ (spMap (dualMap ψ) ≫ v) := by
  intro a
  rw [Category.assoc, hv a, ← Category.assoc, spMap_spMap, dualMap_comp_epsMul, ← spMap_spMap,
    Category.assoc, hψ]

theorem smooth_of_chart {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {R : Type} [CommRing R] [Algebra c.F R] (j : Sp R ⟶ Xo.XF c)
    [IsOpenImmersion j] (hs : j ≫ pullback.snd _ _ = spMap (algebraMap c.F R)) : Algebra.Smooth c.F R := by
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have h : Smooth (spMap (algebraMap c.F R)) := by rw [← hs]; infer_instance
  have h' := (HasRingHomProperty.Spec_iff (P := @Smooth)).1 h
  exact RingHom.smooth_algebraMap.1 h'

theorem exists_integral_chart_frame : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ p : Xo.XF c, ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : Algebra c.F A) (j : Sp A ⟶ Xo.XF c) (y : FrPt Xo c A), IsOpenImmersion j ∧ p ∈ Set.range j ∧ j ≫ pullback.snd _ _ = spMap (algebraMap c.F A) ∧ Algebra.Smooth c.F A ∧ y.x = j ≫ pullback.fst _ _ := by
  intro hT E _ _ _ H Dw l Xo c z
  classical
  have hS := secBaseChange_of_secTwist hT
  let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (Dw.mult τ))).symm
  obtain ⟨R, _, _, jR, o, v, th, hft, hred, hjR, ⟨q, hq⟩, hs, ⟨m⟩, hv, hev, hth, -⟩ :=
    GlobalTheory.ModuliChart.exists_chart_eigenframe hS E H Dw l Xo c _ _ (isTypeFn_fst Dw e) z
  let x : Sp R ⟶ Xo.X := jR ≫ pullback.fst _ _
  have hb : TanBasis x (fun i => (v i).left ≫ m.cm.F) :=
    ((GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo R x o.t.G m.cm.F m.cart).2 _ v).1 hv
  let u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left) :=
    fun τ i => (v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F
  have heig : ∀ τ i, IsEigAt c τ (u τ i) := by
    intro τ i a
    have h := hev (e.symm ⟨τ, i⟩) a
    simp only [Equiv.apply_symm_apply] at h
    have h' : (v (e.symm ⟨τ, i⟩)).left ≫ (o.t.act.act a).left =
      spMap (epsMul (algebraMap c.F R (embK c τ a))) ≫ (v (e.symm ⟨τ, i⟩)).left := h
    show ((v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F) ≫ _ = _ ≫ (v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F
    rw [Category.assoc, ← m.act a, ← Category.assoc, h', Category.assoc]
  obtain ⟨s, hsn⟩ := GlobalTheory.SecTransport.exists_sec_nonzero E H Dw l Xo R x o.t m.toSABMap th hth
  have hsm : Algebra.Smooth c.F R := smooth_of_chart jR hs
  have hreg : IsRegularRing R := GlobalTheory.isRegularRing_of_smooth c.F R
  have hq' : q.asIdeal.IsPrime := q.isPrime
  have hdom : IsDomain (Localization.AtPrime q.asIdeal) := GlobalTheory.isDomain_of_isRegularLocalRing _
  obtain ⟨g, hg, hA⟩ := exists_away_isDomain q.asIdeal
  let A := Localization.Away g
  let ψ : R →+* A := algebraMap R A
  have hψ : ∀ a, ψ (algebraMap c.F R a) = algebraMap c.F A a := fun a =>
    (IsScalarTower.algebraMap_apply c.F R A a).symm
  have hopen : IsOpenImmersion (spMap ψ) := inferInstanceAs
    (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))))
  have hsA : (spMap ψ ≫ jR) ≫ pullback.snd _ _ = spMap (algebraMap c.F A) := by
    rw [Category.assoc, hs, spMap_spMap]
  let x' : Sp A ⟶ Xo.X := spMap ψ ≫ x
  let u' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber A) ⟶ Xo.univ.t.G.left) :=
    fun τ i => spMap (dualMap ψ) ≫ u τ i
  have hbA := GlobalTheory.Frames.tanBasis_baseChange E H Dw l Xo R A ψ x _ _ hb
  have htan : ∀ τ i, IsTanAt x' (u' τ i) := fun τ i => hbA.1 _
  have heig' : ∀ τ i, IsEigAt c τ (u' τ i) := fun τ i => isEigAt_pull ψ hψ τ (heig τ i)
  have hb' : TanBasis x' (fun j => u' (e j).1 (e j).2) := by
    have : (fun j => u' (e j).1 (e j).2) = fun i => spMap (dualMap ψ) ≫ (v i).left ≫ m.cm.F := by
      funext j
      show _ ≫ (v (e.symm (e j))).left ≫ m.cm.F = _
      rw [Equiv.symm_apply_apply]
    rw [this]; exact hbA
  have hbasis := (GlobalTheory.Frames.eigBasis_iff_tanBasis E H Dw l Xo c A x' u' _ e htan heig').2 hb'
  obtain ⟨s', hs', -⟩ := GlobalTheory.Frames.SecPull.existsUnique_secBC E H Dw l Xo R A ψ 1 x x' rfl s
  have hgen := GlobalTheory.FrameGenerator.secGen_of_secNZ_baseChange hS E H Dw l Xo R x s hsn A ψ x' s' rfl hs'
  have hx : x' ≫ Xo.s = sOf c A := by
    have h1 : x' ≫ Xo.s =
        ((spMap ψ ≫ jR) ≫ pullback.snd _ _) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
      simp only [x', x, Category.assoc]
      rw [pullback.condition]
    rw [h1, hsA, sOf, spMap_spMap]
  refine ⟨A, inferInstance, hA, inferInstance, spMap ψ ≫ jR, ⟨x', hx, u', htan, heig', hbasis, s', hgen⟩,
    inferInstance, ?_, hsA, smooth_of_chart _ hsA, (Category.assoc _ _ _).symm⟩
  have hr : q ∈ Set.range (PrimeSpectrum.comap ψ) := by
    rw [PrimeSpectrum.localization_away_comap_range A g]
    exact hg
  obtain ⟨q', hq''⟩ := hr
  refine ⟨q', ?_⟩
  exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg jR hq'').trans hq)

end GlobalTheory.LocalFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralSmoothChartFrameModuliStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_smooth_chart_frame_moduli : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ p : Xo.XF c, ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : Algebra c.F A) (j : Sp A ⟶ Xo.XF c) (y : FrPt Xo c A), IsOpenImmersion j ∧ p ∈ Set.range j ∧ j ≫ pullback.snd _ _ = spMap (algebraMap c.F A) ∧ Algebra.Smooth c.F A ∧ y.x = j ≫ pullback.fst _ _ := by
  first | exact @GlobalTheory.LocalFrame.exists_integral_chart_frame | exact GlobalTheory.LocalFrame.exists_integral_chart_frame | (intros; apply GlobalTheory.LocalFrame.exists_integral_chart_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralCongrWeakApproximationStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralCongrWeakApproximation
namespace GlobalTheory.WeakApprox

theorem exists_integral_congr (Ω : Type) [Field Ω] (ι : Type) [Finite ι]
    (v : ι → Valuation Ω (WithZero (Multiplicative ℤ)))
    (hgen : ∀ i, ∃ x, v i x =
      ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (hind : ∀ i j, i ≠ j → ¬ (v i).IsEquiv (v j)) (i₀ : ι) (a : Ω) (ha : v i₀ a ≤ 1) :
    ∃ a' : Ω, (∀ i, v i a' ≤ 1) ∧ v i₀ (a - a') < 1 := by
  classical
  haveI := Fintype.ofFinite ι

  have hn : ∀ i, ∃ n : ℤ, 1 ≤ n ∧
      v i a ≤ ((Multiplicative.ofAdd n : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro i
    rcases eq_or_ne (v i a) 0 with h | h
    · exact ⟨1, le_rfl, by simp [h]⟩
    · obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.mp h
      refine ⟨max 1 (Multiplicative.toAdd m), le_max_left _ _, ?_⟩
      rw [← hm, WithZero.coe_le_coe]
      exact le_max_right (1 : ℤ) (Multiplicative.toAdd m)
  choose n hn1 hn2 using hn

  obtain ⟨t, ht⟩ := ReciprocityTheory.ChartRestriction.G.Lift.exists_val_eq v hgen hind
    (fun i => if i = i₀ then -1 else n i)
  have ht0 : v i₀ t < 1 := by
    rw [ht i₀, if_pos rfl, ← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero,
      Multiplicative.ofAdd_lt]
    norm_num
  have h1t : v i₀ (1 + t) = 1 := by
    rw [(v i₀).map_add_eq_of_lt_left (by rwa [(v i₀).map_one]), (v i₀).map_one]
  have hne : 1 + t ≠ 0 := by
    intro h0
    rw [h0, (v i₀).map_zero] at h1t
    exact zero_ne_one h1t
  refine ⟨a / (1 + t), fun i => ?_, ?_⟩
  · rw [map_div₀]
    by_cases hi : i = i₀
    · subst hi
      rw [h1t, div_one]
      exact ha
    · have hti : v i t = ((Multiplicative.ofAdd (n i) : Multiplicative ℤ) :
          WithZero (Multiplicative ℤ)) := by
        rw [ht i, if_neg hi]
      have hlt : v i 1 < v i t := by
        rw [hti, (v i).map_one, ← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero,
          Multiplicative.ofAdd_lt]
        linarith [hn1 i]
      rw [(v i).map_add_eq_of_lt_right hlt, hti]
      exact div_le_one_of_le₀ (hn2 i) zero_le'
  · have hsub : a - a / (1 + t) = a * t / (1 + t) := by
      field_simp
      ring
    rw [hsub, map_div₀, h1t, div_one, map_mul]
    calc v i₀ a * v i₀ t ≤ 1 * v i₀ t := by gcongr
      _ = v i₀ t := one_mul _
      _ < 1 := ht0

end GlobalTheory.WeakApprox
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_congr_weak_approximation : ∀ (Ω : Type) [Field Ω] (ι : Type) [Finite ι] (v : ι → Valuation Ω (WithZero (Multiplicative ℤ))), (∀ i, ∃ x, v i x = ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) → (∀ i j, i ≠ j → ¬ (v i).IsEquiv (v j)) → ∀ (i₀ : ι) (a : Ω), v i₀ a ≤ 1 → ∃ a' : Ω, (∀ i, v i a' ≤ 1) ∧ v i₀ (a - a') < 1 := by
  first | exact @GlobalTheory.WeakApprox.exists_integral_congr | exact GlobalTheory.WeakApprox.exists_integral_congr | (intros; apply GlobalTheory.WeakApprox.exists_integral_congr <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.SubalgebraEqIntegralClosureOfValuesResidues
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.SubalgebraEqIntegralClosureOfValuesResidues
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj

namespace GlobalTheory.LocStructNak

variable {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A]

theorem dvd_of_vL_le [∀ ζ : Pts O A, IsDVRAt ζ] (c b : ↥(As O A))
    (h : ∀ ζ : Pts O A, vL ζ c ≤ vL ζ b) : c ∣ b := by
  have h0 : ∀ ζ : Pts O A, algebraMap ↥(As O A) (Loc ζ) b ∈
      Ideal.map (algebraMap ↥(As O A) (Loc ζ)) (Ideal.span {c}) := by
    intro ζ
    have h1 := h ζ
    rw [vL_eq_addVal, vL_eq_addVal, IsDiscreteValuationRing.addVal_le_iff_dvd] at h1
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    exact h1
  exact Ideal.mem_span_singleton.1 (Ideal.mem_of_localization_maximal (fun P hP => h0 ⟨P, hP⟩))


omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem exists_residue (C : Subalgebra O ↥(As O A)) (ζ : Pts O A) (b c d : ↥(As O A))
    (hc : c ∈ C) (hd : d ∈ C) (hd0 : d ∉ ζ.asIdeal) (h : d * b - c ∈ ζ.asIdeal) :
    ∃ c' ∈ C, b - c' ∈ ζ.asIdeal := by
  haveI : Algebra.IsIntegral ↥C ↥(As O A) := Algebra.IsIntegral.tower_top O
  haveI := ζ.isMaximal
  have hmax : (ζ.asIdeal.comap (algebraMap ↥C ↥(As O A))).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal ζ.asIdeal
  obtain ⟨y, z, hz, hyz⟩ := hmax.exists_inv (x := ⟨d, hd⟩) (by simpa [Ideal.mem_comap] using hd0)
  have hz' : (z : ↥(As O A)) ∈ ζ.asIdeal := hz
  have hyz' : (y : ↥(As O A)) * d + z = 1 := congrArg Subtype.val hyz
  refine ⟨y * c, C.mul_mem y.2 hc, ?_⟩
  have e : b - y * c = y * (d * b - c) + b * z := by
    linear_combination (-b) * hyz'
  rw [e]
  exact ζ.asIdeal.add_mem (ζ.asIdeal.mul_mem_left _ h) (ζ.asIdeal.mul_mem_left _ hz')

theorem exists_approx [∀ ζ : Pts O A, IsDVRAt ζ] [Finite (Pts O A)] (C : Subalgebra O ↥(As O A))
    (hval : ∀ n : Pts O A → ℕ, ∃ c ∈ C, ∀ ζ, vL ζ c = (n ζ : ℕ∞))
    (hres : ∀ (ζ : Pts O A) (b : ↥(As O A)), ∃ c ∈ C, b - c ∈ ζ.asIdeal)
    (n : Pts O A → ℕ) (b : ↥(As O A)) : ∃ c ∈ C, ∀ ζ, (n ζ : ℕ∞) ≤ vL ζ (b - c) := by
  classical
  letI := Fintype.ofFinite (Pts O A)
  obtain ⟨N, hN⟩ : ∃ N, ∑ ζ, n ζ = N := ⟨_, rfl⟩
  induction N generalizing n with
  | zero =>
    refine ⟨0, C.zero_mem, fun ζ => ?_⟩
    rw [(Finset.sum_eq_zero_iff.1 hN) ζ (Finset.mem_univ _)]
    simp
  | succ N ih =>
    obtain ⟨ζ₀, -, h0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := n)
      (by rw [hN]; omega)
    have hsum : ∑ ζ, Function.update n ζ₀ (n ζ₀ - 1) ζ = N := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ _)]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ζ₀), ← Finset.sdiff_singleton_eq_erase] at hN
      omega
    obtain ⟨c₁, hc₁, h₁⟩ := ih _ hsum
    obtain ⟨c, hc, hv⟩ := hval (Function.update n ζ₀ (n ζ₀ - 1))
    obtain ⟨b', hb'⟩ := dvd_of_vL_le c (b - c₁) (fun ζ => by rw [hv]; exact h₁ ζ)
    obtain ⟨c', hc', hm⟩ := hres ζ₀ b'
    refine ⟨c₁ + c * c', C.add_mem hc₁ (C.mul_mem hc hc'), fun ζ => ?_⟩
    have e : b - (c₁ + c * c') = c * (b' - c') := by linear_combination hb'
    rw [e, vL_mul, hv]
    by_cases hζ : ζ = ζ₀
    · subst hζ
      have h1 : 1 ≤ vL ζ (b' - c') := by
        rw [Order.one_le_iff_ne_zero, Ne, vL_eq_zero_iff]
        exact not_not.2 hm
      rw [Function.update_self]
      calc (n ζ : ℕ∞) = ((n ζ - 1 : ℕ) : ℕ∞) + 1 := by
            have : n ζ = (n ζ - 1) + 1 := by omega
            conv_lhs => rw [this]
            push_cast
            rfl
        _ ≤ _ := add_le_add le_rfl h1
    · rw [Function.update_of_ne hζ]
      exact le_self_add

theorem as_le_of_val_of_residue (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing A] [Algebra O A] (ϖ : O) (hU : IsUnif A ϖ) [∀ ζ : Pts O A, IsDVRAt ζ] [Finite (Pts O A)]
    [Module.Finite O ↥(As O A)] (C : Subalgebra O A) (hC : C ≤ As O A)
    (hval : ∀ n : Pts O A → ℕ, ∃ c ∈ C, ∀ ζ, ord ϖ ζ c = (((n ζ : ℕ) : ℤ) : WithTop ℤ))
    (hres : ∀ (ζ : Pts O A), ∀ b ∈ As O A, ∃ c ∈ C, ∃ d ∈ C,
      ord ϖ ζ d = 0 ∧ 0 < ord ϖ ζ (d * b - c)) : As O A ≤ C := by
  set C' : Subalgebra O ↥(As O A) := C.comap (As O A).val with hC'
  have hinj : Function.Injective (ENat.map (Nat.cast : ℕ → ℤ)) :=
    (ENat.strictMono_map_iff.2 Nat.strictMono_cast).injective
  have hzero : ∀ (ζ : Pts O A) (a : ↥(As O A)), ord ϖ ζ (a : A) = 0 ↔ a ∉ ζ.asIdeal := by
    intro ζ a
    rw [ord_of_mem ζ hU a.2, ← vL_eq_zero_iff]
    constructor
    · intro h
      exact hinj h
    · intro h
      change (vL ζ a).map (Nat.cast : ℕ → ℤ) = 0
      rw [h]
      rfl
  have hval' : ∀ n : Pts O A → ℕ, ∃ c ∈ C', ∀ ζ, vL ζ c = (n ζ : ℕ∞) := by
    intro n
    obtain ⟨c, hc, h⟩ := hval n
    refine ⟨⟨c, hC hc⟩, hc, fun ζ => hinj ?_⟩
    rw [← ord_of_mem ζ hU (hC hc), h ζ, ENat.map_natCast]
  have hres' : ∀ (ζ : Pts O A) (b : ↥(As O A)), ∃ c ∈ C', b - c ∈ ζ.asIdeal := by
    intro ζ b
    obtain ⟨c, hc, d, hd, hd0, h⟩ := hres ζ b b.2
    refine exists_residue C' ζ b ⟨c, hC hc⟩ ⟨d, hC hd⟩ hc hd ((hzero ζ ⟨d, hC hd⟩).1 hd0) ?_
    by_contra hn
    exact h.ne' ((hzero ζ _).2 hn)
  have key : (⊤ : Submodule O ↥(As O A)) ≤ Subalgebra.toSubmodule C' := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal O)
      Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson _) ?_
    intro b _
    obtain ⟨c, hc, h⟩ := exists_approx C' hval' hres' (ep ϖ) b
    obtain ⟨b', hb'⟩ := dvd_of_vL_le (algebraMap O ↥(As O A) ϖ) (b - c)
      (fun ζ => by rw [← coe_ep ζ hU]; exact h ζ)
    have e : b = c + ϖ • b' := by rw [Algebra.smul_def, ← hb']; ring
    rw [e]
    exact Submodule.add_mem_sup hc (Submodule.smul_mem_smul
      ((IsLocalRing.mem_maximalIdeal ϖ).2 hU.irreducible.not_isUnit) Submodule.mem_top)
  intro x hx
  exact key (Submodule.mem_top (x := (⟨x, hx⟩ : ↥(As O A))))

end GlobalTheory.LocStructNak
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.SubalgebraEqIntegralClosureOfValuesResiduesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subalgebra_eq_integralClosure_of_values_residues : ∀ (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A] (ϖ : O), IsUnif A ϖ → ∀ [∀ ζ : Pts O A, IsDVRAt ζ] [Finite (Pts O A)] [Module.Finite O ↥(As O A)] (C : Subalgebra O A), C ≤ As O A → (∀ n : Pts O A → ℕ, ∃ c ∈ C, ∀ ζ, ord ϖ ζ c = (((n ζ : ℕ) : ℤ) : WithTop ℤ)) → (∀ (ζ : Pts O A), ∀ b ∈ As O A, ∃ c ∈ C, ∃ d ∈ C, ord ϖ ζ d = 0 ∧ 0 < ord ϖ ζ (d * b - c)) → As O A ≤ C := by
  first | exact @GlobalTheory.LocStructNak.as_le_of_val_of_residue | exact GlobalTheory.LocStructNak.as_le_of_val_of_residue | (intros; apply GlobalTheory.LocStructNak.as_le_of_val_of_residue <;> assumption)
end
end
