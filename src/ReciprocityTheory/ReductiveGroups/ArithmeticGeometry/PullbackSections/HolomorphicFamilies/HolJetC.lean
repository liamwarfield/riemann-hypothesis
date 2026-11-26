module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EqZeroOfMulEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Taylor
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.TaylorMul
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.TM

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped ContDiff Topology

variable {g : ℕ}

theorem mD_local {f h : (Fin g → ℂ) → ℂ} (hfh : f =ᶠ[𝓝 0] h) (s : Multiset (Fin g → ℂ)) :
    mD f 0 s = mD h 0 s := by
  unfold mD lD
  rw [((hfh.iteratedFDeriv ℂ _).eq_of_nhds)]

theorem tay_local {f h : (Fin g → ℂ) → ℂ} (hfh : f =ᶠ[𝓝 0] h) (s : Multiset (Fin g → ℂ)) : tay f s = tay h s := by
  ext n
  show mD f 0 (dirs n + s) / fct n = mD h 0 (dirs n + s) / fct n
  rw [mD_local hfh]

theorem mD_add {f h : (Fin g → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (hh : ContDiffAt ℂ ω h 0)
    (s : Multiset (Fin g → ℂ)) : mD (f + h) 0 s = mD f 0 s + mD h 0 s := by
  unfold mD lD
  rw [iteratedFDeriv_add_apply (hf.of_le le_top) (hh.of_le le_top)]
  rfl

theorem tay_add {f h : (Fin g → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (hh : ContDiffAt ℂ ω h 0)
    (s : Multiset (Fin g → ℂ)) : tay (f + h) s = tay f s + tay h s := by
  ext n
  rw [map_add (f := _)]
  show mD (f + h) 0 (dirs n + s) / fct n = mD f 0 (dirs n + s) / fct n + mD h 0 (dirs n + s) / fct n
  rw [mD_add hf hh, add_div]

theorem mD_zero (θ : (Fin g → ℂ) → ℂ) : mD θ 0 0 = θ 0 := by
  have key : ∀ l : List (Fin g → ℂ), l = [] →
      iteratedFDeriv ℂ l.length θ 0 (fun i => l.get i) = θ 0 := by
    rintro l rfl
    simp
  exact key _ (Multiset.toList_eq_nil.2 rfl)

theorem mD_const (c : ℂ) (s : Multiset (Fin g → ℂ)) :
    mD (fun _ : Fin g → ℂ => c) 0 s = if s = 0 then c else 0 := by
  by_cases hs : s = 0
  · subst hs
    have key : ∀ l : List (Fin g → ℂ), l = [] →
        iteratedFDeriv ℂ l.length (fun _ : Fin g → ℂ => c) 0 (fun i => l.get i) = c := by
      rintro l rfl
      simp
    rw [if_pos rfl]
    exact key _ (Multiset.toList_eq_nil.2 rfl)
  · have hlen : s.toList.length ≠ 0 := by
      rw [Multiset.length_toList]
      exact fun h0 => hs (Multiset.card_eq_zero.1 h0)
    unfold mD lD
    rw [iteratedFDeriv_const_of_ne hlen, if_neg hs]
    rfl

theorem tay_const (c : ℂ) : tay (g := g) (fun _ => c) 0 = C c := by
  ext n
  rw [MvPowerSeries.coeff_C]
  show mD (fun _ => c) 0 (dirs n + 0) / fct n = _
  rw [add_zero, mD_const]
  by_cases hn : n = 0
  · subst hn
    simp [dirs, fct]
  · have hd : dirs n ≠ 0 := by
      intro h0
      apply hn
      have h1 : Finsupp.toMultiset n = 0 := by simpa [dirs] using h0
      simpa using congrArg Multiset.toFinsupp h1
    rw [if_neg hd, if_neg hn, zero_div]

theorem mD_cons_deriv {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) (v : Fin g → ℂ) (t : Multiset (Fin g → ℂ)) :
    mD θ 0 (v ::ₘ t) = mD (fun y => fderiv ℂ θ y v) 0 t := by
  have ht : ((t.toList : List (Fin g → ℂ)) : Multiset (Fin g → ℂ)) = t := Multiset.coe_toList t
  have hperm : (v ::ₘ t) = ((t.toList ++ [v] : List (Fin g → ℂ)) : Multiset (Fin g → ℂ)) := by
    conv_lhs => rw [← ht]
    rw [Multiset.cons_coe, Multiset.coe_eq_coe]
    exact (List.perm_append_singleton v t.toList).symm
  have hlen : (t.toList ++ [v]).length = t.toList.length + 1 := by simp
  rw [hperm, mD_coe hθ, lD_eq θ 0 (t.toList ++ [v]) hlen, iteratedFDeriv_succ_apply_right]
  have hf : ContDiffAt ℂ ω (fderiv ℂ θ) 0 := hθ.fderiv_right (by simp)
  have hcomp : (fun y => fderiv ℂ θ y v) = (ContinuousLinearMap.apply ℂ ℂ v) ∘ (fderiv ℂ θ) := rfl
  unfold mD lD
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_left _ hf le_top]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.apply_apply]
  congr 1
  · congr 1
    funext i
    simp only [Fin.init]
    exact List.getElem_append_left i.isLt
  · simp

theorem deriv_analytic {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) (v : Fin g → ℂ) :
    ContDiffAt ℂ ω (fun y => fderiv ℂ θ y v) 0 :=
  (hθ.fderiv_right (by simp)).clm_apply contDiffAt_const

theorem pderiv_tay {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) (j : Fin g) :
    MvPowerSeries.pderiv ((0 : Fin 1), j) (tay θ 0) =
      tay (fun y => fderiv ℂ θ y (Pi.single j 1)) 0 := by
  ext n
  rw [MvPowerSeries.coeff_pderiv]
  show mD θ 0 (dirs (n + Finsupp.single ((0 : Fin 1), j) 1) + 0) / fct (n + Finsupp.single ((0 : Fin 1), j) 1) * ((n ((0 : Fin 1), j) : ℂ) + 1) =
    mD (fun y => fderiv ℂ θ y (Pi.single j 1)) 0 (dirs n + 0) / fct n
  have hd : dirs (n + Finsupp.single ((0 : Fin 1), j) 1) = (Pi.single j 1 : Fin g → ℂ) ::ₘ dirs n := by
    unfold dirs
    rw [Finsupp.toMultiset_add, Finsupp.toMultiset_single, one_nsmul, Multiset.map_add (f := _),
      Multiset.map_singleton, add_comm, Multiset.singleton_add]
  have hf : fct (n + Finsupp.single ((0 : Fin 1), j) 1) = fct n * ((n ((0 : Fin 1), j) : ℂ) + 1) := by
    unfold fct
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ ((0 : Fin 1), j)),
      ← Finset.mul_prod_erase Finset.univ (fun p => ((n p).factorial : ℂ)) (Finset.mem_univ ((0 : Fin 1), j))]
    have hrest : ∏ x ∈ Finset.univ.erase ((0 : Fin 1), j), (((n + Finsupp.single ((0 : Fin 1), j) 1 : Fin 1 × Fin g →₀ ℕ) x).factorial : ℂ) =
        ∏ x ∈ Finset.univ.erase ((0 : Fin 1), j), ((n x).factorial : ℂ) := by
      refine Finset.prod_congr rfl fun x hx => ?_
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hx), add_zero]
    rw [hrest, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
    push_cast
    ring
  have hne : ((n ((0 : Fin 1), j) : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero _
  rw [add_zero, add_zero, hd, mD_cons_deriv hθ, hf, ← div_div, div_mul_cancel₀ _ hne]

theorem deriv_mul_ev {f h : (Fin g → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (hh : ContDiffAt ℂ ω h 0) (v : Fin g → ℂ) :
    (fun y => fderiv ℂ (f * h) y v) =ᶠ[𝓝 0]
      (fun y => fderiv ℂ f y v) * h + f * (fun y => fderiv ℂ h y v) := by
  filter_upwards [hf.eventually (by simp), hh.eventually (by simp)] with y hy1 hy2
  rw [fderiv_mul (hy1.differentiableAt (by simp)) (hy2.differentiableAt (by simp))]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    Pi.add_apply, Pi.mul_apply]
  ring

theorem taylor_mul_coeff_low_degree (N : ℕ) : ∀ (f h : (Fin g → ℂ) → ℂ), ContDiffAt ℂ ω f 0 → ContDiffAt ℂ ω h 0 →
    ∀ n : Fin 1 × Fin g →₀ ℕ, n.degree < N → coeff n (tay (f * h) 0) = coeff n (tay f 0 * tay h 0) := by
  induction N with
  | zero =>
    intro f h _ _ n hn
    exact absurd hn (Nat.not_lt_zero _)
  | succ N ih =>
    intro f h hf hh n hn
    by_cases h0 : n = 0
    · subst h0
      simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul]
      simp only [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
      show mD (f * h) 0 (dirs 0 + 0) / fct 0 = (mD f 0 (dirs 0 + 0) / fct 0) * (mD h 0 (dirs 0 + 0) / fct 0)
      simp [dirs, fct, mD_zero]
    · obtain ⟨x, hx⟩ : ∃ x, n x ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact h0 (Finsupp.ext hc)
      obtain ⟨i, j⟩ := x
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      obtain ⟨m, hm⟩ : ∃ m, m = n - Finsupp.single ((0 : Fin 1), j) 1 := ⟨_, rfl⟩
      have hnm : n = m + Finsupp.single ((0 : Fin 1), j) 1 := by
        rw [hm]
        exact (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hx))).symm
      have hmdeg : m.degree < N := by
        have h1 : n.degree = m.degree + 1 := by
          rw [hnm, map_add (f := _), Finsupp.degree_single]
        omega
      have key : ∀ F : MvPowerSeries (Fin 1 × Fin g) ℂ,
          coeff m (MvPowerSeries.pderiv ((0 : Fin 1), j) F) =
            coeff n F * ((m ((0 : Fin 1), j) : ℂ) + 1) := fun F => by
        rw [MvPowerSeries.coeff_pderiv, ← hnm]
      have hc : ((m ((0 : Fin 1), j) : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero _
      apply mul_right_cancel₀ hc
      rw [← key, ← key]
      have hfh : ContDiffAt ℂ ω (f * h) 0 := hf.mul hh
      have hf' := deriv_analytic hf (Pi.single j 1)
      have hh' := deriv_analytic hh (Pi.single j 1)
      rw [pderiv_tay hfh, tay_local (deriv_mul_ev hf hh (Pi.single j 1)), tay_add (f := (fun y => fderiv ℂ f y (Pi.single j 1)) * h)
        (h := f * fun y => fderiv ℂ h y (Pi.single j 1)) (hf'.mul hh) (hf.mul hh'),
        map_add, Derivation.leibniz, pderiv_tay hf, pderiv_tay hh, ih _ _ hf' hh m hmdeg,
        ih _ _ hf hh' m hmdeg, smul_eq_mul, smul_eq_mul, map_add, mul_comm (tay h 0)]
      ring

theorem taylor_multiplication : TaylorMulSt := by
  refine ⟨fun g f h hf hh => ⟨?_, tay_add hf hh 0⟩, fun g c => tay_const c,
    fun g f h hfh => tay_local hfh 0⟩
  ext n
  exact taylor_mul_coeff_low_degree (n.degree + 1) f h hf hh n (Nat.lt_succ_self _)

end ReciprocityTheory.ChartRestriction.G.PullbackSections.TM
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetB
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff

section JetOf

variable {g : ℕ}

def jetOf (m : ℕ) (θ : (Fin g → ℂ) → ℂ) : Jet ℂ (Fin 1 × Fin g) m := psJet m (tay θ 0)

theorem psJet_add' {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (f h : MvPowerSeries ι ℂ) :
    psJet m (f + h) = psJet m f + psJet m h := by
  simp only [psJet, psTrunc, map_add (f := _), Finset.sum_add_distrib]

theorem jetOf_mul (m : ℕ) {f h : (Fin g → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (hh : ContDiffAt ℂ ω h 0) :
    jetOf m (f * h) = jetOf m f * jetOf m h := by
  rw [jetOf, (TM.taylor_multiplication.1 g f h hf hh).1, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psJet_mul]
  rfl

theorem jetOf_add (m : ℕ) {f h : (Fin g → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (hh : ContDiffAt ℂ ω h 0) :
    jetOf m (f + h) = jetOf m f + jetOf m h := by
  rw [jetOf, (TM.taylor_multiplication.1 g f h hf hh).2, psJet_add']
  rfl

theorem jetOf_const (m : ℕ) (c : ℂ) :
    jetOf m (fun _ : Fin g → ℂ => c) = algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m) c := by
  rw [jetOf, TM.taylor_multiplication.2.1 g c]
  have h : (MvPowerSeries.C c : MvPowerSeries (Fin 1 × Fin g) ℂ) =
      ((MvPolynomial.C c : MvPolynomial (Fin 1 × Fin g) ℂ) : MvPowerSeries (Fin 1 × Fin g) ℂ) := by simp
  rw [h, psJet, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_eq, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.mk_trunc_coe, ← MvPolynomial.algebraMap_eq]
  rfl

theorem jetOf_congr (m : ℕ) {f h : (Fin g → ℂ) → ℂ} (hfh : f =ᶠ[nhds 0] h) : jetOf m f = jetOf m h := by
  rw [jetOf, jetOf, TM.taylor_multiplication.2.2 g f h hfh]

theorem jetAug_psJet {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (f : MvPowerSeries ι ℂ) :
    (jetAug : Jet ℂ ι m →ₐ[ℂ] ℂ) (psJet m f) = MvPowerSeries.constantCoeff f := by
  rw [psJet, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_eq]
  show MvPolynomial.aeval (fun _ => (0 : ℂ)) _ = _
  rw [MvPolynomial.aeval_zero', Algebra.algebraMap_self, RingHom.id_apply, MvPolynomial.constantCoeff_eq,
    MvPowerSeries.coeff_truncTotal _ (by simp), MvPowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem jetAug_jetOf (m : ℕ) (θ : (Fin g → ℂ) → ℂ) : (jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) (jetOf m θ) = θ 0 := by
  rw [jetOf, jetAug_psJet, constantCoeff_tay]
  show lD θ 0 (Multiset.toList 0) = θ 0
  rw [Multiset.toList_zero]
  exact iteratedFDeriv_zero_apply _

theorem jetTrunc_psJet {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (f : MvPowerSeries ι ℂ) :
    (jetTrunc : Jet ℂ ι (m + 1) →ₐ[ℂ] Jet ℂ ι m) (psJet (m + 1) f) = psJet m f := by
  rw [psJet, psJet]
  show Ideal.Quotient.mk _ (psTrunc (m + 1) f) = Ideal.Quotient.mk _ (psTrunc m f)
  rw [Ideal.Quotient.eq]
  exact Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.psTrunc_succ_sub f

theorem jetTrunc_jetOf (m : ℕ) (θ : (Fin g → ℂ) → ℂ) :
    (jetTrunc : Jet ℂ (Fin 1 × Fin g) (m + 1) →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) (jetOf (m + 1) θ) = jetOf m θ :=
  jetTrunc_psJet m _

theorem ne_zero_of_isUnit_jetOf (m : ℕ) {θ : (Fin g → ℂ) → ℂ} (h : IsUnit (jetOf m θ)) : θ 0 ≠ 0 := by
  have := h.map (jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ)
  rw [jetAug_jetOf] at this
  exact this.ne_zero

end JetOf

section HolJet

variable {g : ℕ} {Y : Scheme.{0}}

abbrev cpt : Sp ℂ := IsLocalRing.closedPoint (CommRingCat.of ℂ)

def IsHolFam (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) : Prop :=
  ∀ (U : Y.Opens) (f : Γ(Y, U)), IsOpen {z | ⊤ ≤ e z ⁻¹ᵁ U} ∧
    DifferentiableOn ℂ (fun z => valAt' (e z) U f) {z | ⊤ ≤ e z ⁻¹ᵁ U}

variable (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e)

set_option backward.isDefEq.respectTransparency false in
theorem top_le_of_mem {x : Sp ℂ ⟶ Y} {U : Y.Opens} (h : x cpt ∈ U) : ⊤ ≤ x ⁻¹ᵁ U :=
  (Scheme.preimage_eq_top_of_closedPoint_mem x h).ge

include hol in
theorem eventually_mem {U : Y.Opens} (hU : e 0 cpt ∈ U) : ∀ᶠ z in nhds 0, ⊤ ≤ e z ⁻¹ᵁ U :=
  (hol U 0).1.mem_nhds (top_le_of_mem hU)

include hol in
theorem contDiffAt_val {U : Y.Opens} (hU : e 0 cpt ∈ U) (f : Γ(Y, U)) :
    ContDiffAt ℂ ω (fun z => valAt' (e z) U f) 0 :=
  (analyticAt_val e hol U f 0 (top_le_of_mem hU)).contDiffAt

def jetRingHom (m : ℕ) (U : Y.Opens) (hU : e 0 cpt ∈ U) : Γ(Y, U) →+* Jet ℂ (Fin 1 × Fin g) m where
  toFun f := jetOf m (fun z => valAt' (e z) U f)
  map_one' := by
    rw [← map_one (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m)), ← jetOf_const]
    refine jetOf_congr m ((eventually_mem e hol hU).mono fun z hz => ?_)
    exact valAt'_one _ _ hz
  map_mul' f h := by
    rw [← jetOf_mul m (contDiffAt_val e hol hU f) (contDiffAt_val e hol hU h)]
    congr 1
    funext z
    exact valAt'_mul _ _ f h
  map_zero' := by
    rw [← map_zero (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m)), ← jetOf_const]
    congr 1
    funext z
    have := valAt'_sub (e z) U 0 0
    rw [sub_self, sub_self] at this
    exact this
  map_add' f h := by
    rw [← jetOf_add m (contDiffAt_val e hol hU f) (contDiffAt_val e hol hU h)]
    congr 1
    funext z
    exact valAt'_add _ _ f h

def jetψ (m : ℕ) (U : Y.Opens) (hU : e 0 cpt ∈ U) :
    Γ(Y, U) ⟶ CommRingCat.of (Jet ℂ (Fin 1 × Fin g) m) :=
  CommRingCat.ofHom (jetRingHom e hol m U hU)

theorem jetψ_apply (m : ℕ) (U : Y.Opens) (hU : e 0 cpt ∈ U) (f : Γ(Y, U)) :
    jetψ e hol m U hU f = jetOf m (fun z => valAt' (e z) U f) := rfl

theorem jetψ_res (m : ℕ) (U V : Y.Opens) (hU : e 0 cpt ∈ U) (hV : e 0 cpt ∈ V) (h : V ≤ U) :
    Y.presheaf.map (homOfLE h).op ≫ jetψ e hol m V hV = jetψ e hol m U hU := by
  ext f
  rw [CommRingCat.comp_apply, jetψ_apply, jetψ_apply]
  refine jetOf_congr m ((eventually_mem e hol hV).mono fun z hz => ?_)
  exact valAt'_res _ h hz f

theorem jetψ_loc (m : ℕ) (U : Y.Opens) (hU : e 0 cpt ∈ U) (f : Γ(Y, U)) (hf : IsUnit (jetψ e hol m U hU f)) :
    e 0 cpt ∈ Y.basicOpen f := by
  rw [jetψ_apply] at hf
  exact (valAt'_ne_zero_iff (e 0) U (top_le_of_mem hU) f cpt).mp (ne_zero_of_isUnit_jetOf m hf)

def jetPt (m : ℕ) : Sp (Jet ℂ (Fin 1 × Fin g) m) ⟶ Y :=
  nbhdPt (y₀ := e 0 cpt) (jetψ e hol m) (jetψ_res e hol m)

theorem jetPt_closedPoint (m : ℕ) : jetPt e hol m (IsLocalRing.closedPoint _) = e 0 cpt :=
  nbhdPt_closedPoint _ _ (jetψ_loc e hol m)

theorem jetPt_appLE (m : ℕ) (U : Y.Opens) (hU : e 0 cpt ∈ U) (h : ⊤ ≤ jetPt e hol m ⁻¹ᵁ U) :
    (jetPt e hol m).appLE U ⊤ h = jetψ e hol m U hU ≫ (Scheme.ΓSpecIso _).inv :=
  nbhdPt_appLE _ _ (jetψ_loc e hol m) U hU h

theorem jetPt_trunc (m : ℕ) :
    spMap ((jetTrunc : Jet ℂ (Fin 1 × Fin g) (m + 1) →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) : _ →+* _) ≫
      jetPt e hol (m + 1) = jetPt e hol m := by
  unfold jetPt
  rw [spMap, spec_comp_nbhdPt]
  refine nbhdPt_congr _ _ fun U hU => ?_
  ext f
  rw [CommRingCat.comp_apply, jetψ_apply, jetψ_apply]
  exact jetTrunc_jetOf m _

end HolJet

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff

variable {g : ℕ} {Y Y' : Scheme.{0}}

theorem valAt'_comp (x : Sp ℂ ⟶ Y) (φ : Y ⟶ Y') (U : Y'.Opens) (f : Γ(Y', U)) :
    valAt' x (φ ⁻¹ᵁ U) (φ.app U f) = valAt' (x ≫ φ) U f := by
  unfold valAt'
  have e : x ⁻¹ᵁ φ ⁻¹ᵁ U = (x ≫ φ) ⁻¹ᵁ U := rfl
  by_cases h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U
  · rw [dite_eq_left (e ▸ h), dite_eq_left h]
    unfold valAt
    rw [Scheme.Hom.comp_appLE]
    rfl
  · rw [dite_eq_right (e ▸ h), dite_eq_right h]

theorem isHolFam_comp (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (φ : Y ⟶ Y') :
    IsHolFam (fun z => e z ≫ φ) := by
  intro U f
  have := hol (φ ⁻¹ᵁ U) (φ.app U f)
  simp only [valAt'_comp] at this
  exact this


set_option backward.isDefEq.respectTransparency false in
theorem jetPt_comp (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (φ : Y ⟶ Y')
    (e' : (Fin g → ℂ) → (Sp ℂ ⟶ Y')) (hol' : IsHolFam e') (he : ∀ z, e z ≫ φ = e' z) (m : ℕ) :
    jetPt e hol m ≫ φ = jetPt e' hol' m := by
  have hpt : (jetPt e hol m ≫ φ) (IsLocalRing.closedPoint _) = jetPt e' hol' m (IsLocalRing.closedPoint _) := by
    rw [Scheme.Hom.comp_apply, jetPt_closedPoint, jetPt_closedPoint, ← he 0, Scheme.Hom.comp_apply]
  refine hom_ext_of_local hpt fun U h₁ h₂ => ?_
  have hU : e' 0 cpt ∈ U := by
    have : jetPt e' hol' m (IsLocalRing.closedPoint _) ∈ U :=
      h₂ (show IsLocalRing.closedPoint _ ∈ (⊤ : (Spec _).Opens) from trivial)
    rwa [jetPt_closedPoint] at this
  have hU' : φ (e 0 cpt) ∈ U := by
    rw [← Scheme.Hom.comp_apply, he 0]; exact hU
  have k := nbhdPt_comp_appLE (y₀ := e 0 cpt) φ (jetψ e hol m) (jetψ_res e hol m) (jetψ_loc e hol m) U hU' h₁
  refine (k : (jetPt e hol m ≫ φ).appLE U ⊤ h₁ = _).trans ?_
  rw [jetPt_appLE e' hol' m U hU h₂, ← Category.assoc]
  congr 1
  ext f
  rw [CommRingCat.comp_apply, jetψ_apply, jetψ_apply]
  congr 1
  funext z
  rw [valAt'_comp, he z]


set_option backward.isDefEq.respectTransparency false in
theorem jetPt_aug (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (m : ℕ) :
    spMap ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin g) m →+* ℂ) ≫ jetPt e hol m = e 0 := by
  unfold jetPt
  rw [spMap, spec_comp_nbhdPt]
  have hloc : ∀ (U : Y.Opens) (hU : e 0 cpt ∈ U) (f : Γ(Y, U)),
      IsUnit ((jetψ e hol m U hU ≫ CommRingCat.ofHom
        ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin g) m →+* ℂ)) f) →
        e 0 cpt ∈ Y.basicOpen f := by
    intro U hU f hf
    rw [CommRingCat.comp_apply, jetψ_apply] at hf
    change IsUnit ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) _) at hf
    rw [jetAug_jetOf] at hf
    exact (valAt'_ne_zero_iff (e 0) U (top_le_of_mem hU) f cpt).mp hf.ne_zero
  have hres : ∀ (U V : Y.Opens) (hU : e 0 cpt ∈ U) (hV : e 0 cpt ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ (jetψ e hol m V hV ≫ CommRingCat.ofHom
        ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin g) m →+* ℂ)) =
      jetψ e hol m U hU ≫ CommRingCat.ofHom
        ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin g) m →+* ℂ) :=
    fun U V hU hV h => by rw [← Category.assoc, jetψ_res]
  have hpt := nbhdPt_closedPoint _ hres hloc
  refine hom_ext_of_local (hpt.trans rfl) fun U h₁ h₂ => ?_
  have hU : e 0 cpt ∈ U := by
    have : nbhdPt _ hres (IsLocalRing.closedPoint _) ∈ U :=
      h₁ (show IsLocalRing.closedPoint _ ∈ (⊤ : (Spec _).Opens) from trivial)
    rwa [hpt] at this
  rw [nbhdPt_appLE _ hres hloc U hU h₁, Iso.comp_inv_eq]
  ext f
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, jetψ_apply]
  change (jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) _ = _
  rw [jetAug_jetOf, valAt'_of _ _ h₂]
  rfl

end ReciprocityTheory.ChartRestriction.G.PullbackSections
