module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperQuotAdd
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeTail
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsVeryAmpleZFinite

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperSubquotFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace SnapperSubquotientFinite

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem chartRing_fg (I : Chart x) : (chartRing S x I).FG := by
  classical
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  refine ⟨Finset.univ.image (fun l => x l / x i) ∪ I.1.image (fun j => x i / x j), ?_⟩
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff]
    intro a ha
    simp only [Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_union,
      Set.mem_range, Set.mem_image, Finset.mem_coe] at ha
    rcases ha with ⟨l, rfl⟩ | ⟨j, hj, rfl⟩
    · exact ⟨X l, X i, 1, X_mem_monos hi, isHomogeneous_X S l, isHomogeneous_X S i, by simp⟩
    · exact ⟨X i, X j, 1, X_mem_monos hj, isHomogeneous_X S i, isHomogeneous_X S j, by simp⟩
  · rintro a ⟨f, s, e, hs, hf, hse, rfl⟩
    set T := Algebra.adjoin S ((Finset.univ.image (fun l => x l / x i) ∪
      I.1.image (fun j => x i / x j) : Finset Ω) : Set Ω) with hT
    have h1 : aeval x f / x i ^ e ∈ T := by
      have hc : aeval x f / x i ^ e ∈ chartRing S x (singleChart hxi) :=
        ⟨f, X i ^ e, e, pow_mem (X_mem_monos (Finset.mem_singleton_self i)) e, hf,
          isHomogeneous_X_pow _ _, by simp⟩
      refine Algebra.adjoin_mono ?_ (mem_ampleBase_of_mem_chartRing hxi hc)
      rintro _ ⟨l, rfl⟩
      simp
    have h2 : ∀ s ∈ monos (S := S) I.1, ∃ e', s.IsHomogeneous e' ∧ x i ^ e' / aeval x s ∈ T := by
      intro s hs
      induction hs using Submonoid.closure_induction with
      | mem a ha =>
        obtain ⟨j, hj, rfl⟩ := ha
        refine ⟨1, isHomogeneous_X S j, ?_⟩
        rw [aeval_X, pow_one]
        exact Algebra.subset_adjoin (by simp only [Finset.coe_union, Finset.coe_image, Set.mem_union,
          Set.mem_image, Finset.mem_coe]; exact Or.inr ⟨j, hj, rfl⟩)
      | one => exact ⟨0, isHomogeneous_one _ _, by simp⟩
      | mul a b _ _ ha hb =>
        obtain ⟨ea, ha1, ha2⟩ := ha
        obtain ⟨eb, hb1, hb2⟩ := hb
        refine ⟨ea + eb, ha1.mul hb1, ?_⟩
        rw [map_mul, pow_add, mul_div_mul_comm]
        exact T.mul_mem ha2 hb2
    obtain ⟨e', hse', h2'⟩ := h2 s hs
    have hs0 : aeval x s ≠ 0 := eval_ne_zero_of_mem_monos I hs
    have hs0' : s ≠ 0 := by rintro rfl; exact hs0 (map_zero _)
    obtain rfl : e = e' := hse.inj_right hse' hs0'
    have hxe : x i ^ e ≠ 0 := pow_ne_zero _ hxi
    have : aeval x f / aeval x s = (aeval x f / x i ^ e) * (x i ^ e / aeval x s) := by
      field_simp
    rw [this]
    exact T.mul_mem h1 h2'

theorem isNoetherianRing_chart [IsNoetherianRing S] (I : Chart x) : IsNoetherianRing (chartRing S x I) := by
  have : Algebra.FiniteType S (chartRing S x I) := ⟨(Subalgebra.fg_top _).mpr (chartRing_fg I)⟩
  exact Algebra.FiniteType.isNoetherianRing S _

end SnapperSubquotientFinite


set_option maxHeartbeats 1000000 in
open SnapperQuotientAdditivity SnapperSubquotientFinite in
theorem SnapperSubquotFinite.proof (hfin : SnapperFinite.Statement.{u, v, w}) :
    SnapperSubquotFinite.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x E _ _ _ _ F F₁ F₂ hfg h1 h21 i
  have hfg1 : ∀ I, (F₁.sub I).FG := fun I => by
    have := isNoetherianRing_chart (S := k) I
    exact (hfg I).of_le (h1 I)
  have hfg2 : ∀ I, (F₂.sub I).FG := fun I => by
    have := isNoetherianRing_chart (S := k) I
    exact (hfg I).of_le ((h21 I).trans (h1 I))

  have hH : ∀ (G : SubFamily k x E), (∀ I, (G.sub I).FG) → ∀ j,
      FiniteDimensional k (Cech.Hdeg (fun I : Chart x => (G.sub I : Type v)) (fun _ => ⊤)
        G.toSubSystem.res j) := by
    intro G hG j
    have h := hfin k Ω N x E G hG 0 Fin.elim0 Fin.elim0 0 j
    change FiniteDimensional k ((G.toSubSystem.twist (twistSys k x 0)).H j) at h
    rw [SubSystem.twist_twistSys_zero] at h
    have : FiniteDimensional k (Cech.H (fun I : Chart x => (G.sub I : Type v)) G.toSubSystem.res j) := h
    exact (hdegTopEquiv _ _ j).symm.finiteDimensional
  have hdd := CechDSq.proof (N + 1) (support x) k (fun I : Chart x => (F₁.sub I : Type v))
    F₁.toSubSystem.res (fun _ _ _ _ _ => LinearMap.ext fun _ => rfl)
  let φ : ∀ I : Chart x, F₂.sub I →ₗ[k] F₁.sub I := fun I =>
    { toFun := fun y => ⟨y, h21 I y.2⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let ψ : ∀ I : Chart x, F₁.sub I →ₗ[k] F₁.sub I ⧸ SubSystem.quotSub F₁.toSubSystem F₂.toSubSystem I :=
    fun I => (SubSystem.quotSub F₁.toSubSystem F₂.toSubSystem I).mkQ
  have L := Cech.longExact (R := k) (U := support x)
    (A := fun I : Chart x => (F₂.sub I : Type v)) (B := fun I : Chart x => (F₁.sub I : Type v))
    (C := fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁.toSubSystem F₂.toSubSystem I)
    (ρA := F₂.toSubSystem.res) (ρB := F₁.toSubSystem.res)
    (ρC := SubSystem.quotRes F₁.toSubSystem F₂.toSubSystem)
    (dA := fun _ => ⊤) (dB := fun _ => ⊤) (dC := fun _ => ⊤) (φ := φ) (ψ := ψ)
  have L1 := L (fun _ _ _ _ => rfl)
  have L2 := L1 (fun _ _ _ _ => rfl)
  have L3 := L2 (fun _ _ _ => Submodule.mem_top) (fun _ _ _ => Submodule.mem_top)
  have L4 := L3 (fun I a b hab => Subtype.ext (congrArg (fun z : F₁.sub I => (z : E)) hab))
  have L5 := L4 (fun I y => (Submodule.Quotient.mk_eq_zero _).2 y.2)
  have L6 := L5 (fun I m _ hm => ⟨⟨m, (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁.toSubSystem F₂.toSubSystem I)).1 hm⟩, Submodule.mem_top, rfl⟩)
  have L7 := L6 (fun I z _ => (Submodule.Quotient.mk_surjective _ z).imp fun y hy => ⟨Submodule.mem_top, hy⟩)
  have L8 := L7 (fun _ _ _ _ _ => Submodule.mem_top)
  have liftZP_newton := L8 hdd
  obtain ⟨δ, hgδ, -⟩ := (liftZP_newton.2 i).2
  have := hH F₁ hfg1 i
  have := hH F₂ hfg2 (i + 1)
  have hC := Module.Finite.of_exact (f := Cech.mapHdeg _ _ ψ _ _ i) (g := δ.rangeRestrict)
    (LinearMap.exact_iff.2 (by rw [LinearMap.ker_rangeRestrict]; exact LinearMap.exact_iff.1 hgδ))
    δ.surjective_rangeRestrict
  exact (hdegTopEquiv _ _ i).finiteDimensional

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHFreeIndep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

namespace KHFreeIndep

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem cellMon_monomial {I : ∀ k, Finset (ι k)} {t : MRingOver S ι} (ht : t ∈ KH.cellMon S I) :
    ∃ e, t = monomial e 1 := by
  unfold KH.cellMon at ht
  induction ht using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨k, i, -, rfl⟩ := hx
    exact ⟨Finsupp.single ⟨k, i⟩ 1, rfl⟩
  | one => exact ⟨0, by rw [monomial_zero', C_1]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨e, rfl⟩ := hx
    obtain ⟨e', rfl⟩ := hy
    exact ⟨e + e', by rw [monomial_mul, mul_one]⟩


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem eq_zero_of_monomial_mul (e : (Σ k, ι k) →₀ ℕ) {p : MRingOver S ι}
    (h : monomial e (1 : S) * p = 0) : p = 0 := by
  ext d
  have := congrArg (AddMonoidAlgebra.coeff · (e + d)) h
  rw [coeff_monomial_mul, one_mul] at this
  simpa using this


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem eq_zero_of_mk_eq_zero {I : ∀ k, Finset (ι k)} {p : MRingOver S ι}
    (h : LocalizedModule.mk (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι)) p) (1 : KH.cellMon S I) = 0) :
    p = 0 := by
  rw [← LocalizedModule.zero_mk (1 : KH.cellMon S I), LocalizedModule.mk_eq] at h
  obtain ⟨t, ht⟩ := h
  rw [one_smul, one_smul, smul_zero, Submonoid.smul_def, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot] at ht
  obtain ⟨e, he⟩ := cellMon_monomial t.2
  rw [he] at ht
  exact eq_zero_of_monomial_mul e ht

theorem shift_injective (u : (Σ k, ι k) →₀ ℕ) {b b' : (Σ k, ι k) → ℤ} (hb : negExp b ≤ u)
    (hb' : negExp b' ≤ u) (h : posExp b + u - negExp b = posExp b' + u - negExp b') : b = b' := by
  funext p
  have h1 := DFunLike.congr_fun h p
  have h2 := Finsupp.le_def.1 hb p
  have h3 := Finsupp.le_def.1 hb' p
  simp only [posExp, negExp, Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply,
    Finsupp.coe_equivFunOnFinite_symm] at h1 h2 h3
  omega

theorem smul_smul_monoFrac (I : ∀ k, Finset (ι k)) (u : (Σ k, ι k) →₀ ℕ) (r : S) (b : (Σ k, ι k) → ℤ)
    (hI : ∀ k, negSet b k ⊆ I k) (hb : negExp b ≤ u) :
    (monomial u (1 : S) : MRingOver S ι) • (r • monoFrac S I b) =
      LocalizedModule.mk (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι))
        (monomial (posExp b + u - negExp b) r)) (1 : KH.cellMon S I) := by
  rw [monoFrac, dif_pos hI, LocalizedModule.smul'_mk, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  rw [one_smul, one_smul, one_smul, Submonoid.smul_def]
  rw [← Ideal.Quotient.mk_eq_mk, ← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul,
    ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul]
  congr 1
  simp only [smul_eq_mul, smul_monomial, monomial_mul, mul_one, one_mul]
  congr 1
  rw [add_tsub_cancel_of_le (le_add_left hb), add_comm]

theorem eq_zero_of_sum_smul_monoFrac (I : ∀ k, Finset (ι k)) (A : Finset ((Σ k, ι k) → ℤ))
    (g : ((Σ k, ι k) → ℤ) → S) (hg : ∀ b ∈ A, ¬ (∀ k, negSet b k ⊆ I k) → g b = 0)
    (h : ∑ b ∈ A, g b • monoFrac S I b = 0) : ∀ a ∈ A, g a = 0 := by
  classical
  set u : (Σ k, ι k) →₀ ℕ := ∑ b ∈ A.filter (fun b => ∀ k, negSet b k ⊆ I k), negExp b with hu
  set c : ((Σ k, ι k) → ℤ) → ((Σ k, ι k) →₀ ℕ) := fun b => posExp b + u - negExp b with hc
  have hle : ∀ b ∈ A, (∀ k, negSet b k ⊆ I k) → negExp b ≤ u := fun b hb hI =>
    Finset.single_le_sum (f := negExp) (fun _ _ => zero_le) (Finset.mem_filter.2 ⟨hb, hI⟩)
  have hterm : ∀ b ∈ A, (monomial u (1 : S) : MRingOver S ι) • (g b • monoFrac S I b) =
      LocalizedModule.mk (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι)) (monomial (c b) (g b)))
        (1 : KH.cellMon S I) := by
    intro b hb
    by_cases hI : ∀ k, negSet b k ⊆ I k
    · exact smul_smul_monoFrac I u (g b) b hI (hle b hb hI)
    · rw [hg b hb hI, zero_smul, smul_zero, monomial_zero, map_zero, LocalizedModule.zero_mk]
  have key : ∑ b ∈ A, monomial (c b) (g b) = 0 := by
    apply eq_zero_of_mk_eq_zero (I := I)
    have e1 : LocalizedModule.mk (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι))
        (∑ b ∈ A, monomial (c b) (g b))) (1 : KH.cellMon S I) =
        ∑ b ∈ A, LocalizedModule.mk (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι))
          (monomial (c b) (g b))) (1 : KH.cellMon S I) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact map_sum (LocalizedModule.mkLinearMap (KH.cellMon S I) _) _ _
    rw [e1, ← Finset.sum_congr rfl hterm, ← Finset.smul_sum, h, smul_zero]
  intro a ha
  by_cases hI : ∀ k, negSet a k ⊆ I k
  · have hk := congrArg (AddMonoidAlgebra.coeff · (c a)) key
    rw [coeff_sum, Finset.sum_eq_single a, coeff_monomial, if_pos rfl,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hk
    · exact hk
    · intro b hb hba
      by_cases hbI : ∀ k, negSet b k ⊆ I k
      · rw [coeff_monomial, if_neg]
        exact fun hcb => hba (shift_injective u (hle b hb hbI) (hle a ha hI) hcb)
      · simp [hg b hb hbI]
    · exact fun hna => absurd ha hna
  · exact hg a ha hI

end KHFreeIndep

theorem KHFreeIndep.full : KHFreeIndep.Statement := by
  intro S _ K _ _ ι _ _ n A f h a ha
  classical
  funext J
  let g : ((Σ k, ι k) → ℤ) → S := fun b =>
    if hb : ∀ k, negSet b k ⊆ J.1.1 k then f b ⟨J.1, hb⟩ else 0
  have hsum : ∑ b ∈ A, g b • monoFrac S J.1.1 b = 0 := by
    have h0 := congrFun h J.1
    rw [Finset.sum_apply, Pi.zero_apply] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [embed, LinearMap.pi_apply, g]
    split_ifs with hb1
    · rfl
    · simp [monoFrac, hb1]
  have hJ := KHFreeIndep.eq_zero_of_sum_smul_monoFrac J.1.1 A g (fun b _ hb => dif_neg hb) hsum a ha
  rw [show g a = f a J from dif_pos J.2] at hJ
  simpa using hJ

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleZExtend
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u v w

namespace VeryAmpleZExtend

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

theorem prod_mem_pow {r : ℕ} (H : SubSystem S x Ω) {h : Fin (r + 1) → Ω} (hh : ∀ l, h l ∈ H.secs)
    (I : Chart x) (T : Finset (Fin (r + 1))) : ∏ l ∈ T, h l ∈ (H.pow T.card).sub I := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.card_empty]; exact one_mem_twistMod_zero I
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, mul_comm]
    have h1 : h a ∈ (H.pow 1).sub I := by
      rw [SubSystem.pow_sub, pow_one]
      exact (Submodule.restrictScalars_mem _ _ _).mp ((Submodule.mem_iInf _).mp (hh a) I)
    exact AmpleTwistLocal.mul_mem_pow H I ih 1 h1


omit [Module S E] [IsScalarTower S Ω E] in
theorem smul_mem_twist_pow (F : SubSystem S x E) (H : SubSystem S x Ω) (I : Chart x) {a b : ℕ} {z : E}
    {w : Ω} (hz : z ∈ (F.twist (H.pow a)).sub I) (hw : w ∈ (H.pow b).sub I) :
    w • z ∈ (F.twist (H.pow (a + b))).sub I := by
  change z ∈ Submodule.span _ _ at hz
  refine Submodule.span_induction
    (p := fun z _ => w • z ∈ (F.twist (H.pow (a + b))).sub I) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨q, hq, y, hy, rfl⟩
    refine Submodule.subset_span ⟨q * w, AmpleTwistLocal.mul_mem_pow H I hq b hw, y, hy, ?_⟩
    rw [smul_smul, mul_comm]
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro z z' _ _ hz hz'; rw [smul_add]; exact Submodule.add_mem _ hz hz'
  · intro t z _ hz
    have e : w • (t • z) = t • (w • z) := by
      rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_smul, smul_smul, mul_comm]
    rw [e]; exact Submodule.smul_mem _ t hz


omit [Module S E] [IsScalarTower S Ω E] in
theorem gen_smul {r : ℕ} (F : SubSystem S x E) (H : SubSystem S x Ω) {h : Fin (r + 1) → Ω}
    (hh : ∀ l, h l ∈ H.secs) (I : Chart x) (J : Chart h) {j : Fin (r + 1)} (hj : j ∈ J.1) {c : Ω} {a : ℕ}
    (hc : c * h j ^ a ∈ (H.pow a).sub I) {y : E}
    (hy : ∃ m : ℕ, xProd J ^ m • y ∈ (F.twist (H.pow (J.1.card * m))).sub I) :
    ∃ m : ℕ, xProd J ^ m • (c • y) ∈ (F.twist (H.pow (J.1.card * m))).sub I := by
  classical
  obtain ⟨m, hm⟩ := hy
  have hJ : xProd J = h j * ∏ l ∈ J.1.erase j, h l := (Finset.mul_prod_erase J.1 h hj).symm
  have hcard : (J.1.erase j).card + 1 = J.1.card := Finset.card_erase_add_one hj
  have hw := AmpleTwistLocal.mul_mem_pow H I hc _
    (AmpleTwistLocal.pow_mem_pow H I (prod_mem_pow H hh I (J.1.erase j)) a)
  refine ⟨m + a, ?_⟩
  have e1 : xProd J ^ (m + a) • (c • y) =
      (c * h j ^ a * (∏ l ∈ J.1.erase j, h l) ^ a) • (xProd J ^ m • y) := by
    rw [smul_smul, smul_smul, hJ]
    congr 1
    ring
  have e2 : J.1.card * (m + a) = J.1.card * m + (a + (J.1.erase j).card * a) := by
    rw [← hcard]; ring
  rw [e1, e2]
  exact smul_mem_twist_pow F H I hm hw

theorem proof : VeryAmpleZExtend.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ F H r h hh J j hj c hc K hK f hf
  classical
  have key : ∀ I : Chart x, ∀ᶠ M in atTop, c ^ M • f ∈ secsOnZChart F.toSubSystem H h I J := by
    intro I
    obtain ⟨a, ha⟩ := Set.mem_iInter.mp hc I
    rw [one_mul] at ha
    obtain ⟨e, n, hn⟩ := hK I
    rw [one_mul] at hn
    change c ^ e * AmpleAffineGen.chartRatio K I * h j ^ n ∈ (H.pow n).sub I at hn

    have hfU := F.mono K (AmpleAffineGen.unionChart I K) (AmpleAffineGen.subset_unionChart_right I K) f hf
    obtain ⟨t, ht, htf⟩ := (F.mem_iff I (AmpleAffineGen.unionChart I K)
      (AmpleAffineGen.subset_unionChart_left I K) f).mp hfU
    obtain ⟨v, hv⟩ := ht.exists_left_inv
    obtain ⟨D, hD⟩ := AmpleAffineGen.exists_pow_mul_mem I K v.2
    have hv' : (v : Ω) * (t : Ω) = 1 := congrArg Subtype.val hv
    have hρf : AmpleAffineGen.chartRatio I K ^ D • f ∈ F.sub I := by
      have e1 : AmpleAffineGen.chartRatio I K ^ D • f =
          (⟨_, hD⟩ : chartRing S x I) • ((t : Ω) • f) := by
        rw [Subalgebra.smul_def, smul_smul]
        congr 1
        change _ = AmpleAffineGen.chartRatio I K ^ D * (v : Ω) * (t : Ω)
        rw [mul_assoc, hv', mul_one]
      rw [e1]
      exact Submodule.smul_mem _ _ htf

    have hP := prod_mem_pow H hh I (J.1.erase j)
    have hcard : (J.1.erase j).card + 1 = J.1.card := Finset.card_erase_add_one hj
    have hJ : xProd J = h j * ∏ l ∈ J.1.erase j, h l := (Finset.mul_prod_erase J.1 h hj).symm
    have hz : (c ^ e * AmpleAffineGen.chartRatio K I * h j ^ n) ^ D •
        (AmpleAffineGen.chartRatio I K ^ D • f) ∈ (F.toSubSystem.twist (H.pow (n * D))).sub I :=
      Submodule.subset_span ⟨_, AmpleTwistLocal.pow_mem_pow H I hn D, _, hρf, rfl⟩
    have hz2 := smul_mem_twist_pow F.toSubSystem H I hz
      (AmpleTwistLocal.pow_mem_pow H I hP (n * D))
    have h0 : ∃ m : ℕ, xProd J ^ m • (c ^ (e * D) • f) ∈
        (F.toSubSystem.twist (H.pow (J.1.card * m))).sub I := by
      refine ⟨n * D, ?_⟩
      have e1 : xProd J ^ (n * D) • (c ^ (e * D) • f) =
          (∏ l ∈ J.1.erase j, h l) ^ (n * D) • ((c ^ e * AmpleAffineGen.chartRatio K I * h j ^ n) ^ D •
            (AmpleAffineGen.chartRatio I K ^ D • f)) := by
        rw [smul_smul, smul_smul, smul_smul, hJ]
        congr 1
        have hr := AmpleAffineGen.chartRatio_mul_chartRatio I K
        calc (h j * ∏ l ∈ J.1.erase j, h l) ^ (n * D) * c ^ (e * D)
            = (∏ l ∈ J.1.erase j, h l) ^ (n * D) * ((c ^ e * h j ^ n) ^ D *
                (AmpleAffineGen.chartRatio K I * AmpleAffineGen.chartRatio I K) ^ D) := by
              rw [hr, one_pow, mul_one]; ring
          _ = _ := by ring
      have e2 : J.1.card * (n * D) = n * D + (J.1.erase j).card * (n * D) := by
        rw [← hcard]; ring
      rw [e1, e2]
      exact hz2

    have hstep : ∀ q : ℕ, ∃ m : ℕ, xProd J ^ m • (c ^ (e * D + q) • f) ∈
        (F.toSubSystem.twist (H.pow (J.1.card * m))).sub I := by
      intro q
      induction q with
      | zero => exact h0
      | succ q ih =>
        rw [← Nat.add_assoc, pow_succ', ← smul_smul]
        exact gen_smul F.toSubSystem H hh I J hj ha ih
    refine eventually_atTop.mpr ⟨e * D, fun M hM => ?_⟩
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hM
    exact Submodule.subset_span (hstep q)
  exact (eventually_all.mpr key).mono fun M hM => (Submodule.mem_iInf _).mpr hM

end VeryAmpleZExtend

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHFreeDecomp
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

namespace KHFreeDecomp

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem cellMon_monomial {I : ∀ k, Finset (ι k)} {t : MRingOver S ι} (ht : t ∈ KH.cellMon S I) :
    ∃ u : (Σ k, ι k) →₀ ℕ, t = monomial u 1 ∧ ∀ q ∈ u.support, q.2 ∈ I q.1 := by
  classical
  induction ht using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    refine ⟨Finsupp.single ⟨k, i⟩ 1, rfl, fun q hq => ?_⟩
    rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hq)]
    exact hi
  | one => exact ⟨0, by rw [← C_1, C_apply], by simp⟩
  | mul f g _ _ hf hg =>
    obtain ⟨u, rfl, hu⟩ := hf
    obtain ⟨v, rfl, hv⟩ := hg
    refine ⟨u + v, by rw [monomial_mul, one_mul], fun q hq => ?_⟩
    rcases Finset.mem_union.mp (Finsupp.support_add hq) with h | h
    · exact hu q h
    · exact hv q h

section Frac

variable {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]

def overDen (T : Submonoid (MRingOver S ι)) (t : T) : M →ₗ[S] LocalizedModule T M where
  toFun m := LocalizedModule.mk m t
  map_add' x y := by
    simp only [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk'_add]
  map_smul' s m := by
    rw [RingHom.id_apply, LocalizedModule.smul'_mk]

theorem overDen_apply (T : Submonoid (MRingOver S ι)) (t : T) (m : M) :
    overDen T t m = LocalizedModule.mk m t := rfl

end Frac

theorem quot_mk_smul (s : S) (p : MRingOver S ι) :
    Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι)) (s • p) = s • Ideal.Quotient.mk ⊥ p := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, Ideal.Quotient.mk_algebraMap]

theorem mk_monomial_eq (I : ∀ k, Finset (ι k)) (u v : (Σ k, ι k) →₀ ℕ) (hu : ∀ q ∈ u.support, q.2 ∈ I q.1)
    (ht : (monomial u (1 : S) : MRingOver S ι) ∈ KH.cellMon S I) :
    LocalizedModule.mk (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι)) (monomial v 1)) ⟨monomial u 1, ht⟩ =
      monoFrac S I (fun q => (v q : ℤ) - u q) := by
  classical
  have hneg : ∀ k, negSet (fun q => (v q : ℤ) - u q) k ⊆ I k := by
    intro k i hi
    simp only [negSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hu ⟨k, i⟩ (Finsupp.mem_support_iff.mpr (by omega))
  have hexp : negExp (fun q => (v q : ℤ) - u q) + v = u + posExp (fun q => (v q : ℤ) - u q) := by
    ext q
    simp only [Finsupp.add_apply, posExp, negExp, Finsupp.coe_equivFunOnFinite_symm]
    omega
  rw [monoFrac, dite_eq_left hneg, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
    monomial_mul, mul_one]
  rw [hexp]

theorem locPart_le (I : ∀ k, Finset (ι k)) (c d : K → ℤ) :
    KH.locPart ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) (KH.cellMon S I) c ≤
      Submodule.span S (monoFrac S I '' {a | blockSum a = c + d}) := by
  classical
  rcases subsingleton_or_nontrivial S with hS | hS
  · intro x _
    have hx : x = 0 := by rw [← one_smul S x, Subsingleton.elim (1 : S) 0, zero_smul]
    rw [hx]
    exact zero_mem _
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨m, ⟨t, ht⟩, b, htb, hm, rfl⟩
  obtain ⟨u, rfl, huI⟩ := cellMon_monomial ht
  have hub : ∀ k, ∑ i, u ⟨k, i⟩ = b k := by
    intro k
    refine htb u ?_ k
    rw [support_monomial, if_neg one_ne_zero]
    exact Finset.mem_singleton_self u
  have hle : KH.quotPart S (⊥ : Ideal (MRingOver S ι)) ((c + fun k => (b k : ℤ)) + d) ≤
      (Submodule.span S (monoFrac S I '' {a | blockSum a = c + d})).comap
        (overDen (KH.cellMon S I) ⟨monomial u 1, ht⟩) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨p, ⟨hpos, hp⟩, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    have hsum : p = ∑ v ∈ p.support, AddMonoidAlgebra.coeff p v • (monomial v 1 : MRingOver S ι) := by
      conv_lhs => rw [p.as_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [smul_monomial, smul_eq_mul, mul_one]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum, map_sum]
    refine Submodule.sum_mem _ fun v hv => ?_
    rw [quot_mk_smul, map_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun q => (v q : ℤ) - u q, ?_, ?_⟩)
    · have hv' := hp v hv
      show blockSum _ = c + d
      funext k
      simp only [blockSum, Finset.sum_sub_distrib]
      have h1 : ∑ i, ((v ⟨k, i⟩ : ℕ) : ℤ) = ((((c + fun k => (b k : ℤ)) + d) k).toNat : ℤ) := by
        exact_mod_cast hv' k
      have h2 : ∑ i, ((u ⟨k, i⟩ : ℕ) : ℤ) = b k := by exact_mod_cast hub k
      have h3 := hpos k
      simp only [Pi.add_apply] at h1 h3 ⊢
      omega
    · rw [overDen_apply, mk_monomial_eq I u v huI ht]
  exact hle hm

theorem embed_apply_cell [LinearOrder K] [∀ k, LinearOrder (ι k)] (a : (Σ k, ι k) → ℤ) (n : ℕ)
    (F : KH.Cell K ι n → S) (I : KH.Cell K ι n) :
    embed S a n (fun J => F J.1) I = F I • monoFrac S I.1 a := by
  classical
  unfold embed
  rw [LinearMap.pi_apply]
  split_ifs with h
  · rfl
  · rw [LinearMap.zero_apply, monoFrac, dite_eq_right h, smul_zero]

end KHFreeDecomp


open KHFreeDecomp in
theorem KHFreeDecomp.full : KHFreeDecomp.Statement := by
  intro S _ K _ _ ι _ _ c d n φ hφ
  classical
  have hI : ∀ I : KH.Cell K ι n, ∃ l : ((Σ k, ι k) → ℤ) →₀ S,
      l ∈ Finsupp.supported S S {a | blockSum a = c + d} ∧
        Finsupp.linearCombination S (monoFrac S I.1) l = φ I := by
    intro I
    have hx : φ I ∈ KH.locPart ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d))
        (KH.cellMon S I.1) c := hφ I (Set.mem_univ _)
    exact (Finsupp.mem_span_image_iff_linearCombination S).mp (locPart_le I.1 c d hx)
  choose l hl hlφ using hI
  let _ : Fintype (KH.Cell K ι n) := by unfold KH.Cell; infer_instance
  refine ⟨Finset.univ.biUnion fun I => (l I).support, fun a J => l J.1 a, ?_, ?_⟩
  · intro a ha
    obtain ⟨I, -, haI⟩ := Finset.mem_biUnion.mp ha
    exact hl I haI
  · funext I
    rw [Finset.sum_apply, ← hlφ I, Finsupp.linearCombination_apply, Finsupp.sum]
    beta_reduce
    refine (Finset.sum_subset (s₁ := (l I).support) (s₂ := Finset.univ.biUnion fun I => (l I).support)
      (f := fun a => l I a • monoFrac S I.1 a) (fun a ha => Finset.mem_biUnion.mpr ⟨I, Finset.mem_univ _, ha⟩) ?_).trans
      (Finset.sum_congr rfl fun a _ => (embed_apply_cell a n (fun J => l J a) I).symm)
    intro a _ ha
    rw [Finsupp.mem_support_iff, not_not] at ha
    rw [ha, zero_smul]

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PZChartLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

namespace ZChartLocal

open AmpleAffineGen AmpleTwistLocal

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]


omit [Module S E] [IsScalarTower S Ω E] in
theorem smul_mem_twist_pow (F : SubSystem S x E) (H : SubSystem S x Ω) (I : Chart x) {c d : ℕ}
    {y : E} {w : Ω} (hy : y ∈ (F.twist (H.pow c)).sub I) (hw : w ∈ (H.pow d).sub I) :
    w • y ∈ (F.twist (H.pow (c + d))).sub I := by
  change y ∈ Submodule.span _ _ at hy
  refine Submodule.span_induction
    (p := fun y _ => w • y ∈ (F.twist (H.pow (c + d))).sub I) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨q, hq, z, hz, rfl⟩
    exact Submodule.subset_span ⟨q * w, mul_mem_pow H I hq d hw, z, hz, by rw [smul_smul, mul_comm]⟩
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
  · intro a z _ hz
    have e : w • (a • z) = a • (w • z) := by
      change w • ((a : Ω) • z) = (a : Ω) • (w • z)
      rw [smul_smul, smul_smul, mul_comm]
    rw [e]
    exact Submodule.smul_mem _ a hz

theorem prod_mem_pow (H : SubSystem S x Ω) (I : Chart x) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hh : ∀ l, h l ∈ H.secs) (T : Finset (Fin (r + 1))) : ∏ l ∈ T, h l ∈ (H.pow T.card).sub I := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.card_empty]; exact one_mem_twistMod_zero I
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, mul_comm]
    have h1 : h a ∈ (H.pow 1).sub I := by
      rw [SubSystem.pow_sub, pow_one]; exact (Submodule.mem_iInf _).mp (hh a) I
    exact mul_mem_pow H I ih 1 h1


omit [Module S E] [IsScalarTower S Ω E] in
theorem ratio_pow_smul_mem (F : SubSystem S x E) (I K : Chart x) (k : ℕ) {y : E} (hy : y ∈ F.sub I) :
    chartRatio I K ^ k • y ∈ F.sub I :=
  Submodule.smul_mem (F.sub I) (⟨_, pow_mem (chartRatio_mem I K) k⟩ : chartRing S x I) hy


omit [Module S E] [IsScalarTower S Ω E] in
theorem loc_subFamily (G : SubFamily S x E) (I K : Chart x) {y : E}
    (hy : y ∈ G.sub (unionChart I K)) : ∃ c : ℕ, chartRatio I K ^ c • y ∈ G.sub I := by
  obtain ⟨a, ha, hay⟩ := (G.mem_iff I (unionChart I K) (subset_unionChart_left I K) y).mp hy
  obtain ⟨w, hw⟩ := ha.exists_left_inv
  obtain ⟨D, hD⟩ := exists_pow_mul_mem I K w.2
  refine ⟨D, ?_⟩
  have hw' : (w : Ω) * (a : Ω) = 1 := congrArg Subtype.val hw
  have e : chartRatio I K ^ D • y = (⟨_, hD⟩ : chartRing S x I) • ((a : Ω) • y) := by
    change _ = (chartRatio I K ^ D * (w : Ω)) • ((a : Ω) • y)
    rw [smul_smul, mul_assoc, hw', mul_one]
  rw [e]
  exact Submodule.smul_mem _ _ hay


omit [Module S E] [IsScalarTower S Ω E] in
theorem loc_twist (G : SubFamily S x E) (H : LineBundle S x) (I K : Chart x) (q : ℕ) {y : E}
    (hy : y ∈ (G.toSubSystem.twist (H.toSubSystem.pow q)).sub (unionChart I K)) :
    ∃ c : ℕ, chartRatio I K ^ c • y ∈ (G.toSubSystem.twist (H.toSubSystem.pow q)).sub I := by
  change y ∈ Submodule.span _ _ at hy
  refine Submodule.span_induction (p := fun y _ => ∃ c : ℕ,
    chartRatio I K ^ c • y ∈ (G.toSubSystem.twist (H.toSubSystem.pow q)).sub I) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨p, hp, z, hz, rfl⟩
    obtain ⟨D₁, h₁⟩ := exists_pow_mul_mem_of_eq (H.powBundle q)
      (LineBundle.powBundle_toSubSystem H q) I K hp
    obtain ⟨D₂, h₂⟩ := loc_subFamily G I K hz
    refine ⟨D₁ + D₂, Submodule.subset_span ⟨_, h₁, _, h₂, ?_⟩⟩
    rw [smul_smul, smul_smul, pow_add]
    congr 1
    ring
  · exact ⟨0, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  · rintro y₁ y₂ - - ⟨c₁, h₁⟩ ⟨c₂, h₂⟩
    refine ⟨c₁ + c₂, ?_⟩
    have e : chartRatio I K ^ (c₁ + c₂) • (y₁ + y₂) =
        chartRatio I K ^ c₂ • (chartRatio I K ^ c₁ • y₁) + chartRatio I K ^ c₁ • (chartRatio I K ^ c₂ • y₂) := by
      rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, Nat.add_comm c₂ c₁]
    rw [e]
    exact Submodule.add_mem _ (ratio_pow_smul_mem _ I K c₂ h₁) (ratio_pow_smul_mem _ I K c₁ h₂)
  · rintro a y - ⟨c, hc⟩
    obtain ⟨D, hD⟩ := exists_pow_mul_mem I K a.2
    refine ⟨D + c, ?_⟩
    have e : chartRatio I K ^ (D + c) • (a • y) = (⟨_, hD⟩ : chartRing S x I) • (chartRatio I K ^ c • y) := by
      change chartRatio I K ^ (D + c) • ((a : Ω) • y) = (chartRatio I K ^ D * (a : Ω)) • (chartRatio I K ^ c • y)
      rw [smul_smul, smul_smul, pow_add]
      congr 1
      ring
    rw [e]
    exact Submodule.smul_mem _ _ hc

end ZChartLocal


open AmpleAffineGen AmpleTwistLocal ZChartLocal in
theorem ZChartLocal.proof (hSmul : ZChartSmul.Statement.{u, v, w}) : ZChartLocal.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ G H r h hh J j hj b hb K hK j₀ hj₀ I I' hI' z hz
  classical
  have hbpow : ∀ (k : ℕ) {y : E}, y ∈ secsOnZChart G.toSubSystem H.toSubSystem h I J →
      b ^ k • y ∈ secsOnZChart G.toSubSystem H.toSubSystem h I J := by
    intro k
    induction k with
    | zero => intro y hy; rwa [pow_zero, one_smul]
    | succ k ih =>
      intro y hy
      rw [pow_succ', mul_smul]
      exact hSmul S Ω N x E G.toSubSystem H.toSubSystem r h hh J j hj I b hb _ (ih hy)
  have hIU : I'.1 ⊆ (unionChart I K).1 := by
    rw [hI']; exact Finset.insert_subset (Finset.mem_union_right _ hj₀) Finset.subset_union_left
  have hzU : z ∈ secsOnZChart G.toSubSystem H.toSubSystem h (unionChart I K) J := by
    refine Submodule.span_mono ?_ hz
    rintro y ⟨n, hn⟩
    exact ⟨n, (G.toSubSystem.twist (H.toSubSystem.pow _)).mono I' _ hIU _ hn⟩
  obtain ⟨e, n, hn⟩ := hK I
  have hR := prod_mem_pow H.toSubSystem I hh (J.1.erase j)
  have hJ : xProd J = h j * ∏ l ∈ J.1.erase j, h l := (Finset.mul_prod_erase J.1 h hj).symm
  have hcard : (J.1.erase j).card + 1 = J.1.card := Finset.card_erase_add_one hj
  generalize ∏ l ∈ J.1.erase j, h l = R at hR hJ
  have hu := mul_mem_pow H.toSubSystem I hn _ (pow_mem_pow H.toSubSystem I hR n)
  generalize hud : b ^ e * (xProd I ^ K.1.card / xProd K ^ I.1.card) * h j ^ n * R ^ n = u at hu
  have huv : u * chartRatio I K = b ^ e * xProd J ^ n := by
    have h1 := chartRatio_mul_chartRatio I K
    rw [chartRatio, chartRatio] at h1
    rw [← hud, hJ, chartRatio]
    linear_combination (b ^ e * (h j * R) ^ n) * h1
  change z ∈ Submodule.span S _ at hzU
  refine Submodule.span_induction (p := fun z _ =>
    ∃ e : ℕ, b ^ e • z ∈ secsOnZChart G.toSubSystem H.toSubSystem h I J) ?_ ?_ ?_ ?_ hzU
  · rintro y ⟨m, hm⟩
    obtain ⟨c, hc⟩ := loc_twist G H I K _ hm
    refine ⟨e * c, Submodule.subset_span ⟨m + n * c, ?_⟩⟩
    have h2 := smul_mem_twist_pow G.toSubSystem H.toSubSystem I hc (pow_mem_pow H.toSubSystem I hu c)
    have e1 : xProd J ^ (m + n * c) • b ^ (e * c) • y = u ^ c • chartRatio I K ^ c • xProd J ^ m • y := by
      rw [smul_smul, smul_smul, smul_smul, ← mul_pow, huv]
      congr 1
      ring
    have e2 : J.1.card * m + (1 * n + (J.1.erase j).card * n) * c = J.1.card * (m + n * c) := by
      rw [← hcard]; ring
    rw [e1, ← e2]
    exact h2
  · exact ⟨0, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  · rintro y₁ y₂ - - ⟨e₁, h₁⟩ ⟨e₂, h₂⟩
    refine ⟨e₁ + e₂, ?_⟩
    have e3 : b ^ (e₁ + e₂) • (y₁ + y₂) = b ^ e₂ • (b ^ e₁ • y₁) + b ^ e₁ • (b ^ e₂ • y₂) := by
      rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, Nat.add_comm e₂ e₁]
    rw [e3]
    exact Submodule.add_mem _ (hbpow _ h₁) (hbpow _ h₂)
  · rintro s y - ⟨e', h'⟩
    exact ⟨e', by rw [smul_comm]; exact Submodule.smul_mem _ s h'⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end
