module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrictionLocal

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrictionSystems
section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrictionPowers
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem res_mem_chartRing_of_mem_twistMod_zero {I : Chart x} {a : Ω} (ha : a ∈ twistMod S x 0 I) :
    a ∈ chartRing S x I := by
  obtain ⟨i, hi⟩ := I.2.1
  rw [twistMod_eq_span 0 I hi, zpow_zero, Submodule.mem_span_singleton] at ha
  obtain ⟨c, rfl⟩ := ha
  rw [chartRing_smul_def, mul_one]; exact c.2

theorem res_mem_twistMod_zero_of_mem_chartRing {I : Chart x} {a : Ω} (ha : a ∈ chartRing S x I) :
    a ∈ twistMod S x 0 I := by
  have := (twistMod S x 0 I).smul_mem ⟨a, ha⟩ (one_mem_twistMod_zero I)
  rwa [chartRing_smul_def, mul_one] at this

theorem SubSystem.res_mul_mem_pow (H : SubSystem S x Ω) (I : Chart x) {m : ℕ} {a : Ω}
    (ha : a ∈ (H.pow m).sub I) (n : ℕ) {b : Ω} (hb : b ∈ (H.pow n).sub I) :
    a * b ∈ (H.pow (m + n)).sub I := by
  induction n generalizing b with
  | zero =>
    have hb' : b ∈ chartRing S x I := res_mem_chartRing_of_mem_twistMod_zero hb
    have := ((H.pow m).sub I).smul_mem ⟨b, hb'⟩ ha
    rw [chartRing_smul_def] at this
    rw [mul_comm]; exact this
  | succ n ih =>
    change b ∈ ((H.pow n).twist H).sub I at hb
    change a * b ∈ ((H.pow (m + n)).twist H).sub I
    refine Submodule.span_induction (p := fun z _ => a * z ∈ ((H.pow (m + n)).twist H).sub I)
      ?_ ?_ ?_ ?_ hb
    · rintro _ ⟨q, hq, z, hz, rfl⟩
      refine Submodule.subset_span ⟨q, hq, a * z, ih hz, ?_⟩
      simp only [smul_eq_mul]; ring
    · rw [mul_zero]; exact Submodule.zero_mem _
    · intro u v _ _ hu hv; rw [mul_add]; exact Submodule.add_mem _ hu hv
    · intro c u _ hu
      rw [chartRing_smul_def, mul_left_comm, ← chartRing_smul_def]
      exact Submodule.smul_mem _ c hu

theorem LineBundle.res_exists_mul_mem_pow (H : LineBundle S x) {I J : Chart x} (hIJ : I.1 ⊆ J.1)
    (n : ℕ) {z : Ω} (hz : z ∈ (H.pow n).sub J) :
    ∃ a : chartRing S x I, IsUnit (chartIncl hIJ a) ∧ (a : Ω) * z ∈ (H.pow n).sub I := by
  induction n generalizing z with
  | zero =>
    obtain ⟨a, ha, haz⟩ := ((twistBundle S x 0).mem_iff I J hIJ z).mp hz
    exact ⟨a, ha, haz⟩
  | succ n ih =>
    change z ∈ ((H.pow n).twist H.toSubSystem).sub J at hz
    change ∃ a : chartRing S x I, IsUnit (chartIncl hIJ a) ∧
      (a : Ω) * z ∈ ((H.pow n).twist H.toSubSystem).sub I
    refine Submodule.span_induction (p := fun z _ => ∃ a : chartRing S x I,
      IsUnit (chartIncl hIJ a) ∧ (a : Ω) * z ∈ ((H.pow n).twist H.toSubSystem).sub I) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨q, hq, w, hw, rfl⟩
      obtain ⟨a₁, ha₁, hq'⟩ := (H.mem_iff I J hIJ q).mp hq
      obtain ⟨a₂, ha₂, hw'⟩ := ih hw
      refine ⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂,
        Submodule.subset_span ⟨_, hq', _, hw', ?_⟩⟩
      simp only [smul_eq_mul, Subalgebra.coe_mul]; ring
    · exact ⟨1, by rw [map_one]; exact isUnit_one, by rw [mul_zero]; exact Submodule.zero_mem _⟩
    · rintro u v _ _ ⟨a₁, ha₁, hu⟩ ⟨a₂, ha₂, hv⟩
      refine ⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂, ?_⟩
      have h1 := Submodule.smul_mem _ a₂ hu
      have h2 := Submodule.smul_mem _ a₁ hv
      rw [chartRing_smul_def] at h1 h2
      convert Submodule.add_mem _ h1 h2 using 1
      simp only [Subalgebra.coe_mul]; ring
    · rintro c u _ ⟨a, ha, hu⟩
      obtain ⟨a', ha', hc⟩ := exists_isUnit_mul_mem hIJ c
      refine ⟨a' * a, by rw [map_mul]; exact ha'.mul ha, ?_⟩
      have := Submodule.smul_mem _ (⟨_, hc⟩ : chartRing S x I) hu
      rw [chartRing_smul_def] at this
      convert this using 1
      rw [chartRing_smul_def]; simp only [Subalgebra.coe_mul]; ring

section AmpleChart

variable {H : SubSystem S x Ω} {σ : Ω} {I : Chart x}

theorem res_ampleChart_mul {a b : Ω} (ha : a ∈ ampleChart H 1 σ I) (hb : b ∈ ampleChart H 1 σ I) :
    a * b ∈ ampleChart H 1 σ I := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨m, hm⟩ := hb
  refine ⟨n + m, ?_⟩
  rw [one_mul] at hn hm ⊢
  have := H.res_mul_mem_pow I hn m hm
  convert this using 1; ring

theorem res_chartRing_sub_ampleChart {a : Ω} (ha : a ∈ chartRing S x I) : a ∈ ampleChart H 1 σ I :=
  ⟨0, by rw [pow_zero, mul_one, mul_zero]; exact res_mem_twistMod_zero_of_mem_chartRing ha⟩

theorem res_ampleChart_pow {a : Ω} (ha : a ∈ ampleChart H 1 σ I) (n : ℕ) :
    a ^ n ∈ ampleChart H 1 σ I := by
  induction n with
  | zero => rw [pow_zero]; exact res_chartRing_sub_ampleChart (one_mem _)
  | succ n ih => rw [pow_succ]; exact res_ampleChart_mul ih ha

end AmpleChart


variable (x) in
def resUnionChart (I J : Chart x) : Chart x :=
  ⟨I.1 ∪ J.1, I.2.1.mono Finset.subset_union_left, Finset.union_subset I.2.2 J.2.2⟩

theorem res_isHomogeneous_prod_X (s : Finset (Fin (N + 1))) :
    (∏ i ∈ s, (X i : Poly S N)).IsHomogeneous s.card := by
  have := IsHomogeneous.prod s (fun i => (X i : Poly S N)) (fun _ => 1)
    (fun i _ => isHomogeneous_X S i)
  simpa using this

theorem res_aeval_prod_X (s : Finset (Fin (N + 1))) :
    aeval x (∏ i ∈ s, (X i : Poly S N)) = ∏ i ∈ s, x i := by
  simp [map_prod]

theorem res_xProd_ne_zero (I : Chart x) : xProd I ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hi => (mem_support x).mp (I.2.2 hi)

theorem res_exists_pow_mul_mem_chartRing (I J : Chart x) {u : Ω}
    (hu : u ∈ chartRing S x (resUnionChart x I J)) :
    ∃ M : ℕ, (xProd J ^ I.1.card / xProd I ^ J.1.card) ^ M * u ∈ chartRing S x I := by
  set t' := xProd J ^ I.1.card / xProd I ^ J.1.card with ht'
  obtain ⟨i₀, hi₀⟩ := I.2.1
  have hx₀ : x i₀ ≠ 0 := (mem_support x).mp (I.2.2 hi₀)
  let T : Ω → Prop := fun u => ∃ M : ℕ, t' ^ M * u ∈ chartRing S x I
  have hTmem : ∀ {u}, u ∈ chartRing S x I → T u := fun hu => ⟨0, by rw [pow_zero, one_mul]; exact hu⟩
  have hTmul : ∀ {u v}, T u → T v → T (u * v) := by
    rintro u v ⟨M, hM⟩ ⟨M', hM'⟩
    refine ⟨M + M', ?_⟩
    have := mul_mem hM hM'
    convert this using 1; ring

  have hgen : ∀ i ∈ I.1 ∪ J.1, T (x i₀ / x i) := by
    intro i hi
    rcases Finset.mem_union.mp hi with hiI | hiJ
    · exact hTmem ⟨X i₀, X i, 1, X_mem_monos hiI, isHomogeneous_X S i₀, isHomogeneous_X S i,
        by simp⟩
    · have hxi : x i ≠ 0 := (mem_support x).mp (J.2.2 hiJ)
      obtain ⟨a, ha⟩ : ∃ a, I.1.card = a + 1 :=
        ⟨I.1.card - 1, (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr I.2.1)).symm⟩
      obtain ⟨c, hc⟩ : ∃ c, (J.1.erase i).card = c := ⟨_, rfl⟩
      have hJc : J.1.card = c + 1 := by rw [← hc, Finset.card_erase_add_one hiJ]
      refine ⟨1, X i₀ * (∏ l ∈ J.1.erase i, (X l : Poly S N)) * (∏ l ∈ J.1, (X l : Poly S N)) ^ a,
        (∏ l ∈ I.1, (X l : Poly S N)) ^ J.1.card, (a + 1) * (c + 1),
        pow_mem (prod_mem fun l hl => X_mem_monos hl) _, ?_, ?_, ?_⟩
      · have h1 := ((isHomogeneous_X S i₀).mul (res_isHomogeneous_prod_X (S := S) (J.1.erase i))).mul
          ((res_isHomogeneous_prod_X (S := S) J.1).pow a)
        convert h1 using 1
        rw [hc, hJc]; ring
      · have h1 := (res_isHomogeneous_prod_X (S := S) I.1).pow J.1.card
        convert h1 using 1
        rw [ha, hJc]
      · have hprod : ∏ l ∈ J.1, x l = x i * ∏ l ∈ J.1.erase i, x l := (Finset.mul_prod_erase _ _ hiJ).symm
        have hxI := res_xProd_ne_zero I
        simp only [map_mul, map_pow, aeval_X, res_aeval_prod_X, ht', xProd]
        unfold xProd at hxI
        rw [ha, hprod]
        field_simp
        ring

  have hmono : ∀ s ∈ monos (S := S) (I.1 ∪ J.1), ∃ e : ℕ, s.IsHomogeneous e ∧
      T (x i₀ ^ e / aeval x s) := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem s hs =>
      obtain ⟨i, hi, rfl⟩ := hs
      exact ⟨1, isHomogeneous_X S i, by rw [pow_one, aeval_X]; exact hgen i (Finset.mem_coe.mp hi)⟩
    | one => exact ⟨0, isHomogeneous_one _ _, hTmem (by rw [pow_zero, map_one, div_one]; exact one_mem _)⟩
    | mul s s' _ _ hs hs' =>
      obtain ⟨e, he, hT⟩ := hs
      obtain ⟨e', he', hT'⟩ := hs'
      refine ⟨e + e', he.mul he', ?_⟩
      have := hTmul hT hT'
      convert this using 1
      rw [pow_add, map_mul, div_mul_div_comm]
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := hu
  have hs0 : aeval x s ≠ 0 := eval_ne_zero_of_mem_monos (resUnionChart x I J) hs
  obtain ⟨e', he', hT⟩ := hmono s hs
  have hee : e = e' := hse.inj_right he' (fun h => hs0 (by rw [h, map_zero]))
  subst hee
  have h1 : aeval x f / x i₀ ^ e ∈ chartRing S x I :=
    ⟨f, X i₀ ^ e, e, pow_mem (X_mem_monos hi₀) e, hf, isHomogeneous_X_pow i₀ e, by
      rw [map_pow, aeval_X]⟩
  obtain ⟨M, hM⟩ := hTmul (hTmem h1) hT
  refine ⟨M, ?_⟩
  convert hM using 2
  field_simp

theorem res_exists_pow_mul_mem_ampleRing (H : LineBundle S x) {σ b : Ω} {J : Chart x}
    (hb : b ∈ ampleRing H.toSubSystem 1 σ)
    (hbJ : ∀ I : Chart x, ∃ e : ℕ,
      b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card) ∈ ampleChart H.toSubSystem 1 σ I)
    {z : Ω} (hz : z ∈ ampleChart H.toSubSystem 1 σ J) :
    ∃ E : ℕ, b ^ E * z ∈ ampleRing H.toSubSystem 1 σ := by
  have hloc : ∀ I : Chart x, ∃ E : ℕ, b ^ E * z ∈ ampleChart H.toSubSystem 1 σ I := by
    intro I
    have hIK : I.1 ⊆ (resUnionChart x I J).1 := Finset.subset_union_left
    have hJK : J.1 ⊆ (resUnionChart x I J).1 := Finset.subset_union_right
    obtain ⟨n, hn⟩ := hz
    rw [one_mul] at hn
    have hnK := (H.pow n).mono J (resUnionChart x I J) hJK _ hn
    obtain ⟨a, ha, haz⟩ := H.res_exists_mul_mem_pow hIK n hnK
    have haz' : (a : Ω) * z ∈ ampleChart H.toSubSystem 1 σ I :=
      ⟨n, by rw [one_mul, mul_assoc]; exact haz⟩
    obtain ⟨v, hv⟩ := ha.exists_right_inv
    have hav : (a : Ω) * (v : Ω) = 1 := congrArg Subtype.val hv
    obtain ⟨M, hM⟩ := res_exists_pow_mul_mem_chartRing I J v.2
    obtain ⟨e, he⟩ := hbJ I
    refine ⟨e * M, ?_⟩
    have hxI := res_xProd_ne_zero I
    have hxJ := res_xProd_ne_zero J
    have htt : (xProd J ^ I.1.card / xProd I ^ J.1.card) *
        (xProd I ^ J.1.card / xProd J ^ I.1.card) = 1 := by
      field_simp
    have key : b ^ (e * M) * z = ((xProd J ^ I.1.card / xProd I ^ J.1.card) ^ M * (v : Ω)) *
        (b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card)) ^ M * ((a : Ω) * z) := by
      have : ((xProd J ^ I.1.card / xProd I ^ J.1.card) ^ M * (v : Ω)) *
          (b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card)) ^ M * ((a : Ω) * z) =
          ((xProd J ^ I.1.card / xProd I ^ J.1.card) *
            (xProd I ^ J.1.card / xProd J ^ I.1.card)) ^ M * b ^ (e * M) * ((a : Ω) * v) * z := by
        ring
      rw [this, htt, hav]; ring
    rw [key]
    exact res_ampleChart_mul (res_ampleChart_mul (res_chartRing_sub_ampleChart hM) (res_ampleChart_pow he M)) haz'
  choose E hE using hloc
  refine ⟨Finset.univ.sup E, Set.mem_iInter.mpr fun I => ?_⟩
  have hle : E I ≤ Finset.univ.sup E := Finset.le_sup (Finset.mem_univ I)
  have hbI : b ∈ ampleChart H.toSubSystem 1 σ I := Set.mem_iInter.mp hb I
  rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
  exact res_ampleChart_mul (res_ampleChart_pow hbI _) (hE I)

theorem res_span_chart_le {R : Set Ω} {I J : Chart x} (hIJ : I.1 ⊆ J.1) {z : Ω}
    (hz : z ∈ Submodule.span (chartRing S x I) R) : z ∈ Submodule.span (chartRing S x J) R := by
  refine Submodule.span_induction (p := fun z _ => z ∈ Submodule.span (chartRing S x J) R)
    (fun w hw => Submodule.subset_span hw) (Submodule.zero_mem _)
    (fun _ _ _ _ hu hv => Submodule.add_mem _ hu hv) ?_ hz
  intro c u _ hu
  have := Submodule.smul_mem _ (chartIncl hIJ c) hu
  rw [chartRing_smul_def] at this ⊢
  exact this

theorem res_mem_span_iff_exists_isUnit {R : Set Ω} {I J : Chart x} (hIJ : I.1 ⊆ J.1) (z : Ω) :
    z ∈ Submodule.span (chartRing S x J) R ↔ ∃ a : chartRing S x I, IsUnit (chartIncl hIJ a) ∧
      (a : Ω) • z ∈ Submodule.span (chartRing S x I) R := by
  constructor
  · intro hz
    refine Submodule.span_induction (p := fun z _ => ∃ a : chartRing S x I, IsUnit (chartIncl hIJ a) ∧
      (a : Ω) • z ∈ Submodule.span (chartRing S x I) R) ?_ ?_ ?_ ?_ hz
    · intro w hw
      exact ⟨1, by rw [map_one]; exact isUnit_one,
        by rw [OneMemClass.coe_one, one_smul]; exact Submodule.subset_span hw⟩
    · exact ⟨1, by rw [map_one]; exact isUnit_one, by rw [smul_zero]; exact Submodule.zero_mem _⟩
    · rintro u v _ _ ⟨a₁, ha₁, hu⟩ ⟨a₂, ha₂, hv⟩
      refine ⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂, ?_⟩
      have h1 := Submodule.smul_mem _ a₂ hu
      have h2 := Submodule.smul_mem _ a₁ hv
      rw [chartRing_smul_def, smul_eq_mul] at h1 h2
      convert Submodule.add_mem _ h1 h2 using 1
      simp only [smul_eq_mul, Subalgebra.coe_mul]; ring
    · rintro c u _ ⟨a, ha, hu⟩
      obtain ⟨a', ha', hc⟩ := exists_isUnit_mul_mem hIJ c
      refine ⟨a' * a, by rw [map_mul]; exact ha'.mul ha, ?_⟩
      have := Submodule.smul_mem _ (⟨_, hc⟩ : chartRing S x I) hu
      rw [chartRing_smul_def, smul_eq_mul] at this
      convert this using 1
      rw [chartRing_smul_def]; simp only [smul_eq_mul, Subalgebra.coe_mul]; ring
  · rintro ⟨a, ⟨u, hu⟩, haz⟩
    have hJ := res_span_chart_le hIJ haz
    have hinv : ((↑u⁻¹ : chartRing S x J) : Ω) * (a : Ω) = 1 := by
      have := congrArg Subtype.val (Units.inv_mul u)
      rw [hu] at this
      exact this
    have hz : z = (↑u⁻¹ : chartRing S x J) • ((a : Ω) • z) := by
      rw [chartRing_smul_def, smul_eq_mul, ← mul_assoc, hinv, one_mul]
    rw [hz]
    exact Submodule.smul_mem _ _ hJ

end

end GroundTheory.Heights₂.Heights.Kleiman
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}

def redSys (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (P : SubSystem k x Ω) (γ : Ω) : SubSystem k y K' where
  sub I := Submodule.span (chartRing k y I)
    ((fun q => redAt k x y (q / γ)) '' P.sub (liftChart hxy I))
  mono I J h z hz := by
    refine Submodule.span_induction (p := fun z _ => z ∈ Submodule.span (chartRing k y J)
      ((fun q => redAt k x y (q / γ)) '' P.sub (liftChart hxy J))) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨q, hq, rfl⟩
      exact Submodule.subset_span ⟨q, P.mono _ _ h q hq, rfl⟩
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
    · intro a z _ hz; exact Submodule.smul_mem _ (chartIncl h a) hz

def RedGood (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (P : SubSystem k x Ω) (γ : Ω) : Prop :=
  ∀ (I : Chart y), ∀ q ∈ P.sub (liftChart hxy I), q / γ ∈ locAt k x y

variable (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
include hsp

theorem mem_redSys_iff {P : SubSystem k x Ω} {γ : Ω} (hP : RedGood hxy P γ) (I : Chart y) (z : K') :
    z ∈ (redSys hxy P γ).sub I ↔ ∃ q ∈ P.sub (liftChart hxy I), redAt k x y (q / γ) = z := by
  constructor
  · intro hz
    refine Submodule.span_induction (p := fun z _ => ∃ q ∈ P.sub (liftChart hxy I),
      redAt k x y (q / γ) = z) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩
    · exact ⟨0, Submodule.zero_mem _, by rw [zero_div]; exact (locAt_zero hsp).2⟩
    · rintro u v _ _ ⟨q, hq, rfl⟩ ⟨q', hq', rfl⟩
      refine ⟨q + q', Submodule.add_mem _ hq hq', ?_⟩
      rw [add_div]; exact (locAt_add hsp (hP I q hq) (hP I q' hq')).2
    · rintro c u _ ⟨q, hq, rfl⟩
      obtain ⟨a, ha, hac⟩ := exists_redAt_eq (k := k) (x := x) (y := y) hsp hxy I c.2
      refine ⟨a * q, ?_, ?_⟩
      · have := Submodule.smul_mem _ (⟨a, ha⟩ : chartRing k x (liftChart hxy I)) hq
        rwa [chartRing_smul_def] at this
      · rw [chartRing_smul_def, ← hac, mul_div_assoc]
        exact (locAt_mul hsp (chartRing_sub_locAt hsp hxy I ha).1 (hP I q hq)).2
  · rintro ⟨q, hq, rfl⟩; exact Submodule.subset_span ⟨q, hq, rfl⟩

theorem redGood_twist {P Q : SubSystem k x Ω} {γ δ : Ω} (hP : RedGood hxy P γ)
    (hQ : RedGood hxy Q δ) : RedGood hxy (P.twist Q) (γ * δ) := by
  intro I z hz
  refine Submodule.span_induction (p := fun z _ => z / (γ * δ) ∈ locAt k x y) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨q, hq, p, hp, rfl⟩
    have : q • p / (γ * δ) = q / δ * (p / γ) := by rw [smul_eq_mul]; ring
    rw [this]; exact (locAt_mul hsp (hQ I q hq) (hP I p hp)).1
  · rw [zero_div]; exact (locAt_zero hsp).1
  · intro u v _ _ hu hv; rw [add_div]; exact (locAt_add hsp hu hv).1
  · intro c u _ hu
    rw [chartRing_smul_def, mul_div_assoc]
    exact (locAt_mul hsp (chartRing_sub_locAt hsp hxy I c.2).1 hu).1

theorem redSys_twist {P Q : SubSystem k x Ω} {γ δ : Ω} (hP : RedGood hxy P γ)
    (hQ : RedGood hxy Q δ) :
    redSys hxy (P.twist Q) (γ * δ) = (redSys hxy P γ).twist (redSys hxy Q δ) := by
  have hPQ := redGood_twist hsp hxy hP hQ
  refine SubSystem.ext_sub fun I => le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨z, hz, rfl⟩
    refine Submodule.span_induction (p := fun z _ => redAt k x y (z / (γ * δ)) ∈
      ((redSys hxy P γ).twist (redSys hxy Q δ)).sub I) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨q, hq, p, hp, rfl⟩
      have : q • p / (γ * δ) = q / δ * (p / γ) := by rw [smul_eq_mul]; ring
      rw [this, (locAt_mul hsp (hQ I q hq) (hP I p hp)).2]
      exact Submodule.subset_span ⟨_, Submodule.subset_span ⟨q, hq, rfl⟩, _,
        Submodule.subset_span ⟨p, hp, rfl⟩, rfl⟩
    · rw [zero_div, (locAt_zero hsp).2]; exact Submodule.zero_mem _
    · intro u v hu hv ihu ihv
      rw [add_div, (locAt_add hsp (hPQ I u hu) (hPQ I v hv)).2]
      exact Submodule.add_mem _ ihu ihv
    · intro c u hu ihu
      rw [chartRing_smul_def, mul_div_assoc,
        (locAt_mul hsp (chartRing_sub_locAt hsp hxy I c.2).1 (hPQ I u hu)).2]
      have := Submodule.smul_mem _ (⟨_, (chartRing_sub_locAt hsp hxy I c.2).2⟩ : chartRing k y I) ihu
      rwa [chartRing_smul_def] at this
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q', hq', p', hp', rfl⟩
    obtain ⟨q, hq, rfl⟩ := (mem_redSys_iff hsp hxy hQ I q').mp hq'
    obtain ⟨p, hp, rfl⟩ := (mem_redSys_iff hsp hxy hP I p').mp hp'
    have : q • p / (γ * δ) = q / δ * (p / γ) := by rw [smul_eq_mul]; ring
    refine Submodule.subset_span ⟨q • p, Submodule.subset_span ⟨q, hq, p, hp, rfl⟩, ?_⟩
    change redAt k x y (q • p / (γ * δ)) = redAt k x y (q / δ) * redAt k x y (p / γ)
    rw [this, (locAt_mul hsp (hQ I q hq) (hP I p hp)).2]

theorem redGood_twistSys_zero : RedGood hxy (twistSys k x 0) 1 := by
  intro I q hq
  rw [div_one]; exact (chartRing_sub_locAt hsp hxy I (res_mem_chartRing_of_mem_twistMod_zero hq)).1

theorem redSys_twistSys_zero : redSys hxy (twistSys k x 0) 1 = twistSys k y 0 := by
  refine SubSystem.ext_sub fun I => le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, rfl⟩
    change redAt k x y (q / 1) ∈ twistMod k y 0 I
    rw [div_one]
    exact res_mem_twistMod_zero_of_mem_chartRing
      (chartRing_sub_locAt hsp hxy I (res_mem_chartRing_of_mem_twistMod_zero hq)).2
  · intro z hz
    obtain ⟨a, ha, rfl⟩ := exists_redAt_eq (k := k) (x := x) (y := y) hsp hxy I (res_mem_chartRing_of_mem_twistMod_zero hz)
    exact Submodule.subset_span ⟨a, res_mem_twistMod_zero_of_mem_chartRing ha, by
      change redAt k x y (a / 1) = redAt k x y a
      rw [div_one]⟩

theorem redSys_pow {P : SubSystem k x Ω} {γ : Ω} (hP : RedGood hxy P γ) (n : ℕ) :
    RedGood hxy (P.pow n) (γ ^ n) ∧ redSys hxy (P.pow n) (γ ^ n) = (redSys hxy P γ).pow n := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact ⟨redGood_twistSys_zero hsp hxy, redSys_twistSys_zero hsp hxy⟩
  | succ n ih =>
    rw [pow_succ]
    change RedGood hxy ((P.pow n).twist P) (γ ^ n * γ) ∧
      redSys hxy ((P.pow n).twist P) (γ ^ n * γ) = ((redSys hxy P γ).pow n).twist (redSys hxy P γ)
    exact ⟨redGood_twist hsp hxy ih.1 hP, by rw [redSys_twist hsp hxy ih.1 hP, ih.2]⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

theorem mul_mem_chartRing_of_mul_eq_one {S : Type u} [CommRing S] {Ω : Type w} [Field Ω]
    [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω} {I : Chart x} {P M : Submodule (chartRing S x I) Ω}
    (hPM : P * M = 1) {q m : Ω} (hq : q ∈ P) (hm : m ∈ M) : q * m ∈ chartRing S x I := by
  have := Submodule.mul_mem_mul hq hm
  rw [hPM, Submodule.mem_one] at this
  obtain ⟨c, hc⟩ := this
  rw [← hc]; exact c.2

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}
  (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
  {Nb : LineBundle k x} {r : ℕ} {h : Fin (r + 1) → Ω}

theorem mem_sub_of_isVeryAmpleBy (hV : IsVeryAmpleBy Nb.toSubSystem h) (l : Fin (r + 1)) (I : Chart x) :
    h l ∈ Nb.sub I :=
  (Submodule.mem_iInf _).mp (hV.mem_secs l) I

include hsp

theorem exists_redGood (hV : IsVeryAmpleBy Nb.toSubSystem h) (I₀ : Chart y) :
    ∃ l₀ : Fin (r + 1), h l₀ ≠ 0 ∧ (∀ l, h l / h l₀ ∈ locAt k x y) ∧
      RedGood hxy Nb.toSubSystem (h l₀) := by
  obtain ⟨M, hM⟩ := Nb.invertible (liftChart hxy I₀)
  have hgen := hV.generates (liftChart hxy I₀)
  have hA : ∀ {q m : Ω}, q ∈ Nb.sub (liftChart hxy I₀) → m ∈ M → q * m ∈ locAt k x y :=
    fun hq hm => (chartRing_sub_locAt hsp hxy I₀ (mul_mem_chartRing_of_mul_eq_one hM hq hm)).1
  have h1 : (1 : Ω) ∈ Nb.sub (liftChart hxy I₀) * M := by
    rw [hM]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  obtain ⟨l₀, m₀, hm₀, hne⟩ : ∃ l₀, ∃ m₀ ∈ M, redAt k x y (h l₀ * m₀) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hzero : ∀ q ∈ Nb.sub (liftChart hxy I₀), ∀ m ∈ M, redAt k x y (q * m) = 0 := by
      intro q hq m hm
      rw [← hgen] at hq
      refine Submodule.span_induction (p := fun q _ => redAt k x y (q * m) = 0) ?_ ?_ ?_ ?_ hq
      · rintro _ ⟨l, rfl⟩; exact hcon l m hm
      · rw [zero_mul]; exact (locAt_zero hsp).2
      · intro u v hu hv ihu ihv
        rw [add_mul, (locAt_add hsp (hA (hgen ▸ hu) hm) (hA (hgen ▸ hv) hm)).2, ihu, ihv, add_zero]
      · intro c u hu ihu
        rw [chartRing_smul_def, mul_assoc,
          (locAt_mul hsp (chartRing_sub_locAt hsp hxy I₀ c.2).1 (hA (hgen ▸ hu) hm)).2, ihu, mul_zero]
    have := Submodule.mul_induction_on (C := fun z => z ∈ locAt k x y ∧ redAt k x y z = 0) h1
      (fun q hq m hm => ⟨hA hq hm, hzero q hq m hm⟩)
      (fun u v hu hv => ⟨(locAt_add hsp hu.1 hv.1).1, by
        rw [(locAt_add hsp hu.1 hv.1).2, hu.2, hv.2, add_zero]⟩)
    rw [(locAt_one hsp).2] at this
    exact one_ne_zero this.2
  have hgm : h l₀ * m₀ ∈ locAt k x y := hA (mem_sub_of_isVeryAmpleBy hV l₀ _) hm₀
  have hgm0 := (locAt_inv hsp hgm hne).1
  have hg0 : h l₀ ≠ 0 := left_ne_zero_of_mul hgm0
  have hm0 : m₀ ≠ 0 := right_ne_zero_of_mul hgm0
  have hl : ∀ l, h l / h l₀ ∈ locAt k x y := by
    intro l
    rw [← mul_div_mul_right (h l) (h l₀) hm0]
    exact (locAt_div hsp (hA (mem_sub_of_isVeryAmpleBy hV l _) hm₀) hgm hne).1
  refine ⟨l₀, hg0, hl, ?_⟩
  intro I q hq
  have hgenI := hV.generates (liftChart hxy I)
  rw [← hgenI] at hq
  refine Submodule.span_induction (p := fun q _ => q / h l₀ ∈ locAt k x y) ?_ ?_ ?_ ?_ hq
  · rintro _ ⟨l, rfl⟩; exact hl l
  · rw [zero_div]; exact (locAt_zero hsp).1
  · intro u v _ _ hu hv; rw [add_div]; exact (locAt_add hsp hu hv).1
  · intro c u _ hu
    rw [chartRing_smul_def, mul_div_assoc]
    exact (locAt_mul hsp (chartRing_sub_locAt hsp hxy I c.2).1 hu).1

variable {g : Ω}

theorem redSys_sub_eq (hV : IsVeryAmpleBy Nb.toSubSystem h) (hg : RedGood hxy Nb.toSubSystem g)
    (I : Chart y) : (redSys hxy Nb.toSubSystem g).sub I =
      Submodule.span (chartRing k y I) (Set.range fun l => redAt k x y (h l / g)) := by
  have hgen := hV.generates (liftChart hxy I)
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, rfl⟩
    have hq' := hq
    rw [← hgen] at hq'
    refine Submodule.span_induction (p := fun q _ => redAt k x y (q / g) ∈
      Submodule.span (chartRing k y I) (Set.range fun l => redAt k x y (h l / g))) ?_ ?_ ?_ ?_ hq'
    · rintro _ ⟨l, rfl⟩; exact Submodule.subset_span ⟨l, rfl⟩
    · rw [zero_div, (locAt_zero hsp).2]; exact Submodule.zero_mem _
    · intro u v hu hv ihu ihv
      rw [add_div, (locAt_add hsp (hg I u (hgen ▸ hu)) (hg I v (hgen ▸ hv))).2]
      exact Submodule.add_mem _ ihu ihv
    · intro c u hu ihu
      rw [chartRing_smul_def, mul_div_assoc,
        (locAt_mul hsp (chartRing_sub_locAt hsp hxy I c.2).1 (hg I u (hgen ▸ hu))).2]
      have := Submodule.smul_mem _ (⟨_, (chartRing_sub_locAt hsp hxy I c.2).2⟩ : chartRing k y I) ihu
      rwa [chartRing_smul_def] at this
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨l, rfl⟩
    exact Submodule.subset_span ⟨h l, mem_sub_of_isVeryAmpleBy hV l _, rfl⟩

theorem exists_lineBundle_redSys (hV : IsVeryAmpleBy Nb.toSubSystem h) (hg0 : g ≠ 0)
    (hg : RedGood hxy Nb.toSubSystem g) (hgsec : ∀ I : Chart x, g ∈ Nb.sub I) :
    ∃ Q' : LineBundle k y, Q'.toSubSystem = redSys hxy Nb.toSubSystem g := by
  refine ⟨LineBundle.mk (SubFamily.mk (redSys hxy Nb.toSubSystem g) ?_) ?_ ?_, rfl⟩
  · intro I J hIJ z
    rw [redSys_sub_eq hsp hxy hV hg, redSys_sub_eq hsp hxy hV hg]
    exact res_mem_span_iff_exists_isUnit hIJ z
  · intro I
    rw [redSys_sub_eq hsp hxy hV hg]
    exact Submodule.fg_span (Set.finite_range _)
  · intro I
    obtain ⟨M, hM⟩ := Nb.invertible (liftChart hxy I)
    refine ⟨Submodule.span (chartRing k y I) ((fun m => redAt k x y (m * g)) '' M), ?_⟩
    have hA : ∀ {q m : Ω}, q ∈ Nb.sub (liftChart hxy I) → m ∈ M →
        q * m ∈ chartRing k x (liftChart hxy I) :=
      fun hq hm => mul_mem_chartRing_of_mul_eq_one hM hq hm
    have hmg : ∀ {m : Ω}, m ∈ M → m * g ∈ locAt k x y := fun hm =>
      (chartRing_sub_locAt hsp hxy I (by rw [mul_comm]; exact hA (hgsec _) hm)).1
    have hsplit : ∀ q m : Ω, q * m = q / g * (m * g) := fun q m => by field_simp
    apply le_antisymm
    · change Submodule.span _ _ * Submodule.span _ _ ≤ 1
      rw [Submodule.span_mul_span, Submodule.span_le]
      rintro _ ⟨_, ⟨q, hq, rfl⟩, _, ⟨m, hm, rfl⟩, rfl⟩
      show redAt k x y (q / g) * redAt k x y (m * g) ∈ (1 : Submodule (chartRing k y I) K')
      rw [← (locAt_mul hsp (hg I q hq) (hmg hm)).2, ← hsplit]
      exact Submodule.mem_one.mpr ⟨⟨_, (chartRing_sub_locAt hsp hxy I (hA hq hm)).2⟩, rfl⟩
    · rw [Submodule.one_le]
      have h1 : (1 : Ω) ∈ Nb.sub (liftChart hxy I) * M := by
        rw [hM]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
      have := Submodule.mul_induction_on (C := fun z => z ∈ locAt k x y ∧ redAt k x y z ∈
          (redSys hxy Nb.toSubSystem g).sub I *
            Submodule.span (chartRing k y I) ((fun m => redAt k x y (m * g)) '' M)) h1
        (fun q hq m hm => ⟨(chartRing_sub_locAt hsp hxy I (hA hq hm)).1, by
          rw [hsplit, (locAt_mul hsp (hg I q hq) (hmg hm)).2]
          exact Submodule.mul_mem_mul (Submodule.subset_span ⟨q, hq, rfl⟩)
            (Submodule.subset_span ⟨m, hm, rfl⟩)⟩)
        (fun u v hu hv => ⟨(locAt_add hsp hu.1 hv.1).1, by
          rw [(locAt_add hsp hu.1 hv.1).2]; exact Submodule.add_mem _ hu.2 hv.2⟩)
      rw [(locAt_one hsp).2] at this
      exact this.2

theorem restrictData_redSys (hg : RedGood hxy Nb.toSubSystem g) (Q' : LineBundle k y)
    (hQ : Q'.toSubSystem = redSys hxy Nb.toSubSystem g) :
    RestrictData Nb.toSubSystem hxy Q'.toSubSystem (fun q => redAt k x y (q / g)) := by
  rw [hQ]
  exact
    { mem := fun I q hq => Submodule.subset_span ⟨q, hq, rfl⟩
      add := fun I q hq q' hq' => by
        rw [add_div]; exact (locAt_add hsp (hg I q hq) (hg I q' hq')).2
      smul := fun I q hq f s e hs hf hse => by
        have hsy : aeval y s ≠ 0 := eval_ne_zero_of_mem_monos I hs
        rw [mul_div_assoc, (locAt_mul hsp (mem_locAt hf hse hsy) (hg I q hq)).2,
          redAt_eq hsp hf hse hsy]
      span := fun I => rfl }

variable {σ : Ω}

theorem ne_zero_of_redAt_div (hσ : σ / g ∈ locAt k x y) (hσr : redAt k x y (σ / g) ≠ 0) : σ ≠ 0 :=
  fun h0 => (locAt_inv hsp hσ hσr).1 (by rw [h0, zero_div])

theorem redAt_mem_ampleChart (hg : RedGood hxy Nb.toSubSystem g) (Q' : LineBundle k y)
    (hQ : Q'.toSubSystem = redSys hxy Nb.toSubSystem g) (hσ : σ / g ∈ locAt k x y)
    (hσr : redAt k x y (σ / g) ≠ 0) (I : Chart y) {c : Ω}
    (hc : c ∈ ampleChart Nb.toSubSystem 1 σ (liftChart hxy I)) :
    c ∈ locAt k x y ∧ redAt k x y c ∈ ampleChart Q'.toSubSystem 1 (redAt k x y (σ / g)) I := by
  obtain ⟨n, hn⟩ := hc
  rw [one_mul] at hn
  have hpow := redSys_pow hsp hxy hg n
  have h1 : c * σ ^ n / g ^ n ∈ locAt k x y := hpow.1 I _ hn
  have hσ0 := ne_zero_of_redAt_div hsp hσ hσr
  have hg0 : g ≠ 0 := fun h0 => (locAt_inv hsp hσ hσr).1 (by rw [h0, div_zero])
  have hσn := locAt_pow hsp hσ n
  have hσnr : redAt k x y ((σ / g) ^ n) ≠ 0 := by rw [hσn.2]; exact pow_ne_zero _ hσr
  have hc_eq : c * σ ^ n / g ^ n / (σ / g) ^ n = c := by rw [div_pow]; field_simp
  obtain ⟨hcl, hcr⟩ := locAt_div hsp h1 hσn.1 hσnr
  rw [hc_eq] at hcl hcr
  refine ⟨hcl, n, ?_⟩
  rw [one_mul, hQ, ← hpow.2, hcr, hσn.2, div_mul_cancel₀ _ (pow_ne_zero _ hσr)]
  exact Submodule.subset_span ⟨_, hn, rfl⟩

theorem exists_lift_ampleChart (hg : RedGood hxy Nb.toSubSystem g) (Q' : LineBundle k y)
    (hQ : Q'.toSubSystem = redSys hxy Nb.toSubSystem g) (hσ : σ / g ∈ locAt k x y)
    (hσr : redAt k x y (σ / g) ≠ 0) (I : Chart y) {a : K'}
    (ha : a ∈ ampleChart Q'.toSubSystem 1 (redAt k x y (σ / g)) I) :
    ∃ e ∈ ampleChart Nb.toSubSystem 1 σ (liftChart hxy I), redAt k x y e = a := by
  obtain ⟨n, hn⟩ := ha
  have hpow := redSys_pow hsp hxy hg n
  rw [one_mul, hQ, ← hpow.2, mem_redSys_iff hsp hxy hpow.1] at hn
  obtain ⟨q, hq, hqa⟩ := hn
  have hσ0 := ne_zero_of_redAt_div hsp hσ hσr
  have hg0 : g ≠ 0 := fun h0 => (locAt_inv hsp hσ hσr).1 (by rw [h0, div_zero])
  refine ⟨q / σ ^ n, ⟨n, by rw [one_mul, div_mul_cancel₀ _ (pow_ne_zero _ hσ0)]; exact hq⟩, ?_⟩
  have hσn := locAt_pow hsp hσ n
  have hσnr : redAt k x y ((σ / g) ^ n) ≠ 0 := by rw [hσn.2]; exact pow_ne_zero _ hσr
  have heq : q / σ ^ n = q / g ^ n / (σ / g) ^ n := by rw [div_pow]; field_simp
  rw [heq, (locAt_div hsp (hpow.1 I q hq) hσn.1 hσnr).2, hqa, hσn.2,
    mul_div_cancel_right₀ _ (pow_ne_zero _ hσr)]

theorem redAt_mem_ampleBase (hg0 : g ≠ 0) (hgl : ∀ l, h l / g ∈ locAt k x y) {j : Fin (r + 1)}
    (hr : redAt k x y (h j / g) ≠ 0) {z : Ω} (hz : z ∈ ampleBase (S := k) h j) :
    z ∈ locAt k x y ∧
      redAt k x y z ∈ ampleBase (S := k) (fun l => redAt k x y (h l / g)) j := by
  refine Algebra.adjoin_induction (p := fun z _ => z ∈ locAt k x y ∧
    redAt k x y z ∈ ampleBase (S := k) (fun l => redAt k x y (h l / g)) j) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨l, rfl⟩
    dsimp only
    rw [← div_div_div_cancel_right₀ hg0 (h l) (h j)]
    obtain ⟨h1, h2⟩ := locAt_div hsp (hgl l) (hgl j) hr
    exact ⟨h1, by rw [h2]; exact Algebra.subset_adjoin ⟨l, rfl⟩⟩
  · intro c
    obtain ⟨h1, h2⟩ := locAt_algebraMap hsp c
    exact ⟨h1, by rw [h2]; exact Subalgebra.algebraMap_mem _ c⟩
  · intro u v _ _ hu hv
    obtain ⟨h1, h2⟩ := locAt_add hsp hu.1 hv.1
    exact ⟨h1, by rw [h2]; exact add_mem hu.2 hv.2⟩
  · intro u v _ _ hu hv
    obtain ⟨h1, h2⟩ := locAt_mul hsp hu.1 hv.1
    exact ⟨h1, by rw [h2]; exact mul_mem hu.2 hv.2⟩

theorem subset_support_of_redAt_ne_zero (hg : RedGood hxy Nb.toSubSystem g)
    (hσ : σ / g ∈ locAt k x y) (hσr : redAt k x y (σ / g) ≠ 0) (I₀ : Chart y) {b : Ω}
    (hb : b ∈ locAt k x y) (hbr : redAt k x y b ≠ 0) {J : Chart x}
    (hbJ : ∀ I : Chart x, ∃ e : ℕ,
      b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card) ∈ ampleChart Nb.toSubSystem 1 σ I) :
    J.1 ⊆ support y := by
  obtain ⟨e, he⟩ := hbJ (liftChart hxy I₀)
  have h1 : b ^ e * (xProd (liftChart hxy I₀) ^ J.1.card / xProd J ^ (liftChart hxy I₀).1.card) ∈
      locAt k x y := by
    obtain ⟨n, hn⟩ := he
    rw [one_mul] at hn
    have hpow := redSys_pow hsp hxy hg n
    have hc1 := hpow.1 I₀ _ hn
    have hσn := locAt_pow hsp hσ n
    have hσnr : redAt k x y ((σ / g) ^ n) ≠ 0 := by rw [hσn.2]; exact pow_ne_zero _ hσr
    have hσ0 := ne_zero_of_redAt_div hsp hσ hσr
    have hg0 : g ≠ 0 := fun h0 => (locAt_inv hsp hσ hσr).1 (by rw [h0, div_zero])
    have := (locAt_div hsp hc1 hσn.1 hσnr).1
    convert this using 1
    rw [div_pow]; field_simp
  have hbe := locAt_pow hsp hb e
  have hber : redAt k x y (b ^ e) ≠ 0 := by rw [hbe.2]; exact pow_ne_zero _ hbr
  have hb0 : b ≠ 0 := (locAt_inv hsp hb hbr).1
  have ht := (locAt_div hsp h1 hbe.1 hber).1
  rw [mul_div_cancel_left₀ _ (pow_ne_zero _ hb0)] at ht
  have hf := (res_isHomogeneous_prod_X (S := k) J.1).pow I₀.1.card
  have hs : ((∏ l ∈ I₀.1, (X l : Poly k N)) ^ J.1.card).IsHomogeneous (J.1.card * I₀.1.card) := by
    rw [mul_comm]; exact (res_isHomogeneous_prod_X (S := k) I₀.1).pow J.1.card
  have hsy : aeval y ((∏ l ∈ I₀.1, (X l : Poly k N)) ^ J.1.card) ≠ 0 := by
    rw [map_pow, res_aeval_prod_X]; exact pow_ne_zero _ (res_xProd_ne_zero I₀)
  have hti : (xProd (liftChart hxy I₀) ^ J.1.card / xProd J ^ (liftChart hxy I₀).1.card)⁻¹ =
      aeval x ((∏ l ∈ J.1, (X l : Poly k N)) ^ I₀.1.card) /
        aeval x ((∏ l ∈ I₀.1, (X l : Poly k N)) ^ J.1.card) := by
    rw [inv_div, map_pow, map_pow, res_aeval_prod_X, res_aeval_prod_X]; rfl
  have ht0 : xProd (liftChart hxy I₀) ^ J.1.card / xProd J ^ (liftChart hxy I₀).1.card ≠ 0 :=
    div_ne_zero (pow_ne_zero _ (res_xProd_ne_zero _)) (pow_ne_zero _ (res_xProd_ne_zero _))
  have hmem := mem_locAt (x := x) hf hs hsy
  rw [← hti] at hmem
  have hmul := (locAt_mul hsp ht hmem).2
  rw [mul_inv_cancel₀ ht0, (locAt_one hsp).2, hti, redAt_eq hsp hf hs hsy] at hmul
  have hJy : aeval y ((∏ l ∈ J.1, (X l : Poly k N)) ^ I₀.1.card) ≠ 0 := by
    intro h0; rw [h0, zero_div, mul_zero] at hmul; exact one_ne_zero hmul
  rw [map_pow, res_aeval_prod_X] at hJy
  intro i hi
  exact (mem_support y).mpr (Finset.prod_ne_zero_iff.mp (pow_ne_zero_iff
    (Finset.card_pos.mpr I₀.2.1).ne' |>.mp hJy) i hi)

end

end GroundTheory.Heights₂.Heights.Kleiman
