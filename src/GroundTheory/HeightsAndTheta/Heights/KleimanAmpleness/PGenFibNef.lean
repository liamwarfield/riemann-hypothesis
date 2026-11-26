module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleZFamily

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGenFibNef
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver)
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing blockWeight IsMultiHomog IsMultiProjPrime gradedPiece hilbFn intNum
  genFib)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

namespace GenFibNef

section Transport

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {F₁ F₂ : Type} [Field F₁] [Field F₂] (e : F₁ ≃+* F₂)


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem isMultiHomog_map_iff (f : MRing ι F₁) (b : K → ℕ) :
    NumbersDVR.IsMultiHomog (map (e : F₁ →+* F₂) f) b ↔ NumbersDVR.IsMultiHomog f b := by
  unfold NumbersDVR.IsMultiHomog IsWeightedHomogeneous
  simp only [coeff_map, ne_eq, RingHom.coe_coe, EmbeddingLike.map_eq_zero_iff]

noncomputable def quotEquiv (P : Ideal (MRing ι F₁)) :
    (MRing ι F₁ ⧸ P) ≃+* (MRing ι F₂ ⧸ P.map (map (e : F₁ →+* F₂))) :=
  Ideal.quotientEquiv P _ (mapEquiv (Σ k, ι k) e) (by
    congr 1)


omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem quotEquiv_mk (P : Ideal (MRing ι F₁)) (f : MRing ι F₁) :
    quotEquiv e P (Ideal.Quotient.mk P f) = Ideal.Quotient.mk _ (map (e : F₁ →+* F₂) f) := rfl


omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem quotEquiv_smul (P : Ideal (MRing ι F₁)) (r : F₁) (x : MRing ι F₁ ⧸ P) :
    quotEquiv e P (r • x) = e r • quotEquiv e P x := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h₁ : r • Ideal.Quotient.mk P f = Ideal.Quotient.mk P (C r * f) := by
    rw [← Ideal.Quotient.mkₐ_eq_mk F₁, ← map_smul, smul_eq_C_mul]
  have h₂ : e r • Ideal.Quotient.mk (P.map (map (e : F₁ →+* F₂))) (map (e : F₁ →+* F₂) f) =
      Ideal.Quotient.mk (P.map (map (e : F₁ →+* F₂))) (C (e r) * map (e : F₁ →+* F₂) f) := by
    rw [← Ideal.Quotient.mkₐ_eq_mk F₂, ← map_smul, smul_eq_C_mul]
  rw [h₁, quotEquiv_mk, quotEquiv_mk, h₂, map_mul, map_C]
  rfl


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem quotEquiv_mem_gradedPiece (P : Ideal (MRing ι F₁)) (n : K → ℕ) (x : MRing ι F₁ ⧸ P)
    (hx : x ∈ gradedPiece P n) : quotEquiv e P x ∈ gradedPiece (P.map (map (e : F₁ →+* F₂))) n := by
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hx
  refine Submodule.mem_map.2 ⟨map (e : F₁ →+* F₂) f, ?_, rfl⟩
  rw [mem_weightedHomogeneousSubmodule] at hf ⊢
  exact (isMultiHomog_map_iff e f n).2 hf

theorem finrank_gradedPiece_map (P : Ideal (MRing ι F₁)) (n : K → ℕ) :
    Module.finrank F₂ (gradedPiece (P.map (map (e : F₁ →+* F₂))) n) =
      Module.finrank F₁ (gradedPiece P n) := by
  let j₀ : gradedPiece P n →+ gradedPiece (P.map (map (e : F₁ →+* F₂))) n :=
    { toFun := fun x => ⟨quotEquiv e P x.1, quotEquiv_mem_gradedPiece e P n x.1 x.2⟩
      map_zero' := Subtype.ext (map_zero (quotEquiv e P))
      map_add' := fun a b => Subtype.ext (map_add (quotEquiv e P) a.1 b.1) }
  have hinj : Function.Injective j₀ := fun a b h =>
    Subtype.ext ((quotEquiv e P).injective (congrArg Subtype.val h))
  have hsurj : Function.Surjective j₀ := by
    rintro ⟨z, hz⟩
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.1 hz
    have hg' : map (e.symm : F₂ →+* F₁) g ∈ weightedHomogeneousSubmodule F₁ (blockWeight ι) n := by
      rw [mem_weightedHomogeneousSubmodule] at hg ⊢
      have hgg : map (e : F₁ →+* F₂) (map (e.symm : F₂ →+* F₁) g) = g :=
        (mapEquiv (Σ k, ι k) e).apply_symm_apply g
      have h' : NumbersDVR.IsMultiHomog (map (e : F₁ →+* F₂) (map (e.symm : F₂ →+* F₁) g)) n := by
        rw [hgg]
        exact hg
      exact (isMultiHomog_map_iff e _ n).1 h'
    refine ⟨⟨Ideal.Quotient.mk P (map (e.symm : F₂ →+* F₁) g), Submodule.mem_map.2 ⟨_, hg', rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change quotEquiv e P (Ideal.Quotient.mk P (map (e.symm : F₂ →+* F₁) g)) = Ideal.Quotient.mk _ g
    rw [quotEquiv_mk]
    congr 1
    exact (mapEquiv (Σ k, ι k) e).apply_symm_apply g
  let j := AddEquiv.ofBijective j₀ ⟨hinj, hsurj⟩
  have hrank := rank_eq_of_equiv_equiv (e : F₁ → F₂) j e.bijective (fun r m => by
    apply Subtype.ext
    exact quotEquiv_smul e P r m)
  unfold Module.finrank
  rw [hrank]

theorem hilbFn_map (P : Ideal (MRing ι F₁)) :
    hilbFn (P.map (map (e : F₁ →+* F₂))) = hilbFn P := by
  funext m
  unfold hilbFn
  split_ifs
  · rw [finrank_gradedPiece_map]
  · rfl

theorem intNum_map (P : Ideal (MRing ι F₁)) {n : ℕ} (bs : Fin n → K → ℤ) :
    intNum F₂ (P.map (map (e : F₁ →+* F₂))) bs = intNum F₁ P bs := by
  unfold intNum
  rw [hilbFn_map]

end Transport

end GenFibNef

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestrictGenerated
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace RestrictGenerated

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {K' : Type w} [Field K'] [Algebra S K'] {y : Fin (N + 1) → K'}
  {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}


variable (y) in
def toChartY (I : Chart x) (h : ∀ i ∈ I.1, y i ≠ 0) : Chart y :=
  ⟨I.1, I.2.1, fun i hi => (mem_support y).mpr (h i hi)⟩

theorem liftChart_toChartY (I : Chart x) (h : ∀ i ∈ I.1, y i ≠ 0) :
    liftChart hxy (toChartY y I h) = I := rfl

theorem r_zero {Q : SubSystem S x Ω} {Q' : SubSystem S y K'} {r : Ω → K'}
    (h : RestrictData Q hxy Q' r) (J : Chart y) : r 0 = 0 := by
  have := h.add J 0 (Q.sub _).zero_mem 0 (Q.sub _).zero_mem
  rw [add_zero] at this
  simpa using this

theorem r_sub {Q : SubSystem S x Ω} {Q' : SubSystem S y K'} {r : Ω → K'}
    (h : RestrictData Q hxy Q' r) (J : Chart y) {u v : Ω}
    (hu : u ∈ Q.sub (liftChart hxy J)) (hv : v ∈ Q.sub (liftChart hxy J)) :
    r (u - v) = r u - r v := by
  have := h.add J (u - v) (sub_mem hu hv) v hv
  rw [sub_add_cancel] at this
  exact eq_sub_of_add_eq this.symm

theorem exists_of_mem {Q : SubSystem S x Ω} {Q' : SubSystem S y K'} {r : Ω → K'}
    (h : RestrictData Q hxy Q' r) (J : Chart y) {t : K'} (ht : t ∈ Q'.sub J) :
    ∃ w ∈ Q.sub (liftChart hxy J), r w = t := by
  rw [← h.span J] at ht
  induction ht using Submodule.span_induction with
  | mem t ht => obtain ⟨w, hw, rfl⟩ := ht; exact ⟨w, hw, rfl⟩
  | zero => exact ⟨0, zero_mem _, r_zero h J⟩
  | add t t' _ _ ht ht' =>
    obtain ⟨w, hw, rfl⟩ := ht
    obtain ⟨w', hw', rfl⟩ := ht'
    exact ⟨w + w', add_mem hw hw', h.add J w hw w' hw'⟩
  | smul b t _ ht =>
    obtain ⟨w, hw, rfl⟩ := ht
    obtain ⟨f, s, e, hs, hf, hse, hb⟩ := b.2
    let a : chartRing S x (liftChart hxy J) := ⟨aeval x f / aeval x s, f, s, e, hs, hf, hse, rfl⟩
    refine ⟨a • w, (Q.sub _).smul_mem a hw, ?_⟩
    show r (aeval x f / aeval x s * w) = (b : K') * r w
    rw [h.smul J w hw f s e hs hf hse, hb]

theorem sub_ne_bot (Q' : LineBundle S y) (J : Chart y) : Q'.toSubSystem.sub J ≠ ⊥ := by
  intro h0
  obtain ⟨Q'', hQ''⟩ := Q'.invertible J
  have h1 : (1 : K') ∈ (1 : Submodule (chartRing S y J) K') := Submodule.mem_one.mpr ⟨1, map_one _⟩
  rw [← hQ''] at h1
  change (1 : K') ∈ Q'.toSubSystem.sub J * Q'' at h1
  rw [h0, Submodule.bot_mul] at h1
  exact one_ne_zero ((Submodule.mem_bot _).mp h1)

theorem mem_twist_of_eq_zero (Q : LineBundle S x) (Q' : LineBundle S y) {r : Ω → K'}
    {pp : Ideal (Poly S N)} (hpp : primeOf (S := S) y = pp)
    (h : RestrictData Q.toSubSystem hxy Q'.toSubSystem r) (J : Chart y) {z : Ω}
    (hz : z ∈ Q.toSubSystem.sub (liftChart hxy J)) (hr : r z = 0) :
    z ∈ (Q.toSubSystem.twist (idealSys x pp)).sub (liftChart hxy J) := by
  obtain ⟨w₀, hw₀, hrw₀⟩ : ∃ w ∈ Q.toSubSystem.sub (liftChart hxy J), r w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply sub_ne_bot Q' J
    rw [← h.span J, Submodule.span_eq_bot]
    rintro _ ⟨w, hw, rfl⟩
    exact hcon w hw
  obtain ⟨Q'', hQ''⟩ := Q.invertible (liftChart hxy J)
  have hmulA : ∀ u ∈ Q.toSubSystem.sub (liftChart hxy J), ∀ v ∈ Q'',
      u * v ∈ chartRing S x (liftChart hxy J) := by
    intro u hu v hv
    have : u * v ∈ Q.toSubSystem.sub (liftChart hxy J) * Q'' := Submodule.mul_mem_mul hu hv
    change u * v ∈ Q.sub (liftChart hxy J) * Q'' at this
    rw [hQ''] at this
    obtain ⟨b, hb⟩ := Submodule.mem_one.mp this
    rw [← hb]; exact b.2
  have hkey : ∀ v ∈ Q'', z * v ∈ idealMod (x := x) pp (liftChart hxy J) := by
    intro v hv
    obtain ⟨f, s, e, hs, hf, hse, ha⟩ := hmulA z hz v hv
    obtain ⟨g, t, e', ht, hg, hte, hb⟩ := hmulA w₀ hw₀ v hv
    have h1 := h.smul J w₀ hw₀ f s e hs hf hse
    have h2 := h.smul J z hz g t e' ht hg hte
    have heq : aeval x f / aeval x s * w₀ = aeval x g / aeval x t * z := by
      rw [← ha, ← hb]; ring
    rw [heq, h2, hr, mul_zero] at h1
    have hs0 : aeval y s ≠ 0 := eval_ne_zero_of_mem_monos J hs
    have hfy : aeval y f = 0 :=
      (div_eq_zero_iff.mp ((mul_eq_zero.mp h1.symm).resolve_right hrw₀)).resolve_right hs0
    have hfp : f ∈ pp := by
      rw [← hpp]; exact (mem_primeOf_of_isHomogeneous y hf).mpr hfy
    rw [ha]
    exact Submodule.subset_span ⟨f, s, e, hfp, hs, hf, hse, rfl⟩
  have hall : ∀ m ∈ Q.sub (liftChart hxy J) * Q'',
      z * m ∈ (Q.toSubSystem.twist (idealSys x pp)).sub (liftChart hxy J) := by
    intro m hm
    induction hm using Submodule.mul_induction_on' with
    | mem_mul_mem q hq v hv =>
      refine Submodule.subset_span ⟨z * v, hkey v hv, q, hq, ?_⟩
      rw [smul_eq_mul]; ring
    | add m _ m' _ hm hm' => rw [mul_add]; exact add_mem hm hm'
  have h1 : (1 : Ω) ∈ Q.sub (liftChart hxy J) * Q'' := by
    rw [hQ'']; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  simpa using hall 1 h1

end RestrictGenerated


open RestrictGenerated in
theorem RestrictGenerated.proof : RestrictGenerated.Statement.{u, w} := by
  intro S _ Ω _ _ N x K' _ _ y hxy pp _ hyp Q Q' r h hgen I
  have hX : ∀ i, (X i : Poly S N) ∈ pp ↔ y i = 0 := fun i => by
    rw [← hyp, mem_primeOf_of_isHomogeneous y (isHomogeneous_X S i), aeval_X]
  have hQtw : ∀ (I' : Chart x) (i : Fin (N + 1)), i ∈ I'.1 → y i = 0 →
      Q.toSubSystem.sub I' ≤ (Q.toSubSystem.twist (idealSys x pp)).sub I' := fun I' i hi hyi =>
    StepThree.OnW.Gen.sub_le_twist_idealSys_of_mem _ I' hi ((hX i).mpr hyi)
  by_cases hI : ∀ i ∈ I.1, y i ≠ 0
  swap
  · push Not at hI
    obtain ⟨i, hi, hyi⟩ := hI
    exact le_sup_of_le_right (hQtw I i hi hyi)

  have hlift : ∀ t ∈ Q'.toSubSystem.secs, ∃ s : Chart x → Ω, (∀ I', s I' ∈ Q.toSubSystem.sub I') ∧
      (∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 →
        s I₁ - s I₂ ∈ (Q.toSubSystem.twist (idealSys x pp)).sub I₂) ∧
      ∀ (I' : Chart x) (hI' : ∀ i ∈ I'.1, y i ≠ 0), r (s I') = t := by
    intro t ht
    have ht' : ∀ J, t ∈ Q'.toSubSystem.sub J := fun J => (Submodule.mem_iInf _).mp ht J
    choose w hw hrw using fun J => exists_of_mem h J (ht' J)
    classical
    have hmem : ∀ I', (if hI' : ∀ i ∈ I'.1, y i ≠ 0 then w (toChartY y I' hI') else 0) ∈
        Q.toSubSystem.sub I' := by
      intro I'
      split_ifs with hI'
      · have := hw (toChartY y I' hI')
        rwa [liftChart_toChartY] at this
      · exact zero_mem _
    refine ⟨fun I' => if hI' : ∀ i ∈ I'.1, y i ≠ 0 then w (toChartY y I' hI') else 0, hmem,
      fun I₁ I₂ h12 => ?_, fun I' hI' => ?_⟩
    · by_cases h2 : ∀ i ∈ I₂.1, y i ≠ 0
      · have h1 : ∀ i ∈ I₁.1, y i ≠ 0 := fun i hi => h2 i (h12 hi)
        have hm1 := Q.toSubSystem.mono I₁ I₂ h12 _ (hw (toChartY y I₁ h1))
        have hm2 := hw (toChartY y I₂ h2)
        dsimp only
        rw [dite_eq_left h1, dite_eq_left h2]
        exact mem_twist_of_eq_zero Q Q' hyp h (toChartY y I₂ h2) (sub_mem hm1 hm2)
          (by rw [r_sub h (toChartY y I₂ h2) hm1 hm2, hrw, hrw, sub_self])
      · push Not at h2
        obtain ⟨i, hi, hyi⟩ := h2
        exact hQtw I₂ i hi hyi (sub_mem (Q.toSubSystem.mono I₁ I₂ h12 _ (hmem I₁)) (hmem I₂))
    · dsimp only
      rw [dite_eq_left hI']
      exact hrw _
  let J : Chart y := toChartY y I hI
  have hJ : ∀ t ∈ Q'.toSubSystem.sub J, ∃ u ∈ Submodule.span (chartRing S x I)
      {z | ∃ s : Chart x → Ω, (∀ I', s I' ∈ Q.toSubSystem.sub I') ∧
        (∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → s I₁ - s I₂ ∈ (Q.toSubSystem.twist (idealSys x pp)).sub I₂) ∧
        z = s I}, u ∈ Q.toSubSystem.sub I ∧ r u = t := by
    intro t ht
    rw [← hgen J] at ht
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨s, hs, hc, hr⟩ := hlift t ht
      exact ⟨s I, Submodule.subset_span ⟨s, hs, hc, rfl⟩, hs I, hr I hI⟩
    | zero => exact ⟨0, zero_mem _, zero_mem _, r_zero h J⟩
    | add t t' _ _ ht ht' =>
      obtain ⟨u, hu, hu', rfl⟩ := ht
      obtain ⟨v, hv, hv', rfl⟩ := ht'
      exact ⟨u + v, add_mem hu hv, add_mem hu' hv', h.add J u hu' v hv'⟩
    | smul b t _ ht =>
      obtain ⟨u, hu, hu', rfl⟩ := ht
      obtain ⟨f, s, e, hs, hf, hse, hb⟩ := b.2
      let a : chartRing S x I := ⟨aeval x f / aeval x s, f, s, e, hs, hf, hse, rfl⟩
      refine ⟨a • u, Submodule.smul_mem _ a hu, Submodule.smul_mem _ a hu', ?_⟩
      show r (aeval x f / aeval x s * u) = (b : K') * r u
      rw [h.smul J u hu' f s e hs hf hse, hb]
  intro q hq
  obtain ⟨u, hu, hu', hru⟩ := hJ (r q) (h.mem J q hq)
  have hd : q - u ∈ (Q.toSubSystem.twist (idealSys x pp)).sub I :=
    mem_twist_of_eq_zero Q Q' hyp h J (sub_mem hq hu') (by rw [r_sub h J hq hu', hru, sub_self])
  rw [show q = u + (q - u) by abel]
  exact Submodule.add_mem_sup hu hd

end

end GroundTheory.Heights₂.Heights.Kleiman
end
