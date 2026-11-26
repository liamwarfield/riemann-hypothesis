module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellHOfCellSec
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSegreBase
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideSide

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PBundlePair
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open scoped Pointwise
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver GeneratesOver)

noncomputable section

section FirstTyping

variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}

theorem twist_sub_eq_mul (F Q : Kleiman.SubSystem S x Ω) (I : Kleiman.Chart x) :
    (F.twist Q).sub I = Q.sub I * F.sub I := by
  rw [Submodule.mul_eq_span_mul_set]
  change Submodule.span _ _ = _
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_mul, SetLike.mem_coe, smul_eq_mul]
  constructor
  · rintro ⟨q, hq, w, hw, rfl⟩
    exact ⟨q, hq, w, hw, rfl⟩
  · rintro ⟨q, hq, w, hw, rfl⟩
    exact ⟨q, hq, w, hw, rfl⟩

theorem exists_mul_eq_prod_pow {I : Finset (Fin (N + 1))} {s : Kleiman.Poly S N} (hs : s ∈ Kleiman.monos I) :
    ∃ (r d d' : ℕ) (s' : Kleiman.Poly S N), s.IsHomogeneous d ∧ s'.IsHomogeneous d' ∧
      d + d' = r * I.card ∧ s * s' = (∏ j ∈ I, X j) ^ r := by
  classical
  induction hs using Submonoid.closure_induction with
  | mem z hz =>
    obtain ⟨j, hj, rfl⟩ := hz
    have hj' : j ∈ I := by exact_mod_cast hj
    refine ⟨1, 1, (I.erase j).card, ∏ l ∈ I.erase j, X l, isHomogeneous_X S j, ?_, ?_, ?_⟩
    · simpa using IsHomogeneous.prod (I.erase j) (fun l => (X l : Kleiman.Poly S N)) (fun _ => 1)
        (fun l _ => isHomogeneous_X S l)
    · rw [one_mul, add_comm]
      exact Finset.card_erase_add_one hj'
    · rw [pow_one]
      exact Finset.mul_prod_erase I (fun l => (X l : Kleiman.Poly S N)) hj'
  | one => exact ⟨0, 0, 0, 1, isHomogeneous_one _ _, isHomogeneous_one _ _, by simp, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨r, d, d', s', h1, h2, h3, h4⟩ := ha
    obtain ⟨r₂, d₂, d₂', t', g1, g2, g3, g4⟩ := hb
    refine ⟨r + r₂, d + d₂, d' + d₂', s' * t', h1.mul g1, h2.mul g2, by rw [add_mul]; omega, ?_⟩
    rw [pow_add, ← h4, ← g4]
    ring

theorem mem_sub_iff_gam (Q : Kleiman.LineBundle S x) (I : Kleiman.Chart x) (t : Ω) :
    t ∈ Q.sub I ↔ ∃ n : ℕ, Kleiman.xProd I ^ n * t ∈ Q.gam ((n * I.1.card : ℕ) : ℤ) := by
  classical
  have hxI : Kleiman.xProd I ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi => (Kleiman.mem_support x).mp (I.2.2 hi)
  have hprod : ∀ r : ℕ, aeval x ((∏ j ∈ I.1, (X j : Kleiman.Poly S N)) ^ r) = Kleiman.xProd I ^ r := by
    intro r
    simp [Kleiman.xProd, map_prod]
  constructor
  · intro ht
    obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (Kleiman.mem_support x).mp (I.2.2 hi)
    have hsub : (Kleiman.singleChart hxi).1 ⊆ I.1 := Finset.singleton_subset_iff.mpr hi
    obtain ⟨a, ⟨u, hu⟩, hat⟩ := (Q.mem_iff _ I hsub t).mp ht
    have hev : ∀ᶠ n : ℕ in Filter.atTop, ∀ J, x i ^ n • ((a : Ω) • t) ∈
        (Q.twist (Kleiman.twistSys S x (n : ℤ))).sub J :=
      Filter.eventually_all.mpr fun J =>
        Kleiman.ExtensionProof.eventually_pow_smul_mem Q.toSubFamily hxi hat J
    obtain ⟨n, hn⟩ := hev.exists
    have hgam : x i ^ n • ((a : Ω) • t) ∈ Q.gam (n : ℤ) := Kleiman.ExtensionProof.mem_gam.mpr hn
    have hinv : (a : Ω) * ((↑u⁻¹ : Kleiman.chartRing S x I) : Ω) = 1 := by
      have := congrArg Subtype.val (Units.mul_inv u)
      rw [hu] at this
      exact this
    obtain ⟨g, s, r, hs, hg, hsr, hb⟩ := (↑u⁻¹ : Kleiman.chartRing S x I).2
    obtain ⟨r', d, d', s', hsd, hs', hdd, hss⟩ := exists_mul_eq_prod_pow hs
    have hs0 : aeval x s ≠ 0 := Kleiman.eval_ne_zero_of_mem_monos I hs
    have hrd : r = d := hsr.inj_right hsd (fun h => hs0 (by rw [h, map_zero]))
    subst hrd
    have h1 : (∏ l ∈ I.1.erase i, (X l : Kleiman.Poly S N)).IsHomogeneous (I.1.erase i).card := by
      simpa using IsHomogeneous.prod (I.1.erase i) (fun l => (X l : Kleiman.Poly S N)) (fun _ => 1)
        (fun l _ => isHomogeneous_X S l)
    have hPh := ((h1.pow n).mul hg).mul hs'
    have hmem := Kleiman.ExtensionProof.smul_mem_gam Q.toSubSystem hPh hgam
    refine ⟨n + r', ?_⟩
    have hc := Finset.card_erase_add_one hi
    have hdeg : ((n : ℤ) + (((I.1.erase i).card * n + r + d' : ℕ) : ℤ)) =
        (((n + r') * I.1.card : ℕ) : ℤ) := by
      rw [← hc] at hdd ⊢
      have hdd' : ((r : ℤ) + d') = r' * ((I.1.erase i).card + 1) := by exact_mod_cast hdd
      push_cast
      linear_combination hdd'
    rw [hdeg] at hmem
    convert hmem using 1
    have hag : (a : Ω) * aeval x g = aeval x s := by
      rw [hb] at hinv
      field_simp at hinv
      linear_combination hinv
    have hss' : aeval x s * aeval x s' = (x i * ∏ l ∈ I.1.erase i, x l) ^ r' := by
      have := congrArg (aeval x) hss
      simp only [map_mul, map_pow, map_prod, aeval_X] at this
      rw [this, Finset.mul_prod_erase I.1 x hi]
    simp only [smul_eq_mul, map_mul, map_pow, map_prod, aeval_X, Kleiman.xProd]
    rw [← Finset.mul_prod_erase I.1 x hi]
    linear_combination (-(x i * ∏ l ∈ I.1.erase i, x l) ^ n * t) * hss' +
      (-(x i * ∏ l ∈ I.1.erase i, x l) ^ n * t * aeval x s') * hag
  · rintro ⟨n, hn⟩
    have h1 := (Kleiman.ExtensionProof.mem_gam.mp hn) I
    have hs : (∏ j ∈ I.1, (X j : Kleiman.Poly S N)) ^ n ∈ Kleiman.monos I.1 :=
      pow_mem (prod_mem fun j hj => Kleiman.X_mem_monos hj) n
    have hsh : ((∏ j ∈ I.1, (X j : Kleiman.Poly S N)) ^ n).IsHomogeneous (I.1.card * n) := by
      have := IsHomogeneous.prod I.1 (fun l => (X l : Kleiman.Poly S N)) (fun _ => 1)
        (fun l _ => isHomogeneous_X S l)
      simpa using this.pow n
    have h2 := Kleiman.ExtensionProof.inv_smul_mem Q.toSubSystem h1 hs hsh (by push_cast; ring)
    rw [hprod, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hxI), one_mul] at h2
    exact h2

end FirstTyping

section SecondTyping

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type} [Field Ω]
  [Algebra S Ω]

theorem mem_secOver_iff_charts (y : (Σ k, ι k) → Ω) (δ : K → ℤ) (t : Ω) :
    t ∈ secOver S y δ ↔ ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      t * ∏ k, y ⟨k, c k⟩ ^ (-δ k) ∈ chartRingOver S y c := by
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]

end SecondTyping

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RelDimMIdealOverEqTrdeg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open GroundTheory.Heights₂.Heights.NumbersDVR (segreVec)

theorem relDim_mIdealOver_eq_trdeg {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ t : ℕ, Algebra.trdeg F (chartRingOver F y c) = t ∧
      relDim (mIdealOver F y) = ((t : ℕ) : WithBot (WithTop ℤ)) := by
  have hy := trdeg_quotient_mIdealOver (F := F) y c hc
  have _ : (mIdealOver F y).IsPrime := RingHom.ker_isPrime _
  have hfin := trdeg_lt_aleph0_of_finiteType (R := F) (S := MvPolynomial (Σ k, ι k) F ⧸ mIdealOver F y)
  rw [hy] at hfin
  obtain ⟨t, ht⟩ := Cardinal.lt_aleph0.1 (lt_of_le_of_lt le_self_add hfin)
  have dimy : ringKrullDim (MvPolynomial (Σ k, ι k) F ⧸ mIdealOver F y) =
      ((t + Fintype.card K : ℕ) : ℕ∞) := by
    rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F, hy, ht]
    simp
  refine ⟨t, ht, ?_⟩
  unfold relDim
  rw [dimy]
  have e₁ : WithBot.map (fun d : ℕ∞ => WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) d)
      ((((t + Fintype.card K : ℕ) : ℕ∞)) : WithBot ℕ∞) =
      (((((t + Fintype.card K : ℕ) : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := rfl
  rw [e₁, Nat.cast_add, add_sub_cancel_right]
  rfl

theorem SegreDim.proof : SegreDim.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y hy
  choose c hc using hy
  obtain ⟨t, ht, hrel⟩ := relDim_mIdealOver_eq_trdeg (F := F) y c hc
  obtain ⟨t', ht', hrel'⟩ := relDim_mIdealOver_eq_trdeg (F := F) (segreJoin y) (segreChart c c)
    (segreChart_adm y (segreVec_ne_zero y hc) hc)
  have heq : chartRingOver F (segreJoin y) (segreChart c c) = chartRingOver F y c :=
    le_antisymm (segre_diag_le (S := F) y c) (chartRingOver_le_segre (S := F) y c c)
  rw [heq, ht] at ht'
  have htt : t = t' := by exact_mod_cast ht'
  rw [hrel, hrel', htt]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MemMIdealOverIff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver)

noncomputable section

section Homog

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]

theorem aeval_mul_block (v : (Σ k, ι k) → Ω) (c : K → Ω) (b : K → ℕ) (g : MvPolynomial (Σ k, ι k) S)
    (hg : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) g b) :
    aeval (fun p => v p * c p.1) g = aeval v g * ∏ k, c k ^ b k := by
  have hb : ∀ e ∈ g.support, ∀ k, ∑ i, e ⟨k, i⟩ = b k := by
    intro e he k
    rw [sum_block_eq_blockWeight, hg (mem_support_iff.mp he)]
  have h2 : ((MvPolynomial.aeval c : MvPolynomial K Ω →ₐ[Ω] Ω).restrictScalars S).comp (mConeMapOver S v) =
      aeval fun p => v p * c p.1 := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMapOver]
  rw [← h2, AlgHom.comp_apply, AlgHom.restrictScalars_apply, mConeMapOver_eq_of_block v hb, map_mul, map_prod,
    aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
  simp only [map_pow, aeval_X]

theorem mem_mIdealOver_iff (y : (Σ k, ι k) → Ω) (f : MvPolynomial (Σ k, ι k) S) :
    f ∈ mIdealOver S y ↔
      ∀ b : K → ℕ, aeval y (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f) = 0 := by
  constructor
  · intro hf b
    rw [← coeff_mConeMapOver, RingHom.mem_ker.mp hf, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  · intro h
    refine RingHom.mem_ker.mpr (MvPolynomial.ext _ _ fun d => ?_)
    have := coeff_mConeMapOver (S := S) y (⇑d) f
    rw [Finsupp.equivFunOnFinite_symm_coe] at this
    rw [this, h, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]

end Homog

theorem CurveLift.full : CurveLift.Statement := by
  intro k _ N Ω _ _ x Q n m s _hx hgen pp e hW
  have hpp := hW.isPrime
  obtain ⟨i, hXi⟩ := hW.relevant
  have hi : x i ≠ 0 := fun h0 => hXi (hW.le (by
    rw [Kleiman.mem_primeOf_of_isHomogeneous x (isHomogeneous_X k i), aeval_X, h0]))
  have hPt := Kleiman.PrimeFiltration.Point.proof k Ω N x pp hpp hW.homog hW.le i hi hXi

  obtain ⟨K', _, _, ψ, hker⟩ : ∃ (K' : Type) (_ : Field K') (_ : Algebra k K')
      (ψ : Kleiman.chartRing k x (Kleiman.singleChart hi) →ₐ[k] K'),
      RingHom.ker ψ = Kleiman.chartPrime pp hi := by
    have : (Kleiman.chartPrime pp hi).IsPrime := hPt.1
    refine ⟨FractionRing (Kleiman.chartRing k x (Kleiman.singleChart hi) ⧸ Kleiman.chartPrime pp hi),
      inferInstance, inferInstance,
      (IsScalarTower.toAlgHom k _ _).comp (Ideal.Quotient.mkₐ k (Kleiman.chartPrime pp hi)), ?_⟩
    ext a
    rw [RingHom.mem_ker]
    change algebraMap _ (FractionRing (Kleiman.chartRing k x (Kleiman.singleChart hi) ⧸ Kleiman.chartPrime pp hi))
      (Ideal.Quotient.mk (Kleiman.chartPrime pp hi) a) = 0 ↔ _
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hy : Kleiman.primeOf (S := k) (fun a => ψ (Kleiman.ratio hi a)) = pp := hPt.2 K' ψ hker

  have hiI : i ∈ (Kleiman.singleChart hi).1 := Finset.mem_singleton_self i
  let g : Fin m → Ω := fun b => x i ^ (-n) * s b
  have hgQ : Submodule.span (Kleiman.chartRing k x (Kleiman.singleChart hi)) (Set.range g) =
      Q.sub (Kleiman.singleChart hi) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      have hb : s b ∈ (Q.twist (Kleiman.twistSys k x n)).sub (Kleiman.singleChart hi) := by
        rw [← hgen]; exact Submodule.subset_span ⟨b, rfl⟩
      obtain ⟨y, hy, hyb⟩ := (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem n _ hiI (s b)).mp hb
      have : g b = y := by
        simp only [g, hyb, smul_eq_mul, zpow_neg]
        field_simp
      rw [SetLike.mem_coe, this]
      exact hy
    · intro y hy
      have hy' : x i ^ n * y ∈ Submodule.span (Kleiman.chartRing k x (Kleiman.singleChart hi)) (Set.range s) := by
        rw [hgen]
        exact (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem n _ hiI _).mpr ⟨y, hy, rfl⟩
      obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hy'
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨a, ?_⟩
      simp only [g, Subalgebra.smul_def, smul_eq_mul] at ha ⊢
      have : ∑ b, (a b : Ω) * (x i ^ (-n) * s b) = x i ^ (-n) * ∑ b, (a b : Ω) * s b := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
      rw [this, ha, zpow_neg]
      field_simp

  obtain ⟨Q', hQQ⟩ := Q.invertible (Kleiman.singleChart hi)
  rw [← hgQ] at hQQ
  have hone : (1 : Ω) ∈ Submodule.span (Kleiman.chartRing k x (Kleiman.singleChart hi)) (Set.range g) * Q' := by
    rw [hQQ]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  obtain ⟨w, hwQ, hsum⟩ : ∃ w : Fin m → Ω, (∀ b, w b ∈ Q') ∧ ∑ b, g b * w b = 1 := by
    refine Submodule.mul_induction_on
      (C := fun z => ∃ w : Fin m → Ω, (∀ b, w b ∈ Q') ∧ ∑ b, g b * w b = z) hone ?_ ?_
    · intro q hq q' hq'
      obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hq
      refine ⟨fun b => (a b : Ω) * q', fun b => Q'.smul_mem (a b) hq', ?_⟩
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Subalgebra.smul_def, smul_eq_mul]
      ring
    · rintro _ _ ⟨w, hw, rfl⟩ ⟨w', hw', rfl⟩
      refine ⟨w + w', fun b => Q'.add_mem (hw b) (hw' b), ?_⟩
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by simp [mul_add]
  have hgA : ∀ a b, g a * w b ∈ Kleiman.chartRing k x (Kleiman.singleChart hi) := by
    intro a b
    have h := Submodule.mul_mem_mul
      (Submodule.subset_span ⟨a, rfl⟩ : g a ∈ Submodule.span (Kleiman.chartRing k x (Kleiman.singleChart hi))
        (Set.range g)) (hwQ b)
    rw [hQQ, Submodule.mem_one] at h
    obtain ⟨z, hz⟩ := h
    rw [← hz]
    exact z.2

  obtain ⟨j0, hj0⟩ : ∃ j0, ψ ⟨g j0 * w j0, hgA j0 j0⟩ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h1 : (1 : Kleiman.chartRing k x (Kleiman.singleChart hi)) = ∑ j, ⟨g j * w j, hgA j j⟩ :=
      Subtype.ext (by simp [hsum])
    have h2 := congrArg ψ h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_one, map_sum] at h2
    simp [hcon] at h2
  let t : Fin m → K' := fun b => ψ ⟨g b * w j0, hgA b j0⟩
  refine ⟨mIdealOver k (graphVec (fun a => ψ (Kleiman.ratio hi a)) t),
    isMultiProjPrime_mIdealOver_graph _ _ ⟨i, ?_⟩ ⟨j0, hj0⟩, ?_, by rw [comap_mIdealOver_graph, hy]⟩
  · have : Kleiman.ratio (S := k) hi i = 1 := Subtype.ext (div_self hi)
    rw [this, map_one]
    exact one_ne_zero
  · intro f hf
    rw [mem_mIdealOver_iff] at hf ⊢
    intro b
    have hfb := weightedHomogeneousComponent_isWeightedHomogeneous (w := NumbersDVR.blockWeight (graphIdx N m)) b f
    let u : (Σ c, graphIdx N m c) → Kleiman.chartRing k x (Kleiman.singleChart hi) := fun p =>
      match p with
      | ⟨Sum.inl (), a⟩ => Kleiman.ratio hi a
      | ⟨Sum.inr (), c⟩ => ⟨g c * w j0, hgA c j0⟩
    have hu : (fun p => (u p : Ω)) = fun p => graphVec x s p *
        (Sum.elim (fun _ : Unit => (x i)⁻¹) (fun _ : Unit => x i ^ (-n) * w j0)) p.1 := by
      funext p
      rcases p with ⟨⟨⟩ | ⟨⟩, a⟩
      · change x a / x i = x a * (x i)⁻¹
        rw [div_eq_mul_inv]
      · change x i ^ (-n) * s a * w j0 = s a * (x i ^ (-n) * w j0)
        ring
    have h0 : aeval u (weightedHomogeneousComponent (NumbersDVR.blockWeight (graphIdx N m)) b f) = 0 := by
      apply Subtype.ext
      change (Kleiman.chartRing k x (Kleiman.singleChart hi)).val (aeval u _) = 0
      rw [comp_aeval_apply]
      change aeval (fun p => (u p : Ω)) _ = 0
      rw [hu, aeval_mul_block _ _ b _ hfb, hf b, zero_mul]
    have hψu : (fun p => ψ (u p)) = graphVec (fun a => ψ (Kleiman.ratio hi a)) t := by
      funext p
      rcases p with ⟨⟨⟩ | ⟨⟩, a⟩ <;> rfl
    rw [← hψu, ← comp_aeval_apply, h0, map_zero]

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def ModelGenerated.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ β : K → ℤ,
      ∃ c₀ : ℤ, ∀ c : ℤ, c₀ ≤ c → IndefiniteRowSideFullHecke.Kleiman2.IsGenerated F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def RowChartAct.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ)
    (e : ι k₀ ≃ Fin (N + 1)) (γ : K → ℤ) (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm))
    (I : ∀ k, Finset (ι k)) (r a : Ω),
    r ∈ Kleiman.chartRing (S := S) (x := IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J →
    a ∈ cellSec S y γ (baseCell k₀ e J.1 I) → r * a ∈ cellSec S y γ (baseCell k₀ e J.1 I)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideMore
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def RowSub.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ)
    (e : ι k₀ ≃ Fin (N + 1)) (γ : K → ℤ) (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm))
    (I : ∀ k, Finset (ι k)),
    (∀ k, (I k).Nonempty) → CellMeets y I →
      chartSecOver S y k₀ e γ J ⊆ cellSec S y γ (baseCell k₀ e J.1 I)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailTail
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)

def SpanSecs.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ (T : Set Ω) (d : ℤ) (s : Ω),
        s ∈ (⨅ I : Kleiman.Chart x,
            (Submodule.span (Kleiman.chartRing F x I) T * Kleiman.twistMod F x d I).restrictScalars F) ↔
          ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
            s * y ⟨k₀, c k₀⟩ ^ (-d) ∈ Submodule.span (chartRingOver F y c) T

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ZpowMemSubalgebraOfInvMem
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2 (pullDeg baseDeg)
open GroundTheory.Heights₂.Heights.NumbersDVR (segreVec)

section Twist

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)

theorem zpow_mem_subalgebra_of_inv_mem (A : Subalgebra S Ω) {u : Ω} (hu : u ∈ A) (hu' : u⁻¹ ∈ A) (n : ℤ) :
    u ^ n ∈ A := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast]
    exact pow_mem hu m
  · rw [zpow_neg, zpow_natCast, ← inv_pow]
    exact pow_mem hu' m

theorem prod_segreChart_twist (d c : ∀ k, ι k) (β : K → ℤ) (n : ℤ) :
    ∏ k, segreJoin y ⟨k, segreChart d c k⟩ ^ (-(pullDeg β + n • baseDeg (Sum.inl ()) : Unit ⊕ K → ℤ) k) =
      segreVec y d ^ (-n) * ∏ k, y ⟨k, c k⟩ ^ (-β k) := by
  rw [Fintype.prod_sum_type]
  simp [pullDeg, baseDeg]
  rfl


omit [DecidableEq K] in
theorem prod_add_const (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (β : K → ℤ) (n : ℤ) :
    ∏ k, y ⟨k, c k⟩ ^ (-(β + fun _ => n : K → ℤ) k) = segreVec y c ^ (-n) * ∏ k, y ⟨k, c k⟩ ^ (-β k) := by
  have e : ∀ k, y ⟨k, c k⟩ ^ (-(β + fun _ => n : K → ℤ) k) = y ⟨k, c k⟩ ^ (-n) * y ⟨k, c k⟩ ^ (-β k) := fun k => by
    rw [Pi.add_apply, neg_add, zpow_add₀ (hc k), mul_comm]
  simp only [e, Finset.prod_mul_distrib, Finset.prod_zpow]
  rfl

theorem secOver_segreJoin_twist (β : K → ℤ) (n : ℤ) :
    secOver S (segreJoin y) (pullDeg β + n • baseDeg (Sum.inl ())) = secOver S y (β + fun _ => n) := by
  ext s
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]
  constructor
  · intro h c hc
    have := h (segreChart c c) (segreChart_adm y (segreVec_ne_zero y hc) hc)
    rw [prod_segreChart_twist] at this
    rw [prod_add_const y c hc]
    exact segre_diag_le y c this
  · intro h C hC
    obtain ⟨d, c, rfl⟩ := segreChart_eta C
    have hd : segreVec y d ≠ 0 := hC (Sum.inl ())
    have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => hC (Sum.inr k)
    have hc0 : segreVec y c ≠ 0 := segreVec_ne_zero y hc
    have hs := chartRingOver_le_segre y d c (h c hc)
    rw [prod_add_const y c hc] at hs
    set R := chartRingOver S (segreJoin y) (segreChart d c)
    have hu : segreVec y c / segreVec y d ∈ R := Algebra.subset_adjoin ⟨⟨Sum.inl (), c⟩, rfl⟩
    have hu' : (segreVec y c / segreVec y d)⁻¹ ∈ R := by
      rw [inv_div]
      exact chartRingOver_le_segre y d c (segreVec_div_mem y c d)
    have e : s * (segreVec y d ^ (-n) * ∏ k, y ⟨k, c k⟩ ^ (-β k)) =
        s * (segreVec y c ^ (-n) * ∏ k, y ⟨k, c k⟩ ^ (-β k)) * (segreVec y c / segreVec y d) ^ n := by
      rw [div_zpow, zpow_neg, zpow_neg]
      field_simp
    rw [prod_segreChart_twist, e]
    exact mul_mem hs (zpow_mem_subalgebra_of_inv_mem R hu hu' n)

end Twist

theorem SegreTwist.proof : SegreTwist.Statement := by
  intro S _ K _ _ ι _ Ω _ _ y _ β c
  exact secOver_segreJoin_twist y β c

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockEqAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver chartRingOver secOver secMOver)

noncomputable section

section OneBlock

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]

variable {κ : Type} [Fintype κ]


omit [Fintype κ] in
theorem chartRingOver_oneBlock_eq (x : κ → Ω) (c : Unit → κ) :
    chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) c = Algebra.adjoin F (Set.range fun i => x i / x (c ())) := by
  unfold chartRingOver
  congr 1
  ext z
  constructor
  · rintro ⟨⟨⟨⟩, a⟩, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨(), a⟩, rfl⟩


omit [Fintype κ] in
theorem mem_secOver_oneBlock (x : κ → Ω) (n : ℤ) (t : Ω) :
    t ∈ secOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => n) ↔
      ∀ j, x j ≠ 0 → t * x j ^ (-n) ∈ Algebra.adjoin F (Set.range fun i => x i / x j) := by
  unfold secOver
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply, Finset.univ_unique,
    Finset.prod_singleton, Subalgebra.mem_toSubmodule, chartRingOver_oneBlock_eq]
  constructor
  · intro h j hj
    exact h (fun _ => j) (fun _ => hj)
  · intro h c hc
    exact h (c ()) (hc ())


omit [Fintype κ] in
theorem secOver_oneBlock_comp {κ' : Type} (σ : κ' ≃ κ) (x : κ → Ω) (n : ℤ) :
    secOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (x ∘ σ)) (fun _ => n) = secOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => n) := by
  ext t
  rw [mem_secOver_oneBlock, mem_secOver_oneBlock]
  have hr : ∀ j', Set.range (fun i' => x (σ i') / x (σ j')) = Set.range (fun i => x i / x (σ j')) :=
    fun j' => σ.surjective.range_comp (fun i => x i / x (σ j'))
  simp only [Function.comp_apply]
  constructor
  · intro h j hj
    obtain ⟨j', rfl⟩ := σ.surjective j
    have := h j' hj
    rwa [hr] at this
  · intro h j' hj'
    rw [hr]
    exact h (σ j') hj'


omit [Fintype κ] in
theorem relDim_oneBlock_eq_iff (P : Ideal (MvPolynomial (Σ _ : Unit, κ) F)) (e : ℕ) :
    FieldNumbers.relDim P = ((e : ℕ) : WithBot (WithTop ℤ)) ↔
      ringKrullDim (MvPolynomial (Σ _ : Unit, κ) F ⧸ P) = ((e + 1 : ℕ) : WithBot ℕ∞) := by
  rw [FieldNumbers.CutRegular.relDim_eq_natCast_iff, Fintype.card_unit]

end OneBlock

section FirstTyping

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω] {N : ℕ}

theorem twistSys_secs_eq_secOver (x : Fin (N + 1) → Ω) (n : ℤ) :
    (Kleiman.twistSys F x n).secs = secOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => n) := by
  ext t
  rw [mem_secs_iff, mem_secOver_oneBlock]
  refine forall_congr' fun j => forall_congr' fun hj => ?_
  change t ∈ Kleiman.twistMod F x n (Kleiman.singleChart hj) ↔ _
  rw [Kleiman.twistMod_eq_span n _ (Finset.mem_singleton_self j), Submodule.mem_span_singleton]
  have hA : Kleiman.chartRing F x (Kleiman.singleChart hj) =
      Algebra.adjoin F (Set.range fun i => x i / x j) :=
    (chartRingOver_oneBlock x (fun _ => j) hj).symm.trans (chartRingOver_oneBlock_eq x (fun _ => j))
  rw [← hA]
  have hxn : x j ^ n ≠ 0 := zpow_ne_zero n hj
  constructor
  · rintro ⟨a, rfl⟩
    rw [Kleiman.chartRing_smul_def, zpow_neg, mul_assoc, mul_inv_cancel₀ hxn, mul_one]
    exact a.2
  · intro h
    refine ⟨⟨_, h⟩, ?_⟩
    rw [Kleiman.chartRing_smul_def]
    show t * x j ^ (-n) * x j ^ n = t
    rw [zpow_neg]
    exact inv_mul_cancel_right₀ hxn t

theorem mIdealOver_oneBlock (x : Fin (N + 1) → Ω) :
    mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) = Kleiman.primeOfOne (S := F) x := by
  have hc : ((MvPolynomial.uniqueAlgEquiv Ω Unit).toAlgHom.restrictScalars F).comp
      (mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x)) = (Kleiman.cone (S := F) x).comp (Kleiman.oneBlock (S := F) (N := N)) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMapOver, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, Kleiman.cone, Kleiman.oneBlock, ReciprocityTheory.ChartRestriction.G.Geo.coneMap]
  ext f
  rw [mIdealOver, RingHom.mem_ker, Kleiman.primeOfOne, Ideal.mem_comap, Kleiman.primeOf_eq, RingHom.mem_ker]
  have h := congrArg (fun φ => φ f) hc
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at h
  rw [← h]
  exact (map_eq_zero_iff _ (MvPolynomial.uniqueAlgEquiv Ω Unit).injective).symm

theorem isSubvar_primeOf_iff (x : Fin (N + 1) → Ω) (e : ℕ) :
    Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) e ↔
      (∃ i, x i ≠ 0) ∧ ringKrullDim (Kleiman.Poly F N ⧸ Kleiman.primeOf (S := F) x) = ((e + 1 : ℕ) : WithBot ℕ∞) := by
  have hX : ∀ i, (X i : Kleiman.Poly F N) ∈ Kleiman.primeOf (S := F) x ↔ x i = 0 := fun i => by
    rw [Kleiman.mem_primeOf_of_isHomogeneous x (isHomogeneous_X F i), aeval_X]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := h.relevant
    exact ⟨⟨i, fun hx => hi ((hX i).mpr hx)⟩, h.dim⟩
  · rintro ⟨⟨i, hi⟩, hdim⟩
    exact ⟨inferInstance, fun p hp d => Kleiman.homogeneousComponent_mem_primeOf x hp d, le_rfl,
      ⟨i, fun h => hi ((hX i).mp h)⟩, hdim⟩

theorem isSubvar_iff_relDim (x : Fin (N + 1) → Ω) (e : ℕ) :
    Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) e ↔
      (∃ i, x i ≠ 0) ∧ FieldNumbers.relDim (mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x)) = ((e : ℕ) : WithBot (WithTop ℤ)) := by
  rw [isSubvar_primeOf_iff, relDim_oneBlock_eq_iff, mIdealOver_oneBlock, HilbertPositive.ringKrullDim_primeOfOne]

end FirstTyping

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem ModelDim.proof : ModelDim.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hmod n
  subst hx
  exact ModelDimEq.full F K ι Ω y k₀ N e hmod n

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerMore
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def CellZeroConst.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)
    (s : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0 → Ω),
    cellD S y 0 s = 0 →
      ∀ c c' : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0, CellMeets y c.1 → CellMeets y c'.1 → s c = s c'

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideTer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def RowSecGlue.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ)
    (e : ι k₀ ≃ Fin (N + 1)) (γ : K → ℤ) (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (a : Ω),
    (∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → a ∈ cellSec S y γ (baseCell k₀ e J.1 fun k => {c k})) →
      a ∈ chartSecOver S y k₀ e γ J

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerBis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def CechContract.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (Ω : Type) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (G : Kleiman.Chart x → Submodule S Ω) (J₀ : Kleiman.Chart x),
    J₀.1.card = 1 →
    (∀ J J' : Kleiman.Chart x, J.1 ⊆ J'.1 → G J ≤ G J') →
    (∀ J J' : Kleiman.Chart x, J'.1 = J₀.1 ∪ J.1 → G J' = G J) →
    CechAugExact S G (G J₀)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraBis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def ModelRowExact.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ)
    (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ (γ : K → ℤ)
      (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)),
      CellAugExact F y (fun I => cellSec F y γ (baseCell k₀ e J.1 I))
        (Submodule.span F (chartSecOver F y k₀ e γ J))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreMore
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def DoubleCech.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (N : ℕ)
    (x : Fin (N + 1) → Ω) (T : Kleiman.SubSystem F x Ω) (B : (∀ k, Finset (ι k)) → Submodule F Ω)
    (M : Kleiman.Chart x → (∀ k, Finset (ι k)) → Submodule F Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∃ j, x j ≠ 0) →
    (∀ I, ¬ CellMeets y I → B I = ⊥) →
    (∀ J I, ¬ CellMeets y I → M J I = ⊥) →
    (∀ (J J' : Kleiman.Chart x) I, J.1 ⊆ J'.1 → M J I ≤ M J' I) →
    (∀ J (I I' : ∀ k, Finset (ι k)), (∀ k, I k ⊆ I' k) → CellMeets y I' → M J I ≤ M J I') →
    (∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → CellMeets y I → CechAugExact F (fun J => M J I) (B I)) →
    (∀ J, CellAugExact F y (M J) ((T.sub J).restrictScalars F)) →
    ∀ n : ℕ, Nonempty (T.H n ≃ₗ[F] cellHOf F y B n)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestFurther
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver)

def RatioDim.Statement : Prop :=
  ∀ (k : Type) [Field k] (N m : ℕ) (W : Ideal (NumbersDVR.MRing (graphIdx N m) k)), W.IsPrime →
    NumbersDVR.IsMultiHomogIdeal W → ∀ j : Fin m,
      (X ⟨Sum.inr (), j⟩ : NumbersDVR.MRing (graphIdx N m) k) ∉ W →
      (∀ b : Fin m, ∃ f g : Kleiman.Poly k N,
        rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) g ∉ W ∧
        rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) g * X ⟨Sum.inr (), b⟩ -
          rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) f * X ⟨Sum.inr (), j⟩ ∈ W) →
      ringKrullDim (NumbersDVR.MRing (graphIdx N m) k ⧸ W) =
        ringKrullDim (Kleiman.Poly k N ⧸ W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c))) + 1

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellPosExact
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

section

variable (S : Type) [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)] {Ω : Type} [Field Ω] [Algebra S Ω]

def CellPosExact (y : (Σ k, ι k) → Ω) (G : (∀ k, Finset (ι k)) → Submodule S Ω) : Prop :=
  ∀ q : ℕ, ∀ s ∈ cellCOf S G (q + 1), cellD S y (q + 1) s = 0 →
    ∃ t ∈ cellCOf S G q, cellD S y q t = s

end

def CellContract.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)
    (G : (∀ k, Finset (ι k)) → Submodule S Ω) (c : ∀ k, ι k),
    (∀ k, y ⟨k, c k⟩ ≠ 0) →
    (∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → ¬ CellMeets y I → G I = ⊥) →
    (∀ I I' : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → (∀ k, I k ⊆ I' k) → CellMeets y I' → G I ≤ G I') →
    (∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → ∀ k,
      G (Function.update I k (insert (c k) (I k))) = G I) →
    CellPosExact S y G

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSegreFibresNef
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime intNum)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

theorem segreFibresNef_of_map (hA : SegreLiftComap.Statement) (hB : SegreLiftPrime.Statement)
    (hC : SegreLiftRelDim.Statement) (hN : SegreLiftIntNum.Statement)
    (hD : SegreFibreIdeal.Statement) (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω]
    (F : Type) [Field F] (φ : O →+* F) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (β : K → ℤ) :
    IndefiniteRowSideFullHecke.Kleiman2.IsNefIdeal F ((mIdealOver O (segreJoin y)).map (MvPolynomial.map φ))
                              (IndefiniteRowSideFullHecke.Kleiman2.pullDeg β) ↔
      IndefiniteRowSideFullHecke.Kleiman2.IsNefIdeal F ((mIdealOver O y).map (MvPolynomial.map φ)) β := by
  obtain ⟨hrel, hle, hlift⟩ := hD O Ω F φ K ι y
  constructor
  · intro h W hW hPW hdim
    have hpos := h (segreLift ι F W) (hB F K ι W hW) (hlift W hPW)
      (by rw [hC F K ι W hW]; exact hdim)
    rwa [hN F K ι W hW β] at hpos
  · intro h W' hW' hPW' hdim
    obtain ⟨hWp, heq⟩ := hA F K ι W' hW' fun g hg => hPW' (hrel hg)
    have hPW : (mIdealOver O y).map (MvPolynomial.map φ) ≤ W'.comap (segreIncl ι F) :=
      hle.trans (Ideal.comap_mono hPW')
    have hdimW : relDim (W'.comap (segreIncl ι F)) = ((1 : ℕ) : WithBot (WithTop ℤ)) := by
      rw [← hC F K ι _ hWp, ← heq]
      exact hdim
    have hpos := h _ hWp hPW hdimW
    rw [heq, hN F K ι _ hWp β]
    exact hpos

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
