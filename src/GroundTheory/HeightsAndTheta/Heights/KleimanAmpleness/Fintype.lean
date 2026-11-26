module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsSumEqOneOfMulEqOne
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PBundlePair
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CechHcSubsingletonOfBlock
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockBase

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Fintype
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

instance graphIdx.fintype (N m : ℕ) : ∀ k, Fintype (graphIdx N m k) := fun k => by
  cases k <;> infer_instance

def ModelNefEq.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ (β : K → ℤ)
      (Q : Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)),
      (∀ c : ℤ, (Q.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).secs =
          secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) →
      (Kleiman.Nef Q.toSubSystem ↔ IndefiniteRowSideFullHecke.Kleiman2.IsNef F y β)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ZpowMemSubringOfInvMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

noncomputable section

section Base

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]

theorem mem_of_forall_mem_locIn (B : Subalgebra F Ω) {u : Ω}
    (h : ∀ p : Ideal B, p.IsMaximal → u ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn B p) : u ∈ B := by
  let I : Ideal B :=
    { carrier := {a | (a : Ω) * u ∈ B}
      add_mem' := fun {a b} ha hb => by
        show ((a : Ω) + b) * u ∈ B
        rw [add_mul]; exact B.add_mem ha hb
      zero_mem' := by show (0 : Ω) * u ∈ B; rw [zero_mul]; exact B.zero_mem
      smul_mem' := fun c a ha => by
        show ((c : Ω) * a) * u ∈ B
        rw [mul_assoc]; exact B.mul_mem c.2 ha }
  by_cases hI : I = ⊤
  · have h1 : (1 : B) ∈ I := hI ▸ Submodule.mem_top
    have h2 : ((1 : B) : Ω) * u ∈ B := h1
    simpa using h2
  · obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I hI
    have := hp.isPrime
    obtain ⟨a, b, hb, hu⟩ := mem_locIn.mp (h p hp)
    have hb0 : (b : Ω) ≠ 0 := coe_ne_zero_of_not_mem hb
    refine absurd (hIp ?_) hb
    show (b : Ω) * u ∈ B
    rw [hu, mul_div_cancel₀ _ hb0]
    exact a.2

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}


omit [Fintype K] [DecidableEq K] in
theorem adjoin_base_le (y : (Σ k, ι k) → Ω) (k₀ : K) (c : ∀ k, ι k) :
    Algebra.adjoin F (Set.range fun i => IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ i / IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ (c k₀)) ≤
      chartRingOver F y c := by
  rw [Algebra.adjoin_le_iff]
  rintro _ ⟨i, rfl⟩
  exact Algebra.subset_adjoin ⟨⟨k₀, i⟩, rfl⟩

theorem prod_baseDeg (y : (Σ k, ι k) → Ω) (k₀ : K) (c : ∀ k, ι k) (m : ℤ) :
    (∏ k, y ⟨k, c k⟩ ^ (-(m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) = y ⟨k₀, c k₀⟩ ^ (-m) := by
  rw [Finset.prod_eq_single k₀]
  · simp [IndefiniteRowSideFullHecke.Kleiman2.baseDeg]
  · intro k _ hk
    simp [IndefiniteRowSideFullHecke.Kleiman2.baseDeg, hk]
  · intro h; exact absurd (Finset.mem_univ k₀) h

theorem zpow_mem_subring_of_inv_mem (z : Subring Ω) {r : Ω} (hr : r ∈ z) (hr' : r⁻¹ ∈ z) (m : ℤ) : r ^ m ∈ z := by
  rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast]; exact z.pow_mem hr n
  · rw [zpow_neg, zpow_natCast, ← inv_pow]; exact z.pow_mem hr' n

theorem secOver_baseDeg_eq (y : (Σ k, ι k) → Ω) (k₀ : K) (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀) (m : ℤ) :
    secOver F y (m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) =
      secOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ => m) := by
  set x' := IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ with hx'
  have hmem : ∀ t, t ∈ secOver F y (m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) ↔
      ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → t * y ⟨k₀, c k₀⟩ ^ (-m) ∈ chartRingOver F y c := by
    intro t
    simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
      Subalgebra.mem_toSubmodule, prod_baseDeg]
  ext t
  rw [hmem, mem_secOver_oneBlock]
  constructor
  · intro ht j hj
    apply mem_of_forall_mem_locIn
    intro p hp
    have hpp := hp.isPrime
    have hz : IndefiniteRowSideFullHecke.Kleiman2.locIn _ p ∈ IndefiniteRowSideFullHecke.Kleiman2.modelPts F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') := by
      refine ⟨fun _ => j, fun _ => hj, ?_⟩
      rw [chartRingOver_oneBlock_eq]
      exact ⟨p, hp.isPrime, rfl⟩
    rw [← hy.2] at hz
    obtain ⟨c, hc, q, hq, hzq⟩ := hz
    have hA : ∀ a ∈ chartRingOver F y c, a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn _ p := fun a ha => by
      rw [hzq, mem_locIn]
      exact ⟨⟨a, ha⟩, 1, fun h => one_not_mem_of_prime hq h, by simp⟩
    have hB : ∀ a ∈ Algebra.adjoin F (Set.range fun i => x' i / x' j), a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn _ p :=
      fun a ha => mem_locIn.mpr ⟨⟨a, ha⟩, 1, fun h => one_not_mem_of_prime hpp h, by simp⟩
    have hyc : y ⟨k₀, c k₀⟩ ≠ 0 := hc k₀
    have hr : y ⟨k₀, c k₀⟩ / x' j ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn _ p := hB _ (Algebra.subset_adjoin ⟨c k₀, rfl⟩)
    have hr' : (y ⟨k₀, c k₀⟩ / x' j)⁻¹ ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn _ p := by
      rw [inv_div]
      exact hA _ (Algebra.subset_adjoin ⟨⟨k₀, j⟩, rfl⟩)
    have e : t * x' j ^ (-m) = t * y ⟨k₀, c k₀⟩ ^ (-m) * (y ⟨k₀, c k₀⟩ / x' j) ^ m := by
      rw [div_zpow, zpow_neg, zpow_neg]
      field_simp
    rw [e]
    exact Subring.mul_mem _ (hA _ (ht c hc)) (zpow_mem_subring_of_inv_mem _ hr hr' m)
  · intro ht c hc
    exact adjoin_base_le y k₀ c (ht (c k₀) (hc k₀))

end Base

theorem BaseRealises.proof : BaseRealises.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hy b c
  rw [Kleiman.twistBundle_toSubSystem, Kleiman.twistSys_twist_twistSys, twistSys_secs_eq_secOver, ← add_smul,
    secOver_baseDeg_eq y k₀ hy, hx, secOver_oneBlock_comp]

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiProjPrimeSegreLift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime intNum)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

noncomputable section

namespace SegreNef

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem map_id_ideal {σ : Type*} (I : Ideal (MvPolynomial σ F)) :
    I.map (MvPolynomial.map (RingHom.id F)) = I := by
  have h : (MvPolynomial.map (RingHom.id F) : MvPolynomial σ F →+* MvPolynomial σ F) = RingHom.id _ :=
    RingHom.ext MvPolynomial.map_id
  rw [h, Ideal.map_id]

theorem comap_segreLift (W : Ideal (MRing ι F)) : (segreLift ι F W).comap (segreIncl ι F) = W := by
  have h : (segreLiftMap ι F W).comp (segreIncl ι F) =
      (Polynomial.CAlgHom : (MRing ι F ⧸ W) →ₐ[F] Polynomial (MRing ι F ⧸ W)).comp
        (Ideal.Quotient.mkₐ F W) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [segreIncl, segreLiftMap, segreLiftVal]
  ext g
  rw [Ideal.mem_comap, segreLift, RingHom.mem_ker]
  have hg := congrArg (fun φ => φ g) h
  simp only [AlgHom.comp_apply] at hg
  rw [hg, Polynomial.CAlgHom_apply, Polynomial.C_eq_zero, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem]

theorem genPt_block_ne_zero (W : Ideal (MRing ι F)) [W.IsPrime] (hW : IsMultiProjPrime W) :
    ∀ k, ∃ i, ModelGenericPoint.genPt W ⟨k, i⟩ ≠ 0 := fun k => by
  obtain ⟨i, hi⟩ := hW.relevant k
  exact ⟨i, (ModelGenericPoint.genPt_ne_zero W _).mpr hi⟩

theorem segreJoin_block_ne_zero {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) :
    ∀ k, ∃ i, segreJoin y ⟨k, i⟩ ≠ 0
  | Sum.inl () => ⟨fun k => (hy k).choose,
      show ∏ k, y ⟨k, (hy k).choose⟩ ≠ 0 from Finset.prod_ne_zero_iff.mpr fun k _ => (hy k).choose_spec⟩
  | Sum.inr k => hy k

theorem segreLift_eq_mIdealOver (W : Ideal (MRing ι F)) [W.IsPrime] (hW : IsMultiProjPrime W) :
    segreLift ι F W = mIdealOver F (segreJoin (ModelGenericPoint.genPt W)) := by
  have hy : mIdealOver F (ModelGenericPoint.genPt W) = W :=
    ModelGenericPoint.mIdealOver_genPt W hW.multiHomog
  have hP' : IsMultiProjPrime (mIdealOver F (segreJoin (ModelGenericPoint.genPt W))) :=
    isMultiProjPrime_mIdealOver _ (segreJoin_block_ne_zero _ (genPt_block_ne_zero W hW))
  obtain ⟨hrel, hle, hlift⟩ := SegreFibreIdeal.proof F _ F (RingHom.id F) K ι (ModelGenericPoint.genPt W)
  simp only [map_id_ideal] at hrel hle hlift
  have hc : (mIdealOver F (segreJoin (ModelGenericPoint.genPt W))).comap (segreIncl ι F) = W := by
    refine le_antisymm ?_ (hy.ge.trans hle)
    have h := hlift W hy.le
    exact (Ideal.comap_mono h).trans (comap_segreLift W).le
  calc segreLift ι F W
      = segreLift ι F ((mIdealOver F (segreJoin (ModelGenericPoint.genPt W))).comap (segreIncl ι F)) := by
        rw [hc]
    _ = _ := ((SegreLiftComap.proof F K ι _ hP' hrel).2).symm

theorem isMultiProjPrime_segreLift (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) :
    IsMultiProjPrime (segreLift ι F W) := by
  have := hW.isPrime
  rw [segreLift_eq_mIdealOver W hW]
  exact isMultiProjPrime_mIdealOver _ (segreJoin_block_ne_zero _ (genPt_block_ne_zero W hW))

end SegreNef

open SegreNef

theorem SegreLiftRelDim.proof_of_segreDim (hD : SegreDim.Statement) : SegreLiftRelDim.Statement := by
  intro F _ K _ _ ι _ W hW
  have := hW.isPrime
  rw [segreLift_eq_mIdealOver W hW,
    hD F K ι _ (ModelGenericPoint.genPt W) (genPt_block_ne_zero W hW),
    ModelGenericPoint.mIdealOver_genPt W hW.multiHomog]

theorem SegreLiftIntNum.proof_of_segreNum (hN : SegreNum.Statement) : SegreLiftIntNum.Statement := by
  intro F _ K _ _ ι _ W hW β
  have := hW.isPrime
  have h := hN F K ι _ (ModelGenericPoint.genPt W) (genPt_block_ne_zero W hW) 1 ![β]
  have hfun : (fun j : Fin 1 => IndefiniteRowSideFullHecke.Kleiman2.pullDeg (K₁ := Unit) (![β] j)) = ![IndefiniteRowSideFullHecke.Kleiman2.pullDeg β] := by
    funext j
    fin_cases j
    rfl
  rw [hfun, ModelGenericPoint.mIdealOver_genPt W hW.multiHomog] at h
  rw [segreLift_eq_mIdealOver W hW]
  exact h

theorem SegreNef.proof_of_lift (hC : SegreLiftRelDim.Statement) (hN : SegreLiftIntNum.Statement) :
    SegreNef.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y _ β
  have h := segreFibresNef_of_map SegreLiftComap.proof (fun F _ K _ _ ι _ W hW => isMultiProjPrime_segreLift W hW)
    hC hN SegreFibreIdeal.proof F Ω F (RingHom.id F) K ι y β
  rw [map_id_ideal, map_id_ideal] at h
  exact h

theorem SegreNef.proof (hD : SegreDim.Statement) (hN : SegreNum.Statement) : SegreNef.Statement :=
  SegreNef.proof_of_lift (SegreLiftRelDim.proof_of_segreDim hD) (SegreLiftIntNum.proof_of_segreNum hN)

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistModNatMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open scoped Pointwise
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

section Charts

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem PowRealises.twist_sub (G Q : Kleiman.SubSystem F x Ω) (I : Kleiman.Chart x) :
    (G.twist Q).sub I = Q.sub I * G.sub I := by
  rw [Submodule.mul_eq_span_mul_set]
  show Submodule.span _ _ = _
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_mul, SetLike.mem_coe, smul_eq_mul]
  constructor
  · rintro ⟨q, hq, g, hg, rfl⟩; exact ⟨q, hq, g, hg, rfl⟩
  · rintro ⟨q, hq, g, hg, rfl⟩; exact ⟨q, hq, g, hg, rfl⟩

theorem PowRealises.twistSys_sub (c : ℤ) (I : Kleiman.Chart x) :
    (Kleiman.twistSys F x c).sub I = Kleiman.twistMod F x c I := rfl

theorem PowRealises.twistMod_mul (a b : ℤ) (I : Kleiman.Chart x) :
    Kleiman.twistMod F x a I * Kleiman.twistMod F x b I = Kleiman.twistMod F x (a + b) I := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (Kleiman.mem_support x).mp (I.2.2 hi)
  rw [Kleiman.twistMod_eq_span a I hi, Kleiman.twistMod_eq_span b I hi, Kleiman.twistMod_eq_span (a + b) I hi,
    Submodule.span_mul_span, Set.singleton_mul_singleton, ← zpow_add₀ hxi]

theorem PowRealises.twistMod_zero (I : Kleiman.Chart x) : Kleiman.twistMod F x 0 I = 1 := by
  obtain ⟨i, hi⟩ := I.2.1
  rw [Kleiman.twistMod_eq_span 0 I hi, zpow_zero, Submodule.one_eq_span]

theorem PowRealises.twistMod_nat_mul (c : ℤ) (I : Kleiman.Chart x) :
    ∀ p : ℕ, Kleiman.twistMod F x ((p : ℤ) * c) I = Kleiman.twistMod F x c I ^ p
  | 0 => by rw [Nat.cast_zero, zero_mul, pow_zero]; exact PowRealises.twistMod_zero I
  | p + 1 => by
    rw [pow_succ', ← PowRealises.twistMod_nat_mul c I p, PowRealises.twistMod_mul]
    congr 1
    push_cast
    ring

theorem PowRealises.pow_sub (Q : Kleiman.SubSystem F x Ω) (I : Kleiman.Chart x) :
    ∀ p : ℕ, (Q.pow p).sub I = Q.sub I ^ p
  | 0 => by rw [pow_zero]; exact PowRealises.twistMod_zero I
  | p + 1 => by
    show ((Q.pow p).twist Q).sub I = _
    rw [PowRealises.twist_sub, PowRealises.pow_sub Q I p, pow_succ']

end Charts

section Model

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]

theorem PowRealises.mem_span_inv_iff (A : Subalgebra F Ω) {u z : Ω} (hu : u ≠ 0) :
    z ∈ Submodule.span A {u⁻¹} ↔ z * u ∈ A := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    rw [Subalgebra.smul_def, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hu, mul_one]
    exact a.2
  · intro h
    refine ⟨⟨z * u, h⟩, ?_⟩
    rw [Subalgebra.smul_def, smul_eq_mul]
    exact mul_inv_cancel_right₀ hu z

variable {K : Type} [Fintype K] {ι : K → Type}

theorem PowRealises.mem_secOver (y : (Σ k, ι k) → Ω) (n : K → ℤ) (s : Ω) :
    s ∈ secOver F y n ↔ ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      s * ∏ k, y ⟨k, c k⟩ ^ (-n k) ∈ chartRingOver F y c := by
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]

theorem PowRealises.span_secOver_eq (y : (Σ k, ι k) → Ω) (n : K → ℤ) (hg : IndefiniteRowSideFullHecke.Kleiman2.IsGenerated F y n)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    Submodule.span (chartRingOver F y c) (secOver F y n : Set Ω) =
      Submodule.span (chartRingOver F y c) {(∏ k, y ⟨k, c k⟩ ^ (-n k))⁻¹} := by
  have hu : (∏ k, y ⟨k, c k⟩ ^ (-n k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  apply le_antisymm
  · rw [Submodule.span_le]
    intro t ht
    exact (PowRealises.mem_span_inv_iff _ hu).mpr ((PowRealises.mem_secOver y n t).mp ht c hc)
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    obtain ⟨m, s, hs, hgen⟩ := hg
    obtain ⟨u, hu', hsum⟩ := hgen c hc
    have key : (∏ k, y ⟨k, c k⟩ ^ (-n k))⁻¹ =
        ∑ j, (⟨u j, hu' j⟩ : chartRingOver F y c) • s j := by
      rw [← one_mul (_⁻¹), ← hsum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Subalgebra.smul_def, smul_eq_mul, mul_assoc, mul_inv_cancel_right₀ hu]
    rw [key]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (hs j))

theorem PowRealises.prod_exp [DecidableEq K] (y : (Σ k, ι k) → Ω) (k₀ : K) (β : K → ℤ) (p : ℕ) (c d : ℤ)
    (cc : ∀ k, ι k) (hc : ∀ k, y ⟨k, cc k⟩ ≠ 0) :
    y ⟨k₀, cc k₀⟩ ^ (-d) * (∏ k, y ⟨k, cc k⟩ ^ (-(β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) ^ p =
      ∏ k, y ⟨k, cc k⟩ ^ (-(p • β + ((p : ℤ) * c + d) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) := by
  have h0 : y ⟨k₀, cc k₀⟩ ^ (-d) = ∏ k, y ⟨k, cc k⟩ ^ (-(d • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) := by
    rw [Finset.prod_eq_single k₀]
    · simp [IndefiniteRowSideFullHecke.Kleiman2.baseDeg]
    · intro k _ hk
      simp [IndefiniteRowSideFullHecke.Kleiman2.baseDeg, hk]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [h0, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ (hc k)]
  congr 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
  ring

end Model

theorem PowRealises.proof (hG : ModelGenerated.Statement) (hS : SpanSecs.Statement) : PowRealises.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hmod Q β hQ p ct
  obtain ⟨c₀, hc₀⟩ := Kleiman.Generated.full F Ω N x Q
  obtain ⟨c₁, hc₁⟩ := hG F K ι Ω y k₀ hmod β
  obtain ⟨c, hc0, hc1⟩ : ∃ c, c₀ ≤ c ∧ c₁ ≤ c := ⟨max c₀ c₁, le_max_left _ _, le_max_right _ _⟩
  have hgenQ := hc₀ c hc0
  have hgenY := hc₁ c hc1
  obtain ⟨d, rfl⟩ : ∃ d, ct = (p : ℤ) * c + d := ⟨ct - (p : ℤ) * c, by ring⟩
  have hchart : ∀ I : Kleiman.Chart x, (Kleiman.twistMul Q.toSubSystem p ((p : ℤ) * c + d)).sub I =
      Submodule.span (Kleiman.chartRing F x I)
          ((secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) ^ p) * Kleiman.twistMod F x d I := by
    intro I
    have h1 : (Q.toSubSystem.twist (Kleiman.twistSys F x c)).sub I =
        Submodule.span (Kleiman.chartRing F x I) (secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) := by
      rw [← hgenQ I, hQ c]
    rw [PowRealises.twist_sub, PowRealises.twistSys_sub] at h1
    show ((Q.toSubSystem.pow p).twist (Kleiman.twistSys F x ((p : ℤ) * c + d))).sub I = _
    rw [PowRealises.twist_sub, PowRealises.twistSys_sub, PowRealises.pow_sub, ← PowRealises.twistMod_mul,
      PowRealises.twistMod_nat_mul, ← Submodule.span_pow, ← h1, mul_pow]
    ring
  have hsecs : (Kleiman.twistMul Q.toSubSystem p ((p : ℤ) * c + d)).secs = ⨅ I : Kleiman.Chart x,
      (Submodule.span (Kleiman.chartRing F x I)
          ((secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) ^ p) *
        Kleiman.twistMod F x d I).restrictScalars F := by
    simp only [Kleiman.SubSystem.secs, hchart]
  ext s
  rw [hsecs, hS F K ι Ω y k₀ N e x hx hmod _ d s, PowRealises.mem_secOver]
  refine forall_congr' fun cc => forall_congr' fun hc => ?_
  have hu : (∏ k, y ⟨k, cc k⟩ ^ (-(β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  rw [← Submodule.span_pow, PowRealises.span_secOver_eq y _ hgenY cc hc, Submodule.span_pow, Set.singleton_pow,
    inv_pow, PowRealises.mem_span_inv_iff _ (pow_ne_zero _ hu), mul_assoc, PowRealises.prod_exp y k₀ β p c d cc hc]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.XMemMIdealOverIff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver)

noncomputable section

section Generic

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ a, Fintype (ι a)] {k : Type} [Field k]


omit [Fintype K] [DecidableEq K] [∀ a, Fintype (ι a)] in
theorem X_mem_mIdealOver_iff {Ω : Type} [Field Ω] [Algebra k Ω] (y : (Σ a, ι a) → Ω) (p : Σ a, ι a) :
    (X p : NumbersDVR.MRing ι k) ∈ mIdealOver k y ↔ y p = 0 := by
  change mConeMapOver k y (X p) = 0 ↔ _
  simp [mConeMapOver, X_ne_zero]

def genPtOf (W : Ideal (NumbersDVR.MRing ι k)) [W.IsPrime] :
    (Σ a, ι a) → FractionRing (NumbersDVR.MRing ι k ⧸ W) :=
  fun p => algebraMap _ _ (Ideal.Quotient.mk W (X p))


omit [Fintype K] [DecidableEq K] [∀ a, Fintype (ι a)] in
theorem aeval_genPtOf (W : Ideal (NumbersDVR.MRing ι k)) [W.IsPrime] (g : NumbersDVR.MRing ι k) :
    aeval (genPtOf W) g = algebraMap _ (FractionRing (NumbersDVR.MRing ι k ⧸ W)) (Ideal.Quotient.mk W g) := by
  have h : (aeval (genPtOf W) : NumbersDVR.MRing ι k →ₐ[k] FractionRing (NumbersDVR.MRing ι k ⧸ W)) =
      (IsScalarTower.toAlgHom k (NumbersDVR.MRing ι k ⧸ W) (FractionRing (NumbersDVR.MRing ι k ⧸ W))).comp
        (Ideal.Quotient.mkₐ k W) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [genPtOf]
  exact congrArg (fun φ : NumbersDVR.MRing ι k →ₐ[k] FractionRing (NumbersDVR.MRing ι k ⧸ W) => φ g) h

theorem mIdealOver_genPtOf (W : Ideal (NumbersDVR.MRing ι k)) [W.IsPrime] (hh : NumbersDVR.IsMultiHomogIdeal W) :
    mIdealOver k (genPtOf W) = W := by
  have hz : ∀ g, aeval (genPtOf W) g = 0 ↔ g ∈ W := fun g => by
    rw [aeval_genPtOf, ← Ideal.Quotient.eq_zero_iff_mem]
    exact (IsFractionRing.injective (NumbersDVR.MRing ι k ⧸ W) (FractionRing (NumbersDVR.MRing ι k ⧸ W))).eq_iff'
      (map_zero _)
  ext f
  change mConeMapOver k (genPtOf W) f = 0 ↔ f ∈ W
  constructor
  · intro h
    rw [← sum_weightedHomogeneousComponent (NumbersDVR.blockWeight ι) f,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
    refine Ideal.sum_mem _ fun b _ => (hz _).mp ?_
    rw [← coeff_mConeMapOver, h, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  · intro hf
    ext e
    rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply,
      ← Finsupp.equivFunOnFinite_symm_coe e, coeff_mConeMapOver]
    exact (hz _).mpr (hh f hf _)

end Generic

theorem DegEq.proof (hGR : GraphRestrict.Statement) (hIR : Kleiman.InterNumRestrict.Statement.{0, 0})
    (hNM : NumModel.Statement) : DegEq.Statement := by
  intro k _ N Ω _ _ x Q n m s _ hgen pp W hsub hW hle hcomap
  classical
  have := hW.isPrime
  have hWy : mIdealOver k (genPtOf W) = W := mIdealOver_genPtOf W hW.multiHomog
  let x' : Fin (N + 1) → FractionRing (NumbersDVR.MRing (graphIdx N m) k ⧸ W) := fun a => genPtOf W ⟨Sum.inl (), a⟩
  let s' : Fin m → FractionRing (NumbersDVR.MRing (graphIdx N m) k ⧸ W) := fun b => genPtOf W ⟨Sum.inr (), b⟩
  have hy : graphVec x' s' = genPtOf W := by
    funext p
    rcases p with ⟨⟨⟩ | ⟨⟩, a⟩ <;> rfl
  have hzero : ∀ p, genPtOf W p = 0 ↔ (X p : NumbersDVR.MRing (graphIdx N m) k) ∈ W := fun p => by
    rw [← X_mem_mIdealOver_iff (k := k), hWy]
  have hxy : ∀ i, x' i ≠ 0 → x i ≠ 0 := fun i h h0 =>
    h ((hzero _).mpr (hle ((X_mem_mIdealOver_iff (graphVec x s) ⟨Sum.inl (), i⟩).mpr h0)))
  have hx' : ∃ i, x' i ≠ 0 := by
    obtain ⟨i, hi⟩ := hW.relevant (Sum.inl ())
    exact ⟨i, fun h => hi ((hzero _).mp h)⟩
  have hs' : ∃ j, s' j ≠ 0 := by
    obtain ⟨j, hj⟩ := hW.relevant (Sum.inr ())
    exact ⟨j, fun h => hj ((hzero _).mp h)⟩
  have hyW : mIdealOver k (graphVec x' s') = W := by rw [hy]; exact hWy
  have hleW : mIdealOver k (graphVec x s) ≤ mIdealOver k (graphVec x' s') := hyW.symm ▸ hle
  have hpp : Kleiman.primeOf (S := k) x' = pp := by
    rw [← comap_mIdealOver_graph (S := k) x' s', hyW, hcomap]
  obtain ⟨Q', r, hR, hgen'⟩ := hGR k N Ω x Q n m s _ x' s' hxy hgen hleW hx' hs'
  have hsub' : Kleiman.IsSubvar x' pp 1 := ⟨hsub.isPrime, hsub.homog, le_of_eq hpp, hsub.relevant, hsub.dim⟩
  have h1 := hIR k Ω N x _ x' hxy (hsub.le.trans hpp.ge) pp 1 hsub' ![Q] ![Q'] (fun _ => r)
    (fun i => by fin_cases i; exact hR)
  have h2 := hNM k (Unit ⊕ Unit) (graphIdx N m) _ (graphVec x' s') baseBlock N (Equiv.refl _) x' rfl
    (GraphModel.full k N _ x' Q' n m s' hx' hgen') 1 ![Q'] ![graphDeg n]
    (fun i => by fin_cases i; exact realises_graph Q' n s' hgen') (by rw [hpp]; exact hsub')
  rw [hyW, hpp] at h2
  have e1 : (fun i => (![Q] i).toSubSystem) = ![Q.toSubSystem] := by
    funext i; fin_cases i; rfl
  have e2 : (fun i => (![Q'] i).toSubSystem) = ![Q'.toSubSystem] := by
    funext i; fin_cases i; rfl
  rw [e1, e2] at h1
  rw [e2] at h2
  rw [← h2, h1]

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistSubEqChartSecOver
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver GeneratesOver)

noncomputable section

namespace ModelTwistGenerated

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {K : Type} [Fintype K] {ι : K → Type}

theorem secOver_mul (y : (Σ k, ι k) → Ω) {β γ : K → ℤ} {a b : Ω} (ha : a ∈ secOver S y β)
    (hb : b ∈ secOver S y γ) : a * b ∈ secOver S y (β + γ) := by
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule] at ha hb ⊢
  intro c hc
  have : a * b * ∏ k, y ⟨k, c k⟩ ^ (-(β + γ) k) =
      (a * ∏ k, y ⟨k, c k⟩ ^ (-β k)) * (b * ∏ k, y ⟨k, c k⟩ ^ (-γ k)) := by
    rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Pi.add_apply, neg_add, zpow_add₀ (hc k)]
  rw [this]
  exact Subalgebra.mul_mem _ (ha c hc) (hb c hc)

theorem one_mem_secOver (y : (Σ k, ι k) → Ω) : (1 : Ω) ∈ secOver S y 0 := by
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply]
  intro c _
  simp only [Pi.zero_apply, neg_zero, zpow_zero, Finset.prod_const_one, mul_one]
  exact Subalgebra.one_mem _

theorem pow_mem_secOver (y : (Σ k, ι k) → Ω) {δ : K → ℤ} {a : Ω} (ha : a ∈ secOver S y δ) (m : ℕ) :
    a ^ m ∈ secOver S y ((m : ℤ) • δ) := by
  induction m with
  | zero => simpa using one_mem_secOver (S := S) y
  | succ m ih =>
    have h := secOver_mul y ih ha
    rw [pow_succ]
    convert h using 2
    push_cast
    rw [add_smul, one_smul]

variable [DecidableEq K]

theorem coord_mem_secOver (y : (Σ k, ι k) → Ω) (k₀ : K) (i : ι k₀) :
    y ⟨k₀, i⟩ ∈ secOver S y (IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) := by
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule, IndefiniteRowSideFullHecke.Kleiman2.baseDeg]
  intro c _
  rw [Fintype.prod_eq_single k₀ fun k hk => by rw [Pi.single_eq_of_ne hk]; simp]
  rw [Pi.single_eq_same, zpow_neg_one, ← div_eq_mul_inv]
  exact Algebra.subset_adjoin ⟨⟨k₀, i⟩, rfl⟩

theorem prod_coord_mem_secOver (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1))
    (s : Finset (Fin (N + 1))) :
    ∏ j ∈ s, (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) j ∈
      secOver S y ((s.card : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) := by
  induction s using Finset.induction_on with
  | empty => simpa using one_mem_secOver (S := S) y
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.card_insert_of_notMem hj]
    have h := secOver_mul y (coord_mem_secOver (S := S) y k₀ (e.symm j)) ih
    convert h using 2 <;> first | rfl | (push_cast; rw [add_smul, one_smul, add_comm])

variable {N : ℕ} {y : (Σ k, ι k) → Ω} {k₀ : K} (e : ι k₀ ≃ Fin (N + 1))

theorem twist_sub_eq_chartSecOver (β : K → ℤ)
    (Q : Kleiman.LineBundle S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm))
    (hQ : ∀ c : ℤ, (Q.twist (Kleiman.twistSys S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).secs =
      secOver S y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀))
    (c : ℕ) (I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) :
    ((Q.twist (Kleiman.twistSys S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) (c : ℤ))).sub I : Set Ω) =
      chartSecOver S y k₀ e (β + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) I := by
  have hsubQ : (Q.sub I : Set Ω) = chartSecOver S y k₀ e β I := by
    refine Set.ext fun t => ?_
    rw [SetLike.mem_coe, mem_sub_iff_gam]
    refine exists_congr fun n => ?_
    rw [Kleiman.SubSystem.gam, hQ]
  let X := IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : X i ≠ 0 := (Kleiman.mem_support _).mp (I.2.2 hi)
  have hcard := Finset.card_erase_add_one hi
  have hxI : Kleiman.xProd I = X i * ∏ j ∈ I.1.erase i, X j := (Finset.mul_prod_erase I.1 _ hi).symm
  have hxic : X i ^ c ∈ secOver S y ((c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) :=
    pow_mem_secOver y (coord_mem_secOver y k₀ (e.symm i)) c
  have hP : (∏ j ∈ I.1.erase i, X j) ^ c ∈
      secOver S y ((c : ℤ) • (((I.1.erase i).card : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) :=
    pow_mem_secOver y (prod_coord_mem_secOver y k₀ e _) c
  ext t
  rw [SetLike.mem_coe, twist_sub_eq_mul]
  change t ∈ Kleiman.twistMod S X (c : ℤ) I * Q.sub I ↔ _
  rw [Kleiman.twistMod_eq_span (c : ℤ) I hi, Submodule.mem_span_singleton_mul, zpow_natCast]
  constructor
  · rintro ⟨b, hb, rfl⟩
    have hb' : b ∈ chartSecOver S y k₀ e β I := by rw [← hsubQ]; exact hb
    obtain ⟨n, hn⟩ := hb'
    refine ⟨n, ?_⟩
    have h := secOver_mul y hxic hn
    rw [show Kleiman.xProd I ^ n * (X i ^ c * b) = X i ^ c * (Kleiman.xProd I ^ n * b) by ring]
    convert h using 2
    abel
  · rintro ⟨n, hn⟩
    refine ⟨(X i ^ c)⁻¹ * t, ?_, ?_⟩
    · rw [← SetLike.mem_coe, hsubQ]
      refine ⟨n + c, ?_⟩
      have h := secOver_mul y hP hn
      rw [show Kleiman.xProd I ^ (n + c) * ((X i ^ c)⁻¹ * t) =
          (∏ j ∈ I.1.erase i, X j) ^ c * (Kleiman.xProd I ^ n * t) by
        rw [hxI]; field_simp; ring]
      convert h using 2
      funext k
      rw [← hcard]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    · change X i ^ c * ((X i ^ c)⁻¹ * t) = t
      field_simp

end ModelTwistGenerated


open ModelTwistGenerated in
theorem ModelTwistGenerated.proof (hCG : ChartSecGen.Statement) : ModelTwistGenerated.Statement := by
  classical
  intro S _ K _ _ ι _ Ω _ _ y k₀ hS hM β
  obtain ⟨i₀, -⟩ := hM.1 k₀
  have hpos : 0 < Fintype.card (ι k₀) := Fintype.card_pos_iff.mpr ⟨i₀⟩
  set N := Fintype.card (ι k₀) - 1
  have hcard : Fintype.card (ι k₀) = N + 1 := by omega
  let e : ι k₀ ≃ Fin (N + 1) := Fintype.equivFinOfCardEq hcard
  set x := IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm with hx
  obtain ⟨Q, hQ⟩ := BundleOfDeg.full S K ι Ω y k₀ N e hM β
  obtain ⟨c₀, hc₀⟩ := GroundTheory.Heights₂.Heights.Kleiman.Generated.full S Ω N x Q
  refine ⟨max c₀ 0, fun c hc => ?_⟩
  lift c to ℕ using le_trans (le_max_right _ _) hc with m
  set L := Q.twist (Kleiman.twistSys S x (m : ℤ)) with hL
  have hgen : L.Generated := hc₀ m (le_trans (le_max_left _ _) hc)
  have hfin : ∀ I : Kleiman.Chart x, ∃ T : Finset Ω, (T : Set Ω) ⊆ L.secs ∧
      Submodule.span (Kleiman.chartRing S x I) (T : Set Ω) = L.sub I := by
    intro I
    obtain ⟨i, hi⟩ := I.2.1
    have hfg : (L.sub I).FG := by
      rw [hL, twist_sub_eq_mul]
      change (Kleiman.twistMod S x (m : ℤ) I * Q.sub I).FG
      rw [Kleiman.twistMod_eq_span (m : ℤ) I hi]
      exact (Submodule.fg_span_singleton _).mul (Q.fg I)
    rw [← hgen I] at hfg ⊢
    obtain ⟨T, hT, hTs⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).mp hfg
    exact ⟨T, hT, hTs.symm⟩
  choose T hTsub hTspan using hfin
  let _ : Fintype (Kleiman.Chart x) := Fintype.ofFinite _
  let U : Finset Ω := Finset.univ.biUnion T
  have hUsub : (U : Set Ω) ⊆ L.secs := by
    intro z hz
    obtain ⟨I, -, hzI⟩ := Finset.mem_biUnion.mp hz
    exact hTsub I hzI
  have hUspan : ∀ I, Submodule.span (Kleiman.chartRing S x I) (U : Set Ω) = L.sub I := by
    intro I
    apply le_antisymm
    · rw [← hgen I]
      exact Submodule.span_mono hUsub
    · rw [← hTspan I]
      exact Submodule.span_mono fun z hz => Finset.mem_biUnion.mpr ⟨I, Finset.mem_univ _, hz⟩
  have hsecs : L.secs = secOver S y (β + (m : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) := hQ m
  let η : Fin U.card → Ω := fun j => (U.equivFin.symm j : Ω)
  have hrange : Set.range η = (U : Set Ω) := by
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      exact (U.equivFin.symm j).2
    · intro hz
      exact ⟨U.equivFin ⟨z, hz⟩, by simp [η]⟩
  have hη : ∀ j, η j ∈ secOver S y (β + (m : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) := by
    intro j
    rw [← hsecs]
    exact hUsub (U.equivFin.symm j).2
  refine ⟨U.card, η, hη, (hCG S K ι Ω y k₀ N e hM _ U.card η hη).mpr fun I => ?_⟩
  rw [hrange, hUspan I]
  exact twist_sub_eq_chartSecOver e β Q hQ m I

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiHomogRename
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomog)

namespace RowChartAct

variable {S : Type} [CommRing S] {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiHomog_mul {f g : MRingOver S ι} {a b : K → ℕ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a)
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g b) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, hf m₁ hm₁ k, hg m₂ hm₂ k, Pi.add_apply]

theorem isMultiHomog_rename [DecidableEq K] (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) {f : MvPolynomial (Fin (N + 1)) S}
    {d : ℕ} (hf : f.IsHomogeneous d) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (rename (fun j => (⟨k₀, e.symm j⟩ : Σ k, ι k)) f) (Pi.single k₀ d) := by
  classical
  have hρ : Function.Injective (fun j => (⟨k₀, e.symm j⟩ : Σ k, ι k)) := fun j j' h =>
    e.symm.injective (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
  intro m' hm' k
  rw [support_rename_of_injective hρ] at hm'
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hm'
  have hd := hf (mem_support_iff.mp hm)
  by_cases hk : k = k₀
  · subst hk
    have hval : ∀ i, Finsupp.mapDomain (fun j => (⟨k, e.symm j⟩ : Σ k, ι k)) m ⟨k, i⟩ = m (e i) := fun i => by
      have hi : (⟨k, i⟩ : Σ k, ι k) = (fun j => (⟨k, e.symm j⟩ : Σ k, ι k)) (e i) := by simp
      rw [hi, Finsupp.mapDomain_apply_of_injective hρ]
    simp_rw [hval]
    rw [Pi.single_eq_same, Equiv.sum_comp e (fun j => m j), ← hd]
    simp [Finsupp.weight_apply, Finsupp.sum_fintype]
  · rw [Pi.single_eq_of_ne hk]
    refine Finset.sum_eq_zero fun i _ => Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨j, hj⟩
    exact hk (congrArg Sigma.fst hj).symm

end RowChartAct

theorem RowChartAct.proof : RowChartAct.Statement := by
  intro S _ K _ _ ι _ _ Ω _ _ y k₀ N e γ J I r a hr ha
  obtain ⟨f, s, d, hs, hf, hsd, rfl⟩ := hr
  set ρ : Fin (N + 1) → Σ k, ι k := fun j => ⟨k₀, e.symm j⟩ with hρ
  have hsmem : rename ρ s ∈ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.cellMon S (baseCell k₀ e J.1 I) := by
    have hle : (Kleiman.monos (S := S) J.1).map (rename ρ : MvPolynomial _ S →ₐ[S] MRingOver S ι).toRingHom.toMonoidHom ≤
        ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.cellMon S (baseCell k₀ e J.1 I) := by
      rw [Kleiman.monos, MonoidHom.map_mclosure]
      refine Submonoid.closure_le.mpr ?_
      rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      refine Submonoid.subset_closure ⟨k₀, e.symm j, ?_, by simp [ρ]⟩
      unfold baseCell
      rw [Function.update_self]
      exact Finset.mem_union_right _ (Finset.mem_map_of_mem _ hj)
    exact hle ⟨s, hs, rfl⟩
  unfold cellSec at ha ⊢
  split_ifs at ha ⊢ with hM
  · induction ha using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨g, t, b, ht, htb, hγ, hg, rfl⟩ := hz
      apply Submodule.subset_span
      refine ⟨rename ρ f * g, rename ρ s * t, b + Pi.single k₀ d, mul_mem hsmem ht, ?_, ?_, ?_, ?_⟩
      · rw [add_comm b]
        exact RowChartAct.isMultiHomog_mul (RowChartAct.isMultiHomog_rename k₀ e hsd) htb
      · intro k
        have h1 := hγ k
        simp only [Pi.add_apply, Nat.cast_add]
        omega
      · have h2 := RowChartAct.isMultiHomog_mul (RowChartAct.isMultiHomog_rename k₀ e hf) hg
        have heq : (Pi.single k₀ d + fun k => (γ k + b k).toNat) =
            fun k => (γ k + ((b + Pi.single k₀ d : K → ℕ) k : ℕ)).toNat := funext fun k => by
          have h1 := hγ k
          simp only [Pi.add_apply, Nat.cast_add]
          omega
        rw [heq] at h2
        exact h2
      · simp only [map_mul, aeval_rename]
        rw [div_mul_div_comm]
        rfl
    | zero => simp
    | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
    | smul c u _ hu => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hu
  · rw [Submodule.mem_bot] at ha ⊢
    rw [ha, mul_zero]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellLocSys
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def cellLocSys {S : Type} [CommRing S] {X : Type} {Ω : Type} [Field Ω] [Algebra S Ω] (G : X → Submodule S Ω)
    (f : Ω) : X → Submodule S Ω :=
  fun I => ⨆ n : ℕ, (G I).comap (LinearMap.mulLeft S (f ^ n))

def CellLocGlue.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)
    (G : (∀ k, Finset (ι k)) → Submodule S Ω) (R : Subring Ω) (m : ℕ) (f u : Fin m → Ω),
    (∀ l, f l ∈ R) → (∀ l, u l ∈ R) → ∑ l, u l * f l = 1 →
    (∀ I, ∀ r ∈ R, ∀ a ∈ G I, r * a ∈ G I) →
    (∀ l, CellPosExact S y (cellLocSys G (f l))) →
    CellPosExact S y G

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
