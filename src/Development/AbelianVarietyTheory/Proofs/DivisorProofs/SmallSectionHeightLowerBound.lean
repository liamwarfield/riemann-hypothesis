module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaThetaFunctionsOrientedPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthInChartChartIndependent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier

namespace GlobalTheory.SmallSecHeight

variable {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}

theorem isClosed_of_ne (hd : topologicalKrullDim Z = 1) {z : Z} (hz : z ≠ genericPoint Z) :
    IsClosed ({z} : Set Z) := by
  let C (w : Z) : IrreducibleCloseds Z := ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩
  rcases Order.krullDim_le_one_iff.1 (show Order.krullDim (IrreducibleCloseds Z) ≤ 1 from hd.le) (C z) with h | h
  · rw [← closure_subset_iff_isClosed]
    intro w hw
    have h1 : C w ≤ C z := closure_minimal (singleton_subset_iff.2 hw) isClosed_closure
    have h2 : z ∈ closure ({w} : Set Z) := h h1 (subset_closure rfl)
    exact ((specializes_iff_mem_closure.2 h2).antisymm (specializes_iff_mem_closure.2 hw)).eq
  · exact absurd (IsGenericPoint.eq (eq_univ_of_univ_subset (@h
      ⟨univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩ (subset_univ _))) (genericPoint_spec Z)) hz

theorem eq_genericPoint (hZ : IsArithVar q 0) {z : Z} (h : CharZero (Z.residueField z)) :
    z = genericPoint Z := by
  by_contra hz
  have := hZ.finite_residueField (isClosed_of_ne hZ.dim_eq hz)
  exact not_finite (Z.residueField z)

theorem apply_closedPoint (hZ : IsArithVar q 0) (y : Sp ℂ ⟶ Z) :
    y (IsLocalRing.closedPoint ℂ) = genericPoint Z :=
  eq_genericPoint hZ (Scheme.SpecToEquivOfField ℂ Z y).2.hom.charZero

theorem numberField (hZ : IsArithVar q 0) (hc : CharZero (Z.residueField (genericPoint Z))) :
    NumberField (Z.residueField (genericPoint Z)) := by
  obtain ⟨N, j, _, hj⟩ := hZ.isProjOver
  have := isProper_str k N
  have : IsProper q := hj ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hZ.finite)
  let t := q ≫ spMap (Int.castRingHom k)
  have h0 (z : Z) (n : ℤ) : n ∈ (t z).asIdeal ↔ (n : Z.residueField z) = 0 := by
    have e : Z.fromSpecResidueField z ≫ t = spMap (Int.castRingHom (Z.residueField z)) := by
      rw [← Spec.map_preimage (Z.fromSpecResidueField z ≫ t)]
      congr 1
      exact CommRingCat.hom_ext (RingHom.ext_int _ _)
    have e2 : t z = spMap (Int.castRingHom (Z.residueField z)) (IsLocalRing.closedPoint _) := by
      rw [← e]
      exact congrArg t (Scheme.fromSpecResidueField_apply _ _).symm
    rw [e2]
    change (n : Z.residueField z) ∈ IsLocalRing.maximalIdeal _ ↔ _
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot]
  have h1 (z : Z) (hz : t z = t (genericPoint Z)) : z = genericPoint Z :=
    eq_genericPoint hZ (charZero_of_inj_zero fun n hn => by
      have := (h0 _ n).1 (hz ▸ (h0 z n).2 (by exact_mod_cast hn))
      exact_mod_cast this)
  have h2 : t.QuasiFiniteAt (genericPoint Z) := by
    rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
    have : Subsingleton (t.fiber (t (genericPoint Z))) := ⟨fun a b =>
      (t.fiberHomeo _).injective (Subtype.ext ((h1 _ (t.fiberHomeo _ a).2).trans (h1 _ (t.fiberHomeo _ b).2).symm))⟩
    exact isOpen_discrete _
  rw [Scheme.Hom.quasiFiniteAt_iff] at h2
  have hf : LocallyQuasiFinite (Z.fromSpecResidueField (genericPoint Z) ≫ t) := by
    rw [Scheme.fromSpecResidueField, Category.assoc]
    infer_instance
  rw [← Spec.map_preimage (Z.fromSpecResidueField _ ≫ _), HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite),
    RingHom.ext_int (Spec.preimage (Z.fromSpecResidueField _ ≫ t)).hom
      ((algebraMap ℚ (Z.residueField (genericPoint Z))).comp (algebraMap ℤ ℚ))] at hf
  have := RingHom.quasiFinite_algebraMap.1 hf.of_comp
  exact { to_finiteDimensional := Module.Finite.of_quasiFinite }

def ptsEquiv (hZ : IsArithVar q 0) :
    (Σ σ : k →+* ℂ, CxPts q σ) ≃ (Z.residueField (genericPoint Z) →+* ℂ) := by
  refine (Equiv.ofBijective (fun y : Σ σ : k →+* ℂ, CxPts q σ => y.2.1) ⟨?_, fun y => ?_⟩).trans
    (Equiv.ofBijective (fun f : Z.residueField (genericPoint Z) →+* ℂ =>
      (Scheme.SpecToEquivOfField ℂ Z).symm ⟨_, CommRingCat.ofHom f⟩) ⟨fun f g h => ?_, fun y => ?_⟩).symm
  · rintro ⟨σ, y, hy⟩ ⟨σ', y', hy'⟩ (rfl : y = y')
    obtain rfl : σ = σ' := congrArg CommRingCat.Hom.hom (Spec.map_injective (hy.symm.trans hy'))
    rfl
  · exact ⟨⟨(Spec.preimage (y ≫ q)).hom, y, (Spec.map_preimage _).symm⟩, rfl⟩
  · exact congrArg CommRingCat.Hom.hom (eq_of_heq (Sigma.mk.inj ((Equiv.injective _) h)).2)
  · obtain ⟨⟨z, f⟩, rfl⟩ := (Scheme.SpecToEquivOfField ℂ Z).symm.surjective y
    obtain rfl := eq_genericPoint hZ f.hom.charZero
    exact ⟨f.hom, rfl⟩

theorem mult_nsmul [IsLocallyNoetherian Z] (D : CartierDiv Z) (n : ℕ) (z : Z) :
    (n • D).mult z = n * D.mult z := by
  induction n with
  | zero =>
    rw [zero_nsmul, (CartierDiv.isEqn_zero z).mult_eq, Units.val_one, (unitAt_one z).ord_eq_zero]
    simp
  | succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

theorem ratVal_pow {σ : k →+* ℂ} {y : CxPts q σ} (hy : under y = genericPoint Z)
    (f : Z.functionField) (n : ℕ) : ratVal (f ^ n) y = ratVal f y ^ n := by
  induction n with
  | zero =>
    have e := ratVal_fnOf (y := y) mem_ptsIn_top trivial 1
    rw [map_one, ev_one mem_ptsIn_top] at e
    rw [pow_zero, pow_zero, e]
  | succ n ih =>
    rw [pow_succ, pow_succ, ratVal_mul (hy ▸ regAt_genericPoint _) (hy ▸ regAt_genericPoint _), ih]

theorem curveDeg_pow [IsLocallyNoetherian Z] (hZ : IsArithVar q 0)
    (hc : CharZero (Z.residueField (genericPoint Z))) (M N : HermLB q) (n : ℕ) (c d : ℝ)
    (a : M.B.ι → N.B.ι) (hU : ∀ j, M.B.U j ≤ N.B.U (a j))
    (hg : ∀ j j' h h', fnOf _ h' (N.B.g (a j) (a j')).val = fnOf _ h (M.B.g j j').val ^ (n + 1))
    (hφ : ∀ σ j y, (N.φ σ).φ (a j) y = (n + 1) * ((M.φ σ).φ j y - 2 * c))
    (hd : ∀ r (hr : IsRatSec M.B r), M.curveDeg hr = d)
    {t : N.B.ι → Z.functionFieldˣ} (ht : IsRatSec N.B t) :
    N.curveDeg ht = (n + 1) * (d - c * Nat.card (Z.residueField (genericPoint Z) →+* ℂ)) := by
  have := hZ.isNoetherian
  obtain ⟨r, hr⟩ := exists_isRatSec M.isLB
  obtain ⟨j₀, h₀⟩ := exists_chart M.isLB (genericPoint Z)
  let r' (j : M.B.ι) : Z.functionFieldˣ := t (a j₀) / r j₀ ^ (n + 1) * r j
  have hr' : IsRatSec M.B r' := fun i j h => by
    simp only [r', Units.val_mul, hr i j h]
    ring
  have key (j) (hj : genericPoint Z ∈ M.B.U j) : t (a j) = r' j * r j ^ n := by
    apply Units.ext
    have e₁ := hr j j₀ (memInf hj h₀)
    have := (r j₀).ne_zero
    rw [ht _ (a j₀) (memInf (hU _ hj) (hU _ h₀)), hg j j₀ (memInf hj h₀)]
    simp only [r', Units.val_mul, Units.val_pow_eq_pow_val, Units.val_div_eq_div_val, e₁]
    field_simp
    ring
  have h₁ (z : Z) : (N.div ht).mult z = (M.div hr').mult z + n * (M.div hr).mult z := by
    obtain ⟨j, hj⟩ := exists_chart M.isLB z
    rw [← mult_nsmul, ← CartierDiv.mult_add,
      ((presents_divOfRatSec N.isLB ht).isEqn _ z (hU _ hj)).mult_eq, key j (gen_mem hj),
      (((presents_divOfRatSec M.isLB hr').isEqn _ z hj).add
        (((presents_divOfRatSec M.isLB hr).isEqn _ z hj).nsmul n)).mult_eq]
  have h₂ (σ) (y : CxPts q σ) : logNorm (N.φ σ) t y =
      logNorm (M.φ σ) r' y + n * logNorm (M.φ σ) r y + (n + 1) * c := by
    have hy : under y = genericPoint Z := apply_closedPoint hZ y.1
    have ho (D : CartierDiv Z) : y ∈ offSupp q σ D := mem_offSupp.2 (hy ▸ D.genericPoint_notMem_supp)
    have hj := mem_pick (M.φ σ).isLB y
    have hu (g : Z.functionFieldˣ) : ‖ratVal (g : Z.functionField) y‖ ≠ 0 :=
      norm_ne_zero_iff.2 (ratVal_ne_zero (hy ▸ unitAt_genericPoint g.ne_zero))
    rw [logNorm_eq _ ht (ho _) (ptsIn_mono (hU _) hj), logNorm, logNorm, hφ,
      key _ (gen_mem (mem_ptsIn.1 hj)), Units.val_mul, Units.val_pow_eq_pow_val,
      ratVal_mul (hy ▸ regAt_genericPoint _) (hy ▸ regAt_genericPoint _), ratVal_pow hy, norm_mul,
      norm_pow, Real.log_mul (hu _) (pow_ne_zero _ (hu _)), Real.log_pow]
    ring
  have hfin (D : CartierDiv Z) : (Function.support fun z =>
      (D.mult z : ℝ) * Real.log (Nat.card (Z.residueField z))).Finite :=
    D.finite_support_mult.subset fun z hz h0 => hz (by simp [h0])
  have := numberField hZ hc
  have : Finite (Σ σ : k →+* ℂ, CxPts q σ) := .of_equiv _ (ptsEquiv hZ).symm
  have (σ : k →+* ℂ) : Finite (CxPts q σ) := .of_injective _ (sigma_mk_injective (i := σ))
  have := hZ.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  have (σ : k →+* ℂ) := Fintype.ofFinite (CxPts q σ)
  have e := hd _ hr
  have e' := hd _ hr'
  have e₀ : ∑ᶠ z, ((N.div ht).mult z : ℝ) * Real.log (Nat.card (Z.residueField z)) =
      ∑ᶠ z, ((M.div hr').mult z : ℝ) * Real.log (Nat.card (Z.residueField z)) +
      n * ∑ᶠ z, ((M.div hr).mult z : ℝ) * Real.log (Nat.card (Z.residueField z)) := by
    rw [mul_finsum, ← finsum_add_distrib (hfin _) ((hfin (M.div hr)).subset fun z hz h0 => hz (by
      simp only [h0, mul_zero]))]
    refine finsum_congr fun z => ?_
    rw [h₁]
    push_cast
    ring
  rw [HermLB.curveDeg, e₀, ← Nat.card_congr (ptsEquiv hZ), Nat.card_sigma]
  rw [HermLB.curveDeg] at e e'
  simp only [finsum_eq_sum_of_fintype, h₂, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Finset.sum_mul, Nat.card_eq_fintype_card, Nat.cast_sum] at e e' ⊢
  linear_combination e' + n * e

theorem le_ptHt : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (L : HermLB p) (m : ℕ) (c b : ℝ) (x : X) (s : ((L.shift (fun _ => -c) fun _ => rfl).pow m).B.Sec), 1 ≤ m →
    s ∈ ((L.shift (fun _ => -c) fun _ => rfl).pow m).smallSec → x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s →
    IsAlgPt x → IsPtHt L x b → c ≤ b := by
  intro k _ X _ p D hX L m c b x s hm hs hx ⟨hc, hd⟩ ⟨h, H, hb⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hm
  obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint x
  have := hX.isNoetherian_sub i
  have hr : range i = closure {i (genericPoint Z)} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact h₁.def.symm
  rw [topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hr] at hd
  have hbij : Function.Bijective (i.residueFieldMap (genericPoint Z)).hom := by
    refine ⟨RingHom.injective _, fun u => ?_⟩
    obtain ⟨u, rfl⟩ := Z.residue_surjective _ u
    obtain ⟨u, rfl⟩ := i.stalkMap_surjective _ u
    exact ⟨X.residue _ u, ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i _) u⟩
  let E := RingEquiv.ofBijective _ hbij
  have hc' : CharZero (Z.residueField (genericPoint Z)) := (RingHom.charZero_iff hbij.1).1 hc
  have hcΓ : CharZero Γ(Z, ⊤) := (Z.Γevaluation (genericPoint Z)).hom.charZero
  have hZ : IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hcΓ hd
  have hcard : Nat.card (X.residueField (i (genericPoint Z)) →+* ℂ) =
      Nat.card (Z.residueField (genericPoint Z) →+* ℂ) :=
    Nat.card_congr ⟨fun f => f.comp E.symm.toRingHom, fun f => f.comp E.toRingHom,
      fun f => by ext; simp, fun f => by ext; simp⟩
  have := numberField hZ hc'
  have hpos : (0 : ℝ) < Nat.card (Z.residueField (genericPoint Z) →+* ℂ) := by
    exact_mod_cast Nat.card_pos
  let P := (L.shift (fun _ => -c) fun _ => rfl).pow (n + 1)
  have hu : genericPoint Z ∈ nonzeroLocus (GlobalTheory.secPull s i) := by
    rw [GlobalTheory.nonzeroLocus_secPull]; exact hx
  have key := curveDeg_pow hZ hc' (L.restr i) (P.restr i) n c (h (i (genericPoint Z))) (fun j _ => j)
    (fun j z hz => mem_iInter.2 fun _ => mem_iInter.2 fun u => mem_iInter.1 hz u)
    (fun j j' h h' => ?_) (fun σ j y => ?_) (fun r hr => (H.point Z i hcΓ hd r hr).symm)
    (isRatSec_ratOfSec _ hu)
  · have h0 : 0 ≤ (P.restr i).curveDeg (isRatSec_ratOfSec _ hu) := by
      refine le_of_le_of_eq ?_ (HermLB.curveDeg_sec (L := P) i s hu fun σ y =>
        mem_ptsIn.2 ((apply_closedPoint hZ y.1).symm ▸ hu)).symm
      refine sub_nonneg.2 (le_trans (b := 0) ?_ (finsum_nonneg fun z => mul_nonneg
        (Int.cast_nonneg (mult_divOfSec_nonneg z)) (Real.log_natCast_nonneg _)))
      have np {α : Type} {f : α → ℝ} (hf : ∀ a, f a ≤ 0) : ∑ᶠ a, f a ≤ 0 :=
        finsum_induction (· ≤ 0) le_rfl (fun _ _ => add_nonpos) hf
      refine np fun σ => np fun y => ?_
      exact div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos (Weight.nsq_nonneg _ _ _) (hs σ _)) zero_le_two
    rw [key, hb, hcard, ← sub_mul] at h0
    exact sub_nonneg.1 (nonneg_of_mul_nonneg_left (nonneg_of_mul_nonneg_right h0 (by positivity)) hpos)
  · have e (u : PUnit → L.B.ι) (z : Z) (hz : z ∈ (P.restr i).B.U fun _ => u) : z ∈ i ⁻¹ᵁ L.B.U (u ⟨⟩) :=
      mem_iInter.1 (mem_iInter.1 hz ⟨⟩) ⟨⟩
    have e₁ : (P.restr i).B.g (fun _ => j) (fun _ => j') =
        res (X := Z) (U := i ⁻¹ᵁ (L.B.U (j ⟨⟩) ⊓ L.B.U (j' ⟨⟩)))
          (V := (P.restr i).B.U (fun _ => j) ⊓ (P.restr i).B.U fun _ => j') (fun z hz => ⟨e _ z hz.1, e _ z hz.2⟩)
          (pullU i _ (L.B.g (j ⟨⟩) (j' ⟨⟩))) ^ (n + 1) := by
      refine (pull_g _ i _ _).trans ?_
      have e₂ : P.B.g j j' = res (X := X) (U := L.B.U (j ⟨⟩) ⊓ L.B.U (j' ⟨⟩)) (V := P.B.U j ⊓ P.B.U j')
          (fun _ hz => ⟨mem_iInter.1 hz.1 ⟨⟩, mem_iInter.1 hz.2 ⟨⟩⟩) (L.B.g (j ⟨⟩) (j' ⟨⟩)) ^ (n + 1) := by
        change ∏ _k : PUnit, _ = _
        refine (Fintype.prod_unique _).trans ((zpow_natCast _ _).trans ?_)
        rfl
      refine (congrArg (fun u => res _ (pullU i _ u)) e₂).trans ?_
      rw [map_pow, map_pow]
      refine congrArg (· ^ (n + 1)) (Units.ext ?_)
      exact (congrArg (resG Z _) (app_resG _ _ _)).trans (resG_resG _ _ _)
    rw [e₁, Units.val_pow_eq_pow_val, map_pow]
    refine congrArg (· ^ (n + 1)) ?_
    exact (fnOf_resG _ h' _).trans ((congrArg (fun u : Γ(Z, _)ˣ => fnOf _ h u.val)
      (pull_g L.B i j j')).trans (fnOf_resG _ h _)).symm
  · refine ((P.φ σ).pull_φ i rfl _ y).trans ((Weight.zpow_φ _ _ _ _).trans ?_)
    rw [show ((L.restr i).φ σ).φ j y = _ from (L.φ σ).pull_φ i rfl j y]
    change _ * (_ + 2 * -c) = _
    push_cast
    ring

end GlobalTheory.SmallSecHeight
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevOpMemFixed
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.TwTrLevel

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem mem_fixed_iff (ρ : Representation ℂ G V) (H : Subgroup G) (v : V) :
    v ∈ fixed ρ H ↔ ∀ h ∈ H, ρ h v = v := by
  simp [fixed, GlobalTheory.PRep.eig]

theorem out_eq_of_inv {M : Type} (H : Subgroup G) (F : G → M) (hF : ∀ g, ∀ h ∈ H, F (g * h) = F g) (g : G) :
    F (QuotientGroup.mk g : G ⧸ H).out = F g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hh, hF g h h.2]

theorem finite_supp [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G) (hH : IsOpen (H : Set G))
    (f : G → ℂ) (hf : HasCompactSupport f) : {q : G ⧸ H | f q.out ≠ 0}.Finite := by
  haveI := QuotientGroup.discreteTopology hH
  have hc : IsCompact ((QuotientGroup.mk : G → G ⧸ H) '' tsupport f) :=
    hf.isCompact.image QuotientGroup.continuous_mk
  refine hc.finite_of_discrete.subset ?_
  intro q hq
  exact ⟨q.out, subset_tsupport f hq, QuotientGroup.out_eq' q⟩

theorem levOp_apply (ρ : Representation ℂ G V) (K H : Subgroup G) (f : G → ℂ) (A : V →ₗ[ℂ] V) (v : V)
    (hs : {q : G ⧸ H | f q.out ≠ 0}.Finite) :
    levOp ρ K H f A v = ((H.relIndex K : ℕ) : ℂ)⁻¹ • ∑ᶠ q : G ⧸ H, f q.out • ρ q.out (A v) := by
  unfold levOp
  rw [LinearMap.smul_apply]
  congr 1
  have := AddMonoidHom.map_finsum (LinearMap.applyₗ (R := ℂ) (M := V) (M₂ := V) v).toAddMonoidHom
    (f := fun q : G ⧸ H => f q.out • (ρ q.out ∘ₗ A)) (hs.subset ?_)
  · simpa using this
  · intro q hq
    simp only [Function.mem_support, ne_eq, Set.mem_setOf_eq] at hq ⊢
    intro h0
    exact hq (by rw [h0, zero_smul])

theorem A_mem_fixed (ρ : Representation ℂ G V) (θ : G →* G) (hθ : ∀ g, θ (θ g) = g) (A : V →ₗ[ℂ] V)
    (hA : ∀ g, A ∘ₗ ρ g = ρ (θ g) ∘ₗ A) (H : Subgroup G) (hH : ∀ k ∈ H, θ k ∈ H) (w : V)
    (hw : w ∈ fixed ρ H) : A w ∈ fixed ρ H := by
  rw [mem_fixed_iff] at hw ⊢
  intro k hk
  have h1 := LinearMap.congr_fun (hA (θ k)) w
  simp only [LinearMap.coe_comp, Function.comp_apply, hθ] at h1
  rw [← h1, hw _ (hH k hk)]

theorem levOp_mem_fixed [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation ℂ G V) (θ : G →* G)
    (hθ : ∀ g, θ (θ g) = g) (A : V →ₗ[ℂ] V) (hA : ∀ g, A ∘ₗ ρ g = ρ (θ g) ∘ₗ A) (K H : Subgroup G)
    (hHo : IsOpen (H : Set G)) (hH : ∀ k ∈ H, θ k ∈ H) (f : G → ℂ) (hf : IsHecke H f) (v : V)
    (hv : v ∈ fixed ρ H) : levOp ρ K H f A v ∈ fixed ρ H := by
  have hs := finite_supp H hHo f hf.1
  have hu := A_mem_fixed ρ θ hθ A hA H hH v hv
  rw [mem_fixed_iff] at hu
  rw [levOp_apply ρ K H f A v hs, mem_fixed_iff]
  intro k hk
  set F : G → V := fun g => f g • ρ g (A v) with hFdef
  have hF : ∀ g, ∀ h ∈ H, F (g * h) = F g := by
    intro g h hh
    simp only [hFdef, (hf.2 h hh g).2, map_mul, Module.End.mul_apply, hu h hh]
  have hsupp : (Function.support fun q : G ⧸ H => F q.out).Finite := by
    refine hs.subset ?_
    intro q hq
    simp only [Function.mem_support, ne_eq, Set.mem_setOf_eq, hFdef] at hq ⊢
    intro h0
    exact hq (by rw [h0, zero_smul])
  rw [map_smul]
  congr 1
  change ρ k (∑ᶠ q : G ⧸ H, F q.out) = ∑ᶠ q : G ⧸ H, F q.out
  have hm := AddMonoidHom.map_finsum (ρ k).toAddMonoidHom hsupp
  simp only [LinearMap.toAddMonoidHom_coe] at hm
  rw [hm]
  have hk' : ∀ q : G ⧸ H, ρ k (F q.out) = F (k • q).out := by
    intro q
    have e1 : (k • q : G ⧸ H) = QuotientGroup.mk (k * q.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [e1, out_eq_of_inv H F hF]
    simp only [hFdef, map_smul, map_mul, Module.End.mul_apply, (hf.2 k hk q.out).1]
  simp_rw [hk']
  exact finsum_comp_equiv (MulAction.toPerm k : Equiv.Perm (G ⧸ H)) (f := fun q : G ⧸ H => F q.out)

def avgOp (ρ : Representation ℂ G V) (K' K'' : Subgroup G) : V →ₗ[ℂ] V :=
  ((K''.relIndex K' : ℕ) : ℂ)⁻¹ • ∑ᶠ j : K' ⧸ K''.subgroupOf K', ρ (j.out : G)

theorem finite_quot [TopologicalSpace G] [IsTopologicalGroup G] (K K' K'' : Subgroup G)
    (hK : IsCompact (K : Set G)) (h' : IsOpen (K' : Set G)) (h'' : IsOpen (K'' : Set G)) (hle : K' ≤ K) :
    Finite (K' ⧸ K''.subgroupOf K') := by
  have hc : IsCompact (K' : Set G) := hK.of_isClosed_subset (Subgroup.isClosed_of_isOpen K' h') hle
  haveI : CompactSpace K' := isCompact_iff_compactSpace.mp hc
  have ho : IsOpen ((K''.subgroupOf K' : Subgroup K') : Set K') := h''.preimage continuous_subtype_val
  haveI := QuotientGroup.discreteTopology ho
  exact finite_of_compact_of_discrete

theorem avgOp_apply (ρ : Representation ℂ G V) (K' K'' : Subgroup G) [Finite (K' ⧸ K''.subgroupOf K')] (u : V) :
    avgOp ρ K' K'' u = ((K''.relIndex K' : ℕ) : ℂ)⁻¹ • ∑ᶠ j : K' ⧸ K''.subgroupOf K', ρ (j.out : G) u := by
  unfold avgOp
  rw [LinearMap.smul_apply]
  congr 1
  have := AddMonoidHom.map_finsum (LinearMap.applyₗ (R := ℂ) (M := V) (M₂ := V) u).toAddMonoidHom
    (f := fun j : K' ⧸ K''.subgroupOf K' => ρ (j.out : G)) (Set.toFinite _)
  simpa using this

theorem levOp_le [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation ℂ G V) (K K' K'' : Subgroup G)
    (hle : K'' ≤ K') (hK'K : K' ≤ K) [Finite (K' ⧸ K''.subgroupOf K')] (h'o : IsOpen (K' : Set G))
    (h''o : IsOpen (K'' : Set G)) (f : G → ℂ) (hf : IsHecke K' f) (u : V) (hu : u ∈ fixed ρ K'') :
    levOp ρ K K'' f LinearMap.id u = levOp ρ K K' f LinearMap.id (avgOp ρ K' K'' u) := by
  have hs' := finite_supp K' h'o f hf.1
  have hs'' := finite_supp K'' h''o f hf.1
  rw [mem_fixed_iff] at hu
  rw [levOp_apply ρ K K'' f _ u hs'', levOp_apply ρ K K' f _ _ hs', avgOp_apply]
  simp only [LinearMap.id_apply]
  set F : G → V := fun g => f g • ρ g u with hFdef
  have hF : ∀ g, ∀ h ∈ K'', F (g * h) = F g := by
    intro g h hh
    simp only [hFdef, (hf.2 h (hle hh) g).2, map_mul, Module.End.mul_apply, hu h hh]
  set e := Subgroup.quotientEquivProdOfLE hle with hedef
  have he : ∀ (q : G ⧸ K') (j : K' ⧸ K''.subgroupOf K'),
      F (e.symm (q, j)).out = f q.out • ρ q.out (ρ (j.out : G) u) := by
    intro q j
    have h1 : e.symm (q, j) = (QuotientGroup.mk (q.out * (j.out : G)) : G ⧸ K'') := by
      rw [hedef, Subgroup.quotientEquivProdOfLE_symm_apply]
      conv_lhs => rw [← QuotientGroup.out_eq' j]
      rfl
    rw [h1, out_eq_of_inv K'' F hF]
    simp only [hFdef, (hf.2 _ (j.out).2 q.out).2, map_mul, Module.End.mul_apply]
  set S : G ⧸ K' → V := fun q => ∑ᶠ j : K' ⧸ K''.subgroupOf K', f q.out • ρ q.out (ρ (j.out : G) u) with hSdef
  have hL : ∑ᶠ r : G ⧸ K'', F r.out = ∑ᶠ q, S q := by
    rw [← finsum_comp_equiv e.symm]
    rw [finsum_curry]
    · simp only [he, hSdef]
    · refine (hs'.prod (Set.finite_univ (α := K' ⧸ K''.subgroupOf K'))).subset ?_
      rintro ⟨q, j⟩ hp
      simp only [Function.mem_support, ne_eq, he] at hp
      simp only [Set.mem_prod, Set.mem_setOf_eq, Set.mem_univ, and_true]
      intro h0
      exact hp (by rw [h0, zero_smul])
  have hR : ∀ q : G ⧸ K', f q.out • ρ q.out (((K''.relIndex K' : ℕ) : ℂ)⁻¹ •
      ∑ᶠ j : K' ⧸ K''.subgroupOf K', ρ (j.out : G) u) = ((K''.relIndex K' : ℕ) : ℂ)⁻¹ • S q := by
    intro q
    have hm := AddMonoidHom.map_finsum (f q.out • ρ q.out).toAddMonoidHom
      (f := fun j : K' ⧸ K''.subgroupOf K' => ρ (j.out : G) u) (Set.toFinite _)
    simp only [LinearMap.toAddMonoidHom_coe, LinearMap.smul_apply] at hm
    rw [map_smul, smul_comm, hm]
  simp only [hR]
  rw [hL, ← smul_finsum, smul_smul, ← Subgroup.relIndex_mul_relIndex K'' K' K hle hK'K]
  congr 1
  push_cast
  rw [mul_inv, mul_comm]

theorem avgOp_mem (ρ : Representation ℂ G V) (K' K'' : Subgroup G) [Finite (K' ⧸ K''.subgroupOf K')] (u : V)
    (hu : u ∈ fixed ρ K'') : avgOp ρ K' K'' u ∈ fixed ρ K' := by
  rw [mem_fixed_iff] at hu
  rw [avgOp_apply, mem_fixed_iff]
  intro k hk
  set F : K' → V := fun x => ρ (x : G) u with hFdef
  have hF : ∀ x : K', ∀ h ∈ K''.subgroupOf K', F (x * h) = F x := by
    intro x h hh
    simp only [hFdef, Subgroup.coe_mul, map_mul, Module.End.mul_apply, hu _ (Subgroup.mem_subgroupOf.mp hh)]
  rw [map_smul]
  congr 1
  change ρ k (∑ᶠ j : K' ⧸ K''.subgroupOf K', F j.out) = ∑ᶠ j : K' ⧸ K''.subgroupOf K', F j.out
  have hm := AddMonoidHom.map_finsum (ρ k).toAddMonoidHom (f := fun j : K' ⧸ K''.subgroupOf K' => F j.out)
    (Set.toFinite _)
  simp only [LinearMap.toAddMonoidHom_coe] at hm
  rw [hm]
  have hk' : ∀ j : K' ⧸ K''.subgroupOf K', ρ k (F j.out) = F ((⟨k, hk⟩ : K') • j).out := by
    intro j
    have e1 : ((⟨k, hk⟩ : K') • j : K' ⧸ K''.subgroupOf K') = QuotientGroup.mk ((⟨k, hk⟩ : K') * j.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' j]
      rfl
    rw [e1, out_eq_of_inv _ F hF]
    simp only [hFdef, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  simp_rw [hk']
  exact finsum_comp_equiv (MulAction.toPerm (⟨k, hk⟩ : K') : Equiv.Perm (K' ⧸ K''.subgroupOf K'))
    (f := fun j : K' ⧸ K''.subgroupOf K' => F j.out)

theorem avgOp_fix (ρ : Representation ℂ G V) (K' K'' : Subgroup G) [Finite (K' ⧸ K''.subgroupOf K')] (u : V)
    (hu : u ∈ fixed ρ K') : avgOp ρ K' K'' u = u := by
  rw [mem_fixed_iff] at hu
  rw [avgOp_apply]
  have h1 : ∀ j : K' ⧸ K''.subgroupOf K', ρ (j.out : G) u = u := fun j => hu _ (j.out).2
  simp only [h1]
  haveI := Fintype.ofFinite (K' ⧸ K''.subgroupOf K')
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have h2 : (K''.relIndex K' : ℕ) = Fintype.card (K' ⧸ K''.subgroupOf K') := by
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
  have h3 : (Fintype.card (K' ⧸ K''.subgroupOf K') : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := K' ⧸ K''.subgroupOf K')).ne'
  rw [h2, inv_mul_cancel₀ h3, one_smul]

end GlobalTheory.TwTrLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionLowerHeight
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier

namespace GlobalTheory.HtSelfInter

variable {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}

theorem isClosed_of_ne_genericPoint [IsIntegral Z] (hd : topologicalKrullDim Z = 1) {z : Z}
    (hz : z ≠ genericPoint Z) : IsClosed ({z} : Set Z) := by
  rcases Order.krullDim_le_one_iff.1 (show Order.krullDim (IrreducibleCloseds Z) ≤ 1 from hd.le)
    ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩ with h | h
  · refine isClosed_of_closure_subset fun w hw => ?_
    have h₁ : (⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩ : IrreducibleCloseds Z) ≤
        ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩ :=
      closure_minimal (Set.singleton_subset_iff.2 hw) isClosed_closure
    have h₂ : z ∈ closure {w} := h h₁ (subset_closure rfl)
    exact ((specializes_iff_mem_closure.2 h₂).antisymm (specializes_iff_mem_closure.2 hw)).eq
  · exact absurd (IsGenericPoint.eq (Set.eq_univ_of_univ_subset (@h
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩ (Set.subset_univ _)))
      (genericPoint_spec Z)) hz

theorem charZero_residueField_genericPoint [IsIntegral Z] (hc : CharZero Γ(Z, ⊤)) :
    CharZero (Z.residueField (genericPoint Z)) := by
  have h₁ : CharZero Z.functionField :=
    charZero_of_injective_ringHom (fnOf_injective (⊤ : Z.Opens) (Opens.mem_top _))
  let f : Z.functionField →+* Z.residueField (genericPoint Z) := (Z.residue _).hom
  exact charZero_of_injective_ringHom f.injective

theorem eq_genericPoint [IsIntegral Z] {q : Z ⟶ Sp k} (hZ : IsArithVar q 0) {z : Z}
    (hz : CharZero (Z.residueField z)) : z = genericPoint Z := by
  by_contra h
  have := hZ.finite_residueField (isClosed_of_ne_genericPoint hZ.dim_eq h)
  exact not_finite (Z.residueField z)

theorem finite_ringHom [IsIntegral Z] {q : Z ⟶ Sp k} (hZ : IsArithVar q 0) :
    Finite (Z.residueField (genericPoint Z) →+* ℂ) := by
  have hc := charZero_residueField_genericPoint hZ.charZero
  obtain ⟨N, j, _, hj⟩ := hZ.isProjOver
  have := isProper_str k N
  have : IsProper q := hj ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hZ.finite)
  let t := q ≫ spMap (Int.castRingHom k)
  have h₁ : t.QuasiFiniteAt (genericPoint Z) := by
    rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
    have h0 : CharZero ((Sp ℤ).residueField (t (genericPoint Z))) :=
      (t.residueFieldMap (genericPoint Z)).hom.charZero
    have hs (w : t.fiber (t (genericPoint Z))) : t.fiberι _ w = genericPoint Z := by
      have e : t (t.fiberι _ w) = t (genericPoint Z) :=
        (t.range_fiberι (t (genericPoint Z))).le ⟨w, rfl⟩
      rw [← e] at h0
      exact eq_genericPoint hZ (charZero_of_injective_ringHom (t.residueFieldMap _).hom.injective)
    have : Subsingleton (t.fiber (t (genericPoint Z))) := ⟨fun a b =>
      (t.fiberι _).isEmbedding.injective ((hs a).trans (hs b).symm)⟩
    exact isOpen_discrete _
  have h₂ := Scheme.Hom.quasiFiniteAt_iff.1 h₁
  have h₃ : LocallyQuasiFinite (Z.fromSpecResidueField (genericPoint Z) ≫ t) := by
    rw [Scheme.fromSpecResidueField, Category.assoc]
    infer_instance
  rw [← Spec.map_preimage (Z.fromSpecResidueField (genericPoint Z) ≫ t),
    HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite),
    RingHom.ext_int (Spec.preimage (Z.fromSpecResidueField (genericPoint Z) ≫ t)).hom
      ((algebraMap ℚ (Z.residueField (genericPoint Z))).comp (Int.castRingHom ℚ))] at h₃
  have h₄ := RingHom.quasiFinite_algebraMap.1 (RingHom.QuasiFinite.of_comp h₃)
  have : Module.Finite ℚ (Z.residueField (genericPoint Z)) := .of_quasiFinite
  exact .of_equiv _ (RingHom.equivRatAlgHom _ ℂ).symm

theorem nonempty_equiv [IsIntegral Z] {q : Z ⟶ Sp k} (hZ : IsArithVar q 0) :
    Nonempty ((Σ σ : k →+* ℂ, CxPts q σ) ≃ (Z.residueField (genericPoint Z) →+* ℂ)) := by
  have h₁ : Function.Bijective fun y : (Σ σ : k →+* ℂ, CxPts q σ) => y.2.1 := by
    refine ⟨?_, fun y => ⟨⟨(Spec.preimage (y ≫ q)).hom, y, (Spec.map_preimage _).symm⟩, rfl⟩⟩
    rintro ⟨σ, y, hy⟩ ⟨σ', y', hy'⟩ (rfl : y = y')
    obtain rfl : σ = σ' := congrArg CommRingCat.Hom.hom (Spec.map_injective (hy.symm.trans hy'))
    rfl
  have h₂ : Function.Bijective fun φ : Z.residueField (genericPoint Z) →+* ℂ =>
      (Spec.map (CommRingCat.ofHom φ) ≫ Z.fromSpecResidueField (genericPoint Z) : Sp ℂ ⟶ Z) := by
    refine ⟨fun φ ψ h => congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 h)),
      fun y => ?_⟩
    obtain ⟨⟨z, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField ℂ Z).symm.surjective y
    obtain rfl := eq_genericPoint hZ (z := z) φ.hom.charZero
    exact ⟨φ.hom, rfl⟩
  exact ⟨(Equiv.ofBijective _ h₁).trans (Equiv.ofBijective _ h₂).symm⟩

theorem finsum_add_const [IsIntegral Z] {q : Z ⟶ Sp k} (hZ : IsArithVar q 0)
    (f : ∀ σ : k →+* ℂ, CxPts q σ → ℝ) (c : ℝ) :
    ∑ᶠ σ, ∑ᶠ y, (f σ y + c) =
      (∑ᶠ σ, ∑ᶠ y, f σ y) + c * Nat.card (Z.residueField (genericPoint Z) →+* ℂ) := by
  have := finite_ringHom hZ
  have := hZ.finite_emb
  obtain ⟨e⟩ := nonempty_equiv hZ
  have : Finite (Σ σ : k →+* ℂ, CxPts q σ) := .of_equiv _ e.symm
  have (σ : k →+* ℂ) : Finite (CxPts q σ) := .of_injective _ (sigma_mk_injective (i := σ))
  let := Fintype.ofFinite (k →+* ℂ)
  let (σ : k →+* ℂ) := Fintype.ofFinite (CxPts q σ)
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [finsum_eq_sum_of_fintype, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.cast_sum, Finset.mul_sum, mul_comm]

theorem card_ringHom_eq (i : Z ⟶ X) [IsClosedImmersion i] (z : Z) :
    Nat.card (X.residueField (i z) →+* ℂ) = Nat.card (Z.residueField z →+* ℂ) := by
  have hs : Function.Surjective (i.residueFieldMap z).hom := fun a => by
    obtain ⟨b, rfl⟩ := Z.residue_surjective z a
    obtain ⟨c, rfl⟩ := i.stalkMap_surjective z b
    exact ⟨X.residue _ c, congrArg (fun f => f.hom c) (Scheme.residue_residueFieldMap i z)⟩
  let e := RingEquiv.ofBijective _ ⟨(i.residueFieldMap z).hom.injective, hs⟩
  exact Nat.card_congr ⟨fun φ => φ.comp e.symm.toRingHom, fun φ => φ.comp e.toRingHom,
    fun φ => by ext; simp, fun φ => by ext; simp⟩

theorem curveDeg_shift (hX : IsArithVar p D) (L : HermLB p) (t : ℝ) (i : Z ⟶ X) [IsClosedImmersion i]
    [IsIntegral Z] [IsLocallyNoetherian Z] (hc : CharZero Γ(Z, ⊤)) (hd : topologicalKrullDim Z = 1)
    {r : (L.restr i).B.ι → Z.functionFieldˣ} (hr : IsRatSec (L.restr i).B r) :
    ((L.shift (fun _ => t) fun _ => rfl).restr i).curveDeg (r := r) hr =
      (L.restr i).curveDeg hr + t * Nat.card (X.residueField (i (genericPoint Z)) →+* ℂ) := by
  have hZ : IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hc hd
  have e (σ : k →+* ℂ) (y : CxPts (i ≫ p) σ) :
      logNorm (((L.shift (fun _ => t) fun _ => rfl).restr i).φ σ) r y =
        logNorm ((L.restr i).φ σ) r y + -t := by
    have e₁ := ((L.shift (fun _ => t) fun _ => rfl).φ σ).pull_φ i rfl
      (CxPts.pick ((L.restr i).φ σ).isLB y) y
    have e₂ := (L.φ σ).pull_φ i rfl (CxPts.pick ((L.restr i).φ σ).isLB y) y
    have e₃ := e₁.trans (congrArg (· + 2 * t) e₂.symm)
    refine (congrArg (_ - · / 2) e₃).trans ?_
    unfold logNorm
    exact (fun a b : ℝ => (by ring : a - (b + 2 * t) / 2 = a - b / 2 + -t)) _ _
  unfold HermLB.curveDeg
  simp only [e]
  rw [finsum_add_const hZ, card_ringHom_eq]
  exact (fun a b c : ℝ => (by ring : a - (b + -t * c) = a - b + t * c)) _ _ _

theorem isAlgPt_genericPoint (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (hc : CharZero Γ(Z, ⊤))
    (hd : topologicalKrullDim Z = 1) : IsAlgPt (i (genericPoint Z)) := by
  have := charZero_residueField_genericPoint hc
  refine ⟨(i.residueFieldMap _).hom.charZero, ?_⟩
  have h₁ := (genericPoint_spec Z).image i.continuous
  rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
  rw [h₁.def, ← hd]
  exact (IsHomeomorph.topologicalKrullDim_eq _
    i.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm

theorem isNef_shift (hX : IsArithVar p D) {L : HermLB p} {e : ℝ} (hs : L.SemiPos D) (hf : NefFib L)
    (hh : ∀ x, IsAlgPt x → ∃ b, IsPtHt L x b ∧ e ≤ b) :
    (L.shift (fun _ => -e) fun _ => rfl).IsNef D := by
  refine ⟨hs.shift _ _, fun Z i _ _ κ _ _ _ hd => hf Z i κ hd, ?_⟩
  intro Z i _ _ _ hc hd
  obtain ⟨r, hr⟩ := exists_isRatSec (L.restr i).isLB
  obtain ⟨b, ⟨h, H, hb⟩, hle⟩ := hh _ (isAlgPt_genericPoint i hc hd)
  refine ⟨r, hr, ?_⟩
  rw [curveDeg_shift hX L (-e) i hc hd hr, ← H.point Z i hc hd r hr, hb, ← add_mul]
  exact mul_nonneg (by linarith) (Nat.cast_nonneg _)

end GlobalTheory.HtSelfInter
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualWeylWeightProjector
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualWeylWeightProjector
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.UG

namespace GlobalTheory.ExpFrame

def rowProj (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (w : Fin N → ℕ) :
    dualWeyl O N N ν →ₗ[O] dualWeyl O N N ν :=
  (weightedHomogeneousComponent (rowW N N) w).restrict
    (fun x hx => dualWeylModuleRowGraded O N N ν w x hx)

theorem exists_unique_isProj : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (τ : ι)
    (w : Fin N → ℕ), ∃ a, IsProj O N lam τ w a ∧ ∀ a', IsProj O N lam τ w a' → a' = a := by
  intro O _ N ι _ _ lam τ w
  have hP : IsProj O N lam τ w (atFactor τ (rowProj O N (res N (lam τ)) w)) := by
    intro x y hy
    unfold atFactor
    rw [PiTensorProduct.map_tprod]
    congr 1
    funext σ
    by_cases h : σ = τ
    · subst h
      simp only [Function.update_self, LinearMap.restrict_apply, rowProj]
      exact Subtype.ext hy.symm
    · simp [Function.update_of_ne h]
  refine ⟨_, hP, fun a' ha' => ?_⟩
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply]
  let y : dualWeyl O N N (res N (lam τ)) := rowProj O N (res N (lam τ)) w (x τ)
  exact (ha' x y rfl).trans (hP x y rfl).symm

end GlobalTheory.ExpFrame

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualWeylWeightProjectorStatement
open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_dualWeylWeightProjector : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (τ : ι) (w : Fin N → ℕ), ∃ a, IsProj O N lam τ w a ∧ ∀ a', IsProj O N lam τ w a' → a' = a := by
  first | exact @GlobalTheory.ExpFrame.exists_unique_isProj | exact GlobalTheory.ExpFrame.exists_unique_isProj | (intros; apply GlobalTheory.ExpFrame.exists_unique_isProj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeLevelFamilyIff
noncomputable section

open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

def tens {G H : Type} (f : G → ℂ) (g : H → ℂ) : G × H → ℂ := fun y => f y.1 * g y.2

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def geomSt2 (a b : ℕ) (S : Set (Pl E)) (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b)
    (φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) : ℂ :=
  ∑ᶠ p ∈ {p : E[X] × E[X] | p.1 ∈ Ell E a ∧ p.2 ∈ Ell E b ∧ IsCoprime p.1 p.2},
    kap p.1 * kap p.2 * chW l₁ p.1 * chW l₂ p.2 * ∏ᶠ w ∈ S, stTw2 a b w (atPl w p.1) (atPl w p.2) (φ w)

end GlobalTheory.BCT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasString
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CuspRep

namespace GlobalTheory.GalDef

def wAt {n : ℕ} (lam : DomWeight n) (k : ℕ) : ℤ := if h : k < n then lam.w ⟨k, h⟩ else 0

def IsRunAt {n : ℕ} (lam : DomWeight n) (p t : ℕ) : Prop :=
  p + t ≤ n ∧ (∀ k, p ≤ k → k < p + t → wAt lam k = wAt lam p) ∧ (1 ≤ p → wAt lam p < wAt lam (p - 1)) ∧
    (p + t < n → wAt lam (p + t) < wAt lam p)

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def jumpsOf (ι : Qbar l ≃+* ℂ) (lam : (E →+* ℂ) → DomWeight n) (τ : E →+* Qbar l) : Multiset ℤ :=
  Finset.univ.val.map fun k : Fin n => (k : ℤ) - (lam (ι.toRingHom.comp τ)).w k

def FrobSat (ι : Qbar l ≃+* ℂ) (π : Submodule ℂ (UA E n → ℂ)) (sgn : ℤˣ) (cp : G E Ω → Polynomial (Qbar l)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → IsUnramU π w →
    ∀ (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (T : Multiset ℂˣ),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ → GlobalTheory.LFun.HasSatGL w σ.ρ T →
      ∀ (B : ValuationSubring Ω) (g : G E Ω), IsPlaceOver (F := E) B w → IsFrob (F := E) B (normV w) g →
        cp (g ^ (sgn : ℤ)) = (T.map fun z : ℂˣ =>
          X - C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((n : ℂ) - 1) / 2)))).prod

def HasString (l : ℕ) (π : Submodule ℂ (UA E n → ℂ)) (t : ℕ) : Prop :=
  ∃ w : HeightOneSpectrum (𝓞 E), IsSplitAt w ∧ ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧ IsUnramU π w ∧
    ∃ (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (T : Multiset ℂˣ) (ν : ℂ),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ GlobalTheory.LFun.HasSatGL w σ.ρ T ∧ ‖ν‖ = 1 ∧
        (Multiset.range t).map (fun c : ℕ => ν * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((t : ℂ) - 1) / 2 - c)) ≤
          T.map fun z : ℂˣ => (z : ℂ)

end GlobalTheory.GalDef

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatricesDiscreteCocompactAdelicMatrixSpa
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatricesDiscreteCocompactAdelicMatrixSpa
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.AdelicMatrixLatticeF

theorem lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ),
    IsTopologicalAddGroup (WOF F E nS nT) ∧ LocallyCompactSpace (WOF F E nS nT) ∧
    SecondCountableTopology (WOF F E nS nT) ∧ T2Space (WOF F E nS nT) ∧ DiscreteTopology (ratLF F E nS nT) ∧
    ∃ K : Set (WOF F E nS nT), IsCompact K ∧ ∀ x : WOF F E nS nT, ∃ γ ∈ ratLF F E nS nT, γ + x ∈ K := by
  intro F E _ _ _ _ _ nS nT
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele _
  have : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField _
  have : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩
  have : IsTopologicalRing (AEF F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : LocallyCompactSpace (AEF F E) := e.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (AEF F E) := e.secondCountableTopology
  have : T2Space (AEF F E) := e.isEmbedding.t2Space
  have hg : IsTopologicalAddGroup (WOF F E nS nT) :=
    inferInstanceAs (IsTopologicalAddGroup (Fin nT → Fin nS → AEF F E))
  refine ⟨hg, inferInstanceAs (LocallyCompactSpace (Fin nT → Fin nS → AEF F E)),
    inferInstanceAs (SecondCountableTopology (Fin nT → Fin nS → AEF F E)),
    inferInstanceAs (T2Space (Fin nT → Fin nS → AEF F E)), ?_, ?_⟩
  · obtain ⟨U, hU, hx⟩ := GlobalTheory.AdelicMatrixLattice.discrete_tensor (F := F) (E := E) (AF F)
      (GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F)
    have hN : (Set.univ.pi fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => U) ∈
        nhds (0 : WOF F E nS nT) :=
      set_pi_mem_nhds Set.finite_univ fun _ _ => set_pi_mem_nhds Set.finite_univ fun _ _ => hU
    refine discreteTopology_of_isOpen_singleton_zero ?_
    rw [isOpen_singleton_iff_nhds_eq_pure]
    refine le_antisymm (Filter.le_pure_iff.2 ?_) (pure_le_nhds _)
    have hc : ContinuousAt (fun x : ratLF F E nS nT => (x : WOF F E nS nT)) 0 :=
      continuous_subtype_val.continuousAt
    refine Filter.mem_of_superset (hc.preimage_mem_nhds hN) ?_
    rintro ⟨_, y, rfl⟩ hy
    have hy0 : y = 0 := by
      funext i j
      exact hx _ (hy i (Set.mem_univ i) j (Set.mem_univ j))
    subst hy0
    exact Subtype.ext (map_zero _)
  · obtain ⟨K, hK, hx⟩ := GlobalTheory.AdelicMatrixLattice.cocompact_tensor (F := F) (E := E) (AF F)
      (GlobalTheory.AdeleCocompact.exists_compact_adele F)
    choose c hc using hx
    refine ⟨Set.univ.pi fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K,
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK, fun x => ?_⟩
    exact ⟨_, ⟨Matrix.of fun i j => c (x i j), rfl⟩, fun i _ j _ => hc (x i j)⟩

end GlobalTheory.AdelicMatrixLatticeF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatricesDiscreteCocompactAdelicMatrixSpaStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ),
    IsTopologicalAddGroup (WOF F E nS nT) ∧ LocallyCompactSpace (WOF F E nS nT) ∧
    SecondCountableTopology (WOF F E nS nT) ∧ T2Space (WOF F E nS nT) ∧ DiscreteTopology (ratLF F E nS nT) ∧
    ∃ K : Set (WOF F E nS nT), IsCompact K ∧ ∀ x : WOF F E nS nT, ∃ γ ∈ ratLF F E nS nT, γ + x ∈ K := by
  first | exact @GlobalTheory.AdelicMatrixLatticeF.lattice | exact GlobalTheory.AdelicMatrixLatticeF.lattice | (intros; apply GlobalTheory.AdelicMatrixLatticeF.lattice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleQuotientCompactRepresentatives
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom

namespace GlobalTheory.AdeleCocompactExt

theorem exists_compact_adele_ext : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ C : Set (AE F E), IsCompact C ∧ ∀ a : AE F E, ∃ α : E, a - inclR (F := F) (AF F) α ∈ C := by
  intro F E _ _ _ _ _
  classical
  haveI : IsModuleTopology (AF F) (AE F E) := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.modTop
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  haveI : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul (AF F) (AE F E)
  obtain ⟨K, hK, hK'⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  let b := Module.finBasis F E
  let B : Module.Basis (Fin (Module.finrank F E)) (AF F) (AE F E) := Algebra.TensorProduct.basis (AF F) b
  let φ : (Fin (Module.finrank F E) → AF F) → AE F E := fun c => ∑ i, c i • B i
  have hφ : Continuous φ := continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  refine ⟨φ '' Set.univ.pi (fun _ => K), (isCompact_univ_pi fun _ => hK).image hφ, fun a => ?_⟩
  choose x hx using fun i => hK' (B.repr a i)
  refine ⟨∑ i, x i • b i, fun i => B.repr a i - algebraMap F (AF F) (x i), fun i _ => hx i, ?_⟩
  have hB : ∀ i, B i = (1 : AF F) ⊗ₜ[F] b i := fun i => Algebra.TensorProduct.basis_apply _ _
  have hincl : inclR (F := F) (AF F) (∑ i, x i • b i) = ∑ i, algebraMap F (AF F) (x i) • B i := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_smul,
      Algebra.TensorProduct.includeRight_apply, hB, algebraMap_smul]
  simp only [φ, sub_smul, Finset.sum_sub_distrib, hincl]
  rw [B.sum_repr a]

end GlobalTheory.AdeleCocompactExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionHermitianSignature
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionHermitianSignature
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

namespace GlobalTheory.PlaneSkew.CartanInv

theorem exists_isCartan : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (r s : ℕ), HasSig M r s → ∃ θ, IsCartan M θ :=
  GlobalTheory.CartanEx.exists_isCartan

end GlobalTheory.PlaneSkew.CartanInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionHermitianSignatureStatement
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartanInvolution_hermitianSignature : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (r s : ℕ), HasSig M r s → ∃ θ, IsCartan M θ := by
  first | exact @GlobalTheory.PlaneSkew.CartanInv.exists_isCartan | exact GlobalTheory.PlaneSkew.CartanInv.exists_isCartan | (intros; apply GlobalTheory.PlaneSkew.CartanInv.exists_isCartan <;> assumption)
end
end
