module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingIsoOfComponentIsos

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
noncomputable section

open NumberField MeasureTheory Filter Topology
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
open PositivityTheory.Rg.Rs.An

namespace GlobalTheory.CompanionTheory.Conc

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def UBnd {ι : Type*} (f : ι → AdelicGLn.AdelicGL K n → ℂ) (m : ℕ → ℝ) : Prop :=
  ∀ ω : Set (AdelicGLn.AdelicGL K n), IsCompact ω → ω ⊆ (adelicBorel (K := K) (n := n) : Set _) → ∀ t₀ : ℝ,
    ∀ Q : Set (AdelicGLn.AdelicGL K n), IsCompact Q → ∃ C : ℝ, ∀ i, ∀ b ∈ ω, ∀ x : Fin n → ℝ, (∀ r, -t₀ ≤ sr x r) →
      ∀ q ∈ Q, ‖f i (b * tor K x * q)‖ ≤ C * Real.exp (∑ r ∈ Finset.range n, m r * sr x r)

structure UFam {ι : Type*} (f : ι → AdelicGLn.AdelicGL K n → ℂ) : Prop where
  cont : ∀ i, Continuous (f i)
  left : ∀ i, IsLeftInvariant (f i)
  level : ∃ U : Subgroup (AdelicGLn.integralFiniteGL K n), IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) ∧
    ∀ i (g : AdelicGLn.AdelicGL K n) (u : U),
      f i (g * finEmb K n ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n)) = f i g

abbrev mat (y : archGroup K n) : ArchMatrix K n := ((y : (ArchMatrix K n)ˣ) : ArchMatrix K n)

structure Ker [MeasurableSpace (archGroup K n)] (ν : Measure (archGroup K n)) (β : archGroup K n → ℝ) : Prop where
  cont : Continuous β
  cpt : HasCompactSupport β
  nonneg : ∀ y, 0 ≤ β y
  mass : ∫ y, β y ∂ν = 1
  lip : ∃ L : ℝ, 0 ≤ L ∧ ∀ y y', |β y - β y'| ≤ L * ‖mat y - mat y'‖

def sm [MeasurableSpace (archGroup K n)] (ν : Measure (archGroup K n)) (β : archGroup K n → ℝ)
    (f : AdelicGLn.AdelicGL K n → ℂ) (x : AdelicGLn.AdelicGL K n) : ℂ :=
  ∫ y, (β y : ℂ) * f (x * infEmb K n y) ∂ν

theorem continuous_mat : Continuous (mat : archGroup K n → ArchMatrix K n) :=
  Units.continuous_val.comp continuous_subtype_val

theorem isCompact_ball {ρ : ℝ} (hρ : ρ < 1) :
    IsCompact {y : archGroup K n | ‖mat y - 1‖ ≤ ρ} := by
  have hemb : IsEmbedding (fun y : archGroup K n => mat y) :=
    Units.isOpenEmbedding_val.isEmbedding.comp (Topology.IsEmbedding.subtypeVal)
  have hsub : Metric.closedBall (1 : ArchMatrix K n) ρ ⊆ Set.range (fun y : archGroup K n => mat y) := by
    intro a ha
    have h1 : ‖1 - a‖ < 1 := by
      rw [norm_sub_rev]
      exact lt_of_le_of_lt (by simpa [dist_eq_norm] using ha) hρ
    refine ⟨⟨Units.oneSub (1 - a) h1, Subgroup.mem_top _⟩, ?_⟩
    simp [mat]
  have := (hemb.isInducing.isCompact_preimage_iff hsub).2 (isCompact_closedBall (1 : ArchMatrix K n) ρ)
  convert this using 1
  ext y
  simp [dist_eq_norm]

theorem tent_lip {A : Type*} [SeminormedAddCommGroup A] {ρ : ℝ} (hρ0 : 0 < ρ) (a b e : A) :
    |max 0 (1 - ‖a - e‖ / ρ) - max 0 (1 - ‖b - e‖ / ρ)| ≤ ρ⁻¹ * ‖a - b‖ := by
  have h1 : |max 0 (1 - ‖a - e‖ / ρ) - max 0 (1 - ‖b - e‖ / ρ)| ≤ |(1 - ‖a - e‖ / ρ) - (1 - ‖b - e‖ / ρ)| := by
    simp only [max_comm (0 : ℝ)]
    exact abs_max_sub_max_le_abs _ _ _
  have h2 : (1 - ‖a - e‖ / ρ) - (1 - ‖b - e‖ / ρ) = ρ⁻¹ * (‖b - e‖ - ‖a - e‖) := by
    field_simp
    ring
  rw [h2, abs_mul, abs_of_pos (inv_pos.2 hρ0)] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hρ0.le))
  have h3 := abs_norm_sub_norm_le (b - e) (a - e)
  rw [sub_sub_sub_cancel_right] at h3
  rw [norm_sub_rev a b]
  exact h3

theorem exists_ker [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n))
    [ν.IsHaarMeasure] {U : Set (archGroup K n)} (hU : U ∈ 𝓝 1) :
    ∃ β, Ker ν β ∧ tsupport β ⊆ U := by
  have hc : ContinuousAt (fun y : archGroup K n => mat y) 1 := continuous_mat.continuousAt

  have hb : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ {y : archGroup K n | ‖mat y - 1‖ ≤ ρ} ⊆ U := by
    have hemb : IsInducing (fun y : archGroup K n => mat y) :=
      (Units.isOpenEmbedding_val.isEmbedding.comp (Topology.IsEmbedding.subtypeVal)).isInducing
    rw [hemb.nhds_eq_comap, mem_comap] at hU
    obtain ⟨t, ht, hsub⟩ := hU
    have h1 : mat (1 : archGroup K n) = 1 := rfl
    rw [h1] at ht
    obtain ⟨e, he, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 ht
    refine ⟨min e (1 / 2), by positivity, by
      exact lt_of_le_of_lt (min_le_right _ _) (by norm_num), fun y hy => hsub ?_⟩
    apply hball
    simp only [Metric.mem_closedBall, dist_eq_norm]
    exact le_trans hy (min_le_left _ _)
  obtain ⟨ρ, hρ0, hρ1, hρU⟩ := hb
  set β₀ : archGroup K n → ℝ := fun y => max 0 (1 - ‖mat y - 1‖ / ρ) with hβ₀
  have hβc : Continuous β₀ :=
    continuous_const.max (continuous_const.sub ((continuous_mat.sub continuous_const).norm.div_const _))
  have hsupp : Function.support β₀ ⊆ {y : archGroup K n | ‖mat y - 1‖ ≤ ρ} := by
    intro y hy
    by_contra h
    apply hy
    have h' : ρ < ‖mat y - 1‖ := not_le.1 h
    have : 1 < ‖mat y - 1‖ / ρ := (one_lt_div hρ0).2 h'
    exact max_eq_left (by linarith)
  have hclosed : IsClosed {y : archGroup K n | ‖mat y - 1‖ ≤ ρ} :=
    isClosed_le (continuous_mat.sub continuous_const).norm continuous_const
  have hts : tsupport β₀ ⊆ {y : archGroup K n | ‖mat y - 1‖ ≤ ρ} := closure_minimal hsupp hclosed
  have hcs : HasCompactSupport β₀ := (isCompact_ball hρ1).of_isClosed_subset (isClosed_tsupport _) hts
  have hnn : ∀ y, 0 ≤ β₀ y := fun y => le_max_left _ _
  have hpos : 0 < ∫ y, β₀ y ∂ν := by
    refine hβc.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs hnn (x := 1) ?_
    have : β₀ 1 = 1 := by simp [hβ₀, mat]
    rw [this]; exact one_ne_zero
  set c := ∫ y, β₀ y ∂ν with hcdef
  have hcpos : 0 ≤ c⁻¹ := inv_nonneg.2 hpos.le
  have hk : Ker ν (fun y => c⁻¹ * β₀ y) := by
    refine { cont := continuous_const.mul hβc
             cpt := hcs.mul_left
             nonneg := fun y => mul_nonneg hcpos (hnn y)
             mass := ?_
             lip := ⟨c⁻¹ * ρ⁻¹, mul_nonneg hcpos (inv_nonneg.2 hρ0.le), fun y y' => ?_⟩ }
    · rw [integral_const_mul, ← hcdef, inv_mul_cancel₀ hpos.ne']
    · rw [← mul_sub, abs_mul, abs_of_nonneg hcpos, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hcpos
      exact tent_lip hρ0 _ _ _
  exact ⟨_, hk, (tsupport_mul_subset_right (f := fun _ => c⁻¹) (g := β₀)).trans (hts.trans hρU)⟩

end GlobalTheory.CompanionTheory.Conc

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningAffinePreimage
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningAffinePreimage
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open scoped TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem mem_ker_smul_top_of_one_tmul_eq_zero {A A' M : Type*} [CommRing A] [CommRing A'] [Algebra A A']
    (hs : Function.Surjective (algebraMap A A')) [AddCommGroup M] [Module A M] (x : M)
    (h : (1 : A') ⊗ₜ[A] x = 0) :
    x ∈ (RingHom.ker (algebraMap A A')) • (⊤ : Submodule A M) := by
  have ex : Function.Exact (Submodule.subtype (RingHom.ker (algebraMap A A')))
      (Algebra.linearMap A A') := fun a => by
    constructor
    · intro ha
      exact ⟨⟨a, ha⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact b.2
  have hs' : Function.Surjective (Algebra.linearMap A A') := hs
  have ex2 := rTensor_exact M ex hs'
  have h0 : LinearMap.rTensor M (Algebra.linearMap A A') ((1 : A) ⊗ₜ[A] x) = 0 := by
    simpa using h
  obtain ⟨z, hz⟩ := (ex2 _).1 h0
  have key : ∀ z : (RingHom.ker (algebraMap A A')) ⊗[A] M,
      TensorProduct.lid A M (LinearMap.rTensor M
        (Submodule.subtype (RingHom.ker (algebraMap A A'))) z) ∈
        (RingHom.ker (algebraMap A A')) • (⊤ : Submodule A M) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simpa only [map_add (f := _)] using add_mem ha hb
    | tmul a m => simpa using Submodule.smul_mem_smul a.2 Submodule.mem_top
  have := key z
  rw [hz] at this
  simpa using this

theorem cst_comp_spec {X : Scheme.{0}} {R A : Type} [CommRing R] [CommRing A]
    (f : X ⟶ Spec (CommRingCat.of A)) (q : R →+* A) (V : X.Opens) (r : R) :
    cst (f ≫ Spec.map (CommRingCat.ofHom q)) V r = cst f V (q r) := by
  have := appLE_cst (f := f ≫ Spec.map (CommRingCat.ofHom q)) (f' := f) (π := 𝟙 X) (g := q)
    (by simp) (V := V) (V' := V) le_rfl r
  have e : (𝟙 X : X ⟶ X).appLE V V le_rfl = 𝟙 _ := by
    simp [Scheme.Hom.appLE]
    exact X.presheaf.map_id _
  rw [e] at this
  exact this

theorem pull_surjective_ker {A A' : Type} [CommRing A] [CommRing A'] (g : A →+* A')
    (hg : Function.Surjective g) {X X' : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of A)}
    {f' : X' ⟶ Spec (CommRingCat.of A')} {π : X' ⟶ X}
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) {M : LB X} (hM : M.IsLB)
    {V : X.Opens} (hV : IsAffineOpen V) :
    Function.Surjective (SecOn.pullLE M π V _ le_rfl) ∧
      ∀ s : SecOnR f M V, SecOn.pullLE M π V _ le_rfl ((SecOnR.of f M V).symm s) = 0 →
        s ∈ (RingHom.ker g) • (⊤ : Submodule A (SecOnR f M V)) := by
  letI := g.toAlgebra
  have hb := SecOnR.baseChangeHom_bijective (R := A) (R' := A') hM H hV rfl
  constructor
  · intro y
    obtain ⟨z, hz⟩ := hb.2 y
    obtain ⟨x, rfl⟩ := TensorProduct.mk_surjective A (SecOnR f M V) A' hg z
    refine ⟨x, ?_⟩
    have h := (SecOnR.baseChangeHom_tmul (R := A) (R' := A') H.w le_rfl 1 x).symm.trans hz
    rw [one_smul] at h
    exact h
  · intro s hs
    refine mem_ker_smul_top_of_one_tmul_eq_zero hg s (hb.1 ?_)
    rw [map_zero, SecOnR.baseChangeHom_tmul, one_smul]
    exact hs

theorem mem_smul_top_of_comp {X : Scheme.{0}} {R A : Type} [CommRing R] [CommRing A]
    (f : X ⟶ Spec (CommRingCat.of A)) (q : R →+* A) (M : LB X) (V : X.Opens) (J : Ideal A)
    (K : Ideal R) (hK : ∀ a ∈ J, ∃ r ∈ K, q r = a) (s : SecOnR f M V)
    (hs : s ∈ J • (⊤ : Submodule A (SecOnR f M V))) :
    SecOnR.of (f ≫ Spec.map (CommRingCat.ofHom q)) M V ((SecOnR.of f M V).symm s) ∈
      K • (⊤ : Submodule R (SecOnR (f ≫ Spec.map (CommRingCat.ofHom q)) M V)) := by
  induction hs using Submodule.smul_induction_on' with
  | smul a ha m _ =>
    obtain ⟨r, hr, rfl⟩ := hK a ha
    have e : SecOnR.of (f ≫ Spec.map (CommRingCat.ofHom q)) M V
        ((SecOnR.of f M V).symm (q r • m)) =
        r • SecOnR.of (f ≫ Spec.map (CommRingCat.ofHom q)) M V ((SecOnR.of f M V).symm m) := by
      rw [SecOnR.smul_def r, cst_comp_spec]
      rfl
    rw [e]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  | add x _ y _ hx hy =>
    rw [map_add (f := _), map_add (f := _)]
    exact add_mem hx hy

theorem redL_surjective_ker : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (L : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e))) (hL : ∀ e, (L e).IsLB ∧ (w e).IsGen) (e : ℕ) (V : (Y (e + 1)).left.Opens) (V' : (Y e).left.Opens) (h : β e ⁻¹ᵁ V = V'), IsAffineOpen V → Function.Surjective (redL I Y β hβ L w hL e V V' h.ge) ∧ LinearMap.ker (redL I Y β hβ L w hL e V V' h.ge) = I ^ (e + 1) • ⊤ := by
  intro R _ I Y β hβ L w hL e V V' h hV
  subst h
  have hle : I ^ (e + 1 + 1) ≤ I ^ (e + 1) := Ideal.pow_le_pow_right (Nat.le_succ (e + 1))
  have hq : Function.Surjective (Ideal.Quotient.factor hle) := Ideal.Quotient.factor_surjective hle
  obtain ⟨h1, h2⟩ := pull_surjective_ker (Ideal.Quotient.factor hle) hq (hβ e) (hL (e + 1)).1 hV
  let E := SecOnR.linEquiv (toR I Y e) (SecOn.congr (hL e).1 (LB.isLB_pull (hL (e + 1)).1 (β e)) (w e)
    (hL e).2 (β e ⁻¹ᵁ V))
  have hred (s) : redL I Y β hβ L w hL e V _ le_rfl s =
      E.symm (SecOnR.pull (L (e + 1)) (toR_w I Y β hβ e) V _ le_rfl s) := rfl
  refine ⟨fun y => ?_, le_antisymm (fun s hs => ?_) (Submodule.smul_le.2 fun r hr s _ => ?_)⟩
  · obtain ⟨x, hx⟩ := h1 (E y)
    exact ⟨x, (hred x).trans ((E.symm_apply_eq).2 hx)⟩
  · have hs0 := (E.symm.map_eq_zero_iff).1 ((hred s).symm.trans (LinearMap.mem_ker.1 hs))
    refine mem_smul_top_of_comp (Y (e + 1)).hom (Ideal.Quotient.mk (I ^ (e + 1 + 1))) (L (e + 1)) V
      (RingHom.ker (Ideal.Quotient.factor hle)) (I ^ (e + 1)) (fun a ha => ?_) s (h2 s hs0)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨r, ?_, rfl⟩
    rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at ha
    exact ha
  · rw [LinearMap.mem_ker, map_smul, SecOnR.smul_def]
    have e0 : cst (toR I Y e) (β e ⁻¹ᵁ V) r = 0 := by
      rw [toR, cst_comp_spec, Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
    rw [e0, zero_smul]

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningAffinePreimageStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_affine_preimage : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (L : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e))) (hL : ∀ e, (L e).IsLB ∧ (w e).IsGen) (e : ℕ) (V : (Y (e + 1)).left.Opens) (V' : (Y e).left.Opens) (h : β e ⁻¹ᵁ V = V'), IsAffineOpen V → Function.Surjective (redL I Y β hβ L w hL e V V' h.ge) ∧ LinearMap.ker (redL I Y β hβ L w hL e V V' h.ge) = I ^ (e + 1) • ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.redL_surjective_ker | exact GlobalTheory.CompanionTheory.FormalAlg.Lift.redL_surjective_ker | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.Lift.redL_surjective_ker <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningRestrictionCompatibleOpens
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningRestrictionCompatibleOpens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem redL_restrict : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (L : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e))) (hL : ∀ e, (L e).IsLB ∧ (w e).IsGen) (e : ℕ) (V W : (Y (e + 1)).left.Opens) (V' W' : (Y e).left.Opens) (hV : V' ≤ β e ⁻¹ᵁ V) (hW : W' ≤ β e ⁻¹ᵁ W) (h : W ≤ V) (h' : W' ≤ V') (x : SecOnR (toR I Y (e + 1)) (L (e + 1)) V), redL I Y β hβ L w hL e W W' hW (SecOnR.restrict _ _ h x) = SecOnR.restrict _ _ h' (redL I Y β hβ L w hL e V V' hV x) := by
  intro R _ I Y β hβ L w hL e V W V' W' hV hW h h' x
  have key := SecOnR.pull_restrict (M := L (e + 1)) (toR_w I Y β hβ e) h h' hV hW x
  apply (SecOnR.linEquiv (toR I Y e) (SecOn.congr (hL e).1 (LB.isLB_pull (hL (e + 1)).1 (β e)) (w e)
    (hL e).2 W')).injective
  simp only [redL, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [key]
  obtain ⟨y, hy⟩ := (SecOnR.linEquiv (toR I Y e) (SecOn.congr (hL e).1 (LB.isLB_pull (hL (e + 1)).1 (β e)) (w e)
    (hL e).2 V')).surjective (SecOnR.pull (L (e + 1)) (toR_w I Y β hβ e) V V' hV x)
  rw [← hy, LinearEquiv.symm_apply_apply]
  exact (SecOn.congr_restrict (hL e).1 (LB.isLB_pull (hL (e + 1)).1 (β e)) (w e) (hL e).2 h' y).symm

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningRestrictionCompatibleOpensStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_restriction_compatible_opens : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (L : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e))) (hL : ∀ e, (L e).IsLB ∧ (w e).IsGen) (e : ℕ) (V W : (Y (e + 1)).left.Opens) (V' W' : (Y e).left.Opens) (hV : V' ≤ β e ⁻¹ᵁ V) (hW : W' ≤ β e ⁻¹ᵁ W) (h : W ≤ V) (h' : W' ≤ V') (x : SecOnR (toR I Y (e + 1)) (L (e + 1)) V), redL I Y β hβ L w hL e W W' hW (SecOnR.restrict _ _ h x) = SecOnR.restrict _ _ h' (redL I Y β hβ L w hL e V V' hV x) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.redL_restrict | exact GlobalTheory.CompanionTheory.FormalAlg.Lift.redL_restrict | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.Lift.redL_restrict <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullbackOfKernelSup
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullbackOfKernelSup
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)

namespace GlobalTheory.CompanionTheory.GE.PbKer

theorem isPullback_of_ker_eq_sup {X A B Z : Scheme.{0}} (a : A ⟶ X) (b : B ⟶ X) (f : Z ⟶ A)
    (g : Z ⟶ B) [IsClosedImmersion a] [IsClosedImmersion b] [IsClosedImmersion (f ≫ a)]
    (h : f ≫ a = g ≫ b)
    (hk : Scheme.Hom.ker (f ≫ a) = Scheme.Hom.ker a ⊔ Scheme.Hom.ker b) :
    IsPullback f g a b := by
  have hle : ∀ {W : Scheme.{0}} (u : W ⟶ A) (v : W ⟶ B), u ≫ a = v ≫ b →
      Scheme.Hom.ker (f ≫ a) ≤ Scheme.Hom.ker (u ≫ a) := by
    intro W u v huv
    rw [hk]
    refine sup_le (Scheme.Hom.le_ker_comp u a) ?_
    rw [huv]
    exact Scheme.Hom.le_ker_comp v b
  refine IsPullback.of_isLimit' ⟨h⟩ ?_
  refine PullbackCone.IsLimit.mk h
    (fun s => IsClosedImmersion.lift (f ≫ a) (s.fst ≫ a) (hle s.fst s.snd s.condition)) ?_ ?_ ?_
  · intro s
    rw [← cancel_mono a, Category.assoc]
    exact IsClosedImmersion.lift_fac _ _ _
  · intro s
    rw [← cancel_mono b, Category.assoc, ← h, ← s.condition]
    exact IsClosedImmersion.lift_fac _ _ _
  · intro s m hm1 _
    rw [← cancel_mono (f ≫ a), IsClosedImmersion.lift_fac, ← Category.assoc, hm1]

end GlobalTheory.CompanionTheory.GE.PbKer
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullbackOfKernelSupStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.is_pullback_of_kernel_sup : ∀ {X A B Z : Scheme.{0}} (a : A ⟶ X) (b : B ⟶ X) (f : Z ⟶ A) (g : Z ⟶ B)
    [IsClosedImmersion a] [IsClosedImmersion b] [IsClosedImmersion (f ≫ a)], f ≫ a = g ≫ b →
    Scheme.Hom.ker (f ≫ a) = Scheme.Hom.ker a ⊔ Scheme.Hom.ker b → IsPullback f g a b := by
  first | exact @GlobalTheory.CompanionTheory.GE.PbKer.isPullback_of_ker_eq_sup | exact GlobalTheory.CompanionTheory.GE.PbKer.isPullback_of_ker_eq_sup | (intros; apply GlobalTheory.CompanionTheory.GE.PbKer.isPullback_of_ker_eq_sup <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningSectionHomogeneousForm
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningSectionHomogeneousForm
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace Sp spMap)

namespace GlobalTheory.CompanionTheory.GE

theorem comp_app_eq_zero_iff {X Y Z : Scheme.{0}} (b : X ⟶ Y) [IsIso b] (g : Y ⟶ Z) (U : Z.Opens)
    (s : Γ(Z, U)) : ((b ≫ g).app U).hom s = 0 ↔ (g.app U).hom s = 0 := by
  rw [Scheme.Hom.comp_app]
  have hi : Function.Injective (b.app (g ⁻¹ᵁ U)).hom :=
    (ConcreteCategory.bijective_of_isIso (b.app (g ⁻¹ᵁ U))).1
  change (b.app (g ⁻¹ᵁ U)).hom ((g.app U).hom s) = 0 ↔ _
  exact map_eq_zero_iff _ hi

theorem mem_ker_thickι_iff {R : Type} [CommRing R] (I : Ideal R) (N e : ℕ) (k : Fin (N + 1))
    (s : Γ(PSpace R N, GlobalTheory.ProjSpace.chart R N k)) :
    s ∈ (Scheme.Hom.ker (thickι R I N e)).ideal
        ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩ ↔
      ((GlobalTheory.ProjSpace.baseChange N (Ideal.Quotient.mk (I ^ (e + 1)))).app
        (GlobalTheory.ProjSpace.chart R N k)).hom s = 0 := by
  have h := GlobalTheory.ProjSpace.isPullback_baseChange N (Ideal.Quotient.mk (I ^ (e + 1)))
  have hb : h.isoPullback.hom ≫ thickι R I N e =
      GlobalTheory.ProjSpace.baseChange N (Ideal.Quotient.mk (I ^ (e + 1))) := h.isoPullback_hom_fst
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker, ← hb]
  exact (comp_app_eq_zero_iff h.isoPullback.hom (thickι R I N e) _ s).symm

theorem formOn_eq_zero_iff {R : Type} [CommRing R] {N : ℕ} (k : Fin (N + 1))
    {V : (PSpace R N).Opens} (hV : V = GlobalTheory.ProjSpace.chart R N k) (hle : V ≤ GlobalTheory.ProjSpace.chart R N k)
    {n : ℕ} {f : MvPolynomial (Fin (N + 1)) R} (hf : f.IsHomogeneous n) :
    GlobalTheory.ProjSpace.formOn V k hle n f hf = 0 ↔ f = 0 := by
  subst hV
  rw [← GlobalTheory.ProjSpace.formOn_zero (U := GlobalTheory.ProjSpace.chart R N k) (i := k) (hi := le_rfl) (n := n)]
  exact GlobalTheory.ProjSpace.formOn_chart_inj R N k hf _


open scoped GlobalTheory.ProjSpace in
attribute [local instance] MvPolynomial.gradedAlgebra in
theorem exists_formOn_eq {R : Type} [CommRing R] {N : ℕ} (k : Fin (N + 1))
    (s : Γ(PSpace R N, GlobalTheory.ProjSpace.chart R N k)) :
    ∃ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) R) (hf : f.IsHomogeneous n),
      s = GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n f hf := by
  obtain ⟨p, rfl⟩ := (GlobalTheory.ProjSpace.chartAlgEquiv R N k).surjective s
  obtain ⟨n, f, hf, h⟩ := HomogeneousLocalization.Away.mk_surjective _ (GlobalTheory.ProjSpace.X_mem R N k)
    (GlobalTheory.ProjSpace.polyEquivAway R N k p)
  have hf' : f.IsHomogeneous n := by simpa using hf
  refine ⟨n, f, hf', ?_⟩
  rw [← GlobalTheory.ProjSpace.chartAlgEquiv_dehom R N k hf']
  congr 1
  have h1 := GlobalTheory.ProjSpace.awayToPoly_mk R N k n f hf
  rw [h] at h1
  exact ((GlobalTheory.ProjSpace.polyEquivAway R N k).left_inv p).symm.trans h1

theorem ker_thickι_chart : ∀ {R : Type} [CommRing R] (I : Ideal R) (N e : ℕ) (k : Fin (N + 1)),
    (∀ s ∈ (Scheme.Hom.ker (thickι R I N e)).ideal ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩,
      ∃ (n : ℕ) (t : MvPolynomial (Fin (N + 1)) R) (ht : t.IsHomogeneous n),
        t ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ∧
        s = GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n t ht) ∧
    (∀ (n : ℕ) (t : MvPolynomial (Fin (N + 1)) R) (ht : t.IsHomogeneous n),
      t ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) →
      GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n t ht ∈
        (Scheme.Hom.ker (thickι R I N e)).ideal ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩) := by
  intro R _ I N e k
  have hmem : ∀ (n : ℕ) (t : MvPolynomial (Fin (N + 1)) R) (ht : t.IsHomogeneous n),
      GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n t ht ∈
        (Scheme.Hom.ker (thickι R I N e)).ideal ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩ ↔
      t ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
    intro n t ht
    rw [mem_ker_thickι_iff, GlobalTheory.ProjSpace.baseChange_app_formOn,
      formOn_eq_zero_iff k (GlobalTheory.ProjSpace.baseChange_preimage_chart N _ k), ← RingHom.mem_ker,
      MvPolynomial.ker_map, Ideal.mk_ker]
  refine ⟨fun s hs => ?_, fun n t ht h => (hmem n t ht).2 h⟩
  obtain ⟨n, t, ht, rfl⟩ := exists_formOn_eq k s
  exact ⟨n, t, ht, (hmem n t ht).1 hs, rfl⟩

end GlobalTheory.CompanionTheory.GE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningSectionHomogeneousFormStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_section_homogeneous_form : ∀ {R : Type} [CommRing R] (I : Ideal R) (N e : ℕ) (k : Fin (N + 1)),
    (∀ s ∈ (Scheme.Hom.ker (thickι R I N e)).ideal ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩,
      ∃ (n : ℕ) (t : MvPolynomial (Fin (N + 1)) R) (ht : t.IsHomogeneous n),
        t ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ∧
        s = GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n t ht) ∧
    (∀ (n : ℕ) (t : MvPolynomial (Fin (N + 1)) R) (ht : t.IsHomogeneous n),
      t ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) →
      GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n t ht ∈
        (Scheme.Hom.ker (thickι R I N e)).ideal ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩) := by
  first | exact @GlobalTheory.CompanionTheory.GE.ker_thickι_chart | exact GlobalTheory.CompanionTheory.GE.ker_thickι_chart | (intros; apply GlobalTheory.CompanionTheory.GE.ker_thickι_chart <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartVanishingKillsFormMulPow
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartVanishingKillsFormMulPow
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace resG)
open GlobalTheory.ProjSpace (chart formOn ratioOn ratio)

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.GE

theorem app_presheaf_map {A B : Scheme.{0}} (φ : B ⟶ A) {U V : A.Opens} (h : V ≤ U)
    (h' : φ ⁻¹ᵁ V ≤ φ ⁻¹ᵁ U) (a : Γ(A, U)) :
    (φ.app V).hom ((A.presheaf.map (homOfLE h).op).hom a) =
      (B.presheaf.map (homOfLE h').op).hom ((φ.app U).hom a) := by
  have e := congrArg (fun g => CommRingCat.Hom.hom g a) (φ.naturality (homOfLE h).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact e

variable {R : Type} [CommRing R] {N : ℕ}

private theorem formOn_congr {U : (PSpace R N).Opens} {i : Fin (N + 1)} {hi : U ≤ chart R N i} {n : ℕ}
    {f g : MvPolynomial (Fin (N + 1)) R} (hf : f.IsHomogeneous n) (hg : g.IsHomogeneous n) (h : f = g) :
    formOn U i hi n f hf = formOn U i hi n g hg := by
  subst h
  rfl

theorem formOn_X_pow (U : (PSpace R N).Opens) (i : Fin (N + 1)) (hi : U ≤ chart R N i)
    (j : Fin (N + 1)) (m : ℕ) :
    formOn U i hi m (X j ^ m) (isHomogeneous_X_pow j m) = ratioOn U i hi j ^ m := by
  induction m with
  | zero =>
    rw [formOn_congr _ (isHomogeneous_C _ (1 : R)) (by simp), GlobalTheory.ProjSpace.formOn_C, map_one, pow_zero]
  | succ m ih =>
    rw [formOn_congr _ ((isHomogeneous_X_pow j m).mul (isHomogeneous_X R j)) (pow_succ _ _),
      GlobalTheory.ProjSpace.formOn_mul (isHomogeneous_X_pow j m) (isHomogeneous_X R j), ih, GlobalTheory.ProjSpace.formOn_X, pow_succ]

theorem exists_ratio_pow_mul_eq_zero {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N) [QuasiCompact φ] (n : ℕ)
    (f : MvPolynomial (Fin (N + 1)) R) (hf : f.IsHomogeneous n) (k : Fin (N + 1))
    (h0 : (φ.app (chart R N k)).hom (formOn (chart R N k) k le_rfl n f hf) = 0)
    (j : Fin (N + 1)) :
    ∃ m : ℕ, (φ.app (chart R N j)).hom (ratio R N j k) ^ m *
      (φ.app (chart R N j)).hom (formOn (chart R N j) j le_rfl n f hf) = 0 := by
  have hW : φ ⁻¹ᵁ (chart R N j ⊓ chart R N k) ≤ φ ⁻¹ᵁ chart R N j :=
    (TopologicalSpace.Opens.map φ.base).monotone inf_le_left
  have hW' : φ ⁻¹ᵁ (chart R N j ⊓ chart R N k) ≤ φ ⁻¹ᵁ chart R N k :=
    (TopologicalSpace.Opens.map φ.base).monotone inf_le_right
  have e1 := GlobalTheory.ProjSpace.resG_formOn (U := chart R N j) (i := j) (hi := le_rfl)
    (inf_le_left : chart R N j ⊓ chart R N k ≤ chart R N j) hf
  have e2 := GlobalTheory.ProjSpace.resG_formOn (U := chart R N k) (i := k) (hi := le_rfl)
    (inf_le_right : chart R N j ⊓ chart R N k ≤ chart R N k) hf
  have e3 := GlobalTheory.ProjSpace.formOn_eq_ratioOn_pow_mul (U := chart R N j ⊓ chart R N k) (i := j)
    (hi := inf_le_left) (j := k) inf_le_right hf
  have key : (Y.presheaf.map (homOfLE hW).op).hom
      ((φ.app (chart R N j)).hom (formOn (chart R N j) j le_rfl n f hf)) = 0 := by
    rw [← app_presheaf_map φ inf_le_left hW]
    erw [e1]
    rw [e3, ← e2, map_mul]
    erw [app_presheaf_map φ inf_le_right hW']
    rw [h0, map_zero, mul_zero]
  have hle : Y.basicOpen ((φ.app (chart R N j)).hom (ratio R N j k)) ≤ φ ⁻¹ᵁ (chart R N j ⊓ chart R N k) := by
    rw [← Scheme.preimage_basicOpen, GlobalTheory.ProjSpace.basicOpen_ratioOn]
  refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact Y (U := φ ⁻¹ᵁ chart R N j)
    (φ.isCompact_preimage (GlobalTheory.ProjSpace.isAffineOpen_chart R N j).isCompact) _ _ ?_
  show (Y.presheaf.map (homOfLE _).op).hom _ = 0
  rw [show (homOfLE (Y.basicOpen_le _) : Y.basicOpen ((φ.app (chart R N j)).hom (ratio R N j k)) ⟶ φ ⁻¹ᵁ chart R N j) =
      homOfLE hle ≫ homOfLE hW from rfl, op_comp, Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply, key,
    map_zero]

theorem exists_killsForm_X_pow_mul :
    ∀ {R : Type} [CommRing R] {N : ℕ} {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N) [QuasiCompact φ] (n : ℕ)
    (f : MvPolynomial (Fin (N + 1)) R) (hf : f.IsHomogeneous n) (k : Fin (N + 1)),
    (φ.app (GlobalTheory.ProjSpace.chart R N k)).hom
      (GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n f hf) = 0 →
    ∃ (m : ℕ) (h : (X k ^ m * f : MvPolynomial (Fin (N + 1)) R).IsHomogeneous (m + n)),
      KillsForm φ (m + n) (X k ^ m * f) h := by
  intro R _ N Y φ _ n f hf k h0
  choose m hm using fun j => exists_ratio_pow_mul_eq_zero φ n f hf k h0 j
  refine ⟨∑ j, m j, (isHomogeneous_X_pow k _).mul hf, ?_⟩
  intro j
  rw [GlobalTheory.ProjSpace.formOn_mul (isHomogeneous_X_pow k _) hf, formOn_X_pow, map_mul, map_pow]
  have hle : m j ≤ ∑ j, m j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc, hm j, mul_zero]

end GlobalTheory.CompanionTheory.GE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartVanishingKillsFormMulPowStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_vanishing_kills_form_mul_pow : ∀ {R : Type} [CommRing R] {N : ℕ} {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N) [QuasiCompact φ] (n : ℕ)
    (f : MvPolynomial (Fin (N + 1)) R) (hf : f.IsHomogeneous n) (k : Fin (N + 1)),
    (φ.app (GlobalTheory.ProjSpace.chart R N k)).hom
      (GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n f hf) = 0 →
    ∃ (m : ℕ) (h : (X k ^ m * f : MvPolynomial (Fin (N + 1)) R).IsHomogeneous (m + n)),
      KillsForm φ (m + n) (X k ^ m * f) h := by
  first | exact @GlobalTheory.CompanionTheory.GE.exists_killsForm_X_pow_mul | exact GlobalTheory.CompanionTheory.GE.exists_killsForm_X_pow_mul | (intros; apply GlobalTheory.CompanionTheory.GE.exists_killsForm_X_pow_mul <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemVanishingIdealIffKillsForm
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemVanishingIdealIffKillsForm
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)

namespace GlobalTheory.CompanionTheory.GE.MemVan

variable {R : Type} [CommRing R] {N : ℕ} {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N)

def KilledIn (n : ℕ) (f : MvPolynomial (Fin (N + 1)) R) : Prop :=
  ∃ hf : f.IsHomogeneous n, KillsForm φ n f hf

theorem killedIn_zero (n : ℕ) : KilledIn φ n 0 := by
  unfold KilledIn KillsForm
  refine ⟨isHomogeneous_zero _ _ _, fun k => ?_⟩
  rw [GlobalTheory.ProjSpace.formOn_zero, map_zero]

variable {φ}

theorem KilledIn.add {n : ℕ} {f g : MvPolynomial (Fin (N + 1)) R} (hf : KilledIn φ n f)
    (hg : KilledIn φ n g) : KilledIn φ n (f + g) := by
  obtain ⟨hf1, hf2⟩ := hf
  obtain ⟨hg1, hg2⟩ := hg
  unfold KillsForm at hf2 hg2
  unfold KilledIn KillsForm
  refine ⟨hf1.add hg1, fun k => ?_⟩
  rw [GlobalTheory.ProjSpace.formOn_add hf1 hg1, map_add (f := _), hf2 k, hg2 k, add_zero]

theorem KilledIn.mul {d m : ℕ} {a f : MvPolynomial (Fin (N + 1)) R} (ha : a.IsHomogeneous d)
    (hf : KilledIn φ m f) : KilledIn φ (d + m) (a * f) := by
  obtain ⟨hf1, hf2⟩ := hf
  unfold KillsForm at hf2
  unfold KilledIn KillsForm
  refine ⟨ha.mul hf1, fun k => ?_⟩
  rw [GlobalTheory.ProjSpace.formOn_mul ha hf1, map_mul, hf2 k, mul_zero]

theorem KilledIn.sum {ι : Type*} (s : Finset ι) {n : ℕ} (g : ι → MvPolynomial (Fin (N + 1)) R)
    (hg : ∀ i ∈ s, KilledIn φ n (g i)) : KilledIn φ n (∑ i ∈ s, g i) := by
  exact Finset.sum_induction g (KilledIn φ n) (fun a b ha hb => ha.add hb) (killedIn_zero φ n) hg

theorem killedIn_component_mul_of_homog {d : ℕ} {a h : MvPolynomial (Fin (N + 1)) R}
    (ha : a.IsHomogeneous d) (hh : ∀ n, KilledIn φ n (homogeneousComponent n h)) (n : ℕ) :
    KilledIn φ n (homogeneousComponent n (a * h)) := by
  have hsum : a * h = ∑ m ∈ Finset.range (h.totalDegree + 1), a * homogeneousComponent m h := by
    rw [← Finset.mul_sum, sum_homogeneousComponent]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum]
  refine KilledIn.sum _ _ fun m _ => ?_
  rw [homogeneousComponent_of_mem
    ((mem_homogeneousSubmodule _ _).2 (ha.mul (homogeneousComponent_isHomogeneous m h)))]
  split_ifs with hnm
  · subst hnm
    exact KilledIn.mul ha (hh m)
  · exact killedIn_zero φ n

theorem killedIn_component_mul (a : MvPolynomial (Fin (N + 1)) R)
    {h : MvPolynomial (Fin (N + 1)) R} (hh : ∀ n, KilledIn φ n (homogeneousComponent n h)) (n : ℕ) :
    KilledIn φ n (homogeneousComponent n (a * h)) := by
  have hsum : a * h = ∑ k ∈ Finset.range (a.totalDegree + 1), homogeneousComponent k a * h := by
    rw [← Finset.sum_mul, sum_homogeneousComponent]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum]
  exact KilledIn.sum _ _ fun k _ =>
    killedIn_component_mul_of_homog (homogeneousComponent_isHomogeneous k a) hh n

theorem killedIn_component_of_mem {h : MvPolynomial (Fin (N + 1)) R} (hh : h ∈ vanIdeal φ) :
    ∀ n, KilledIn φ n (homogeneousComponent n h) := by
  unfold vanIdeal Ideal.span at hh
  induction hh using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, hk⟩ := hx
    intro n
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 hm)]
    split_ifs with hnm
    · subst hnm
      exact ⟨hm, hk⟩
    · exact killedIn_zero φ n
  | zero =>
    intro n
    rw [map_zero]
    exact killedIn_zero φ n
  | add x y _ _ ihx ihy =>
    intro n
    rw [map_add (f := _)]
    exact (ihx n).add (ihy n)
  | smul a x _ ih =>
    intro n
    rw [smul_eq_mul]
    exact killedIn_component_mul a ih n

end GlobalTheory.CompanionTheory.GE.MemVan

namespace GlobalTheory.CompanionTheory.GE

theorem mem_vanIdeal_iff_killsForm {R : Type} [CommRing R] {N : ℕ} {Y : Scheme.{0}}
    (φ : Y ⟶ PSpace R N) (n : ℕ) (f : MvPolynomial (Fin (N + 1)) R) (hf : f.IsHomogeneous n) :
    f ∈ vanIdeal φ ↔ KillsForm φ n f hf := by
  constructor
  · intro hmem
    have h1 := MemVan.killedIn_component_of_mem hmem n
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 hf), if_pos rfl] at h1
    obtain ⟨_, hk⟩ := h1
    exact hk
  · intro hk
    refine Ideal.subset_span ?_
    exact ⟨n, hf, hk⟩

end GlobalTheory.CompanionTheory.GE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemVanishingIdealIffKillsFormStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_vanishing_ideal_iff_kills_form : ∀ {R : Type} [CommRing R] {N : ℕ} {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N) (n : ℕ)
    (f : MvPolynomial (Fin (N + 1)) R) (hf : f.IsHomogeneous n), f ∈ vanIdeal φ ↔ KillsForm φ n f hf := by
  first | exact @GlobalTheory.CompanionTheory.GE.mem_vanIdeal_iff_killsForm | exact GlobalTheory.CompanionTheory.GE.mem_vanIdeal_iff_killsForm | (intros; apply GlobalTheory.CompanionTheory.GE.mem_vanIdeal_iff_killsForm <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedImmersionPullbackKernelSup
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)

namespace GlobalTheory.CompanionTheory.GE

theorem ker_inter_eq_sup {X Y A B Z : Scheme.{0}} (t : Y ⟶ X) (a : A ⟶ Y) (b : B ⟶ Y) (f : Z ⟶ A)
    (g : Z ⟶ B) [IsClosedImmersion t] [IsClosedImmersion a] [IsClosedImmersion b]
    (h : IsPullback f g a b) :
    Scheme.Hom.ker ((f ≫ a) ≫ t) = Scheme.Hom.ker (a ≫ t) ⊔ Scheme.Hom.ker (b ≫ t) := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · set K := Scheme.Hom.ker (a ≫ t) ⊔ Scheme.Hom.ker (b ≫ t) with hK
    have hA : Scheme.Hom.ker (a ≫ t) ≤ K.subschemeι.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι]; exact le_sup_left
    have hB : Scheme.Hom.ker (b ≫ t) ≤ K.subschemeι.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι]; exact le_sup_right
    let u : K.subscheme ⟶ A := IsClosedImmersion.lift (a ≫ t) K.subschemeι hA
    let v : K.subscheme ⟶ B := IsClosedImmersion.lift (b ≫ t) K.subschemeι hB
    have hu : u ≫ a ≫ t = K.subschemeι := IsClosedImmersion.lift_fac _ _ _
    have hv : v ≫ b ≫ t = K.subschemeι := IsClosedImmersion.lift_fac _ _ _
    have huv : u ≫ a = v ≫ b := by
      rw [← cancel_mono t, Category.assoc, Category.assoc, hu, hv]
    have hl : h.lift u v huv ≫ (f ≫ a) ≫ t = K.subschemeι := by
      rw [← Category.assoc, ← Category.assoc, h.lift_fst, Category.assoc]
      exact hu
    calc Scheme.Hom.ker ((f ≫ a) ≫ t) ≤ (h.lift u v huv ≫ (f ≫ a) ≫ t).ker :=
          Scheme.Hom.le_ker_comp _ _
      _ = K := by rw [hl, Scheme.IdealSheafData.ker_subschemeι]
  · rw [Category.assoc]
    exact Scheme.Hom.le_ker_comp _ _
  · rw [h.w, Category.assoc]
    exact Scheme.Hom.le_ker_comp _ _

end GlobalTheory.CompanionTheory.GE
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningTwistedSectionTransition
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningTwistedSectionTransition
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem mul_mul_cancel_of_eq_one {A : Type*} [CommRing A] (a b c : A) (h : b * c = 1) :
    a * b * c = a := by
  rw [mul_assoc, h, mul_one]

theorem mul_mul_cancel_of_eq_one' {A : Type*} [CommRing A] (a b c : A) (h : c * b = 1) :
    a * b * c = a := by
  rw [mul_assoc, mul_comm b, h, mul_one]

theorem mulT_bijective_of_inverse :
    ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℤ) (ι : Type) (D : ∀ e, Finset ι → (Y e).left.Opens) (e : ℕ) (t : ℤ) (S : Finset ι) (σ : SecOn (pw (N e) d) (D e S)) (y : SecOn (pw (N e) (-d)) (D e S)), secMulOn rfl σ y = oneOn (N e) (add_neg_cancel d) (D e S) → Function.Bijective (mulT I Y N D d e t S σ) := by
  intro R _ I Y β hβ N v hN d ι D e t S σ y h
  have hc : ∀ i : (N e).ι, @HMul.hMul (Γ((Y e).left, D e S ⊓ (N e).U i)) (Γ((Y e).left, D e S ⊓ (N e).U i)) _ _ (GlobalTheory.LB.coord σ i) (GlobalTheory.LB.coord y i) = 1 := by
    intro i
    have := congrArg (fun z : SecOn (pw (N e) (d + -d)) (D e S) =>
      GlobalTheory.LB.coord z (show (pw (N e) (d + -d)).ι from i)) h
    exact this
  let g : Tm I Y N D d e (t + 1) S →ₗ[R] Tm I Y N D d e t S :=
    mulRight (toR I Y e) (show d * (t + 1) + -d = d * t by ring) y
  refine Function.bijective_iff_has_inverse.2 ⟨g, ?_, ?_⟩
  · intro x
    exact GlobalTheory.LB.sec_ext fun (i : (N e).ι) =>
      mul_mul_cancel_of_eq_one (A := Γ((Y e).left, D e S ⊓ (N e).U i)) _ _ _ (hc i)
  · intro x
    exact GlobalTheory.LB.sec_ext fun (i : (N e).ι) =>
      mul_mul_cancel_of_eq_one' (A := Γ((Y e).left, D e S ⊓ (N e).U i)) _ _ _ (hc i)

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningTwistedSectionTransitionStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_twisted_section_transition : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℤ) (ι : Type) (D : ∀ e, Finset ι → (Y e).left.Opens) (e : ℕ) (t : ℤ) (S : Finset ι) (σ : SecOn (pw (N e) d) (D e S)) (y : SecOn (pw (N e) (-d)) (D e S)), secMulOn rfl σ y = oneOn (N e) (add_neg_cancel d) (D e S) → Function.Bijective (mulT I Y N D d e t S σ) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.mulT_bijective_of_inverse | exact GlobalTheory.CompanionTheory.FormalAlg.Lift.mulT_bijective_of_inverse | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.Lift.mulT_bijective_of_inverse <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningCechRestrictionCommutes
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningCechRestrictionCommutes
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem pullLE_oneOn_eq_congr {X Y : Scheme.{0}} {N : LB X} {N' : LB Y} {β : X ⟶ Y}
    (v : LB.Iso N (N'.pull β)) (hL : (pw N 0).IsLB) (hM : ((pw N' 0).pull β).IsLB)
    (hw : (pullPow v 0).IsGen) (V : Y.Opens) (V' : X.Opens) (e : V' ≤ β ⁻¹ᵁ V) :
    SecOn.pullLE (pw N' 0) β V V' e (oneOn N' rfl V) =
      SecOn.congr hL hM (pullPow v 0) hw V' (oneOn N rfl V') := by
  refine GlobalTheory.LB.sec_ext_of_cover hL.cover fun p q => ?_
  have h := SecOn.coord_congr hL hM (pullPow v 0) hw (oneOn N rfl V') p q
    (O := V' ⊓ ((pw N' 0).pull β).U p ⊓ (pw N 0).U q) inf_le_left
    (inf_le_inf_right _ inf_le_left) (inf_le_inf_right _ inf_le_right)
  have c1 : GlobalTheory.LB.coord (SecOn.pullLE (pw N' 0) β V V' e (oneOn N' rfl V)) p = 1 := by
    rw [SecOn.coord_pullLE]
    exact map_one _
  have c2 : GlobalTheory.LB.coord (oneOn N (rfl : (0 : ℤ) = 0) V') q = 1 := rfl
  have c3 : (show Γ(X, ((pw N' 0).pull β).U p ⊓ (pw N 0).U q)ˣ from (pullPow v 0).s (p, q)) = 1 :=
    zpow_zero _
  rw [c2, c3] at h
  rw [c1]
  refine Eq.trans ?_ h.symm
  simp

theorem red_oneOn : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (ι : Type) (D : ∀ e, Finset ι → (Y e).left.Opens) (hDβ : ∀ e S, D e S ≤ β e ⁻¹ᵁ D (e + 1) S) (a : ℤ) (h : a = 0) (e : ℕ) (S : Finset ι), red I Y N D β hβ v hN hDβ a e S (SecOnR.of _ _ _ (oneOn (N (e + 1)) h (D (e + 1) S))) = SecOnR.of _ _ _ (oneOn (N e) h (D e S)) := by
  intro R _ I Y β hβ N v hN ι D hDβ a h e S
  subst h
  simp only [red, redL, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearEquiv.symm_apply_eq, SecOnR.pull_of, SecOnR.linEquiv_of]
  exact congrArg (SecOnR.of _ _ _) (pullLE_oneOn_eq_congr (v e) _ _ _ _ _ _)

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningCechRestrictionCommutesStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_cech_restriction_commutes : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (ι : Type) (D : ∀ e, Finset ι → (Y e).left.Opens) (hDβ : ∀ e S, D e S ≤ β e ⁻¹ᵁ D (e + 1) S) (a : ℤ) (h : a = 0) (e : ℕ) (S : Finset ι), red I Y N D β hβ v hN hDβ a e S (SecOnR.of _ _ _ (oneOn (N (e + 1)) h (D (e + 1) S))) = SecOnR.of _ _ _ (oneOn (N e) h (D e S)) := by
  exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.red_oneOn
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FontaineLatticeDpowClosed
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FontaineLatticeDpowClosed
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatCHc

theorem subsingleton_Bk_zero (l : ℕ) [Fact l.Prime] : Subsingleton (Lat.Bk l 0) := by
  refine Ideal.Quotient.subsingleton_iff.2 ?_
  rw [pow_zero, Ideal.span_singleton_one]

theorem hc_k : ∀ (l : ℕ) [Fact l.Prime] (M k : ℕ),
    Lat.DPClosed (Lat.ι (Lat.fk l k) (xi0 l) l M) (Lat.γB (Lat.fk l k) (xi0 l)) := by
  intro l _ M k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · intro x _ n
    haveI := subsingleton_Bk_zero l
    exact ⟨0, Subsingleton.elim _ _⟩
  · exact GlobalTheory.CompanionTheory.LatDP.dpClosed _ _ l M k (GlobalTheory.CompanionTheory.LatCHyp.hyp_k l k hk)

end GlobalTheory.CompanionTheory.LatCHc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FontaineLatticeDpowClosedStatement
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fontaine_lattice_dpow_closed : ∀ (l : ℕ) [Fact l.Prime] (M k : ℕ), Lat.DPClosed (Lat.ι (Lat.fk l k) (xi0 l) l M) (Lat.γB (Lat.fk l k) (xi0 l)) := by
  first | exact @GlobalTheory.CompanionTheory.LatCHc.hc_k | exact GlobalTheory.CompanionTheory.LatCHc.hc_k | (intros; apply GlobalTheory.CompanionTheory.LatCHc.hc_k <;> assumption)
end
end
