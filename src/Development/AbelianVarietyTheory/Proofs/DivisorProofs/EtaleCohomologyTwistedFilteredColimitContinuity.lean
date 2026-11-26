module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyFilteredColimitRingsFinitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValIotaLeOfMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductAssoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductGradedComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupUnitAndPrimitiveRootClasses
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyTwistedFilteredColimitContinuity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyTwistedFilteredColimitContinuity
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

theorem GlobalTheory.EtC.pairingProperties : GlobalTheory.EtC.B1 := by
  intro q J _ _ D c hc n i
  have h := GlobalTheory.T.etaleCohomology_filteredColimit_rings_finitary (ZMod q) (tw q i) (GlobalTheory.T.tateTwist_finitary q i) J D c hc n
  exact ⟨fun x _ => h.1 x, fun j y _ hy => h.2 j y hy⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyTwistedFilteredColimitContinuityStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity : GlobalTheory.EtC.B1 := by
  first | (exact @GlobalTheory.EtC.pairingProperties) | (exact GlobalTheory.EtC.pairingProperties) | (intros; apply GlobalTheory.EtC.pairingProperties  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
noncomputable section
namespace GlobalTheory.SUVol
open NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

instance instMeasurableSpaceRealSU (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) :
    MeasurableSpace (realSU Ψ G) := borel _
instance instBorelSpaceRealSU (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) :
    BorelSpace (realSU Ψ G) := ⟨rfl⟩
end GlobalTheory.SUVol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableRisingS
noncomputable section

open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
open scoped ContDiff

namespace GlobalTheory.WeightTwoSum

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

def risingS (σ : ℂ) (m : I → ℕ) : ℂ := ∏ i, ((-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), (2 + σ + j))

def eTerm (φ : I → E →+* ℂ) (m : I → ℕ) (σ : ℂ) (z : I → ℂ) (x : E) : ℂ :=
  ∏ i, (((-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), (2 + σ + j)) * (starRingEnd ℂ (φ i x)) ^ m i *
    (defCoord φ z x i)⁻¹ ^ (2 + m i) * ((‖defCoord φ z x i‖ : ℝ) : ℂ) ^ (-2 * σ))

def dz (j : I) : (I → ℂ) →L[ℝ] ℂ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : I => ℂ) j

def dzbar (j : I) : (I → ℂ) →L[ℝ] ℂ := (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (dz j)

def homFac (z : I → ℂ) : ℂ := ∏ i, ((1 + z i) / (2 * (Real.pi : ℂ) * Complex.I))

def logFac (z : I → ℂ) : ℂ := ((Real.log (Complex.normSq (homFac z)) : ℝ) : ℂ)

def modPt {Φ : Type} (φ : I → E →+* ℂ) (e : I ≃ Φ) (θ : E) (z : I → ℂ) : Φ → ℂ :=
  fun τ => defCoord φ z θ (e.symm τ) / (1 + z (e.symm τ))

@[simp] theorem dz_apply (j : I) (v : I → ℂ) : dz j v = v j := rfl

@[simp] theorem dzbar_apply (j : I) (v : I → ℂ) : dzbar j v = starRingEnd ℂ (v j) := rfl

theorem eTerm_zero (φ : I → E →+* ℂ) (σ : ℂ) (z : I → ℂ) (x : E) : eTerm φ 0 σ z x = defTerm φ 2 z σ x := by
  simp [eTerm, defTerm]

theorem eTerm_origin (φ : I → E →+* ℂ) (m : I → ℕ) (σ : ℂ) (x : E) :
    eTerm φ m σ 0 x = risingS σ m * term φ 2 m σ x := by
  unfold eTerm risingS term
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [defCoord, Pi.zero_apply, zero_mul, add_zero]
  ring

theorem risingS_zero (m : I → ℕ) : risingS 0 m = risingFactor 2 m := by
  simp [risingS, risingFactor]

theorem differentiable_risingS (m : I → ℕ) : Differentiable ℂ fun σ => risingS σ m := by
  unfold risingS
  fun_prop

theorem isOpen_polydisc (I : Type) [Fintype I] : IsOpen (polydisc I) := by
  have : polydisc I = ⋂ i : I, {z : I → ℂ | ‖z i‖ < 1} := by
    ext z; simp [polydisc]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i).norm continuous_const

omit [Fintype I] in
theorem one_add_ne_zero {z : I → ℂ} (hz : z ∈ polydisc I) (i : I) : 1 + z i ≠ 0 := by
  intro h
  have h1 : z i = -1 := by linear_combination h
  have h2 := hz i
  rw [h1] at h2
  simp at h2

theorem homFac_ne_zero {z : I → ℂ} (hz : z ∈ polydisc I) : homFac z ≠ 0 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact Finset.prod_ne_zero_iff.2 fun i _ => div_ne_zero (one_add_ne_zero hz i)
    (mul_ne_zero (mul_ne_zero two_ne_zero hπ) Complex.I_ne_zero)

theorem contDiff_homFac : ContDiff ℂ ∞ (homFac : (I → ℂ) → ℂ) := by
  unfold homFac
  exact contDiff_prod fun i _ => (contDiff_const.add (contDiff_apply ℂ (fun _ => ℂ) i)).div_const _

theorem contDiffOn_logFac : ContDiffOn ℝ ∞ (logFac : (I → ℂ) → ℂ) (polydisc I) := by
  have h1 : ContDiff ℝ ∞ (homFac : (I → ℂ) → ℂ) := contDiff_homFac.restrict_scalars ℝ
  have h2 : ContDiff ℝ ∞ (fun z : I → ℂ => Complex.normSq (homFac z)) := by
    simp only [Complex.normSq_apply]
    exact ((Complex.reCLM.contDiff.comp h1).mul (Complex.reCLM.contDiff.comp h1)).add
      ((Complex.imCLM.contDiff.comp h1).mul (Complex.imCLM.contDiff.comp h1))
  have h3 : ContDiffOn ℝ ∞ (fun z : I → ℂ => Real.log (Complex.normSq (homFac z))) (polydisc I) :=
    h2.contDiffOn.log fun z hz => (Complex.normSq_pos.2 (homFac_ne_zero hz)).ne'
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn h3

theorem contDiffOn_modPt {Φ : Type} [Fintype Φ] (φ : I → E →+* ℂ) (e : I ≃ Φ) (θ : E) :
    ContDiffOn ℂ ∞ (modPt φ e θ) (polydisc I) := by
  refine contDiffOn_pi.2 fun τ => ?_
  unfold modPt defCoord
  refine ContDiffOn.div ?_ ?_ fun z hz => one_add_ne_zero hz _
  · exact (contDiff_const.add ((contDiff_apply ℂ (fun _ => ℂ) _).mul contDiff_const)).contDiffOn
  · exact (contDiff_const.add (contDiff_apply ℂ (fun _ => ℂ) _)).contDiffOn


omit [Fintype I] in
theorem modPt_im_pos {Φ : Type} (φ : I → E →+* ℂ) (e : I ≃ Φ) (θ : E) (hθ : ∀ i, 0 < (φ i θ).im)
    {z : I → ℂ} (hz : z ∈ polydisc I) (τ : Φ) : 0 < (modPt φ e θ z τ).im := by
  unfold modPt defCoord
  set i := e.symm τ
  have h0 : 0 < Complex.normSq (1 + z i) := Complex.normSq_pos.2 (one_add_ne_zero hz i)
  have h1 : Complex.normSq (z i) < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    have := hz i
    nlinarith [norm_nonneg (z i)]
  rw [Complex.div_im, ← sub_div]
  refine div_pos ?_ h0
  rw [Complex.normSq_apply] at h1
  have h2 := hθ i
  simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.one_re,
    Complex.one_im]
  nlinarith [mul_pos h2 (sub_pos.2 h1)]

end GlobalTheory.WeightTwoSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhaseFrame
noncomputable section

namespace GlobalTheory.RiemConst

open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def angles (θ : Fin (r - 1) → ℝ) (a : Fin r) : ℝ :=
  if h : (a : ℕ) < r - 1 then θ ⟨a, h⟩ else -∑ k, θ k

def phaseFrame {Ψ : Finset (E →+* ℂ)} (θ : Ψ → Fin (r - 1) → ℝ) : Frame Ψ r :=
  fun τ => Matrix.diagonal fun a => Complex.exp (Complex.I * (angles (θ τ) a : ℂ))

def inFrame {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) (Y : Ψ → Fin r → Fin r → ℂ) (τ : Ψ) :
    Matrix (Fin r) (Fin r) ℂ :=
  (mat x τ)⁻¹ * Matrix.of (Y τ) * mat x τ

abbrev ChartSp (X : Data E r) : Type := ReciprocityTheory.L2DbarEstimates.V (nd X) × (X.Ψ → Fin (r - 1) → ℝ)

end GlobalTheory.RiemConst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerSquares
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerSquares
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg.TowerSq

theorem isPullback_id_of_mono {C : Type*} [Category C] {X Y Z : C} (h : X ⟶ Y) (f : Y ⟶ Z) [Mono f] :
    IsPullback h (𝟙 X) f (h ≫ f) := by
  refine IsPullback.of_isLimit (c := PullbackCone.mk h (𝟙 X) (by simp)) (PullbackCone.IsLimit.mk _ (fun s => s.snd) (fun s => ?_) (fun s => ?_)
    (fun s m _ h2 => ?_))
  · rw [← cancel_mono f, Category.assoc]
    exact s.condition.symm
  · exact Category.comp_id _
  · simpa using h2

theorem mono_thick' (R : Type) [CommRing R] (I : Ideal R) (e : ℕ) : Mono (thick R I e) := by
  have : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

theorem thickTrans_thick' (R : Type) [CommRing R] (I : Ideal R) (e : ℕ) :
    thickTrans R I e ≫ thick R I (e + 1) = thick R I e := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

end GlobalTheory.FormalAlg.TowerSq


open GlobalTheory.FormalAlg.TowerSq in
theorem GlobalTheory.FormalAlg.towerSquares : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, IsPullback (β e) (Y e).hom ((Y (e + 1)).hom ≫ thick R I (e + 1)) (thick R I e)) ∧ ∀ γ : ∀ e, (Y 0).left ⟶ (Y e).left, γ 0 = 𝟙 _ → (∀ e, γ e ≫ β e = γ (e + 1)) → ∀ e, IsPullback (γ e) (Y 0).hom ((Y e).hom ≫ thick R I e) (thick R I 0) := by
  intro R _ I Y β hβ
  refine ⟨fun e => ?_, fun γ h0 hγ e => ?_⟩
  · have := mono_thick' R I (e + 1)
    have h := (hβ e).paste_vert (isPullback_id_of_mono (thickTrans R I e) (thick R I (e + 1)))
    rw [thickTrans_thick', Category.comp_id] at h
    exact h
  · have hc : ∀ e, ∃ u : Spec (CommRingCat.of (R ⧸ I ^ (0 + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))),
        u ≫ thick R I e = thick R I 0 ∧ IsPullback (γ e) (Y 0).hom (Y e).hom u := by
      intro e
      induction e with
      | zero =>
        rw [h0]
        exact ⟨𝟙 _, Category.id_comp _, IsPullback.of_horiz_isIso ⟨by simp⟩⟩
      | succ e ih =>
        obtain ⟨u, hu, hp⟩ := ih
        refine ⟨u ≫ thickTrans R I e, by rw [Category.assoc, thickTrans_thick', hu], ?_⟩
        rw [← hγ e]
        exact hp.paste_horiz (hβ e)
    obtain ⟨u, hu, hp⟩ := hc e
    have := mono_thick' R I e
    have h := hp.paste_vert (isPullback_id_of_mono u (thick R I e))
    rw [hu, Category.comp_id] at h
    exact h
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerSquaresStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullback_thick_tower_squares : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, IsPullback (β e) (Y e).hom ((Y (e + 1)).hom ≫ thick R I (e + 1)) (thick R I e)) ∧ ∀ γ : ∀ e, (Y 0).left ⟶ (Y e).left, γ 0 = 𝟙 _ → (∀ e, γ e ≫ β e = γ (e + 1)) → ∀ e, IsPullback (γ e) (Y 0).hom ((Y e).hom ≫ thick R I e) (thick R I 0) := by
  first | exact @GlobalTheory.FormalAlg.towerSquares | exact GlobalTheory.FormalAlg.towerSquares | (intros; apply GlobalTheory.FormalAlg.towerSquares <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfPullbackQuotientEq
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NilRigidity

theorem exists_preimage_quotient {R : Type} [CommRing R] (I : Ideal R) (hI : I ≤ nilradical R) (t : Sp R) :
    ∃ t₀ : Sp (R ⧸ I), spMap (Ideal.Quotient.mk I) t₀ = t := by
  have hsurj : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  have hmem : t ∈ PrimeSpectrum.zeroLocus (RingHom.ker (Ideal.Quotient.mk I) : Set R) := by
    rw [Ideal.mk_ker]
    intro x hx
    exact (@nilradical_le_prime _ _ t.asIdeal t.isPrime) (hI hx)
  rw [← range_comap_of_surjective _ _ hsurj] at hmem
  obtain ⟨t₀, ht₀⟩ := hmem
  exact ⟨t₀, ht₀⟩

theorem eq_of_eq_on_quotient {R : Type} [CommRing R] (I : Ideal R) (hI : I ≤ nilradical R)
    (B B' : Over (Sp R)) [GrpObj B] [GrpObj B'] (hB : IsAbelianScheme B) (f g : B ⟶ B')
    (hfg : pullback.fst B.hom (spMap (Ideal.Quotient.mk I)) ≫ f.left =
      pullback.fst B.hom (spMap (Ideal.Quotient.mk I)) ≫ g.left)
    (hη : η[B] ≫ f = η[B] ≫ g) : f = g := by
  haveI := hB.proper
  let π := spMap (Ideal.Quotient.mk I)
  let c : B ⟶ B' := f * g⁻¹
  let j := pullback.fst B.hom π
  let j' : Over.mk (j ≫ B.hom) ⟶ B := Over.homMk j rfl
  have h1 : j' ≫ f = j' ≫ g := Over.OverMorphism.ext hfg
  have h2 : j' ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, h1, mul_inv_cancel]
  have h3 : η[B] ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, hη, mul_inv_cancel]
  have hpt : ∀ x : B.left, c.left x = (η[B'] : 𝟙_ (Over (Sp R)) ⟶ B').left (B.hom x) := by
    intro x
    obtain ⟨t₀, ht₀⟩ := exists_preimage_quotient I hI (B.hom x)
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback B.hom π) x t₀ ht₀.symm
    have e : j ≫ c.left = (j' ≫ c).left := rfl
    rw [← Scheme.Hom.comp_apply, e, h2, Hom.one_def, Over.comp_left]
    rfl
  have hη' : (η[B] : 𝟙_ (Over (Sp R)) ⟶ B).left ≫ B.hom = 𝟙 _ := Over.w η[B]
  have key : c.left = B.hom ≫ (η[B] : 𝟙_ (Over (Sp R)) ⟶ B).left ≫ c.left := by
    refine Scheme.hom_ext_of_forall _ _ fun x ↦ ?_
    obtain ⟨V, hV, hV'⟩ := GlobalTheory.local_rigidity B.left (Sp R) B'.left B.hom _ c.left hη' inferInstance
      (GlobalTheory.surjective_app_of_isAbelianScheme GlobalTheory.globalFns_holds B hB) (B.hom x)
      ((η[B'] : 𝟙_ (Over (Sp R)) ⟶ B').left (B.hom x)) (fun x' hx' ↦ by rw [hpt, hx'])
    exact ⟨B.hom ⁻¹ᵁ V, hV, hV'⟩
  have key' : c = toUnit B ≫ η[B] ≫ c := Over.OverMorphism.ext key
  rw [h3, MonObj.comp_one] at key'
  exact mul_inv_eq_one.1 key'

theorem eq_of_pullback_quotient_eq {R : Type} [CommRing R] (I : Ideal R) (hI : IsNilpotent I)
    (B B' : Over (Sp R)) [GrpObj B] [GrpObj B'] (hB : IsAbelianScheme B) (f g : B ⟶ B') [IsMonHom f] [IsMonHom g]
    (h : (Over.pullback (spMap (Ideal.Quotient.mk I))).map f = (Over.pullback (spMap (Ideal.Quotient.mk I))).map g) :
    f = g := by
  have hI' : I ≤ nilradical R := by
    obtain ⟨n, hn⟩ := hI
    intro x hx
    exact ⟨n, by
      have : x ^ n ∈ I ^ n := Ideal.pow_mem_pow hx n
      rw [hn] at this
      simpa using this⟩
  refine eq_of_eq_on_quotient I hI' B B' hB f g ?_ (by rw [IsMonHom.one_hom, IsMonHom.one_hom])
  have e := congrArg (fun k ↦ k.left ≫ pullback.fst B'.hom (spMap (Ideal.Quotient.mk I))) h
  simp only [Over.pullback_map_left, pullback.lift_fst] at e
  exact e

end GlobalTheory.NilRigidity
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitOfHilbertLatticeHasLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitOfHilbertLatticeHasLevel
set_option autoImplicit false

noncomputable section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

variable {F : Type} [Field F] [NumberField F]


set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
variable {F : Type} [Field F] [NumberField F] in
theorem _root_.GlobalTheory.HilbFam.exists_eq_split_of_hasLevel (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (N : ℕ) (L : _root_.GlobalTheory.HilbFam.Lat F) (hN : 0 < N) (hL : _root_.GlobalTheory.HilbFam.HasLevel N L) :
    ∃ (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (x : F), L = _root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x := by
  obtain ⟨hNL, hLstd⟩ := hL
  have hLint : ∀ v ∈ L, ∀ i, v i ∈ (1 : Submodule (𝓞 F) F) := fun v hv i =>
    (Submodule.mem_pi.1 (hLstd hv)) i (Set.mem_univ i)
  have hN0 : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  have hsingle : ∀ i, Pi.single i (N : F) ∈ L := by
    intro i
    have hstd : (Pi.single i (1 : F) : Fin 2 → F) ∈ _root_.GlobalTheory.HilbFam.stdLat F := by
      refine Submodule.mem_pi.2 fun j _ => ?_
      by_cases hj : j = i
      · subst hj; simpa using (1 : Submodule (𝓞 F) F).one_le.1 le_rfl
      · simp [hj]
    have := hNL _ hstd
    convert this using 1
    ext j
    by_cases hj : j = i
    · subst hj
      simp [Algebra.smul_def]
    · simp [hj]
  let B0 : Submodule (𝓞 F) F := L.map (LinearMap.proj (R := 𝓞 F) (φ := fun _ : Fin 2 => F) 0)
  let C0 : Submodule (𝓞 F) F := L.comap (LinearMap.single (𝓞 F) (fun _ : Fin 2 => F) 1)
  have hB0 : B0 ≤ 1 := by
    rintro _ ⟨v, hv, rfl⟩
    exact hLint v hv 0
  have hC0 : C0 ≤ 1 := by
    intro c hc
    simpa using hLint _ hc 1
  let Bf : FractionalIdeal (𝓞 F)⁰ F := ⟨B0, FractionalIdeal.isFractional_of_le_one B0 hB0⟩
  let Cf : FractionalIdeal (𝓞 F)⁰ F := ⟨C0, FractionalIdeal.isFractional_of_le_one C0 hC0⟩
  have hBne : Bf ≠ 0 := by
    intro h
    have hmem : (N : F) ∈ Bf := by
      show (N : F) ∈ B0
      exact ⟨_, hsingle 0, by simp⟩
    rw [h] at hmem
    exact hN0 ((FractionalIdeal.mem_zero_iff _).1 hmem)
  have hCne : Cf ≠ 0 := by
    intro h
    have hmem : (N : F) ∈ Cf := by
      show Pi.single 1 (N : F) ∈ L
      exact hsingle 1
    rw [h] at hmem
    exact hN0 ((FractionalIdeal.mem_zero_iff _).1 hmem)
  have key : ∀ t ∈ (Bf : Submodule (𝓞 F) F) * ((Bf⁻¹ : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F),
      ∃ y : F, ∀ b ∈ Bf, (![t * b, y * b] : Fin 2 → F) ∈ L := by
    intro t ht
    refine Submodule.mul_induction_on ht ?_ ?_
    · intro b' hb' c hc
      obtain ⟨w, hw, hw0⟩ := (show b' ∈ B0 from hb')
      refine ⟨c * w 1, fun b hb => ?_⟩
      have hcb : c * b ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
        rw [← inv_mul_cancel₀ hBne]
        exact FractionalIdeal.mul_mem_mul hc hb
      obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 hcb
      convert L.smul_mem r hw using 1
      ext i
      fin_cases i
      · simp [Algebra.smul_def, hr, ← hw0]
        ring
      · simp [Algebra.smul_def, hr]
        ring
    · rintro t₁ t₂ ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩
      refine ⟨y₁ + y₂, fun b hb => ?_⟩
      convert L.add_mem (hy₁ b hb) (hy₂ b hb) using 1
      ext i
      fin_cases i <;> simp <;> ring
  have h1 : (1 : F) ∈ (Bf : Submodule (𝓞 F) F) *
      ((Bf⁻¹ : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) := by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hBne]
    exact FractionalIdeal.one_mem_one _
  obtain ⟨x, hx⟩ := key 1 h1
  refine ⟨Units.mk0 (FractionalIdeal.dual ℤ ℚ Cf) (FractionalIdeal.dual_ne_zero ℤ ℚ hCne),
    Units.mk0 Bf hBne, x, ?_⟩
  have hlat : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM
      (Units.mk0 (FractionalIdeal.dual ℤ ℚ Cf) (FractionalIdeal.dual_ne_zero ℤ ℚ hCne)) = Cf := by
    rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual, Units.val_mk0, FractionalIdeal.dual_dual]
  ext v
  unfold _root_.GlobalTheory.HilbFam.split
  rw [Submodule.mem_mk]
  change v ∈ L ↔ v 0 ∈ ((Units.mk0 Bf hBne : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) ∧
    v 1 - v 0 * x ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM
      (Units.mk0 (FractionalIdeal.dual ℤ ℚ Cf) (FractionalIdeal.dual_ne_zero ℤ ℚ hCne))
  rw [hlat, Units.val_mk0]
  change v ∈ L ↔ v 0 ∈ B0 ∧ Pi.single 1 (v 1 - v 0 * x) ∈ L
  constructor
  · intro hv
    refine ⟨⟨v, hv, rfl⟩, ?_⟩
    convert L.sub_mem hv (hx (v 0) ⟨v, hv, rfl⟩) using 1
    ext i
    fin_cases i <;> simp <;> ring
  · rintro ⟨hb, hc⟩
    convert L.add_mem (hx (v 0) hb) hc using 1
    ext i
    fin_cases i <;> simp <;> ring

end GlobalTheory.HilbFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitOfHilbertLatticeHasLevelStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_split_of_hilbertLatticeHasLevel : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F), 0 < N → HasLevel N L → ∃ (𝔞 𝔟 : Frac F) (x : F), L = split 𝔞 𝔟 x := by
  first | exact @GlobalTheory.HilbFam.exists_eq_split_of_hasLevel | exact GlobalTheory.HilbFam.exists_eq_split_of_hasLevel | (intros; apply GlobalTheory.HilbFam.exists_eq_split_of_hasLevel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductGradedCommRingAxiomsHold
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductGradedCommRingAxiomsHold
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory

theorem EtC.a6ring_holds : GlobalTheory.EtC.DivisorRingCompatibility := by
  intro q _ E
  exact ⟨fun hE _ _ a => (GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes q).1 E hE a,
    fun a b c => GlobalTheory.T.tateTwistCupProduct_assoc q E a b c,
    fun a b => GlobalTheory.T.tateTwistCupProduct_graded_comm q E a b⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductGradedCommRingAxiomsHoldStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cupProduct_gradedCommRingAxioms_hold : GlobalTheory.EtC.DivisorRingCompatibility := by
  first | (exact @GlobalTheory.EtC.a6ring_holds) | (exact GlobalTheory.EtC.a6ring_holds) | (intros; apply GlobalTheory.EtC.a6ring_holds  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
noncomputable section

open NumberField

namespace GlobalTheory.HeckeTheta

variable {I : Type} [Fintype I]

def hmon (n : ℤ) (z : ℂ) : ℂ := if 0 ≤ n then (starRingEnd ℂ z) ^ n.toNat else z ^ (-n).toNat

def gauss (n : I → ℤ) (w : I → ℂ) : ℂ :=
  ∏ i, hmon (n i) (w i) * Complex.exp ((-2 * Real.pi * ‖w i‖ ^ 2 : ℝ) : ℂ)

def dil (y : I → ℝ) (v : I → ℂ) : I → ℂ := fun i => (Real.exp (y i / 2) : ℂ) * v i

def theta {ι : Type} (e : ι → I → ℂ) (a : ι → ℂ) (n : I → ℤ) (y : I → ℝ) : ℂ :=
  ∑' j, a j * gauss n (dil y (e j))

def emb {K : Type} [Field K] (φ : I → K →+* ℂ) (α : K) : I → ℂ := fun i => φ i α

def ulog {K : Type} [Field K] [NumberField K] (φ : I → K →+* ℂ) (u : (𝓞 K)ˣ) : I → ℝ :=
  fun i => Real.log (‖φ i ((u : 𝓞 K) : K)‖ ^ 2)

theorem hmon_zero {n : ℤ} (hn : n ≠ 0) : hmon n 0 = 0 := by
  unfold hmon
  split_ifs with h
  · rw [map_zero]; exact zero_pow (by omega)
  · exact zero_pow (by omega)

theorem gauss_zero {n : I → ℤ} (hn : ∃ i, n i ≠ 0) : gauss n 0 = 0 := by
  obtain ⟨i, hi⟩ := hn
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hmon_zero hi])

theorem norm_hmon (n : ℤ) (z : ℂ) : ‖hmon n z‖ = ‖z‖ ^ n.natAbs := by
  unfold hmon
  split_ifs with h
  · rw [norm_pow, Complex.norm_conj]; congr 1; omega
  · rw [norm_pow]; congr 1; omega

end GlobalTheory.HeckeTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertLatticeTwistHasLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertLatticeTwistHasLevel
set_option autoImplicit false

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private theorem mulMat_stdLat_le {F : Type} [Field F] [NumberField F]
    (A : Matrix (Fin 2) (Fin 2) ℤ) :
    _root_.GlobalTheory.HilbFam.mulMat (_root_.GlobalTheory.HilbFam.stdLat F) A ≤
      _root_.GlobalTheory.HilbFam.stdLat F := by
  unfold _root_.GlobalTheory.HilbFam.mulMat
  rintro _ ⟨y, hy, rfl⟩
  unfold _root_.GlobalTheory.HilbFam.stdLat at hy ⊢
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies] at hy ⊢
  intro i
  simp only [LinearMap.coe_restrictScalars, Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hj : y j * (A.map Int.cast) j i = ((A j i : 𝓞 F)) • y j := by
    simp [Algebra.smul_def, mul_comm]
  rw [hj]
  exact Submodule.smul_mem _ _ (hy j (Set.mem_univ j))


set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
theorem _root_.GlobalTheory.HilbFam.hasLevel_twist_of_hasLevel : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ)
    (L : _root_.GlobalTheory.HilbFam.Lat F) (α : Matrix (Fin 2) (Fin 2) (ZMod N)),
    _root_.GlobalTheory.HilbFam.HasLevel N L → _root_.GlobalTheory.HilbFam.HasLevel N (_root_.GlobalTheory.HilbFam.twist N L α) := by
  intro F _ _ _ N L α hL
  obtain ⟨_, hle⟩ := hL
  unfold _root_.GlobalTheory.HilbFam.HasLevel _root_.GlobalTheory.HilbFam.twist
  refine ⟨fun x hx => Submodule.mem_sup_right ?_, sup_le ?_ (mulMat_stdLat_le _)⟩
  · unfold _root_.GlobalTheory.HilbFam.mulMat
    convert Submodule.mem_map_of_mem hx using 1
    ext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Matrix.natCast_apply] <;>
      rw [Algebra.smul_def, map_natCast, mul_comm]
  · unfold _root_.GlobalTheory.HilbFam.mulMat
    exact (Submodule.map_mono hle).trans (mulMat_stdLat_le _)

end GlobalTheory.HilbFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertLatticeTwistHasLevelStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertLatticeTwist_hasLevel : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F) (α : Matrix (Fin 2) (Fin 2) (ZMod N)), HasLevel N L → HasLevel N (twist N L α) := by
  first | exact @GlobalTheory.HilbFam.hasLevel_twist_of_hasLevel | exact GlobalTheory.HilbFam.hasLevel_twist_of_hasLevel | (intros; apply GlobalTheory.HilbFam.hasLevel_twist_of_hasLevel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCmTypeProductSq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCmTypeProductSq
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory

theorem cm_type_normSq_prod_eq_abs_norm (E : Type) [Field E] [NumberField E] (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (d : E) :
    ‖∏ τ : Ψ, τ.1 d‖ ^ 2 = |((Algebra.norm ℚ d : ℚ) : ℝ)| := by
  classical
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := by
    intro τ; ext x; simp [ComplexEmbedding.conjugate_coe_eq]
  have h1 : ((Algebra.norm ℚ d : ℚ) : ℂ) = ∏ τ : E →+* ℂ, τ d := by
    have := Algebra.norm_eq_prod_embeddings ℚ ℂ d
    rw [eq_ratCast] at this
    rw [this]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun σ => rfl)
  have hcompl : ∏ τ ∈ Ψᶜ, τ d = ∏ τ ∈ Ψ, (starRingEnd ℂ) (τ d) := by
    refine Finset.prod_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro τ hτ
      simp only [Finset.mem_compl, Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe] at hτ ⊢
      rw [hΨ, hcc]; exact hτ
    · intro τ hτ
      simp only [Finset.mem_compl, Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe] at hτ ⊢
      exact (hΨ τ).mp hτ
    · intro τ _; exact hcc τ
    · intro τ _; exact hcc τ
    · intro τ _; simp [ComplexEmbedding.conjugate_coe_eq]
  have hsub : ∏ τ : Ψ, τ.1 d = ∏ τ ∈ Ψ, τ d := Finset.prod_coe_sort Ψ (fun τ => τ d)
  set P := ∏ τ ∈ Ψ, τ d with hP
  have h2 : ((Algebra.norm ℚ d : ℚ) : ℂ) = ((Complex.normSq P : ℝ) : ℂ) := by
    rw [h1, ← Finset.prod_mul_prod_compl Ψ, hcompl, ← map_prod, Complex.mul_conj]
  have h3 : ((Algebra.norm ℚ d : ℚ) : ℝ) = Complex.normSq P := by
    have := h2
    rw [show ((Algebra.norm ℚ d : ℚ) : ℂ) = (((Algebra.norm ℚ d : ℚ) : ℝ) : ℂ) by push_cast; rfl] at this
    exact_mod_cast this
  rw [hsub, h3, Complex.normSq_eq_norm_sq, abs_of_nonneg (sq_nonneg _)]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCmTypeProductSqStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_cm_type_product_sq : ∀ (E : Type) [Field E] [NumberField E] (Ψ : Finset (E →+* ℂ)), (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → ∀ d : E, ‖∏ τ : Ψ, τ.1 d‖ ^ 2 = |((Algebra.norm ℚ d : ℚ) : ℝ)| := by
  first | exact @GlobalTheory.cm_type_normSq_prod_eq_abs_norm | exact GlobalTheory.cm_type_normSq_prod_eq_abs_norm | (intros; apply GlobalTheory.cm_type_normSq_prod_eq_abs_norm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitsInCMFieldTwoPrimesDegreeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitsInCMFieldTwoPrimesDegreeOne
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.Euler.SplitPlace

theorem two_primes (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) (p : Ideal (𝓞 F)) [p.IsMaximal] (P P' : p.primesOver (𝓞 E)) (hne : P ≠ P') :
    (∀ R : p.primesOver (𝓞 E), R = P ∨ R = P') ∧
      ∀ R : p.primesOver (𝓞 E), R.1.ramificationIdx (𝓞 F) * R.1.inertiaDeg (𝓞 F) = 1 := by
  classical
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 E)
  rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E, h2] at hsum
  have hpos : ∀ P : p.primesOver (𝓞 E),
      1 ≤ P.1.ramificationIdx (𝓞 F) * P.1.inertiaDeg (𝓞 F) := fun P =>
    Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)
  have hall : ∀ R : p.primesOver (𝓞 E), R = P ∨ R = P' := by
    intro R
    by_contra hR
    push Not at hR
    have h3 := Finset.sum_le_sum_of_subset (f := fun P : p.primesOver (𝓞 E) =>
      P.1.ramificationIdx (𝓞 F) * P.1.inertiaDeg (𝓞 F)) (Finset.subset_univ {R, P, P'})
    rw [hsum, Finset.sum_insert (by simp [hR.1, hR.2]), Finset.sum_pair hne] at h3
    have := hpos R
    have := hpos P
    have := hpos P'
    omega
  refine ⟨hall, fun R => ?_⟩
  have h3 := Finset.sum_le_sum_of_subset (f := fun P : p.primesOver (𝓞 E) =>
    P.1.ramificationIdx (𝓞 F) * P.1.inertiaDeg (𝓞 F)) (Finset.subset_univ {P, P'})
  rw [hsum, Finset.sum_pair hne] at h3
  have := hpos P
  have := hpos P'
  rcases hall R with rfl | rfl <;> omega

theorem split_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (v : HeightOneSpectrum (OF E)), Splits v → (∀ P P' : HeightOneSpectrum (𝓞 E), Over P v → Over P' v → P ≠ P' → ∀ R : HeightOneSpectrum (𝓞 E), Over R v → R = P ∨ R = P') ∧ ∀ P : HeightOneSpectrum (𝓞 E), Over P v → Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧ (∀ (a : OF E) (k : ℕ), algebraMap (OF E) (𝓞 E) a ∈ P.asIdeal ^ k ↔ a ∈ v.asIdeal ^ k) ∧ ∀ b : 𝓞 E, ∃ a : OF E, b - algebraMap (OF E) (𝓞 E) a ∈ P.asIdeal := by
  intro E _ _ _ v hv
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hmax : v.asIdeal.IsMaximal := v.isMaximal
  have hm : ∀ P : HeightOneSpectrum (𝓞 E), Over P v → P.asIdeal ∈ v.asIdeal.primesOver (𝓞 E) :=
    fun P h => ⟨P.isPrime, ⟨h.symm⟩⟩
  have hne : ∀ P P' (h : Over P v) (h' : Over P' v), P ≠ P' →
      (⟨_, hm P h⟩ : v.asIdeal.primesOver (𝓞 E)) ≠ ⟨_, hm P' h'⟩ :=
    fun P P' h h' hn he => hn (HeightOneSpectrum.ext (congrArg Subtype.val he))
  refine ⟨fun P P' h h' hn R hR => ?_, fun P hP => ?_⟩
  · rcases (two_primes _ E h2 v.asIdeal _ _ (hne P P' h h' hn)).1 ⟨_, hm R hR⟩ with e | e
    · exact Or.inl (HeightOneSpectrum.ext (congrArg Subtype.val e))
    · exact Or.inr (HeightOneSpectrum.ext (congrArg Subtype.val e))
  obtain ⟨Q, Q', hn, h, h'⟩ := hv
  have hef := (two_primes _ E h2 v.asIdeal _ _ (hne Q Q' h h' hn)).2 ⟨_, hm P hP⟩
  have hlo : P.asIdeal.LiesOver v.asIdeal := ⟨hP.symm⟩
  have hPm : P.asIdeal.IsMaximal := P.isMaximal
  have he : v.asIdeal.ramificationIdx' P.asIdeal = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot]
    exact Nat.eq_one_of_mul_eq_one_right hef
  have hf : v.asIdeal.inertiaDeg' P.asIdeal = 1 := by
    rw [Ideal.inertiaDeg'_eq_inertiaDeg]
    exact Nat.eq_one_of_mul_eq_one_left hef
  refine ⟨?_, fun a k => ?_, fun b => ?_⟩
  · rw [Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P.asIdeal v.asIdeal v.isPrime v.ne_bot, hf, pow_one]
  · rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot] at he
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.intValuation_le_pow_iff_mem,
      ← HeightOneSpectrum.intValuation_liesOver v P a, he, pow_one]
  · rw [Ideal.inertiaDeg'_algebraMap] at hf
    let _ := Ideal.Quotient.field v.asIdeal
    obtain ⟨c, hc⟩ := (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 hf).2 (Ideal.Quotient.mk _ b)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact ⟨a, Ideal.Quotient.eq.1 hc.symm⟩

end GlobalTheory.CMVal.Euler.SplitPlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitsInCMFieldTwoPrimesDegreeOneStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitsInCMField_two_primes_degree_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (v : HeightOneSpectrum (OF E)), Splits v → (∀ P P' : HeightOneSpectrum (𝓞 E), Over P v → Over P' v → P ≠ P' → ∀ R : HeightOneSpectrum (𝓞 E), Over R v → R = P ∨ R = P') ∧ ∀ P : HeightOneSpectrum (𝓞 E), Over P v → Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧ (∀ (a : OF E) (k : ℕ), algebraMap (OF E) (𝓞 E) a ∈ P.asIdeal ^ k ↔ a ∈ v.asIdeal ^ k) ∧ ∀ b : 𝓞 E, ∃ a : OF E, b - algebraMap (OF E) (𝓞 E) a ∈ P.asIdeal := by
  first | exact @GlobalTheory.CMVal.Euler.SplitPlace.split_place | exact GlobalTheory.CMVal.Euler.SplitPlace.split_place | (intros; apply GlobalTheory.CMVal.Euler.SplitPlace.split_place <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSectionIntegralFiniteIdeleUpToUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSectionIntegralFiniteIdeleUpToUnits
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open scoped nonZeroDivisors

namespace GlobalTheory.CMVal.IdeleIdeal

variable {E : Type} [Field E] [NumberField E]

def ordAt (y : (Af E)ˣ) (w : HeightOneSpectrum (𝓞 E)) : ℕ := (-WithZero.log (Valued.v ((y : Af E) w))).toNat

def idealOf (y : (Af E)ˣ) : Ideal (𝓞 E) := ∏ᶠ w : HeightOneSpectrum (𝓞 E), w.asIdeal ^ ordAt y w

theorem ordAt_eventually (y : (Af E)ˣ) : ∀ᶠ w in Filter.cofinite, ordAt y w = 0 := by
  filter_upwards [(FiniteAdeleRing.isUnit_iff.1 y.isUnit).2] with w hw
  simp [ordAt, hw]

theorem finite_pow (y : (Af E)ˣ) :
    (Function.mulSupport fun w : HeightOneSpectrum (𝓞 E) => w.asIdeal ^ ordAt y w).Finite := by
  have := ordAt_eventually y
  rw [Filter.eventually_cofinite] at this
  refine this.subset fun v hv h1 => hv ?_
  simp [h1]

theorem ordAt_cast {y : (Af E)ˣ} {w : HeightOneSpectrum (𝓞 E)} (h : Valued.v ((y : Af E) w) ≤ 1) :
    (ordAt y w : ℤ) = -WithZero.log (Valued.v ((y : Af E) w)) := by
  have h0 := IdeleModule.coord_ne y w
  have : WithZero.log (Valued.v ((y : Af E) w)) ≤ 0 := by
    rw [← WithZero.exp_le_exp, WithZero.exp_log h0, WithZero.exp_zero]; exact h
  unfold ordAt
  omega

theorem modF_eq {y : (Af E)ˣ} (h : ∀ w, Valued.v ((y : Af E) w) ≤ 1) :
    modF y = ((Ideal.absNorm (idealOf y) : ℕ) : ℝ)⁻¹ := by
  unfold idealOf modF
  rw [map_finprod Ideal.absNorm (finite_pow y)]
  have hf : (Function.mulSupport fun w : HeightOneSpectrum (𝓞 E) => Ideal.absNorm (w.asIdeal ^ ordAt y w)).Finite :=
    (finite_pow y).subset fun w hw h1 => hw (by simp only [h1, map_one])
  have := map_finprod (Nat.castRingHom ℝ) hf
  simp only [eq_natCast] at this
  rw [this, ← finprod_inv_distrib]
  refine finprod_congr fun w => ?_
  rw [map_pow, Nat.cast_pow, ← zpow_natCast, ordAt_cast (h w), zpow_neg, inv_inv]

theorem count_idealOf (y : (Af E)ˣ) (w : HeightOneSpectrum (𝓞 E)) :
    FractionalIdeal.count E w (idealOf y : FractionalIdeal (𝓞 E)⁰ E) = ordAt y w := by
  have h1 : (idealOf y : FractionalIdeal (𝓞 E)⁰ E) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 E), (v.asIdeal : FractionalIdeal (𝓞 E)⁰ E) ^ (ordAt y v : ℤ) := by
    have := map_finprod (FractionalIdeal.coeIdealHom (𝓞 E)⁰ E) (finite_pow y)
    simp only [map_pow, FractionalIdeal.coeIdealHom_apply] at this
    simp only [zpow_natCast]
    exact this
  rw [h1, FractionalIdeal.count_finprod]
  filter_upwards [ordAt_eventually y] with v hv
  simp [hv]

theorem val_eq_of_idealOf_eq {y y' : (Af E)ˣ} (h : ∀ w, Valued.v ((y : Af E) w) ≤ 1)
    (h' : ∀ w, Valued.v ((y' : Af E) w) ≤ 1) (e : idealOf y = idealOf y') (w : HeightOneSpectrum (𝓞 E)) :
    Valued.v ((y : Af E) w) = Valued.v ((y' : Af E) w) := by
  have h1 := count_idealOf y w
  rw [e, count_idealOf, ordAt_cast (h w), ordAt_cast (h' w), neg_inj] at h1
  rw [← WithZero.exp_log (IdeleModule.coord_ne y w), ← h1, WithZero.exp_log (IdeleModule.coord_ne y' w)]

end GlobalTheory.CMVal.IdeleIdeal


open GlobalTheory.CMVal.IdeleIdeal in
theorem GlobalTheory.CMVal.exists_idele_section_of_ideal : ∀ (E : Type) [Field E] [NumberField E] , ∃ g : Ideal (𝓞 E) → (Af E)ˣ, ∀ y : (Af E)ˣ, (∀ w, Valued.v ((y : Af E) w) ≤ 1) → ∃ J : Ideal (𝓞 E), modF y = ((Ideal.absNorm J : ℕ) : ℝ)⁻¹ ∧ ∀ w, Valued.v ((((g J)⁻¹ * y : (Af E)ˣ) : Af E) w) = 1 := by
  intro E _ _
  classical
  refine ⟨fun J => if h : ∃ y : (Af E)ˣ, (∀ w, Valued.v ((y : Af E) w) ≤ 1) ∧ idealOf y = J then h.choose else 1,
    fun y hy => ⟨idealOf y, modF_eq hy, fun w => ?_⟩⟩
  have h : ∃ y' : (Af E)ˣ, (∀ w, Valued.v ((y' : Af E) w) ≤ 1) ∧ idealOf y' = idealOf y := ⟨y, hy, rfl⟩
  simp only [dif_pos h]
  rw [Units.val_mul, mul_coord, inv_coord, map_mul, map_inv₀,
    val_eq_of_idealOf_eq h.choose_spec.1 hy h.choose_spec.2 w, inv_mul_cancel₀ (IdeleModule.coord_ne y w)]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSectionIntegralFiniteIdeleUpToUnitsStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ideal_section_integralFiniteIdele_upToUnits : ∀ (E : Type) [Field E] [NumberField E] , ∃ g : Ideal (𝓞 E) → (Af E)ˣ, ∀ y : (Af E)ˣ, (∀ w, Valued.v ((y : Af E) w) ≤ 1) → ∃ J : Ideal (𝓞 E), modF y = ((Ideal.absNorm J : ℕ) : ℝ)⁻¹ ∧ ∀ w, Valued.v ((((g J)⁻¹ * y : (Af E)ˣ) : Af E) w) = 1 := by
  first | exact @GlobalTheory.CMVal.exists_idele_section_of_ideal | exact GlobalTheory.CMVal.exists_idele_section_of_ideal | (intros; apply GlobalTheory.CMVal.exists_idele_section_of_ideal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarChart
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal

namespace GlobalTheory.FlagQuotHaar

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def HaarChart (X : Data E r) (c : ℝ≥0∞) : Prop :=
  ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) →
    ∫⁻ g, φ (frameOf X g) ∂haarR X = c * ∫⁻ z, φ (cpt X (baseFr X) z) ∂muF X (baseFr X)

def trF {E' : Type} [Field E'] [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r) (e : X.Ψ ≃ X'.Ψ)
    (y : Frame X.Ψ r) : Frame X'.Ψ r :=
  fun τ' => (mat (baseFr X') τ' * (mat (baseFr X) (e.symm τ'))⁻¹ * mat y (e.symm τ') : Matrix (Fin r) (Fin r) ℂ)

end

end GlobalTheory.FlagQuotHaar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaFactorPowTwoMul
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem omegaFactor_pow_two_mul : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 : Frac F) (s : ℕ), (omegaFactor 𝔞 : ℂ) ^ (2 * s) = ((|(discr F : ℚ)| ^ s * FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ^ (2 * s) : ℚ) : ℂ) := by
  intro F _ _ _ 𝔞 s
  have hsq : (omegaFactor 𝔞 : ℝ) ^ 2 = (|(discr F : ℝ)| * ((FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) : ℚ) : ℝ) ^ 2) := by
    simp only [omegaFactor, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm, ← Real.sqrt_eq_rpow]
    rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]
  have h2 : (omegaFactor 𝔞 : ℂ) ^ (2 * s) = (((omegaFactor 𝔞 : ℝ) ^ 2) ^ s : ℝ) := by
    push_cast; rw [pow_mul]
  rw [h2, hsq]
  push_cast
  rw [mul_pow, ← pow_mul]
  congr 2
  rw [← Complex.ofReal_ratCast, Rat.cast_abs, Rat.cast_intCast]

end GlobalTheory.HilbFam
end
