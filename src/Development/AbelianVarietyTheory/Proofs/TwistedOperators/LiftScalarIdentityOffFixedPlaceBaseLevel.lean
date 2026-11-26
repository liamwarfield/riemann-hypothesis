module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarAtOf
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.PhaseBreaksTargetParts
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateDatumLiftJointEigenspaceIntoOnePart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapConjTransposeTwist

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerEqZeroOfMemRangeAdjoint
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalar

theorem ker_le_span_of_rel {K X Y H W : Type} [Field K] [AddCommGroup X] [Module K X] [FiniteDimensional K X] [AddCommGroup Y]
    [Module K Y] [AddCommGroup H] [Module ℂ H] [AddCommGroup W] [Module ℂ W] (σ : K →+* ℂ) (j : X →ₛₗ[σ] H)
    (jW : Y →ₛₗ[σ] W) (T : H →ₗ[ℂ] W) (Rel : X → Y → Prop) (hex : ∀ x, ∃ y, Rel x y)
    (hsp : Submodule.span ℂ (Set.range j) = ⊤)
    (hind : ∀ (n : ℕ) (b : Fin n → Y), LinearIndependent K b → LinearIndependent ℂ fun k => jW (b k))
    (hT : ∀ x y, Rel x y → jW y = T (j x)) :
    LinearMap.ker T ≤ Submodule.span ℂ (j '' {u | Rel u 0}) := by
  have hinj : Function.Injective jW := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    by_contra h0
    exact (hind 1 (fun _ => x) (linearIndependent_unique_iff.2 h0)).ne_zero 0 hx
  choose f hf using hex
  have e : ∀ x, jW (f x) = T (j x) := fun x => hT x _ (hf x)
  let θ : X →ₗ[K] Y :=
    { toFun := f
      map_add' := fun x y => hinj (by rw [map_add (f := _), e, e, e, map_add (f := _), map_add (f := _)])
      map_smul' := fun a x => hinj (by rw [RingHom.id_apply, map_smulₛₗ, e, e, map_smulₛₗ, map_smul]) }
  refine (GlobalTheory.ker_le_span_image_ker_of_semilinear K X Y H W σ θ j jW T hsp hind fun x => (e x).symm).trans
    (Submodule.span_mono (Set.image_mono fun u hu => ?_))
  have h0 : f u = 0 := hu
  exact h0 ▸ hf u

theorem mem_orthogonal_of_le_span {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {N : Submodule ℂ H} {s : Set H}
    (h : N ≤ Submodule.span ℂ s) {v : H} (hv : ∀ u ∈ s, ⟪v, u⟫_ℂ = 0) : v ∈ Nᗮ := by
  refine Submodule.orthogonal_le h ((Submodule.mem_orthogonal' _ _).2 fun u hu => ?_)
  induction hu using Submodule.span_induction with
  | mem u hu => exact hv u hu
  | zero => exact inner_zero_right _
  | add u u' _ _ h h' => rw [inner_add_right, h, h', add_zero]
  | smul a u _ h => rw [inner_smul_right, h, mul_zero]

theorem toF_mem {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) : B.toF ℓ Z y ∈ Z := by
  obtain ⟨f, hf, e⟩ : (B.zE ℓ Z).mulVec y ∈ B.Z0 ℓ Z := (subspace_image_spec _ _ _).2.le ⟨y, rfl⟩
  have : B.toF ℓ Z y = f := (congrArg B.S.basis.equivFun.symm e.symm).trans (B.S.basis.equivFun.symm_apply_apply f)
  exact this ▸ hf

theorem inner_eq_zero_of_mem_range_adjoint {H W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (T : H →ₗ[ℂ] W) {a b : H}
    (ha : a ∈ LinearMap.range (LinearMap.adjoint T)) (hb : T b = 0) : ⟪a, b⟫_ℂ = 0 := by
  obtain ⟨w, rfl⟩ := ha
  rw [LinearMap.adjoint_inner_left, hb, inner_zero_right]

theorem mem_orthogonal_of_rel {K X Y H W : Type} [Field K] [AddCommGroup X] [Module K X] [FiniteDimensional K X] [AddCommGroup Y]
    [Module K Y] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (σ : K →+* ℂ)
    (j : X →ₛₗ[σ] H) (jW : Y →ₛₗ[σ] W) (th : H →ₗ[ℂ] W) (U : W ≃ₗᵢ[ℂ] W) (κ : ℂ) (g : W →ₗ[ℂ] W) (Rel : X → Y → Prop)
    (hex : ∀ x, ∃! y, Rel x y) (hsp : Submodule.span ℂ (Set.range j) = ⊤)
    (hind : ∀ (n : ℕ) (b : Fin n → Y), LinearIndependent K b → LinearIndependent ℂ fun k => jW (b k))
    (hT : ∀ x y, Rel x y → U (jW y) = κ • g (th (j x))) {v : H} (hv : ∀ u, Rel u 0 → ⟪v, j u⟫_ℂ = 0) :
    v ∈ (LinearMap.ker th)ᗮ := by
  have hk := ker_le_span_of_rel σ j jW ((U.symm.toLinearEquiv.toLinearMap ∘ₗ (κ • g)) ∘ₗ th) Rel (fun x => (hex x).exists) hsp
    hind (fun x y h => U.toLinearEquiv.eq_symm_apply.2 (hT x y h))
  refine mem_orthogonal_of_le_span ((LinearMap.ker_le_ker_comp _ _).trans hk) ?_
  rintro _ ⟨u, hu, rfl⟩
  exact hv u hu

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem csum_eq_zero_of_adjoint (h1 : R.models_HV) (h2 : R.models_jV) (i : Fin D.R.m) (t : T0) {f g : A.fam.amb.FL i t}
    (hf : R.jV i t f ∈ LinearMap.range (LinearMap.adjoint (R.thG i t))) (hg : R.thG i t (R.jV i t g) = 0) :
    (A.fam.L i t).S.csum f.1 g.1 = 0 := by
  have h3 : inner ℂ (R.jV i t f) (R.jV i t g) = D.what₂.embLL ((A.fam.L i t).S.csum f.1 g.1) := by
    refine ((h1 i t).2.2 (R.jV i t f) (R.jV i t g)).trans ?_
    refine (congrArg₂ (Bridge.adInner (Bridge.ratF (Vc D i)) (levEnv _ (R.βV i) (R.datVt i t)).J (R.B.L i t).pres.y)
      (h2 i t f) (h2 i t g)).trans ?_
    exact GlobalTheory.PresBasic.isom (R.B.L i t).pres f g
  exact (map_eq_zero _).1 (h3.symm.trans (inner_eq_zero_of_mem_range_adjoint _ hf hg))

end


set_option maxHeartbeats 1600000 in
theorem conjForms_mem_orthogonal_ker : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.IsModels → R.LUnif → ∀ gramR c0R c0L, GlobalTheory.GalLift.Comparison₂ R gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), ∀ (μ' η' : (AE D)ˣ →* Circle) (th : H.H →ₗ[ℂ] (R.HW i σ).H), ∀ ph : ℂ, ph ≠ 0 → (∀ x, ∃! y, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph x y) → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.ConjAt R i σ ph (c0L i) → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjDatum R i σ (c0L i) μ' η' c c₁ H j th → ∀ (ℓ : Lvl D.what₂.LL G) (Z : Submodule D.what₂.LL (A.fam.L i A.μ0).S.Forms), Formalism.DivisionValues.IsRatHerm (Formalism.DivisionValues.cmMax D.what₂.LL) ((A.fam.L i A.μ0).HZ ℓ Z) ((A.fam.L i A.μ0).XQ ℓ Z) → (∀ a k, (A.fam.L i A.μ0).fE ℓ Z a k ∈ Formalism.DivisionValues.cmMax D.what₂.LL) → (∀ z ∈ Z, R.jV i A.μ0 z ∈ LinearMap.range (LinearMap.adjoint (R.thG i A.μ0))) → ∀ x, j ((A.fam.L i A.μ0).toF ℓ Z x) ∈ (LinearMap.ker th)ᗮ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hM hU gramR c0R c0L hT i σ c c₁ H j μ' η' th ph hph hex hC hD ℓ Z hH hE hZ x
  obtain ⟨-, -, u, U, z, ζ, -, -, -, hall⟩ := hC
  obtain ⟨-, κ, -, hκ⟩ := hall μ' η' c c₁ H j th hD
  have hsp := GlobalTheory.ConjSpan.span_conjForms R hM.jV gramR c0R c0L hT i σ c c₁ H j hD.2.2.1
  have : FiniteDimensional D.what₂.LL (A.fam.amb.FL i A.μ0) := Module.Finite.of_basis (A.fam.L i A.μ0).S.basis
  refine mem_orthogonal_of_rel σ j ((R.FW i).j σ) th U κ (R.gW i σ z) (GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph) hex hsp (hU i σ).1
    hκ fun v hv => ?_
  have h0 : R.thG i A.μ0 (R.jV i A.μ0 v) = 0 :=
    (smul_eq_zero.1 ((map_zero _).symm.trans hv).symm).resolve_left hph
  refine (GlobalTheory.LiftLower.inner_conjForms_eq_csumAt R hM.jV gramR c0R c0L hT i σ c c₁ H j hD.2.2.1 _ v).trans ?_
  exact (GlobalTheory.Proof.ConjugateTransposeMajorant.majAt_eq_csumAt (A.fam.L i A.μ0) ℓ Z hH hE).2 v
    (fun y => csum_eq_zero_of_adjoint hM.HV hM.jV i A.μ0 (hZ _ (toF_mem _ ℓ Z y)) h0) σ x

end GlobalTheory.ConjScalar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SemilinearInjectiveOfIndep
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalar

theorem semilinear_injective_of_indep {K L V W ι : Type} [Field K] [Field L] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module L W] {φ : K →+* L} (b : Module.Basis ι K V) (c : V →ₛₗ[φ] W)
    (h : LinearIndependent L fun a => c (b a)) : Function.Injective c := by
  refine (injective_iff_map_eq_zero c).2 fun v hv => ?_
  have hexp : c v = ∑ i ∈ (b.repr v).support, φ (b.repr v i) • c (b i) := by
    conv_lhs => rw [← b.linearCombination_repr v]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smulₛₗ c _ _
  have hz := linearIndependent_iff'.1 h (b.repr v).support (fun i => φ (b.repr v i)) (by rw [← hv, hexp])
  have hrepr : b.repr v = 0 := by
    ext i
    rw [Finsupp.coe_zero, Pi.zero_apply]
    by_contra hne
    exact hne (φ.injective ((hz i (Finsupp.mem_support_iff.2 hne)).trans (map_zero φ).symm))
  exact b.repr.injective (hrepr.trans (map_zero _).symm)

theorem hkF_single_one {D : D7} (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (d : List ℤ)
    (F : Bridge.Gf V → W) (h : Bridge.Gf V) :
    GlobalTheory.Hk3.hkF V P (Finsupp.single d 1) F h = ∑ γ ∈ GlobalTheory.Hk3.rep V P d, F (h * (finHom V).rangeRestrict γ) := by
  simp only [GlobalTheory.Hk3.hkF]
  rw [Finsupp.sum_single_index, one_smul]
  exact zero_smul ℂ _

theorem hkF_transfer {D : D7} (V : HSp D) {K U W W' : Type} [Field K] [AddCommGroup U] [Module K U] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] {φ σ : K →+* ℂ} (c₀ : U →ₛₗ[φ] W) (c₁ : U →ₛₗ[σ] W') (inj : Function.Injective c₀)
    (F : Bridge.Gf V → W) (F' : Bridge.Gf V → W') (hb : ∀ h, ∃ v, F h = c₀ v ∧ F' h = c₁ v)
    (P : Pl D.host.E) (d : List ℤ) (a : K) (e : GlobalTheory.Hk3.hkF V P (Finsupp.single d 1) F = φ a • F) :
    GlobalTheory.Hk3.hkF V P (Finsupp.single d 1) F' = σ a • F' := by
  choose v hv using hb
  funext h
  have e' := congrFun e h
  rw [hkF_single_one, Pi.smul_apply] at e'
  rw [hkF_single_one, Pi.smul_apply]
  have key : ∑ γ ∈ GlobalTheory.Hk3.rep V P d, v (h * (finHom V).rangeRestrict γ) = a • v h := by
    apply inj
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_smulₛₗ]
    simp only [← fun x => (hv x).1]
    exact e'
  simp only [fun x => (hv x).2]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_smulₛₗ, ← key, map_sum]

theorem eigF_conj : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_jV → ∀ gramR c0R c0L, GlobalTheory.GalLift.Comparison₂ R gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ (c0L i) c c₁ H j → ∀ a x, GlobalTheory.ConjScalar.EigK R i a x → GlobalTheory.ConjScalar.EigF R i (fun P d => σ (a P d)) (H.e (j x)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R _ gramR c0R c0L hT i σ c c₁ H j hc a x hx
  have hind : LinearIndependent ℂ fun k => c0L i (bVV D.what₂.LL (lamV D i) k) :=
    (Formalism.IndefR.Bridge.FamTie.mapL hT i).2.1
  have inj : Function.Injective (c0L i) := semilinear_injective_of_indep (bVV D.what₂.LL (lamV D i)) (c0L i) hind
  intro P d hG hL
  have e := hx P d hG hL
  exact hkF_transfer (Vc D i) (c0L i) c₁ inj _ _ (hc.base x) P d (a P d) e

end GlobalTheory.ConjScalar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLiftReadingsScaleClassSumEigenspaces
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointApplyOfOrthogonalKer
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalar

theorem adjoint_apply_of_orthogonal_ker {H W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (T : H →ₗ[ℂ] W) {u : H} {l : ℂ}
    (hu : u ∈ (LinearMap.ker T)ᗮ) (h : T (LinearMap.adjoint T (T u)) = l • T u) : LinearMap.adjoint T (T u) = l • u := by
  have hk : LinearMap.adjoint T (T u) - l • u ∈ LinearMap.ker T := by
    rw [LinearMap.mem_ker, map_sub, map_smul, h, sub_self]
  have hr : LinearMap.adjoint T (T u) ∈ (LinearMap.ker T)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro k hk'
    rw [LinearMap.adjoint_inner_right, LinearMap.mem_ker.mp hk', inner_zero_left]
  have ho : LinearMap.adjoint T (T u) - l • u ∈ (LinearMap.ker T)ᗮ :=
    Submodule.sub_mem _ hr (Submodule.smul_mem _ l hu)
  have hz := Submodule.inner_right_of_mem_orthogonal hk ho
  rwa [inner_self_eq_zero, sub_eq_zero] at hz

theorem inner_apply_of_adjoint_eq {H W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (T : H →ₗ[ℂ] W) {u : H} {l : ℝ}
    (h : LinearMap.adjoint T (T u) = (l : ℂ) • u) (w : H) : ⟪T u, T w⟫_ℂ = (l : ℂ) * ⟪u, w⟫_ℂ := by
  rw [← LinearMap.adjoint_inner_left, h, inner_smul_left, Complex.conj_ofReal]

theorem conj_csumAt {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ) (f g : S.Forms) :
    starRingEnd ℂ (GlobalTheory.LiftLower.csumAt S ((starRingEnd ℂ).comp σ) f g) = GlobalTheory.LiftLower.csumAt S σ f g := by
  unfold GlobalTheory.LiftLower.csumAt
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, RingHom.comp_apply, map_sum, map_mul,
    Complex.star_def, Complex.conj_conj]

end GlobalTheory.ConjScalar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLiftReadingsScaleClassSumEigenspaces
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalar


set_option maxHeartbeats 2000000 in
theorem readings_scale_core : GlobalTheory.Hk3.HoweUnram → GlobalTheory.LowRow.ConjRatLift5 → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (F : Face D A) (ph : ℂ), GlobalTheory.Hk3.Core R F → IsStdChar D R.ψ (-1) → GlobalTheory.ConjScalar.ConjScalarAt R → ∀ fw : FWTie T R κ v₀, BarTie fw → IoExt R → R.LUnif → (∀ i, OMPins T R κ v₀ O i) → ∀ i : Fin D.R.m, (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph → ∀ (ℓ : Lvl D.what₂.LL G) (Z : Submodule D.what₂.LL (A.fam.L i A.μ0).S.Forms), Formalism.DivisionValues.IsRatHerm (Formalism.DivisionValues.cmMax D.what₂.LL) ((A.fam.L i A.μ0).HZ ℓ Z) ((A.fam.L i A.μ0).XQ ℓ Z) → (∀ a k, (A.fam.L i A.μ0).fE ℓ Z a k ∈ Formalism.DivisionValues.cmMax D.what₂.LL) → (∀ z ∈ Z, R.jV i A.μ0 z ∈ LinearMap.range (LinearMap.adjoint (R.thG i A.μ0))) → ∀ (σ : D.what₂.LL →+* ℂ) (a : Pl D.host.E → List ℤ → D.what₂.LL), ∃ l : ℝ, ∀ x x' y y', GlobalTheory.ConjScalar.EigK R i a ((A.fam.L i A.μ0).toF ℓ Z x) → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph ((A.fam.L i A.μ0).toF ℓ Z x) y → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph x' y' → ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ = (l : ℂ) * GlobalTheory.LiftLower.csumAt (A.fam.L i A.μ0).S σ ((A.fam.L i A.μ0).toF ℓ Z x) x' := by
  intro hH hCR D G _ _ Pl0 T0 A T _ R κ v₀ O F ph hC hψ hS fw hbar hio hU hpins i hom ℓ Z hHz hE hZ
  obtain ⟨gramR, c0R, c0L, tie⟩ := hC.fam.tie
  obtain ⟨hex, hconj, hbarσ⟩ := hCR D G Pl0 T0 A T R F κ v₀ O ph (GlobalTheory.Core5.of_core hC) hψ fw hbar hio hU hpins i hom
  have hph : ph ≠ 0 := by
    intro h0
    have h1 : ‖ph‖ = 1 := hom.2.1.2.2.2.2.1
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hcore : GlobalTheory.Hk3.Core R F := hC
  have key : ∀ σ : D.what₂.LL →+* ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → ∀ a : Pl D.host.E → List ℤ → D.what₂.LL, ∃ l : ℝ, ∀ x x' y y',
      GlobalTheory.ConjScalar.EigK R i a ((A.fam.L i A.μ0).toF ℓ Z x) → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph ((A.fam.L i A.μ0).toF ℓ Z x) y →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph x' y' →
      ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ = (l : ℂ) * GlobalTheory.LiftLower.csumAt (A.fam.L i A.μ0).S σ ((A.fam.L i A.μ0).toF ℓ Z x) x' := by
    intro σ hσ a
    have hCA := hconj gramR c0R c0L tie σ hσ
    obtain ⟨μ', η', c, c₁, H, j, th, hD⟩ := hCA.2.1
    have hyp : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.HypConj R i σ μ' η' := by
      obtain ⟨-, -, u, U, z, ζ, -, -, -, hall⟩ := hCA
      exact (hall μ' η' c c₁ H j th hD).1
    obtain ⟨ev, hev⟩ := GlobalTheory.T.conjugateDatumLift_jointEigenspace_into_one_part hH R F hcore gramR c0R c0L tie i σ c c₁ H j hσ μ' η' th hD hyp (fun P d => σ (a P d))
    obtain ⟨l, hl⟩ := hS gramR c0R c0L tie i σ hσ μ' η' c c₁ H j th hD ev
    refine ⟨l, fun x x' y y' hx hy hy' => ?_⟩
    have hE' := eigF_conj R hC.models.jV gramR c0R c0L tie i σ c c₁ H j hD.2.2.1 a _ hx
    have hp := hev _ hE'
    have hperp := conjForms_mem_orthogonal_ker R hC.models hU gramR c0R c0L tie i σ c c₁ H j μ' η' th ph hph hex hCA hD ℓ Z hHz hE hZ x
    have hadj := adjoint_apply_of_orthogonal_ker th hperp (hl _ hp)
    refine (GlobalTheory.ConjLiftCounterexample.gram_of_conjAt hCA hD hy hy').trans ?_
    refine (inner_apply_of_adjoint_eq th hadj _).trans ?_
    rw [GlobalTheory.LiftLower.inner_conjForms_eq_csumAt R hC.models.jV gramR c0R c0L tie i σ c c₁ H j hD.2.2.1]
    rfl
  intro σ a
  by_cases hσ : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ
  · exact key σ hσ a
  · obtain ⟨hσ', hbar'⟩ := hbarσ σ hσ
    obtain ⟨l, hl⟩ := key _ hσ' a
    refine ⟨l, fun x x' y y' hx hy hy' => ?_⟩
    rw [hbar' y y', hl x x' y y' hx hy hy', map_mul, Complex.conj_ofReal, conj_csumAt]

end GlobalTheory.ConjScalar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLiftReadingsScaleClassSumEigenspacesStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalLift_readings_scale_classSum_eigenspaces : GlobalTheory.Hk3.HoweUnram → GlobalTheory.LowRow.ConjRatLift5 → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (F : Face D A) (ph : ℂ), GlobalTheory.Hk3.Core R F → IsStdChar D R.ψ (-1) → GlobalTheory.ConjScalar.ConjScalarAt R → ∀ fw : FWTie T R κ v₀, BarTie fw → IoExt R → R.LUnif → (∀ i, OMPins T R κ v₀ O i) → ∀ i : Fin D.R.m, (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph → ∀ (ℓ : Lvl D.what₂.LL G) (Z : Submodule D.what₂.LL (A.fam.L i A.μ0).S.Forms), Formalism.DivisionValues.IsRatHerm (Formalism.DivisionValues.cmMax D.what₂.LL) ((A.fam.L i A.μ0).HZ ℓ Z) ((A.fam.L i A.μ0).XQ ℓ Z) → (∀ a k, (A.fam.L i A.μ0).fE ℓ Z a k ∈ Formalism.DivisionValues.cmMax D.what₂.LL) → (∀ z ∈ Z, R.jV i A.μ0 z ∈ LinearMap.range (LinearMap.adjoint (R.thG i A.μ0))) → ∀ (σ : D.what₂.LL →+* ℂ) (a : Pl D.host.E → List ℤ → D.what₂.LL), ∃ l : ℝ, ∀ x x' y y', GlobalTheory.ConjScalar.EigK R i a ((A.fam.L i A.μ0).toF ℓ Z x) → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph ((A.fam.L i A.μ0).toF ℓ Z x) y → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph x' y' → ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ = (l : ℂ) * GlobalTheory.LiftLower.csumAt (A.fam.L i A.μ0).S σ ((A.fam.L i A.μ0).toF ℓ Z x) x' := by
  first | exact @GlobalTheory.ConjScalar.readings_scale_core | exact GlobalTheory.ConjScalar.readings_scale_core | (intros; apply GlobalTheory.ConjScalar.readings_scale_core <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.ScalAtZeroOfLiftMat
noncomputable section

open NumberField IsDedekindDomain
open scoped InnerProductSpace Matrix

namespace GlobalTheory.ScalarConjugation

open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links

section Abstract

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem maj_eq_zero {n : ℕ} (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K) (x y : Fin n → K)
    (h : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) X v x x = 0) : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) X v x y = 0 := by
  have hc : ∀ i, Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K _) X v x i = 0 := by
    have hs : ∑ i, ((Complex.normSq (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K _) X v x i) : ℝ) : ℂ) = 0 := by
      rw [← h]
      unfold Formalism.HermitianLatticesTheory.majAt
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.normSq_eq_conj_mul_self]
      rfl
    have hr : ∑ i, Complex.normSq (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K _) X v x i) = 0 := by
      exact_mod_cast hs
    intro i
    exact Complex.normSq_eq_zero.1
      ((Finset.sum_eq_zero_iff_of_nonneg fun k _ => Complex.normSq_nonneg _).1 hr i (Finset.mem_univ i))
  unfold Formalism.HermitianLatticesTheory.majAt
  exact Finset.sum_eq_zero fun i _ => by rw [hc i, star_zero, zero_mul]

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

end Abstract

section Concrete

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

end Concrete

section Comparison₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.MainNotions

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}


end Comparison₂

end GlobalTheory.ScalarConjugation
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftPointsPartEigenformsCoefficientField
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftPointsPartEigenformsCoefficientField
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ZPartEig

theorem heckePolyOf_coeff {L : Type} [Field L] (n q : ℕ) (a : ℕ → L) {k : ℕ} (hk : k ≤ n) :
    (Formalism.L2.Col.heckePolyOf n q a).coeff k = (-1) ^ k * (q : L) ^ (k * (k - 1) / 2) * a k := by
  classical
  simp only [Formalism.L2.Col.heckePolyOf, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  rw [if_pos (Finset.mem_range.2 (Nat.lt_succ_of_le hk))]

theorem heckePolyOf_val_eq {L : Type} [Field L] [CharZero L] (n q : ℕ) (hq : q ≠ 0) (a b : ℕ → L)
    (h : Formalism.L2.Col.heckePolyOf n q a = Formalism.L2.Col.heckePolyOf n q b) {k : ℕ} (hk : k ≤ n) : a k = b k := by
  have e := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p k) h
  simp only [heckePolyOf_coeff n q _ hk] at e
  have hne : ((-1 : L) ^ k * (q : L) ^ (k * (k - 1) / 2)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (Nat.cast_ne_zero.2 hq))
  exact mul_left_cancel₀ hne e

theorem apply_of_mem_maxGen {K V H : Type} [Field K] [AddCommGroup V] [Module K V] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : K →+* ℂ) (j : V →ₛₗ[σ] H) (T : Module.End K V)
    (N : Module.End ℂ H) (hN : Commute N (LinearMap.adjoint N)) (hj : ∀ f, j (T f) = N (j f)) (c : K) (f : V)
    (hf : f ∈ T.maxGenEigenspace c) : N (j f) = σ c • j f := by
  have key : ∀ (k : ℕ) (g : V), j (((T - c • (1 : Module.End K V)) ^ k : Module.End K V) g) =
      (((N - σ c • (1 : Module.End ℂ H)) ^ k : Module.End ℂ H) (j g)) := by
    intro k
    induction k with
    | zero => intro g; simp
    | succ k ih =>
      intro g
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      congr 1
      simp [hj, map_smulₛₗ]
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hf
  have h0 : (((N - σ c • (1 : Module.End ℂ H)) ^ k : Module.End ℂ H) (j f)) = 0 := by rw [← key, hk, map_zero]
  have hmem : j f ∈ N.maxGenEigenspace (σ c) := (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, h0⟩
  rw [GlobalTheory.NormalFamily.maxGenEigenspace_eq hN] at hmem
  exact Module.End.mem_eigenspace_iff.1 hmem

end GlobalTheory.ZPartEig

namespace GlobalTheory.ZPartEig

open GlobalTheory.ConjScalar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def OpLab (R : RealDat3 D A3 Ks) (i : Fin D.R.m) : (A3.liftI i A3.A.μ0).OpIx → Pl D.host.E → List ℤ → Prop :=
  Sum.elim
    (fun k P d => R.pl ((A3.A.fam.L i A3.A.μ0).pl k.1) = P ∧ k.2 ≤ (Vc D i).rank ∧ d = splitLab (Vc D i).rank k.2)
    (fun k P d => R.plI ((A3.liftI i A3.A.μ0).plI k.1) = P ∧ Formalism.L2.Col.InertTypeOk (Vc D i).rank k.2 ∧
      d = GlobalTheory.Hk3.labIn (Vc D i).rank k.2)

theorem opLab_ops (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (i : Fin D.R.m)
    (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV i A3.A.μ0).H) (hh : GlobalTheory.Hk3.IsOpsV R.toRealDat i A3.A.μ0 h) :
    ∀ idx P d, OpLab R i idx P d → GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P ∧
      ∀ f, R.jV i A3.A.μ0 ((A3.liftI i A3.A.μ0).opAll idx f) = h P (Finsupp.single d 1) (R.jV i A3.A.μ0 f) := by
  have hlev := hC.base.lev
  have hfam := hC.base.fam
  have hmod := hC.base.models
  have c3 := (GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hC).2.2.1
  rintro (⟨⟨P', hP'⟩, k⟩ | ⟨⟨Q, hQ⟩, s'⟩) P d hc
  · obtain ⟨rfl, hk, rfl⟩ := hc
    refine ⟨((GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hlev).2.2.2 hfam A3.A.μ0 P' hP').1, fun f => ?_⟩
    exact (GlobalTheory.SplitHeckeLabel.split_ops R.toRealDat F.lv2 hlev hfam hmod).2 i A3.A.μ0 h hh ⟨P', hP'⟩ k hk f
  · obtain ⟨rfl, hs, rfl⟩ := hc
    have hty : ∀ k : A3.okI A3.A.μ0 × List ℕ, Formalism.L2.Col.InertTypeOk (Vc D i).rank k.2 →
        GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 (R.plI k.1) ∧ Formalism.DivisionValues.conjPl (R.plI k.1) = R.plI k.1 ∧
          (GlobalTheory.Hk3.labIn (Vc D i).rank k.2).Pairwise (fun a b => b ≤ a) := fun k hk =>
      ⟨(c3 A3.A.μ0 k.1 k.1.2).1, (c3 A3.A.μ0 k.1 k.1.2).2,
        ((GlobalTheory.Hk3.labIn_selfDual_iff (Vc D i).rank _).2 ⟨k.2, hk.2.2, hk.1, hk.2.1, rfl⟩).2.1⟩
    refine ⟨(c3 A3.A.μ0 Q hQ).1, fun f => ?_⟩
    exact (GlobalTheory.InertHeckeLift.inert_lifts R.toRealDat F.lv2 hlev hfam hmod i A3.A.μ0 (A3.okI A3.A.μ0 × List ℕ)
      (fun k => R.plI k.1) (fun k => GlobalTheory.Hk3.labIn (Vc D i).rank k.2) (A3.heckeLI i A3.A.μ0)
      (fun k => Formalism.L2.Col.InertTypeOk (Vc D i).rank k.2) hty (hC.inert.hL i A3.A.μ0).some (⟨Q, hQ⟩, s') hs).2.2.2 h hh f

theorem exists_opLab (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (i : Fin D.R.m) :
    ∀ P d, GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P → RelLab (Vc D i) P d → ∃ idx, OpLab R i idx P d := by
  have c3 := (GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hC).2.2.2.1
  intro P d hg hr
  rcases hr with ⟨hc, k, hk, rfl⟩ | ⟨hc, hl⟩
  · obtain ⟨P0, hP0, rfl⟩ := (c3 P hg).2 hc
    exact ⟨Sum.inl (⟨P0, hP0⟩, k), rfl, hk, rfl⟩
  · obtain ⟨Q, hQ, rfl⟩ := (c3 P hg).1 hc
    obtain ⟨hlen, hpw, hdual⟩ := (GlobalTheory.LabChar.labels_char (Vc D i) _ d).1 hl
    obtain ⟨s', h1, h2, h3, rfl⟩ := (GlobalTheory.Hk3.labIn_selfDual_iff (Vc D i).rank d).1 ⟨hlen, hpw, hdual hc⟩
    exact ⟨Sum.inr (⟨Q, hQ⟩, s'), rfl, ⟨h2, h3, h1⟩, rfl⟩

theorem opLab_val_eq (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (i : Fin D.R.m)
    (q : Typ3 D.what₂.LL Pl0 I0 (List ℕ)) :
    ∀ idx P d, OpLab R i idx P d → ∀ y y', (A3.liftI i A3.A.μ0).HasRes3 q y → (A3.liftI i A3.A.μ0).HasRes3 q y' →
      y idx = y' idx := by
  rintro (⟨⟨P', hP'⟩, k⟩ | ⟨Q, s'⟩) P d hc y y' hy hy'
  · obtain ⟨-, hk, -⟩ := hc
    have hq : (A3.A.fam.L i A3.A.μ0).q ⟨P', hP'⟩ ≠ 0 := by
      show A3.A.q P' ≠ 0
      rw [((GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hC.base.lev).2.2.2 hC.base.fam A3.A.μ0 P' hP').2.2]
      exact fun h0 => (R.pl P').ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    have e : Formalism.L2.Col.heckePolyOf (A3.A.fam.L i A3.A.μ0).n ((A3.A.fam.L i A3.A.μ0).q ⟨P', hP'⟩)
          (fun j => y (Sum.inl (⟨P', hP'⟩, j))) =
        Formalism.L2.Col.heckePolyOf (A3.A.fam.L i A3.A.μ0).n ((A3.A.fam.L i A3.A.μ0).q ⟨P', hP'⟩)
          (fun j => y' (Sum.inl (⟨P', hP'⟩, j))) :=
      (hy.1 ⟨P', hP'⟩).trans (hy'.1 ⟨P', hP'⟩).symm
    have hk' : k ≤ (A3.A.fam.L i A3.A.μ0).n := by
      have e2 : (A3.A.fam.L i A3.A.μ0).n = A3.A.r + A3.A.t := rfl
      rw [e2, ← R.B.rankL i]; exact hk
    exact heckePolyOf_val_eq _ _ hq _ _ e hk'
  · exact (hy.2 (Q, s')).trans (hy'.2 (Q, s')).symm

end GlobalTheory.ZPartEig

namespace GlobalTheory.ZPartEig

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem thetaLiftPoint_mem_jointEigenspace_of_part (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hW : (R.toCx3 F).H3W F.cr false) (i : Fin D.R.m)
    (p : A3.fam3.base3.Ix) (x : Fin ((lv (F.fc (R.toCx3 F).zs) false).dZ i A3.A.μ0) → D.what₂.LL)
    (hx : (R.toCx3 F).tC F.cr false i A3.A.μ0 (cpt A3.A.v0.embedding x) ∈ (R.toCx3 F).Wp i p) :
    F.cr.toL (R.toCx3 F).zs false i A3.A.μ0 x ∈ (A3.liftI i A3.A.μ0).inertTypeEigenspaceSum (A3.fam3.tr3 i p.1) := by
  have hZ := (hW i p x).2 hx
  have h2 : (A3.A.fam.L i A3.A.μ0).vE (A3.A.fam.lvlA F.P0 F.ψ0) *ᵥ
      ((A3.A.fam.L i A3.A.μ0).zE (A3.A.fam.lvlA F.P0 F.ψ0) ((R.toCx3 F).zs.Zl i A3.A.μ0) *ᵥ x) ∈
      ((A3.liftI i A3.A.μ0).inertTypeEigenspaceSum (A3.fam3.tr3 i p.1)).map
        ((A3.A.fam.L i A3.A.μ0).S.basis.equivFun : (A3.A.fam.L i A3.A.μ0).S.Forms →ₗ[D.what₂.LL] _) := hZ
  obtain ⟨g, hg, hge⟩ := Submodule.mem_map.1 h2
  convert hg using 1
  rw [← LinearEquiv.symm_apply_apply (A3.A.fam.L i A3.A.μ0).S.basis.equivFun g]
  erw [hge]
  rfl

end GlobalTheory.ZPartEig

namespace GlobalTheory.ZPartEig

open GlobalTheory.ConjScalar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


open Classical in
def eigVal (R : RealDat3 D A3 Ks) (i : Fin D.R.m) (q : Typ3 D.what₂.LL Pl0 I0 (List ℕ)) (P : Pl D.host.E) (d : List ℤ) :
    D.what₂.LL :=
  if hx : (∃ y, (A3.liftI i A3.A.μ0).HasRes3 q y) ∧ ∃ idx, OpLab R i idx P d then hx.1.choose hx.2.choose else 0

theorem eig_of_mem (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (i : Fin D.R.m)
    (q : Typ3 D.what₂.LL Pl0 I0 (List ℕ))
    (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV i A3.A.μ0).H) (hh : GlobalTheory.Hk3.IsOpsV R.toRealDat i A3.A.μ0 h)
    (hn : GlobalTheory.Hk3.NormalFam (GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0) h) (f : (A3.A.fam.L i A3.A.μ0).S.Forms)
    (hf : f ∈ (A3.liftI i A3.A.μ0).inertTypeEigenspaceSum q) :
    ∀ P d, GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P → RelLab (Vc D i) P d →
      h P (Finsupp.single d 1) (R.jV i A3.A.μ0 f) = D.what₂.embLL (eigVal R i q P d) • R.jV i A3.A.μ0 f := by
  let E : Submodule ℂ (R.HV i A3.A.μ0).H :=
    ⨅ (P : Pl D.host.E) (d : List ℤ) (_ : GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P ∧ RelLab (Vc D i) P d),
      (h P (Finsupp.single d 1)).eigenspace (D.what₂.embLL (eigVal R i q P d))
  have hle : (A3.liftI i A3.A.μ0).inertTypeEigenspaceSum q ≤ E.comap (R.jV i A3.A.μ0) := by
    unfold InertDat3.inertTypeEigenspaceSum Formalism.L2.Col.eigSum
    refine iSup₂_le fun y hy g hg => ?_
    rw [Submodule.mem_comap]
    simp only [E, Submodule.mem_iInf]
    rintro P d ⟨hgd, hr⟩
    have hex : (∃ y, (A3.liftI i A3.A.μ0).HasRes3 q y) ∧ ∃ idx, OpLab R i idx P d :=
      ⟨⟨y, hy⟩, exists_opLab R F hC i P d hgd hr⟩
    have ha : eigVal R i q P d = hex.1.choose hex.2.choose := by
      unfold eigVal
      rw [dite_eq_left hex]
    have ha' : eigVal R i q P d = y hex.2.choose :=
      ha.trans (opLab_val_eq R F hC i q _ P d hex.2.choose_spec _ _ hex.1.choose_spec hy)
    have hop := opLab_ops R F hC i h hh _ P d hex.2.choose_spec
    have hN : Commute (h P (Finsupp.single d 1)) (LinearMap.adjoint (h P (Finsupp.single d 1))) :=
      (congrArg (Commute (h P (Finsupp.single d 1))) (hn.2 P hop.1 (Finsupp.single d 1))).mpr (hn.1 P P hop.1 hop.1 _ _)
    have key := apply_of_mem_maxGen D.what₂.embLL (R.jV i A3.A.μ0) ((A3.liftI i A3.A.μ0).opAll hex.2.choose) _ hN hop.2
      (y hex.2.choose) g (Formalism.L2.Col.eigAt_le (A3.liftI i A3.A.μ0).opAll y hex.2.choose hg)
    exact Module.End.mem_eigenspace_iff.2 (key.trans (congrArg (fun c => D.what₂.embLL c • R.jV i A3.A.μ0 g) ha'.symm))
  intro P d hg hr
  have e1 := hle hf
  rw [Submodule.mem_comap] at e1
  simp only [E, Submodule.mem_iInf] at e1
  exact Module.End.mem_eigenspace_iff.1 (e1 P d ⟨hg, hr⟩)

theorem points_eig : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (s : ℕ), A3.fam3.Ok3 s → R.WeakCharacterisation F → (R.toCx3 F).H3W F.cr false → ∀ i p, ∃ a, ∀ x, (R.toCx3 F).tC F.cr false i A3.A.μ0 (cpt A3.A.v0.embedding x) ∈ (R.toCx3 F).Wp i p → GlobalTheory.ConjScalar.EigK R.toRealDat i a (F.cr.toL (R.toCx3 F).zs false i A3.A.μ0 x) := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F s _hOk hC hW i p
  obtain ⟨h, hh, hn⟩ :=
    (GlobalTheory.DefiniteOps.definite_ops R.toRealDat F.lv2 hC.base.lev hC.base.fam hC.base.models).2 i A3.A.μ0
  refine ⟨eigVal R i (A3.fam3.tr3 i p.1), fun x hx => ?_⟩
  have hm := thetaLiftPoint_mem_jointEigenspace_of_part R F hW i p x hx
  intro P d hg hr
  have e1 := eig_of_mem R F hC i _ h hh hn _ hm P d hg hr
  have e2 := hh P hg (Finsupp.single d 1) (R.jV i A3.A.μ0 (F.cr.toL (R.toCx3 F).zs false i A3.A.μ0 x))
  exact e2.symm.trans ((congrArg (R.HV i A3.A.μ0).e e1).trans (map_smul _ _ _))

end GlobalTheory.ZPartEig
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftPointsPartEigenformsCoefficientFieldStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftPoints_part_eigenforms_coefficientField : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (s : ℕ), A3.fam3.Ok3 s → R.WeakCharacterisation F → (R.toCx3 F).H3W F.cr false → ∀ i p, ∃ a, ∀ x, (R.toCx3 F).tC F.cr false i A3.A.μ0 (cpt A3.A.v0.embedding x) ∈ (R.toCx3 F).Wp i p → GlobalTheory.ConjScalar.EigK R.toRealDat i a (F.cr.toL (R.toCx3 F).zs false i A3.A.μ0 x) := by
  first | exact @GlobalTheory.ZPartEig.points_eig | exact GlobalTheory.ZPartEig.points_eig | (intros; apply GlobalTheory.ZPartEig.points_eig <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftWeightComplexPointEqTwist
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjScalarCoord

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (b : Bool)

theorem wC_cpt (j : Fin D.R.m) (v : InfinitePlace D.what₂.LL) (c : Fin ((R.toCx3 F).dW b j) → D.what₂.LL) :
    ((Tw.out (s := twAt D.what₂.embLL v) ((R.toCx3 F).wC b j v (cpt v.embedding c)) :
        R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL v)) : (R.HW j (sgAt D.what₂.embLL v)).H) =
      (((Real.sqrt (RealDat.nP F.lv2 b))⁻¹ : ℝ) : ℂ) •
        (R.FW j).j (sgAt D.what₂.embLL v) (∑ k, c k • R.toRealDat.bL F.lv2 b j k) := by
  have e : ((Tw.out (s := twAt D.what₂.embLL v) ((R.toCx3 F).wC b j v (cpt v.embedding c)) :
        R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL v)) : (R.HW j (sgAt D.what₂.embLL v)).H) =
      ((∑ k, cj (twAt D.what₂.embLL v) (v.embedding (c k)) •
        (⟨R.toRealDat.bC F.lv2 b j _ k, Submodule.subset_span ⟨k, rfl⟩⟩ :
          R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL v)) : R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL v)) :
        (R.HW j (sgAt D.what₂.embLL v)).H) := rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, Submodule.coe_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Submodule.coe_smul, emb_eq D.what₂.embLL v, cj_cj, LinearMap.map_smulₛₗ, smul_comm]
  rfl

theorem sqrt_ne : ((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.2 (RealDat.nP_pos (F := F.lv2) b)).ne'

theorem liftWeight_complexPoint_eq_twist (j : Fin D.R.m) (c : Fin ((R.toCx3 F).dW b j) → D.what₂.LL) :
    (Tw.out (s := twAt D.what₂.embLL A3.A.v0) ((R.toCx3 F).w0C b j (cpt A3.A.v0.embedding c)) : (R.HW j (sg0 D A3.A)).H) =
      (R.FW j).j (sg0 D A3.A) (∑ k, c k • R.toRealDat.bL F.lv2 b j k) := by
  have e : (Tw.out (s := twAt D.what₂.embLL A3.A.v0) ((R.toCx3 F).w0C b j (cpt A3.A.v0.embedding c)) : (R.HW j (sg0 D A3.A)).H) =
      ((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ) • ((Tw.out (s := twAt D.what₂.embLL A3.A.v0)
        ((R.toCx3 F).wC b j A3.A.v0 (cpt A3.A.v0.embedding c)) :
          R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL A3.A.v0)) : (R.HW j (sgAt D.what₂.embLL A3.A.v0)).H) := rfl
  rw [e, wC_cpt, smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ (sqrt_ne F b), one_smul]

theorem inner_wC (j : Fin D.R.m) {v : InfinitePlace D.what₂.LL} (hv : v ≠ A3.A.v0) (c c' : Fin ((R.toCx3 F).dW b j) → D.what₂.LL) :
    ⟪(R.toCx3 F).wC b j v (cpt v.embedding c), (R.toCx3 F).wC b j v (cpt v.embedding c')⟫_ℂ =
      (Nat.card (F.lv2.lvl b).P : ℂ)⁻¹ * ⟪(R.FW j).j v.embedding (∑ k, c k • R.toRealDat.bL F.lv2 b j k),
        (R.FW j).j v.embedding (∑ k, c' k • R.toRealDat.bL F.lv2 b j k)⟫_ℂ := by
  have hs : sgAt D.what₂.embLL v = v.embedding := if_neg (R.hv0 ▸ hv)
  have ht : twAt D.what₂.embLL v = false := if_pos hs.symm
  have e : ⟪(R.toCx3 F).wC b j v (cpt v.embedding c), (R.toCx3 F).wC b j v (cpt v.embedding c')⟫_ℂ =
      cj (twAt D.what₂.embLL v) ⟪((Tw.out (s := twAt D.what₂.embLL v) ((R.toCx3 F).wC b j v (cpt v.embedding c)) :
          R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL v)) : (R.HW j (sgAt D.what₂.embLL v)).H),
        ((Tw.out (s := twAt D.what₂.embLL v) ((R.toCx3 F).wC b j v (cpt v.embedding c')) :
          R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL v)) : (R.HW j (sgAt D.what₂.embLL v)).H)⟫_ℂ := rfl
  rw [e, wC_cpt, wC_cpt, inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul, ← mul_inv,
    Real.mul_self_sqrt (RealDat.nP_pos (F := F.lv2) b).le, hs]
  generalize twAt D.what₂.embLL v = s at ht
  subst ht
  unfold Links.cj
  simp only [RealDat.nP, Bool.cond_false, RingHom.id_apply, Complex.ofReal_inv, Complex.ofReal_natCast]

theorem tC_cpt (cr : Crd A3.fam3.amb3 F.fc) (j : Fin D.R.m) (t : T0)
    (x : Fin ((lv (F.fc (R.toCx3 F).zs) b).dZ j t) → D.what₂.LL) :
    (R.toCx3 F).tC cr b j t (cpt A3.fam3.base3.v0.embedding x) =
      (R.toCx3 F).θ' j t ((R.toCx3 F).jL j t (cr.toL (R.toCx3 F).zs b j t x)) := by
  conv_rhs => rw [← (Pi.basisFun D.what₂.LL _).sum_repr x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [CxData.tC, lin_apply, map_sum, map_smul, LinearMap.map_smulₛₗ, Pi.basisFun_repr, Pi.basisFun_apply, cpt,
    RingHom.id_apply]

theorem liftMat_isRatLift_inner : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3), (R.toCx3 F).H5 F.cr false → (R.toCx3 F).RATth F.cr false → ∀ i, (∀ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R.toRealDat i (cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) (F.cr.toL (R.toCx3 F).zs false i A3.A.μ0 x) (∑ k, (((R.toCx3 F).liftMat F.cr false i A3.A.μ0).mulVec x) k • R.toRealDat.bL F.lv2 false i k)) ∧ ∀ v, v ≠ A3.A.v0 → ∀ x y, ⟪(R.toCx3 F).wC false i v (cpt v.embedding (((R.toCx3 F).liftMat F.cr false i A3.A.μ0).mulVec x)), (R.toCx3 F).wC false i v (cpt v.embedding (((R.toCx3 F).liftMat F.cr false i A3.A.μ0).mulVec y))⟫_ℂ = ((Nat.card F.P0 : ℕ) : ℂ)⁻¹ * ⟪(R.FW i).j v.embedding (∑ k, (((R.toCx3 F).liftMat F.cr false i A3.A.μ0).mulVec x) k • R.toRealDat.bL F.lv2 false i k), (R.FW i).j v.embedding (∑ k, (((R.toCx3 F).liftMat F.cr false i A3.A.μ0).mulVec y) k • R.toRealDat.bL F.lv2 false i k)⟫_ℂ := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hT hR i
  refine ⟨fun x => ?_, fun v hv x y => ?_⟩
  · show (R.FW i).j (sg0 D A3.A) _ = _
    refine (liftWeight_complexPoint_eq_twist R F false i _).symm.trans ?_
    have h1 := ((R.toCx3 F).key_lift F.cr false hT hR i A3.A.μ0 x).trans (tC_cpt R F false F.cr i A3.A.μ0 x)
    exact congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H)) h1
  · rw [inner_wC R F false i hv]
    rfl

end GlobalTheory.ConjScalarCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftScalarIdentityOffFixedPlaceBaseLevel
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalarOff

section SlopeTestRemainingChoices
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem range_adjoint_smul_le' {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E'] (c : ℂ) (f : E →ₗ[ℂ] E') :
    LinearMap.range (LinearMap.adjoint (c • f)) ≤ LinearMap.range (LinearMap.adjoint f) := by
  rintro _ ⟨y, rfl⟩
  rw [RealDat3.adjoint_smul']
  exact ⟨starRingEnd ℂ c • y, by simp⟩

theorem jV_mem_range (R : RealDat3 D A3 Ks) (F : Face3 D A3) (j : Fin D.R.m) (t : T0) :
    ∀ z ∈ (R.toCx3 F).Zl j t, R.jV j t z ∈ LinearMap.range (LinearMap.adjoint (R.thG j t)) := by
  intro z hz
  have hx1 := range_adjoint_smul_le' (R.phs j) (Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG j t)) hz
  exact (GlobalTheory.AdjBlock.mem_range_adjoint_tw (twAt D.what₂.embLL A3.A.v0) (R.thG j t) (R.jV j t z)).1 hx1

end SlopeTestRemainingChoices

theorem galD_base : GlobalTheory.Hk3.HoweUnram → GlobalTheory.LowRow.ConjRatLift5 → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ), A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → GlobalTheory.ConjScalar.ConjScalarAt R.toRealDat → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => (cj (twAt D.what₂.embLL A3.A.v0) (R.phs i))) i) → R.toRealDat.LUnif → ((R.toCx3 F).H5 F.cr false ∧ (R.toCx3 F).RATth F.cr false ∧ (R.toCx3 F).H3W F.cr false ∧ (lv (F.fc (R.toCx3 F).zs) false).Proviso) → (R.toCx3 F).GalD F.cr false := by
  intro hHowe hCRL D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O s hOk hC hEx hCS hψ fw hBar hIo hPins hRow0 hPT hU hfacts
  obtain ⟨h5, hrat, h3w, hprov⟩ := hfacts
  have hcore := GlobalTheory.CoreOfWeak.core_of_weak R F hC hEx
  intro j v hv p
  obtain ⟨a, ha⟩ := GlobalTheory.T.thetaLiftPoints_part_eigenforms_coefficientField R F s hOk hC h3w j p
  have hOne := hPT j hU (hRow0 j)
  have hHerm : Formalism.DivisionValues.IsRatHerm (Formalism.DivisionValues.cmMax D.what₂.LL) ((A3.A.fam.L j A3.A.μ0).HZ (A3.A.fam.lvlA F.P0 F.ψ0) ((R.toCx3 F).Zl j A3.A.μ0))
      ((A3.A.fam.L j A3.A.μ0).XQ (A3.A.fam.lvlA F.P0 F.ψ0) ((R.toCx3 F).Zl j A3.A.μ0)) := hprov j
  have hBH : BlockHyp (A3.A.fam.L j A3.A.μ0) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.v0 s :=
    ⟨hOk.ok2.conj, hOk.ok2.irr, hOk.ok2.lifts j A3.A.μ0⟩
  have hfE := GlobalTheory.QuotRational.fE_mem_cmMax _ (A3.A.fam.lvlA F.P0 F.ψ0) ((R.toCx3 F).Zl j A3.A.μ0) A3.A.v0 s hBH hHerm
  obtain ⟨l, hl⟩ := GlobalTheory.T.rationalLift_readings_scale_classSum_eigenspaces hHowe hCRL T R.toRealDat κ v₀ O F.lv2 _ hcore.1 hψ hCS fw hBar hIo hU hPins j hOne
    (A3.A.fam.lvlA F.P0 F.ψ0) ((R.toCx3 F).Zl j A3.A.μ0) hHerm hfE (jV_mem_range R F j A3.A.μ0) v.embedding a
  have hmaj := (GlobalTheory.Proof.ConjugateTransposeMajorant.majAt_eq_csumAt _ (A3.A.fam.lvlA F.P0 F.ψ0) ((R.toCx3 F).Zl j A3.A.μ0) hHerm hfE).1 v
  have hco := GlobalTheory.ConjScalarCoord.liftMat_isRatLift_inner R F h5 hrat j
  have hS : ∀ x, (R.toCx3 F).tC F.cr false j A3.A.μ0 (cpt A3.A.v0.embedding x) ∈ (R.toCx3 F).Wp j p → ∀ y,
      ⟪(R.toCx3 F).wC false j v (cpt v.embedding (((R.toCx3 F).liftMat F.cr false j A3.A.μ0).mulVec x)),
        (R.toCx3 F).wC false j v (cpt v.embedding (((R.toCx3 F).liftMat F.cr false j A3.A.μ0).mulVec y))⟫_ℂ =
      ((l : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((lv (F.fc (R.toCx3 F).zs) false).XT j A3.A.μ0) v x y := by
    intro x hx y
    have e1 := hco.2 v hv x y
    have e2 := hl x (F.cr.toL (R.toCx3 F).zs false j A3.A.μ0 y) _ _ (ha x hx) (hco.1 x) (hco.1 y)
    have e3 := hmaj x y
    rw [e1, e2]
    erw [e3]
    exact mul_left_comm _ _ _
  intro x hx y
  by_cases hP : R.PartAt F j p v
  · have e : R.lam3 j A3.A.μ0 p v = l := hC.scal.off j p v l hv hP hS
    exact (hS x hx y).trans (congrArg (fun t : ℝ => (t : ℂ) * _) e.symm)
  · have h0 := GlobalTheory.ScalarConjugation.maj_eq_zero _ v x y (by by_contra hn; exact hP ⟨x, hx, hn⟩)
    exact (hS x hx y).trans ((mul_eq_zero_of_right _ h0).trans (mul_eq_zero_of_right _ h0).symm)

end GlobalTheory.ConjScalarOff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftScalarIdentityOffFixedPlaceBaseLevelStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftScalarIdentity_offFixedPlace_baseLevel : GlobalTheory.Hk3.HoweUnram → GlobalTheory.LowRow.ConjRatLift5 → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ), A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → GlobalTheory.ConjScalar.ConjScalarAt R.toRealDat → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => (cj (twAt D.what₂.embLL A3.A.v0) (R.phs i))) i) → R.toRealDat.LUnif → ((R.toCx3 F).H5 F.cr false ∧ (R.toCx3 F).RATth F.cr false ∧ (R.toCx3 F).H3W F.cr false ∧ (lv (F.fc (R.toCx3 F).zs) false).Proviso) → (R.toCx3 F).GalD F.cr false := by
  first | exact @GlobalTheory.ConjScalarOff.galD_base | exact GlobalTheory.ConjScalarOff.galD_base | (intros; apply GlobalTheory.ConjScalarOff.galD_base <;> assumption)
end
