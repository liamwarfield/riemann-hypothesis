module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactStandardMaximal

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneFormMapEqKaehlerDifferentialMap
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hodge.FormBC

theorem subsingleton_of_tensor {R : Type} [CommRing R] {Q : Type} [AddCommGroup Q] [Module R Q] [Module.Finite R Q]
    {J : Type} (B : J → Type) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (hcov : ∀ p : PrimeSpectrum R, ∃ (i : J) (q : PrimeSpectrum (B i)), PrimeSpectrum.comap (algebraMap R (B i)) q = p)
    (h : ∀ i, Subsingleton (B i ⊗[R] Q)) : Subsingleton Q := by
  by_contra hQ
  rw [not_subsingleton_iff_nontrivial] at hQ
  obtain ⟨p, hp⟩ := Module.nonempty_support_of_nontrivial (R := R) (M := Q)
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hp
  obtain ⟨i, q, hq⟩ := hcov p
  have := h i
  let κ := q.asIdeal.ResidueField
  have h1 : Subsingleton (κ ⊗[R] Q) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R (B i) κ κ Q).symm.subsingleton
  have hpq : p.asIdeal = q.asIdeal.comap (algebraMap R (B i)) := by rw [← hq]; rfl
  letI : Algebra p.asIdeal.ResidueField κ :=
    (Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R (B i)) hpq).toAlgebra
  haveI : IsScalarTower R p.asIdeal.ResidueField κ := .of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R (B i) κ]
    exact (Ideal.ResidueField.map_algebraMap p.asIdeal q.asIdeal (algebraMap R (B i)) hpq r).symm
  have h2 : Nontrivial (κ ⊗[p.asIdeal.ResidueField] (p.asIdeal.ResidueField ⊗[R] Q)) :=
    Module.FaithfullyFlat.lTensor_nontrivial _ _ _
  exact not_subsingleton _
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R p.asIdeal.ResidueField κ κ Q).subsingleton

theorem bijective_of_lTensor {R : Type} [CommRing R] {N M : Type} [AddCommGroup N] [Module R N] [AddCommGroup M]
    [Module R M] [Module.Finite R N] [Module.Finite R M] [Module.Projective R M] (T : N →ₗ[R] M)
    {J : Type} (B : J → Type) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (hcov : ∀ p : PrimeSpectrum R, ∃ (i : J) (q : PrimeSpectrum (B i)), PrimeSpectrum.comap (algebraMap R (B i)) q = p)
    (h : ∀ i, Function.Bijective (T.lTensor (B i))) : Function.Bijective T := by
  have hs : Function.Surjective T := by
    have hQ : Subsingleton (M ⧸ LinearMap.range T) := subsingleton_of_tensor B hcov fun i ↦ by
      refine ⟨fun a b ↦ ?_⟩
      have key : ∀ x : B i ⊗[R] (M ⧸ LinearMap.range T), x = 0 := fun x ↦ by
        obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective (B i) (Submodule.mkQ_surjective (LinearMap.range T)) x
        obtain ⟨z, rfl⟩ := (h i).2 y
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, show (LinearMap.range T).mkQ ∘ₗ T = 0 from
          LinearMap.range_mkQ_comp T, LinearMap.lTensor_zero, LinearMap.zero_apply]
      rw [key a, key b]
    exact fun m ↦ LinearMap.mem_range.1 ((Submodule.Quotient.mk_eq_zero (LinearMap.range T)).1 (Subsingleton.elim (Submodule.Quotient.mk m) 0))
  obtain ⟨u, hu⟩ := Module.projective_lifting_property T LinearMap.id hs
  let r : N →ₗ[R] LinearMap.ker T := LinearMap.codRestrict _ (LinearMap.id - u ∘ₗ T) fun x ↦ by
    have := LinearMap.congr_fun hu (T x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp [this]
  have hr : r ∘ₗ (LinearMap.ker T).subtype = LinearMap.id := by
    ext x
    simp [r]
  have hrs : Function.Surjective r := fun x ↦ ⟨x.1, LinearMap.congr_fun hr x⟩
  haveI : Module.Finite R (LinearMap.ker T) := Module.Finite.of_surjective r hrs
  have hK : Subsingleton (LinearMap.ker T) := subsingleton_of_tensor B hcov fun i ↦ by
    have key : ∀ x : B i ⊗[R] LinearMap.ker T, x = 0 := fun x ↦ by
      have e : (LinearMap.ker T).subtype.lTensor (B i) x = 0 := (h i).1 <| by
        rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
          show T ∘ₗ (LinearMap.ker T).subtype = 0 from LinearMap.ext fun x ↦ x.2, LinearMap.lTensor_zero,
          LinearMap.zero_apply]
      have e2 := congrArg (r.lTensor (B i)) e
      rwa [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hr, LinearMap.lTensor_id, LinearMap.id_apply, map_zero] at e2
    exact ⟨fun a b ↦ by rw [key a, key b]⟩
  exact ⟨(injective_iff_map_eq_zero T).2 fun x hx ↦ congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : LinearMap.ker T) 0), hs⟩

theorem exists_grp {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) {X' : Scheme.{0}} (s' : X' ⟶ Sp R')
    (φ : X' ⟶ A.left) (h : IsPullback φ s' A.hom (spMap (algebraMap R R'))) :
    ∃ _ : GrpObj (Over.mk s'), IsAbelianScheme (Over.mk s') ∧ SmoothOfRelativeDimension g s' := by
  have abelian_pull {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'}
      [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left} (hG : IsAbelianScheme G)
      (h : IsGrpPullback G' G f φ) : IsAbelianScheme G' := by
    have comm : IsCommMonObj G' := by
      have := hG.comm
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl,
        ← h.2 T y x (pushPt h.1.w y) (pushPt h.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨comm, MorphismProperty.of_isPullback (P := @Smooth) h.1 hG.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) h.1 hG.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hG.geomConnected⟩
  obtain ⟨C, _, ψ, hψ⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A (spMap (algebraMap R R'))
  let e : C ≅ Over.mk s' := Over.isoMk (hψ.1.isoIsPullback _ _ h) (by simp)
  let _ : GrpObj (Over.mk s') := GrpObj.ofIso e
  have : IsMonHom e.hom := inferInstance
  have hC := abelian_pull hA hψ
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  exact ⟨inferInstance, abelian_pull hC (GlobalTheory.SymExtendDvr.isGrpPullback_of_iso e.symm),
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) h hg⟩

theorem lTensor_bijective_of_isBaseChange {S B N M P : Type} [CommRing S] [CommRing B] [Algebra S B]
    [AddCommGroup N] [Module S N] [AddCommGroup M] [Module S M] [AddCommGroup P] [Module S P] [Module B P]
    [IsScalarTower S B P] (T : N →ₗ[S] M) (ev : M →ₗ[S] P) (h₁ : IsBaseChange B ev)
    (h₂ : IsBaseChange B (ev ∘ₗ T)) : Function.Bijective (T.lTensor B) := by
  have e : ∀ x, h₁.equiv (T.lTensor B x) = h₂.equiv x := fun x ↦ by
    induction x with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul b n => simp [IsBaseChange.equiv_tmul]
  refine (Function.Bijective.of_comp_iff' h₁.equiv.bijective _).1 ?_
  have e' : (h₁.equiv ∘ T.lTensor B) = h₂.equiv := funext e
  rw [e']
  exact h₂.equiv.bijective

theorem oneFormMap_eq_kaehlerDifferential_map {R R' B B' : Type} [CommRing R] [CommRing R'] [CommRing B] [CommRing B'] [Algebra R R'] [Algebra R B]
    [Algebra R' B'] [Algebra B B'] [Algebra R B'] [IsScalarTower R R' B'] [IsScalarTower R B B']
    (hα : SemiHom (algebraMap R R') (algebraMap B B')) (x : Ω[B⁄R]) :
    hα.m1 x = KaehlerDifferential.map R R' B B' x := by
  induction x using ind1 with
  | h b c =>
    rw [SemiHom.oneFormMap_smul_semilinear, SemiHom.m1_D, map_smul, KaehlerDifferential.map_D, algebraMap_smul]
  | h0 => simp
  | ha x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem isBaseChange_of_isPushout {R R' B B' W : Type} [CommRing R] [CommRing R'] [CommRing B] [CommRing B']
    [Algebra R R'] [Algebra R B] [Algebra R' B'] [Algebra B B'] [Algebra R B'] [IsScalarTower R R' B']
    [IsScalarTower R B B'] [Algebra.IsPushout R R' B B'] [AddCommGroup W] [Module R W] (ev : W →ₗ[R] Ω[B⁄R])
    (hev : IsBaseChange B ev) (hα : SemiHom (algebraMap R R') (algebraMap B B'))
    (u : R' ⊗[R] W →ₗ[R'] Ω[B'⁄R']) (hu : ∀ c, u (1 ⊗ₜ c) = hα.m1 (ev c)) : IsBaseChange B' u := by
  have h₁ : IsBaseChange B' (KaehlerDifferential.map R R' B B') :=
    IsBaseChange.of_equiv (KaehlerDifferential.tensorKaehlerEquiv R R' B B') fun x ↦ by
      have hx : x ∈ Submodule.span B (Set.range (KaehlerDifferential.D R B)) :=
        (KaehlerDifferential.span_range_derivation R B).ge Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        simp
      | zero => simp
      | add x y _ _ hx hy => rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), hx, hy]
      | smul a x _ hx =>
        rw [TensorProduct.tmul_smul, ← algebraMap_smul B', map_smul, hx, map_smul, algebraMap_smul]
  have h₂ := IsBaseChange.comp hev h₁
  refine IsBaseChange.of_comp (TensorProduct.isBaseChange R W R') ?_
  convert h₂ using 1
  refine LinearMap.ext fun c ↦ ?_
  exact (hu c).trans (oneFormMap_eq_kaehlerDifferential_map hα _)

section Main

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'}
  {φ : X' ⟶ X}

def pairOf (h : IsPullback φ s' s (spMap (algebraMap R R'))) (U : X.affineOpens) : Pair φ :=
  ⟨(⟨φ ⁻¹ᵁ U.1, GlobalTheory.AbLaw.isAffineOpen_preimage_of_isPullback h U.2⟩, U), le_rfl⟩

theorem isBaseChange_at (h : IsPullback φ s' s (spMap (algebraMap R R'))) (hP : Par (OAff s)) (U : X.affineOpens)
    (u : R' ⊗[R] GlobForm s →ₗ[R'] Ω[Sec s' (φ ⁻¹ᵁ U.1)⁄R'])
    (hu : ∀ c : GlobForm s, u (1 ⊗ₜ c) = (semiHom_secPull h.w (pairOf h U)).m1 (c.1 (op U))) :
    IsBaseChange (Sec s' (φ ⁻¹ᵁ U.1)) u := by
  letI : Algebra (Sec s U.1) (Sec s' (φ ⁻¹ᵁ U.1)) := (CechDR.secPull s s' (pairOf h U)).toAlgebra
  letI : Algebra R (Sec s' (φ ⁻¹ᵁ U.1)) :=
    ((algebraMap R' (Sec s' (φ ⁻¹ᵁ U.1))).comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' (Sec s' (φ ⁻¹ᵁ U.1)) := .of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower R (Sec s U.1) (Sec s' (φ ⁻¹ᵁ U.1)) :=
    .of_algebraMap_eq fun r ↦ ((semiHom_secPull h.w (pairOf h U)).map_algebraMap r).symm
  haveI : Algebra.IsPushout R R' (Sec s U.1) (Sec s' (φ ⁻¹ᵁ U.1)) :=
    CommRingCat.isPushout_iff_isPushout.mp (GlobalTheory.AbLaw.isPushout_cst h U.2 rfl)
  exact isBaseChange_of_isPushout (B := Sec s U.1) (B' := Sec s' (φ ⁻¹ᵁ U.1)) (evForm (OAff s) (op U)) (hP (op U))
    (semiHom_secPull h.w (pairOf h U)) u hu

theorem exists_prime (h : IsPullback φ s' s (spMap (algebraMap R R'))) (e : Sp R' ⟶ X') (he : e ≫ s' = 𝟙 _)
    (p : PrimeSpectrum R') : ∃ (U : X.affineOpens) (q : PrimeSpectrum (Sec s' (φ ⁻¹ᵁ U.1))),
      PrimeSpectrum.comap (algebraMap R' (Sec s' (φ ⁻¹ᵁ U.1))) q = p := by
  let y : Sp R' := p
  obtain ⟨V, hV, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := φ (e y)) trivial
  have hU' := GlobalTheory.AbLaw.isAffineOpen_preimage_of_isPullback h hV
  refine ⟨⟨V, hV⟩, hU'.primeIdealOf ⟨e y, hx⟩, ?_⟩
  have e₁ := hU'.fromSpec_primeIdealOf ⟨e y, hx⟩
  have e₂ := affPt_w s' ⟨φ ⁻¹ᵁ V, hU'⟩
  have e₃ := congrArg (fun f ↦ f (hU'.primeIdealOf ⟨e y, hx⟩)) e₂
  have e₄ : s' (e y) = y := by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  have e₅ : s' (hU'.fromSpec (hU'.primeIdealOf ⟨e y, hx⟩)) =
      spMap (algebraMap R' (Sec s' (φ ⁻¹ᵁ V))) (hU'.primeIdealOf ⟨e y, hx⟩) :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans e₃
  exact ((congrArg (fun z ↦ s' z) e₁).symm.trans e₅).symm.trans e₄

end Main

theorem formBC : SteinSt → ParSt → FormBCSt := by
  intro _ hPar R _ A _ g hA hg R' _ _ X' s' φ h
  obtain ⟨_, hA', hg'⟩ := exists_grp A g hA hg s' φ h
  obtain ⟨hP, hV⟩ := hPar R A g hA hg
  obtain ⟨hP', hV'⟩ := hPar R' (Over.mk s') g hA' hg'
  replace hP' : Par (OAff s') := hP'
  replace hV' : VB R' (GlobForm s') g := hV'
  obtain ⟨f₁, f₂, -⟩ := hV'
  obtain ⟨f₃, -, -⟩ := hV
  let _ : Module R (GlobForm s') := Module.compHom _ (algebraMap R R')
  have : IsScalarTower R R' (GlobForm s') := .of_algebraMap_smul fun _ _ ↦ rfl
  let T : R' ⊗[R] GlobForm A.hom →ₗ[R'] GlobForm s' := LinearMap.liftBaseChange R'
    { toFun := pullForm h.w
      map_add' := map_add _
      map_smul' := (pullForm h.w).map_smulₛₗ }
  have hT : ∀ c : GlobForm A.hom, T (1 ⊗ₜ c) = pullForm h.w c := fun c ↦ by simp [T]
  let e : Sp R' ⟶ X' := (η[Over.mk s'] : 𝟙_ (Over (Sp R')) ⟶ Over.mk s').left
  have he : e ≫ s' = 𝟙 _ := Over.w (η[Over.mk s'] : 𝟙_ (Over (Sp R')) ⟶ Over.mk s')
  have hb : Function.Bijective T :=
    bijective_of_lTensor T (fun U : A.left.affineOpens ↦ Sec s' (φ ⁻¹ᵁ U.1)) (exists_prime h e he) fun U ↦ ?_
  · exact ⟨LinearEquiv.ofBijective T hb, fun c ↦ by
      have : LinearEquiv.ofBijective T hb (1 ⊗ₜ c) = pullForm h.w c := hT c
      rw [this]
      exact isPullForm_pullForm h.w c⟩
  · refine lTensor_bijective_of_isBaseChange T (evForm (OAff s') (op ⟨φ ⁻¹ᵁ U.1, GlobalTheory.AbLaw.isAffineOpen_preimage_of_isPullback h U.2⟩)) (hP' _) ?_
    refine isBaseChange_at h hP U _ fun c ↦ ?_
    have k := isPullForm_iff.1 (isPullForm_pullForm h.w c) (pairOf h U)
    exact (congrArg (fun z : GlobForm s' ↦ z.1 (op (pairOf h U).1.1)) (hT c)).trans k.symm

end GlobalTheory.CompanionTheory.Hodge.FormBC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaOperatorEqCasimirSum
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaOperatorEqCasimirSum
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.HCRep.TraceCas

open AutomorphicForm GlobalTheory.CompanionTheory.ArchSmooth GlobalTheory.CompanionTheory.HCRep

theorem sum_sq_eq {L A ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [LieRing L] [LieAlgebra ℝ L]
    [Ring A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    (B : LinearMap.BilinForm ℝ L) (hs : ∀ X Y, B X Y = B Y X) (l : L →ₗ[ℝ] A)
    (b : Module.Basis ι ℝ L) (ε : ι → ℝ) (hε : ∀ i, ε i * ε i = 1)
    (horth : ∀ i j, B (b i) (b j) = if i = j then ε i else 0)
    (c c' : κ → L) (hc : ∀ Y, Y = ∑ k, B (c' k) Y • c k) :
    ∑ i, ε i • (l (b i) * l (b i)) = ∑ k, l (c k) * l (c' k) := by
  have h1 : ∀ i, l (b i) = ∑ k, B (c' k) (b i) • l (c k) := fun i => by
    conv_lhs => rw [hc (b i)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  have h2 : ∀ k, l (c' k) = ∑ i, (ε i * B (b i) (c' k)) • l (b i) := fun k => by
    conv_lhs => rw [eq_sum_of_orthogonal hε horth (c' k)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  calc ∑ i, ε i • (l (b i) * l (b i))
      = ∑ i, ε i • ((∑ k, B (c' k) (b i) • l (c k)) * l (b i)) :=
        Finset.sum_congr rfl fun i _ => by rw [← h1 i]
    _ = ∑ k, l (c k) * ∑ i, (ε i * B (b i) (c' k)) • l (b i) := by
        simp only [Finset.sum_mul, Finset.mul_sum, Finset.smul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
        rw [hs (c' k) (b i)]
    _ = ∑ k, l (c k) * l (c' k) := Finset.sum_congr rfl fun k _ => by rw [← h2 k]

theorem half_sum {A : Type*} [Ring A] [Algebra ℂ A] (e₁ f₁ e₂ f₂ : A) :
    (2 : ℂ) • (((1 / 2 : ℂ) • (e₁ - Complex.I • f₁)) * ((1 / 2 : ℂ) • (e₂ - Complex.I • f₂)) +
      ((1 / 2 : ℂ) • (e₁ + Complex.I • f₁)) * ((1 / 2 : ℂ) • (e₂ + Complex.I • f₂))) =
      e₁ * e₂ - f₁ * f₂ := by
  simp only [smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, add_mul, mul_add, smul_sub, smul_add, smul_smul]
  match_scalars <;> ring_nf <;> simp

theorem mul_neg_add {A : Type*} [Ring A] (x y z t : A) : x * -y + z * t = z * t - x * y := by
  rw [mul_neg]
  abel

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

open Classical in
theorem atEmb_embedding_apply (w v : InfinitePlace E) (z : ℂ) :
    atEmb w.embedding z v = if v = w then z else 0 := by
  classical
  unfold atEmb
  rw [InfinitePlace.mk_embedding, if_pos rfl, Pi.single_apply]

theorem atEmb_neg (τ : E →+* ℂ) (z : ℂ) : atEmb τ (-z) = -atEmb τ z := by
  rw [atEmb_eq τ (-z), atEmb_eq τ z]
  simp only [Complex.neg_re, Complex.neg_im, neg_smul]
  abel

theorem place_formula (τ : E →+* ℂ) :
    (2 : ℂ) • (Formalism.REAL.Cas (Eop (a := a) τ) + Formalism.REAL.Cas (Eop (a := a) (ComplexEmbedding.conjugate τ))) =
      ∑ i, ∑ j, (lieS E a i j (atEmb τ 1) * lieS E a j i (atEmb τ 1) -
        lieS E a i j (atEmb τ Complex.I) * lieS E a j i (atEmb τ Complex.I)) := by
  have hc : ∀ i j : Fin a, Eop (a := a) (ComplexEmbedding.conjugate τ) i j =
      (1 / 2 : ℂ) • (lieS E a i j (atEmb τ 1) + Complex.I • lieS E a i j (atEmb τ Complex.I)) := by
    intro i j
    simp only [Eop, atEmb_conj, map_one, Complex.conj_I, atEmb_neg, map_neg, smul_neg, sub_neg_eq_add]
  simp only [Formalism.REAL.Cas, hc, ← Finset.sum_add_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact half_sum (A := Module.End ℂ (Sm E a)) (lieS E a i j (atEmb τ 1)) (lieS E a i j (atEmb τ Complex.I))
    (lieS E a j i (atEmb τ 1)) (lieS E a j i (atEmb τ Complex.I))

def cInv (z : Cinf E) : mixedEmbedding.mixedSpace E := (0, fun v => z v.1)

theorem cMap_cInv (z : Cinf E) : cMap E (cInv z) = z := rfl

theorem cInv_cMap (x : mixedEmbedding.mixedSpace E) : cInv (cMap E x) = x := by
  refine Prod.ext (funext fun v => ?_) rfl
  exact absurd (IsTotallyComplex.isComplex v.1) (InfinitePlace.not_isComplex_iff_isReal.2 v.2)

theorem mMap_injective : Function.Injective (mMap E a) := by
  intro X Y h
  funext p q
  have h' : cMap E ((X : Matrix (Fin a) (Fin a) (mixedEmbedding.mixedSpace E)) p q) =
      cMap E ((Y : Matrix (Fin a) (Fin a) (mixedEmbedding.mixedSpace E)) p q) := congrFun (congrFun h p) q
  have := congrArg cInv h'
  rwa [cInv_cMap, cInv_cMap] at this

def Mt (i j : Fin a) (x : Cinf E) : (isExpLieAlgebra E a).lieSubalgebra :=
  ⟨(Matrix.single i j (cInv x) : Matrix (Fin a) (Fin a) (mixedEmbedding.mixedSpace E)), mem_lie _⟩

def coordL : (isExpLieAlgebra E a).lieSubalgebra →ₗ[ℝ] Lie E a where
  toFun X := mMap E a (X : ArchMatrix E a)
  map_add' X Y := map_add (mMap E a) (X : ArchMatrix E a) (Y : ArchMatrix E a)
  map_smul' r X := map_smul (mMap E a) r (X : ArchMatrix E a)

theorem coordL_Mt (i j : Fin a) (x : Cinf E) : coordL (Mt i j x) = toL (Matrix.single i j x) := by
  funext p q
  change cMap E (Matrix.single i j (cInv x) p q) = Matrix.single i j x p q
  simp only [Matrix.single_apply]
  split_ifs
  · exact cMap_cInv x
  · exact map_zero _

def liBL : (isExpLieAlgebra E a).lieSubalgebra →ₗ[ℝ] Module.End ℂ (Sm E a) := (lie E a).comp coordL

theorem liBL_apply (X : (isExpLieAlgebra E a).lieSubalgebra) : liBL X = liB X := rfl

theorem liBL_Mt (i j : Fin a) (x : Cinf E) : liBL (Mt i j x) = lieS E a i j x := by
  rw [lieS_apply]
  change lie E a (coordL (Mt i j x)) = _
  rw [coordL_Mt]

theorem trace_Mt (i j : Fin a) (x : Cinf E) (Y : (isExpLieAlgebra E a).lieSubalgebra) :
    archTraceForm E a (Mt j i x) Y = ∑ w, (x w * coordL Y i j w).re := by
  have h : Matrix.trace (mat ((Mt j i x : (isExpLieAlgebra E a).lieSubalgebra) : ArchMatrix E a) *
      mat (Y : ArchMatrix E a)) = cInv x * mat (Y : ArchMatrix E a) i j := by
    change Matrix.trace (Matrix.single j i (cInv x) * mat (Y : ArchMatrix E a)) = _
    rw [Matrix.trace, Finset.sum_eq_single j]
    · simp [Matrix.diag, Matrix.single_mul_apply_same]
    · intro c _ hc
      exact Matrix.single_mul_apply_of_ne _ _ _ _ _ hc _
    · simp
  rw [archTraceForm_apply, h, mixedTraceL_apply]
  simp only [Prod.fst_mul, Pi.mul_apply, cInv, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, Prod.snd_mul]
  refine Finset.sum_bij (fun v _ => v.1) ?_ ?_ ?_ ?_
  · intro _ _
    exact Finset.mem_univ _
  · intro _ _ _ _ h
    exact Subtype.ext h
  · intro w _
    exact ⟨⟨w, IsTotallyComplex.isComplex w⟩, by simp, rfl⟩
  · intro v _
    rfl

open Classical in
theorem toL_single_atEmb (i j p q : Fin a) (w v : InfinitePlace E) (z : ℂ) :
    toL (Matrix.single i j (atEmb w.embedding z)) p q v = if (w, i, j) = (v, p, q) then z else 0 := by
  change Matrix.single i j (atEmb w.embedding z) p q v = _
  simp only [Matrix.single_apply, Prod.mk.injEq]
  by_cases h1 : i = p <;> by_cases h2 : j = q <;> by_cases h3 : w = v <;>
    simp [h1, h2, h3, atEmb_embedding_apply, eq_comm]

def cc : (InfinitePlace E × Fin a × Fin a) × Bool → (isExpLieAlgebra E a).lieSubalgebra
  | ((w, i, j), false) => Mt i j (atEmb w.embedding 1)
  | ((w, i, j), true) => Mt i j (atEmb w.embedding Complex.I)

def cc' : (InfinitePlace E × Fin a × Fin a) × Bool → (isExpLieAlgebra E a).lieSubalgebra
  | ((w, i, j), false) => Mt j i (atEmb w.embedding 1)
  | ((w, i, j), true) => -Mt j i (atEmb w.embedding Complex.I)

theorem trace_cc'_false (w : InfinitePlace E) (i j : Fin a) (Y : (isExpLieAlgebra E a).lieSubalgebra) :
    archTraceForm E a (cc' ((w, i, j), false)) Y = (coordL Y i j w).re := by
  classical
  change archTraceForm E a (Mt j i (atEmb w.embedding 1)) Y = _
  rw [trace_Mt]
  simp [atEmb_embedding_apply, apply_ite Complex.re]

theorem trace_cc'_true (w : InfinitePlace E) (i j : Fin a) (Y : (isExpLieAlgebra E a).lieSubalgebra) :
    archTraceForm E a (cc' ((w, i, j), true)) Y = (coordL Y i j w).im := by
  classical
  change archTraceForm E a (-Mt j i (atEmb w.embedding Complex.I)) Y = _
  rw [map_neg, LinearMap.neg_apply, trace_Mt]
  simp [atEmb_embedding_apply, apply_ite Complex.re]

theorem expansion (Y : (isExpLieAlgebra E a).lieSubalgebra) :
    Y = ∑ k, archTraceForm E a (cc' k) Y • cc k := by
  classical
  apply Subtype.ext
  apply mMap_injective
  change coordL Y = coordL (∑ k, archTraceForm E a (cc' k) Y • cc k)
  have term : ∀ (p q : Fin a) (v : InfinitePlace E) (t : InfinitePlace E × Fin a × Fin a),
      (∑ b, coordL (archTraceForm E a (cc' (t, b)) Y • cc (t, b))) p q v =
        if t = (v, p, q) then coordL Y p q v else 0 := by
    rintro p q v ⟨w, i, j⟩
    rw [Fintype.sum_bool, map_smul, map_smul, trace_cc'_true, trace_cc'_false]
    change (((coordL Y i j w).im • coordL (Mt i j (atEmb w.embedding Complex.I)) +
      (coordL Y i j w).re • coordL (Mt i j (atEmb w.embedding 1))) p q v) = _
    rw [coordL_Mt, coordL_Mt]
    simp only [Pi.add_apply, Pi.smul_apply, toL_single_atEmb]
    split_ifs with h
    · obtain ⟨rfl, rfl, rfl⟩ : w = v ∧ i = p ∧ j = q := by simpa using h
      apply Complex.ext <;> simp
    · simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Fintype.sum_prod_type]
  funext p q v
  let ev : Lie E a →+ ℂ := ⟨⟨fun X => X p q v, rfl⟩, fun _ _ => rfl⟩
  change ev (coordL Y) = ev (∑ t, ∑ b, coordL (archTraceForm E a (cc' (t, b)) Y • cc (t, b)))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  change _ = ∑ t, (∑ b, coordL (archTraceForm E a (cc' (t, b)) Y • cc (t, b))) p q v
  simp only [term]
  simp [ev]

theorem omegaOp_eq_two_cas (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a d : ℕ)
    (b : Module.Basis (Fin d) ℝ (AutomorphicForm.isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (horth : ∀ i j, AutomorphicForm.archTraceForm E a (b i) (b j) = if i = j then ε i else 0) :
    GlobalTheory.CompanionTheory.HCRep.omegaOp (⇑b) ε = (2 : ℂ) • ∑ w : InfinitePlace E,
      (Formalism.REAL.Cas (Eop (a := a) w.embedding) +
        Formalism.REAL.Cas (Eop (a := a) (ComplexEmbedding.conjugate w.embedding))) := by
  have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with e | e <;> rw [e] <;> norm_num
  have key := sum_sq_eq (A := Module.End ℂ (Sm E a)) (archTraceForm E a) archTraceForm_symm (liBL (E := E) (a := a)) b ε hε2 horth cc cc' expansion
  have hL : omegaOp (⇑b) ε = ∑ i, ε i • (liBL (b i) * liBL (b i)) := by
    unfold omegaOp
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [liBL_apply]
    ext φ
    simp
  rw [hL, key, Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.smul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [place_formula, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  change liBL (Mt i j (atEmb w.embedding Complex.I)) * liBL (-Mt j i (atEmb w.embedding Complex.I)) +
    liBL (Mt i j (atEmb w.embedding 1)) * liBL (Mt j i (atEmb w.embedding 1)) = _
  rw [map_neg, liBL_Mt, liBL_Mt, liBL_Mt, liBL_Mt]
  exact mul_neg_add (A := Module.End ℂ (Sm E a)) _ _ _ _

end GlobalTheory.CompanionTheory.HCRep.TraceCas

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaOperatorEqCasimirSumStatement
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.omega_operator_eq_casimir_sum : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a d : ℕ)
    (b : Module.Basis (Fin d) ℝ (AutomorphicForm.isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ),
    (∀ i, ε i = 1 ∨ ε i = -1) →
    (∀ i j, AutomorphicForm.archTraceForm E a (b i) (b j) = if i = j then ε i else 0) →
    GlobalTheory.CompanionTheory.HCRep.omegaOp (⇑b) ε = (2 : ℂ) • ∑ w : InfinitePlace E,
      (Formalism.REAL.Cas (Eop (a := a) w.embedding) +
        Formalism.REAL.Cas (Eop (a := a) (ComplexEmbedding.conjugate w.embedding))) := by
  first | exact @GlobalTheory.CompanionTheory.HCRep.TraceCas.omegaOp_eq_two_cas | exact GlobalTheory.CompanionTheory.HCRep.TraceCas.omegaOp_eq_two_cas | (intros; apply GlobalTheory.CompanionTheory.HCRep.TraceCas.omegaOp_eq_two_cas <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardCompactEntriesIntegral
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardCompactEntriesIntegral
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

noncomputable section

namespace GlobalTheory.CompanionTheory.GodementH.StdInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem compFin_finOne_smul' (v : HeightOneSpectrum (𝓞 F)) (z : AE F E) :
    compFin F E v (finOne F • z) = compFin F E v z := by
  have h1 : GlobalTheory.AdelicU.evFin F v (GlobalTheory.ThK.Dbl.finOne F) = 1 := by
    simp only [GlobalTheory.AdelicU.evFin, GlobalTheory.ThK.Dbl.finOne, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA, LinearMap.inr_apply]
    change (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = 1
    exact map_one _
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x e =>
    rw [TensorProduct.smul_tmul']
    simp [GlobalTheory.AdelicU.compFin, h1]
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy]

theorem absFin_compFin_le_one {z : AE F E} (hz : z ∈ intHat F E) (v : HeightOneSpectrum (𝓞 F)) :
    absFin F v (compFin F E v z) ≤ 1 := by
  let S : AddSubgroup (AE F E) :=
    { carrier := {z | GlobalTheory.AdelicU.absFin F v (GlobalTheory.AdelicU.compFin F E v z) ≤ 1}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq] at hx hy ⊢
        rw [show GlobalTheory.AdelicU.compFin F E v (x + y) = GlobalTheory.AdelicU.compFin F E v x + GlobalTheory.AdelicU.compFin F E v y from map_add _ _ _]
        exact (GlobalTheory.AdelicU.absFin_add_le F v _ _).trans (max_le hx hy)
      zero_mem' := by
        simp only [Set.mem_ofPred_eq]
        rw [show GlobalTheory.AdelicU.compFin F E v 0 = 0 from map_zero _, GlobalTheory.AdelicU.absFin_zero]
        exact zero_le_one
      neg_mem' := fun {x} hx => by
        simp only [Set.mem_ofPred_eq] at hx ⊢
        rw [show GlobalTheory.AdelicU.compFin F E v (-x) = -GlobalTheory.AdelicU.compFin F E v x from map_neg _ _, GlobalTheory.AdelicU.absFin_neg]
        exact hx }
  have hle : intHat F E ≤ S := by
    rw [GlobalTheory.ThK.Dbl.intHat, AddSubgroup.closure_le]
    rintro z ⟨a, -, ha, o, rfl⟩
    show GlobalTheory.AdelicU.absFin F v (GlobalTheory.AdelicU.compFin F E v _) ≤ 1
    have h2 : GlobalTheory.AdelicU.compFin F E v (a • (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) (o : E)) =
        (GlobalTheory.AdelicU.evFin F v a) ⊗ₜ[F] (o : E) := by
      simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, GlobalTheory.AdelicU.compFin, TensorProduct.smul_tmul']
    rw [h2]
    refine (GlobalTheory.AdelicU.absFin_tmul_le F v _ o).trans ?_
    exact nnnorm_le_one_iff_mem.mpr (ha v)
  exact hle hz

theorem absFin_inFrame_le_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n) (B : Base F E) (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)),
    IsStdK (σ := σ) (Y := Y) B b K → ∀ k ∈ K, ∀ (v : Pl (F := F)) (i j : Fin n ⊕ Fin n), absFin F v (compFin F E v (inFrame b k i j)) ≤ 1 := by
  intro F E _ _ _ _ _ σ n Y B b K hK k hk v i j
  have h : GlobalTheory.ThK.Dbl.finOne F • GlobalTheory.ThK.Dbl.inFrame b k i j ∈ GlobalTheory.ThK.Dbl.intHat F E :=
    ((hK k).1 hk).2 k (by simp) i j
  have h' := absFin_compFin_le_one h v
  rwa [compFin_finOne_smul'] at h'

end GlobalTheory.CompanionTheory.GodementH.StdInt

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardCompactEntriesIntegralStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_compact_entries_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n) (B : Base F E) (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)),
    IsStdK (σ := σ) (Y := Y) B b K → ∀ k ∈ K, ∀ (v : Pl (F := F)) (i j : Fin n ⊕ Fin n), absFin F v (compFin F E v (inFrame b k i j)) ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.StdInt.absFin_inFrame_le_one | exact GlobalTheory.CompanionTheory.GodementH.StdInt.absFin_inFrame_le_one | (intros; apply GlobalTheory.CompanionTheory.GodementH.StdInt.absFin_inFrame_le_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PluckerMinorsDetermineColumnSpace
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PluckerMinorsDetermineColumnSpace
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

noncomputable section

namespace GlobalTheory.CompanionTheory.GodementH.Cramer

open Matrix

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

theorem mul_adjugate_submatrix (M : Matrix ι (Fin n) K) (f₀ : Fin n → ι) (i : ι) (j : Fin n) :
    (M * adjugate (M.submatrix f₀ id)) i j = mnr M (Function.update f₀ j i) := by
  have h1 : (M * adjugate (M.submatrix f₀ id)) i j = cramer (M.submatrix f₀ id)ᵀ (M i) j := by
    rw [cramer_eq_adjugate_mulVec, ← adjugate_transpose]
    simp [mulVec, dotProduct, Matrix.mul_apply, transpose_apply, mul_comm]
  rw [h1, cramer_transpose_apply]
  unfold mnr
  congr 1
  ext a b
  by_cases hab : a = j
  · subst hab; simp
  · simp [updateRow_apply, hab, Function.update_apply]

theorem eq_mul_of_minor_ratio (M M' : Matrix ι (Fin n) K) (f₀ f₀' : Fin n → ι)
    (h0 : mnr M f₀ ≠ 0) (h0' : mnr M' f₀' ≠ 0)
    (h : ∀ f, mnr M f / mnr M f₀ = mnr M' f / mnr M' f₀') : ∃ c : GL (Fin n) K, M' = M * c.1 := by
  set c := mnr M' f₀' / mnr M f₀ with hcdef
  have hc : ∀ f, mnr M' f = c * mnr M f := fun f => by
    calc mnr M' f = mnr M' f / mnr M' f₀' * mnr M' f₀' := by rw [div_mul_cancel₀ _ h0']
      _ = mnr M f / mnr M f₀ * mnr M' f₀' := by rw [h f]
      _ = c * mnr M f := by rw [hcdef]; ring
  have hc0 : c ≠ 0 := div_ne_zero h0' h0
  set A := M.submatrix f₀ id with hA
  set A' := M'.submatrix f₀ id with hA'
  have hdA : A.det = mnr M f₀ := rfl
  have hdA' : A'.det = c * A.det := hc f₀
  have hA0 : A.det ≠ 0 := h0
  have hdA'0 : A'.det ≠ 0 := by rw [hdA']; exact mul_ne_zero hc0 h0
  have key : M' * adjugate A' = c • (M * adjugate A) := by
    ext i j
    rw [mul_adjugate_submatrix, Matrix.smul_apply, mul_adjugate_submatrix, hc, smul_eq_mul]
  have e1 : M' * adjugate A' * A' = A'.det • M' := by
    rw [Matrix.mul_assoc, adjugate_mul, Matrix.mul_smul, Matrix.mul_one]
  have hP : (A⁻¹ * A').det ≠ 0 := by
    rw [det_mul, det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero (inv_ne_zero h0) hdA'0
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (A⁻¹ * A') hP, ?_⟩
  show M' = M * (A⁻¹ * A')
  rw [inv_def, Ring.inverse_eq_inv']
  have e2 : M * ((A.det)⁻¹ • adjugate A * A') = ((A.det)⁻¹ * c⁻¹) • (M' * adjugate A' * A') := by
    rw [key, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel_right₀ hc0, Matrix.mul_assoc]
  rw [e2, e1, smul_smul, hdA']
  rw [show A.det⁻¹ * c⁻¹ * (c * A.det) = 1 by field_simp, one_smul]

end GlobalTheory.CompanionTheory.GodementH.Cramer

theorem GlobalTheory.CompanionTheory.GodementH.Cramer.main : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (M M' : Matrix ι (Fin n) K) (f₀ f₀' : Fin n → ι),
    mnr M f₀ ≠ 0 → mnr M' f₀' ≠ 0 → (∀ f, mnr M f / mnr M f₀ = mnr M' f / mnr M' f₀') → ∃ c : GL (Fin n) K, M' = M * c.1 := by
  intro K _ ι _ _ n M M' f₀ f₀' h0 h0' h
  exact GlobalTheory.CompanionTheory.GodementH.Cramer.eq_mul_of_minor_ratio M M' f₀ f₀' h0 h0' h
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PluckerMinorsDetermineColumnSpaceStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plucker_minors_determine_column_space : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (M M' : Matrix ι (Fin n) K) (f₀ f₀' : Fin n → ι),
    mnr M f₀ ≠ 0 → mnr M' f₀' ≠ 0 → (∀ f, mnr M f / mnr M f₀ = mnr M' f / mnr M' f₀') → ∃ c : GL (Fin n) K, M' = M * c.1 := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.Cramer.main | exact GlobalTheory.CompanionTheory.GodementH.Cramer.main | (intros; apply GlobalTheory.CompanionTheory.GodementH.Cramer.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticIntegralCoefficientsBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticIntegralCoefficientsBound
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

namespace GlobalTheory.CompanionTheory.GodementH

theorem trace_norm_local_sizes : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ x : E, ∃ y₁ y₂ : F,
    x ^ 2 - algebraMap F E y₁ * x + algebraMap F E y₂ = 0 ∧ ∀ (v : Pl (F := F)) (τ : E →ₐ[F] FvBar F v),
      ‖algebraMap F (Fv F v) y₁‖₊ ≤ max (absBar F v (τ x)) (absBar F v (τ (σ x))) ∧
      ‖algebraMap F (Fv F v) y₂‖₊ = absBar F v (τ x) * absBar F v (τ (σ x)) := by
  intro F E _ _ _ _ _ σ hCM x
  obtain ⟨_, hEc, hfin2, hconj⟩ := hCM
  obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hσσ : ∀ z, σ (σ z) = z := fun z => τ0.injective (by rw [hconj, hconj, star_star])
  have hσne : ∃ w, σ w ≠ w := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have hreal : NumberField.ComplexEmbedding.IsReal τ0 := by
      rw [NumberField.ComplexEmbedding.isReal_iff]
      refine RingHom.ext fun w => ?_
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
      have h1 := hconj τ0 w
      rw [hcon w] at h1
      exact h1.symm
    exact InfinitePlace.not_isReal_iff_isComplex.2 (hEc.isComplex (InfinitePlace.mk τ0)) ⟨τ0, hreal, rfl⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have hfix : ∀ z : E, σ z = z → ∃ y : F, algebraMap F E y = z := by
    intro z hz
    have hSle : Submodule.span F {(1 : E)} ≤ LinearMap.ker (σ.toLinearMap - LinearMap.id) := by
      rw [Submodule.span_le, Set.singleton_subset_iff]
      simp
    have hker : LinearMap.ker (σ.toLinearMap - LinearMap.id) ≠ ⊤ := by
      intro htop
      obtain ⟨w, hw⟩ := hσne
      have hw' : w ∈ LinearMap.ker (σ.toLinearMap - LinearMap.id) := htop ▸ Submodule.mem_top
      rw [LinearMap.mem_ker] at hw'
      exact hw (sub_eq_zero.1 hw')
    have h1 : Module.finrank F (Submodule.span F {(1 : E)}) = 1 := finrank_span_singleton one_ne_zero
    have hlt := Submodule.finrank_lt hker
    have hge := Submodule.finrank_mono hSle
    have heq := Submodule.eq_of_le_of_finrank_eq hSle (by omega)
    have hzk : z ∈ LinearMap.ker (σ.toLinearMap - LinearMap.id) := by
      rw [LinearMap.mem_ker]
      simp [hz]
    rw [← heq] at hzk
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hzk
    exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩
  obtain ⟨y₁, hy₁⟩ := hfix (x + σ x) (by rw [map_add (f := _), hσσ, add_comm])
  obtain ⟨y₂, hy₂⟩ := hfix (x * σ x) (by rw [map_mul, hσσ, mul_comm])
  refine ⟨y₁, y₂, by rw [hy₁, hy₂]; ring, fun v τ => ?_⟩
  have key : ∀ y : F, τ (algebraMap F E y) =
      algebraMap (Fv F v) (FvBar F v) (algebraMap F (Fv F v) y) := fun y => by
    rw [τ.commutes]
    exact IsScalarTower.algebraMap_apply F (Fv F v) (FvBar F v) y
  constructor
  · rw [← absBar_algebraMap F v, ← key, hy₁, map_add (f := _)]
    exact absBar_add_le F v _ _
  · rw [← absBar_algebraMap F v, ← key, hy₂, map_mul]
    exact absBar_mul F v _ _

end GlobalTheory.CompanionTheory.GodementH
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticIntegralCoefficientsBoundStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_integral_coefficients_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ x : E, ∃ y₁ y₂ : F,
    x ^ 2 - algebraMap F E y₁ * x + algebraMap F E y₂ = 0 ∧ ∀ (v : Pl (F := F)) (τ : E →ₐ[F] FvBar F v),
      ‖algebraMap F (Fv F v) y₁‖₊ ≤ max (absBar F v (τ x)) (absBar F v (τ (σ x))) ∧
      ‖algebraMap F (Fv F v) y₂‖₊ = absBar F v (τ x) * absBar F v (τ (σ x)) := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.trace_norm_local_sizes | exact GlobalTheory.CompanionTheory.GodementH.trace_norm_local_sizes | (intros; apply GlobalTheory.CompanionTheory.GodementH.trace_norm_local_sizes <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLeviMinimalOfCommutesProjections
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLeviMinimalOfCommutesProjections
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.ParCocompact

theorem mul_eq_mul_diagonal_of_comm {R : Type} [CommRing R] {n r : ℕ} {G : Matrix (Fin n) (Fin n) R}
    {C : Matrix (Fin n) (Fin r) R} {L : Matrix (Fin r) (Fin n) R} (hL : L * C = 1)
    (hc : ∀ i, G * Matrix.vecMulVec (fun k => C k i) (L i) = Matrix.vecMulVec (fun k => C k i) (L i) * G) :
    G * C = C * Matrix.diagonal (fun i => (L * (G * C)) i i) := by
  ext k i
  have h := congrArg (fun M => (M * C) k i) (hc i)
  simp only [Matrix.mul_assoc, Matrix.vecMulVec_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_apply] at h
  have h1 : (L i ᵥ* C) i = 1 := by
    have := congrFun (congrFun hL i) i
    simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct] using this
  rw [h1, mul_one] at h
  rw [Matrix.mul_diagonal, ← Matrix.mul_assoc]
  simpa [Matrix.mul_apply, Matrix.mulVec, Matrix.vecMul, dotProduct] using h

theorem mem_leviMin_of_comm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ γ ∈ ratPts σ J, (∀ k, (matHom _ σ J γ).1 * (projFam σ J X Y k).map (inclR (F := F) (AF F)) = (projFam σ J X Y k).map (inclR (F := F) (AF F)) * (matHom _ σ J γ).1) → γ ∈ leviMin σ J X Y ∧ γ ∈ minParOne σ J X := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW γ hγ hcomm
  have hF := pfrA h hJ hW
  have hinj : Function.Injective (inclR (F := F) (AF F) : E → AF F ⊗[F] E) := fun a b hab =>
    congrFun (GlobalTheory.CompanionTheory.RedCov.ratV_injective (F := F) (E := E) (n := 1)
      (show ratV F (fun _ : Fin 1 => a) = ratV F (fun _ : Fin 1 => b) from funext fun _ => hab)) 0
  have key : ∀ p ∈ ratPts σ J, ∃ M : Matrix (Fin n) (Fin n) E,
      (matHom _ σ J p).1 = M.map (inclR (F := F) (AF F)) := by
    intro p hp
    have hp2 : (p.1 : GL (Fin n) (AF F ⊗[F] E)) ∈
        Subgroup.map (Formalism.UG.bc (inclR (F := F) (AF F))) (Formalism.UG.UJ (σ : E →+* E) J) := hp
    obtain ⟨g, -, hg⟩ := Subgroup.mem_map.1 hp2
    refine ⟨g.1, ?_⟩
    rw [show (matHom _ σ J p).1 = ((p.1 : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) _) from rfl, ← hg]
    rfl
  have bmRat : ∀ p ∈ ratPts σ J, ∃ M : Matrix (Fin r) (Fin r) E,
      Bm σ J X Y p = M.map (inclR (F := F) (AF F)) := by
    intro p hp
    obtain ⟨M, hM⟩ := key p hp
    refine ⟨cT (σ : E →+* E) Y * J * (M * X), ?_⟩
    rw [Bm, coefM, hM, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, PositivityTheory.ThKR.cT_map_inclR]
    rfl
  have hrow : ∀ C : Matrix (Fin n) (Fin r) E,
      cT (sigR (AF F) σ) (adMat F C) * JR (AF F) J = (cT (σ : E →+* E) C * J).map (inclR (F := F) (AF F)) := by
    intro C
    rw [Matrix.map_mul, PositivityTheory.ThKR.cT_map_inclR]
    rfl
  have hP : ∀ (C D : Matrix (Fin n) (Fin r) E) (i : Fin r),
      (lineProj σ J C D i).map (inclR (F := F) (AF F)) =
        Matrix.vecMulVec (fun k => adMat F C k i)
          ((cT (sigR (AF F) σ) (adMat F D) * JR (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) i) := by
    intro C D i
    rw [hrow]
    ext a b
    simp only [lineProj, rowOf, Matrix.vecMulVec_apply, Matrix.map_apply, adMat, map_mul]
  have hX := mul_eq_mul_diagonal_of_comm (G := (matHom _ σ J γ).1) hF.yx (fun i => by
    have := hcomm (Sum.inl i)
    rwa [projFam, Sum.elim_inl, hP] at this)
  have hY := mul_eq_mul_diagonal_of_comm (G := (matHom _ σ J γ).1) hF.xy (fun i => by
    have := hcomm (Sum.inr i)
    rwa [projFam, Sum.elim_inr, hP] at this)
  refine ⟨⟨_, _, hX, hY⟩, ⟨Matrix.diagonal _, Matrix.blockTriangular_diagonal _, hX, fun i => ?_⟩⟩
  have hp : γ ∈ minPar σ J X := ⟨_, Matrix.blockTriangular_diagonal _, hX⟩
  have hp' := inv_mem_minPar h hJ hW hp
  refine ⟨uU σ J X Y h hJ hW hp hp' i, ?_, ?_⟩
  · rw [val_uU h hJ hW hp hp' i, Bm_eq hF hX]
  · obtain ⟨M, hM⟩ := bmRat γ hγ
    obtain ⟨M', hM'⟩ := bmRat γ⁻¹ (inv_mem hγ)
    have hu1 : ((uU σ J X Y h hJ hW hp hp' i : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = inclR (F := F) (AF F) (M i i) := by
      rw [val_uU h hJ hW hp hp' i, hM]
      rfl
    have hu2 : (((uU σ J X Y h hJ hW hp hp' i)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = inclR (F := F) (AF F) (M' i i) := by
      show Bm σ J X Y γ⁻¹ i i = _
      rw [hM']
      rfl
    have he : M i i * M' i i = 1 := hinj (by rw [map_mul, ← hu1, ← hu2, Units.mul_inv, map_one])
    have he' : M' i i * M i i = 1 := by rw [mul_comm]; exact he
    have hu : uU σ J X Y h hJ hW hp hp' i =
        Units.map (inclR (F := F) (E := E) (AF F) : E →* AF F ⊗[F] E) ⟨M i i, M' i i, he, he'⟩ :=
      Units.ext (by rw [hu1]; rfl)
    rw [hu]
    exact GlobalTheory.Doubling.absE_inclR _

end GlobalTheory.CompanionTheory.ParCocompact

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLeviMinimalOfCommutesProjectionsStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_levi_minimal_of_commutes_projections : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ γ ∈ ratPts σ J, (∀ k, (matHom _ σ J γ).1 * (projFam σ J X Y k).map (inclR (F := F) (AF F)) = (projFam σ J X Y k).map (inclR (F := F) (AF F)) * (matHom _ σ J γ).1) → γ ∈ leviMin σ J X Y ∧ γ ∈ minParOne σ J X := by
  first | exact @GlobalTheory.CompanionTheory.ParCocompact.mem_leviMin_of_comm | exact GlobalTheory.CompanionTheory.ParCocompact.mem_leviMin_of_comm | (intros; apply GlobalTheory.CompanionTheory.ParCocompact.mem_leviMin_of_comm <;> assumption)
end
end
