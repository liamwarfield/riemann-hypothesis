module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedOfFunctor
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HtpyStOfCxSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeExOfAcyclic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExactOfSpan
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteCover
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNbhd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UOfIsBaseChange
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyOfBaseZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleHomCompSquareZeroSection
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsToCoindShortExact
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopologicalKrullDimLeOfSmooth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteChains
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectFirstCohomologyBaseChange
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCohomologyComparisonSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeTSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransferSumProjectionsDegreeZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeFormsMapInjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExteriorPairingIotaTwo
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOfRTensor
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BilinearStatementWithDescentHypotheses
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1BoundaryOfBoundary
public import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianWedgeProducts.EqZeroOfExteriorPowerMapAdd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemOfSmulEqZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VbOfEquiv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyVectorBundleRank
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FewEquationsStatement
public import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.ClosedPoints.IsClosedPoint
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyDimensionLowerBound
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.AbelianHodgeDeRham.Bridge

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyRankOverField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open scoped CategoryTheory.Obj

set_option autoImplicit false

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.AbelianFirstCohomologyOverField

theorem vb_of_field (hFlat : FlatBCSt) (hLe : PositivityTheory.ObstructionTrivialLocus.H1StructureDimLe) (hGe : H1DimGeAbelianDim) (k : Type) [Field k]
    (A : Over (Sp k)) [GrpObj A] (g : ℕ) (hab : IsAbelianScheme A)
    (hsm : SmoothOfRelativeDimension g A.hom) : VB k (HO1 A.hom) g := by
  let K := AlgebraicClosure k
  have hφ := isGrpPullback_pullback A (spMap (algebraMap k K))
  have hab' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hab hφ
  have hsm' : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap k K))).obj A).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hφ.1 hsm
  obtain ⟨hfin, hle⟩ := hLe k A g hab hsm
  obtain ⟨hfin', hle'⟩ := hLe K _ g hab' hsm'
  have hge := hGe K _ g hab' hsm' hfin'
  have := hab.proper
  obtain ⟨e, -⟩ := hFlat k K _ _ A.hom _ _ hφ.1 inferInstance inferInstance
  have hrank : Module.finrank k (HO1 A.hom) = g := by
    have h1 := e.finrank_eq
    rw [Module.finrank_baseChange] at h1
    omega
  refine ⟨hfin, inferInstance, fun p ↦ ?_⟩
  rw [Module.rankAtStalk_eq_finrank_of_free, hrank]
  rfl

theorem first_cohomology_rank_over_field : FlatBCSt → PositivityTheory.ObstructionTrivialLocus.H1StructureDimLe → H1DimGeAbelianDim → H1StructureFieldDim := by
  intro hFlat hLe hGe R _ A _ g hab hsm hR
  letI := hR.toField
  exact vb_of_field hFlat hLe hGe R A g hab hsm

end GlobalTheory.CompanionTheory.AbelianFirstCohomologyOverField
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinCohStOfCmpSt
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.Hodge

theorem finCohSt_of_cmpSt : CmpSt → FinCohSt := by
  intro h R _ _ X s _ P _ _ S
  letI := GlobalTheory.algebraΓOfHom s
  have hf : ∀ p, Module.Finite R (GlobalTheory.coh (GlobalTheory.structureModule X) p) := fun p ↦
    GlobalTheory.ProperFinite.finite_coh_of_isProper s (GlobalTheory.structureModule X) p
  obtain ⟨⟨e₀⟩, hn⟩ := h R X s inferInstance P S
  refine ⟨?_, fun n ↦ ?_⟩
  · have := hf 0
    exact Module.Finite.equiv e₀.symm
  · obtain ⟨e⟩ := hn n
    have := hf (n + 1)
    exact Module.Finite.equiv e.symm

end GlobalTheory.CompanionTheory.Hodge
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtendedFormNaturality
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.OneFormCoh

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def extForm (hp : Par F) (l : Glob1 F →ₗ[R] R) (T : C) : Ω[F.obj T⁄R] →ₗ[F.obj T] F.obj T :=
  (hp T).lift ((Algebra.linearMap R (F.obj T)) ∘ₗ l)

theorem extForm_ev (hp : Par F) (l : Glob1 F →ₗ[R] R) (T : C) (v : Glob1 F) :
    extForm F hp l T (v.1 T) = algebraMap R (F.obj T) (l v) :=
  (hp T).lift_eq _ v

theorem extended_form_naturality (hp : Par F) (l : Glob1 F →ₗ[R] R) {T T' : C} (φ : T ⟶ T') (α : Ω[F.obj T⁄R]) :
    extForm F hp l T' (p1 F φ α) = mp F φ (extForm F hp l T α) := by
  refine (hp T).inductionOn α ?_ ?_ ?_
  · intro v
    change GlobalTheory.CompanionTheory.OneFormCoh.extForm F hp l T' (GlobalTheory.CechDR.p1 F φ (v.1 T)) =
      GlobalTheory.CatCoh.mp F φ (GlobalTheory.CompanionTheory.OneFormCoh.extForm F hp l T (v.1 T))
    have hv : GlobalTheory.CechDR.p1 F φ (v.1 T) = v.1 T' := by
      first
        | exact v.2 φ
        | exact v.2 T T' φ
        | exact (v.2 φ).symm
        | exact (v.2 T T' φ).symm
    rw [hv, GlobalTheory.CompanionTheory.OneFormCoh.extForm_ev, GlobalTheory.CompanionTheory.OneFormCoh.extForm_ev, AlgHom.commutes]
  · intro s n hn
    rw [GlobalTheory.CechDR.oneFormsMapOfFunctorMorphism_smul, map_smul, map_smul, hn, smul_eq_mul, smul_eq_mul, map_mul]
  · intro n₁ n₂ h₁ h₂
    rw [map_add (f := _), map_add (f := _), h₁, h₂, map_add (f := _), map_add (f := _)]

theorem extForm_sum (hp : Par F) {n : ℕ} (w : Fin n → Glob1 F) (l : Fin n → Glob1 F →ₗ[R] R)
    (hw : ∀ v, ∑ i, l i v • w i = v) (T : C) (α : Ω[F.obj T⁄R]) :
    ∑ i, extForm F hp (l i) T α • (w i).1 T = α := by
  refine (hp T).inductionOn α ?_ ?_ ?_
  · intro v
    change ∑ i, GlobalTheory.CompanionTheory.OneFormCoh.extForm F hp (l i) T (v.1 T) • (w i).1 T = v.1 T
    simp only [GlobalTheory.CompanionTheory.OneFormCoh.extForm_ev, algebraMap_smul]
    have h := congrArg (MainStatements.Hodge.evForm F T) (hw v)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h
    simp only [map_smul] at h
    exact h
  · intro s m hm
    conv_rhs => rw [← hm]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_smul]
  · intro m₁ m₂ h₁ h₂
    conv_rhs => rw [← h₁, ← h₂]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_add (f := _), add_smul]

def muMap : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F :=
  TensorProduct.lift (LinearMap.mk₂ R (fun (f : Z1 F) (v : Glob1 F) T T' φ ↦ f.1 T T' φ • v.1 T')
    (fun f f' v ↦ by funext T T' φ; simp [add_smul])
    (fun r f v ↦ by funext T T' φ; simp)
    (fun f v v' ↦ by funext T T' φ; simp)
    (fun r f v ↦ by funext T T' φ; simp [smul_comm r]))

theorem muMap_tmul (f : Z1 F) (v : Glob1 F) {T T' : C} (φ : T ⟶ T') :
    muMap F (f ⊗ₜ v) T T' φ = f.1 T T' φ • v.1 T' := rfl

def contr (l : Glob1 F →ₗ[R] R) : Z1 F ⊗[R] Glob1 F →ₗ[R] Z1 F :=
  (TensorProduct.rid R (Z1 F)).toLinearMap ∘ₗ LinearMap.lTensor (Z1 F) l

theorem contr_tmul (l : Glob1 F →ₗ[R] R) (f : Z1 F) (v : Glob1 F) :
    contr F l (f ⊗ₜ v) = l v • f := by
  simp [contr]

theorem extForm_muMap (hp : Par F) (l : Glob1 F →ₗ[R] R) (t : Z1 F ⊗[R] Glob1 F) {T T' : C}
    (φ : T ⟶ T') : extForm F hp l T' (muMap F t T T' φ) = (contr F l t).1 T T' φ := by
  induction t using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero]
    exact map_zero _
  | add x y hx hy =>
    simp only [map_add (f := _), Pi.add_apply, Submodule.coe_add, hx, hy]
  | tmul f v =>
    simp only [GlobalTheory.CompanionTheory.OneFormCoh.muMap_tmul, GlobalTheory.CompanionTheory.OneFormCoh.contr_tmul, map_smul, GlobalTheory.CompanionTheory.OneFormCoh.extForm_ev,
      Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Algebra.smul_def]
    ring

theorem sum_contr {n : ℕ} (w : Fin n → Glob1 F) (l : Fin n → Glob1 F →ₗ[R] R)
    (hw : ∀ v, ∑ i, l i v • w i = v) (t : Z1 F ⊗[R] Glob1 F) :
    ∑ i, contr F (l i) t ⊗ₜ[R] w i = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, TensorProduct.zero_tmul, Finset.sum_const_zero]
  | add x y hx hy =>
    simp only [map_add (f := _), TensorProduct.add_tmul, Finset.sum_add_distrib, hx, hy]
  | tmul f v =>
    simp_rw [GlobalTheory.CompanionTheory.OneFormCoh.contr_tmul, TensorProduct.smul_tmul]
    rw [← TensorProduct.tmul_sum, hw]

def pushZ (hp : Par F) (l : Glob1 F →ₗ[R] R) (a : A1 F)
    (ha : ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''),
      a T T'' (φ ≫ ψ) = p1 F ψ (a T T' φ) + a T' T'' ψ) : Z1 F :=
  ⟨fun T T' φ ↦ extForm F hp l T' (a T T' φ), fun T T' T'' φ ψ ↦ by
    change extForm F hp l T'' (a T T'' (φ ≫ ψ)) =
      mp F ψ (extForm F hp l T' (a T T' φ)) + extForm F hp l T'' (a T' T'' ψ)
    rw [ha, map_add (f := _), extended_form_naturality]⟩

theorem main (hF : Framed F) :
    ∃ mu : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F, (∀ f ω T T' φ, mu (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T') ∧
      (∀ a : A1 F, (∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''),
        a T T'' (φ ≫ ψ) = p1 F ψ (a T T' φ) + a T' T'' ψ) → ∃ t, mu t = a) ∧
      ∀ (t : Z1 F ⊗[R] Glob1 F) (β : A0 F), (∀ T T' φ, mu t T T' φ = β T' - p1 F φ (β T)) →
        (H1.mk F).rTensor (Glob1 F) t = 0 := by
  obtain ⟨-, hp, hfin, hproj⟩ := hF
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R (GlobalTheory.CechDR.Glob1 F)
  obtain ⟨w, l, hw⟩ : ∃ (w : Fin n → GlobalTheory.CechDR.Glob1 F) (l : Fin n → GlobalTheory.CechDR.Glob1 F →ₗ[R] R),
      ∀ v, ∑ i, l i v • w i = v := by
    refine ⟨fun i => f (Pi.single i 1), fun i => LinearMap.proj i ∘ₗ g, fun v => ?_⟩
    have hsum : ∑ i, g v i • (Pi.single i 1 : Fin n → R) = g v := by
      ext j
      simp [Pi.single_apply]
    calc ∑ i, (LinearMap.proj i ∘ₗ g) v • f (Pi.single i 1)
        = f (∑ i, g v i • (Pi.single i 1 : Fin n → R)) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          simp only [map_smul, LinearMap.comp_apply, LinearMap.proj_apply]
      _ = v := by
          rw [hsum]
          exact LinearMap.congr_fun hfg v
  refine ⟨GlobalTheory.CompanionTheory.OneFormCoh.muMap F, fun x ω T T' φ => GlobalTheory.CompanionTheory.OneFormCoh.muMap_tmul F x ω φ, ?_, ?_⟩
  · intro a ha
    refine ⟨∑ i, GlobalTheory.CompanionTheory.OneFormCoh.pushZ F hp (l i) a ha ⊗ₜ w i, ?_⟩
    funext T T' φ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [Finset.sum_apply, GlobalTheory.CompanionTheory.OneFormCoh.muMap_tmul]
    exact GlobalTheory.CompanionTheory.OneFormCoh.extForm_sum F hp w l hw T' (a T T' φ)
  · intro t β hβ
    have hzero : ∀ i, GlobalTheory.CatCoh.H1.mk F
        (GlobalTheory.CompanionTheory.OneFormCoh.contr F (l i) t) = 0 := by
      intro i
      rw [GlobalTheory.CatCoh.H1.mk_eq_zero]
      refine ⟨fun T => GlobalTheory.CompanionTheory.OneFormCoh.extForm F hp (l i) T (β T), ?_⟩
      funext T T' φ
      rw [GlobalTheory.CatCoh.amitsur_d0_apply, ← GlobalTheory.CompanionTheory.OneFormCoh.extForm_muMap F hp, hβ, map_sub,
        GlobalTheory.CompanionTheory.OneFormCoh.extended_form_naturality]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← GlobalTheory.CompanionTheory.OneFormCoh.sum_contr F w l hw t, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [LinearMap.rTensor_tmul, hzero, TensorProduct.zero_tmul]

theorem oneFormCohSt : OneFormCohSt := by
  unfold MainStatements.Hodge.OneFormCohSt MainStatements.Hodge.AllF
  intro R _ C _ F hF
  exact GlobalTheory.CompanionTheory.OneFormCoh.main F hF

end GlobalTheory.CompanionTheory.OneFormCoh
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormComponentOfWedgeClassZero
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open KaehlerDifferential

namespace GlobalTheory.CompanionTheory.HypWedge

section Alt

variable {R M N V W : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

def alt2 (B : M →ₗ[R] M →ₗ[R] N) (h : ∀ x, B x x = 0) : M [⋀^Fin 2]→ₗ[R] N where
  toFun v := B (v 0) (v 1)
  map_update_add' := by
    intro _ v i x y
    fin_cases i <;> simp
  map_update_smul' := by
    intro _ v i c x
    fin_cases i <;> simp
  map_eq_zero_of_eq' := by
    intro v i j hv hij
    have hv' : v 0 = v 1 := by
      fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | exact hv | exact hv.symm
    simp only [hv', h]

def ext2 (B : M →ₗ[R] M →ₗ[R] N) (h : ∀ x, B x x = 0) : ⋀[R]^2 M →ₗ[R] N :=
  exteriorPower.alternatingMapLinearEquiv (alt2 B h)

theorem characterExtensionRep_apply (B : M →ₗ[R] M →ₗ[R] N) (h : ∀ x, B x x = 0) (a b : M) :
    ext2 B h (exteriorPower.ιMulti R 2 ![a, b]) = B a b := by
  simp [ext2, alt2]

theorem grpScheme_square_hom_ext_fst_snd {f g : ⋀[R]^2 M →ₗ[R] N}
    (h : ∀ a b, f (exteriorPower.ιMulti R 2 ![a, b]) = g (exteriorPower.ιMulti R 2 ![a, b])) : f = g := by
  refine LinearMap.ext_on (exteriorPower.ιMulti_span R 2 M) ?_
  rintro _ ⟨v, rfl⟩
  have hv : v = ![v 0, v 1] := by
    ext i; fin_cases i <;> rfl
  rw [hv]
  exact h _ _


variable (R M) in
def wB : M →ₗ[R] M →ₗ[R] ⋀[R]^2 M :=
  LinearMap.mk₂ R (fun a b ↦ exteriorPower.ιMulti R 2 ![a, b])
    (fun _ _ _ ↦ Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply, add_mul]))
    (fun _ _ _ ↦ Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply]))
    (fun _ _ _ ↦ Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply, mul_add]))
    (fun _ _ _ ↦ Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply]))

theorem wB_apply (a b : M) : wB R M a b = exteriorPower.ιMulti R 2 ![a, b] := rfl

theorem wB_self (a : M) : wB R M a a = 0 :=
  Subtype.ext (by simp [wB_apply, ExteriorAlgebra.ιMulti_apply])

theorem wB_swap (a b : M) : wB R M a b = -wB R M b a := by
  have h := wB_self (R := R) (a + b)
  simp only [map_add (f := _), LinearMap.add_apply, wB_self, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left ((add_comm _ _).trans h)

theorem exterior_square_map_apply (f : V →ₗ[R] M) (a b : V) :
    exteriorPower.map 2 f (exteriorPower.ιMulti R 2 ![a, b]) = wB R M (f a) (f b) := by
  rw [exteriorPower.map_apply_ιMulti, wB_apply]
  congr 1
  ext i; fin_cases i <;> rfl

def mix (σ : V →ₗ[R] M) (k : W →ₗ[R] M) : V ⊗[R] W →ₗ[R] ⋀[R]^2 M :=
  TensorProduct.lift ((wB R M).compl₁₂ σ k)

theorem mix_tmul (σ : V →ₗ[R] M) (k : W →ₗ[R] M) (v : V) (w : W) :
    mix σ k (v ⊗ₜ w) = wB R M (σ v) (k w) := rfl

theorem decomp (σ : V →ₗ[R] M) (k : W →ₗ[R] M) (hs : ∀ a, ∃ v w, a = σ v + k w) (x : ⋀[R]^2 M) :
    ∃ y u z, x = exteriorPower.map 2 σ y + mix σ k u + exteriorPower.map 2 k z := by
  let S : Submodule R (⋀[R]^2 M) :=
    LinearMap.range (exteriorPower.map 2 σ) ⊔ LinearMap.range (mix σ k) ⊔
      LinearMap.range (exteriorPower.map 2 k)
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← exteriorPower.ιMulti_span R 2 M, Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    have hm : m = ![m 0, m 1] := by
      ext i; fin_cases i <;> rfl
    obtain ⟨v, w, h0⟩ := hs (m 0)
    obtain ⟨v', w', h1⟩ := hs (m 1)
    rw [hm, ← wB_apply, h0, h1]
    have e : wB R M (σ v + k w) (σ v' + k w') =
        exteriorPower.map 2 σ (exteriorPower.ιMulti R 2 ![v, v']) +
          mix σ k (v ⊗ₜ w' - v' ⊗ₜ w) + exteriorPower.map 2 k (exteriorPower.ιMulti R 2 ![w, w']) := by
      rw [exterior_square_map_apply, exterior_square_map_apply, map_sub, mix_tmul, mix_tmul, wB_swap (σ v') (k w)]
      simp only [map_add (f := _), LinearMap.add_apply]
      abel
    rw [e]
    exact S.add_mem (S.add_mem (Submodule.mem_sup_left (Submodule.mem_sup_left ⟨_, rfl⟩))
      (Submodule.mem_sup_left (Submodule.mem_sup_right ⟨_, rfl⟩)))
      (Submodule.mem_sup_right ⟨_, rfl⟩)
  have hx : x ∈ S := hS ▸ Submodule.mem_top
  obtain ⟨x', hx', z', ⟨z, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨_, ⟨y, rfl⟩, _, ⟨u, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx'
  exact ⟨y, u, z, rfl⟩

end Alt

section Coh

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}


variable (F) in
def fn2 : cechDeRhamTotalCocyclesTwo F →ₗ[R] Z2 F where
  toFun c := ⟨c.1.1, (mem_cechDeRhamTotalCocyclesTwo_iff.1 c.2).1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


variable (F) in
def rho : Hyp2 F →ₗ[R] H2 F :=
  Submodule.mapQ _ _ (fn2 F) (by rintro _ ⟨g, rfl⟩; exact ⟨g.1, rfl⟩)

theorem rho_mk (c : cechDeRhamTotalCocyclesTwo F) : rho F (Hyp2.mk F c) = H2.mk F (fn2 F c) := rfl

theorem rho_cup (a b : Hyp1 F) : rho F (cupHyp F a b) = cup F (toO F a) (toO F b) := by
  obtain ⟨a, rfl⟩ := Hyp1.mk_surjective F a
  obtain ⟨b, rfl⟩ := Hyp1.mk_surjective F b
  rfl

theorem key_D (hs : Function.Surjective (toO F)) (f : C1 F) (hf : f ∈ Z1 F) :
    ∃ β : A0 F, (∀ (T T' : C) (φ : T ⟶ T'), D R _ (f T T' φ) = β T' - p1 F φ (β T)) ∧
      ∀ T, dOne R _ (β T) = 0 := by
  obtain ⟨c, hc⟩ := hs (H1.mk F ⟨f, hf⟩)
  obtain ⟨c, rfl⟩ := Hyp1.mk_surjective F c
  rw [toO_mk, H1.mk_eq_mk] at hc
  obtain ⟨g, hg⟩ := hc
  have hg' : ∀ (T T' : C) (φ : T ⟶ T'), g T' - mp F φ (g T) = c.1.1 T T' φ - f T T' φ :=
    fun T T' φ ↦ congrFun (congrFun (congrFun hg T) T') φ
  refine ⟨fun T ↦ c.1.2 T - D R _ (g T), fun T T' φ ↦ ?_, fun T ↦ ?_⟩
  · have h2 : f T T' φ = c.1.1 T T' φ - (g T' - mp F φ (g T)) := by rw [hg']; ring
    change _ = (c.1.2 T' - D R _ (g T')) - p1 F φ (c.1.2 T - D R _ (g T))
    rw [h2, map_sub, map_sub, map_sub, p1_D, cechDeRhamTotalCocyclesOne.conn c φ]
    abel
  · simp [cechDeRhamTotalCocyclesOne.closed c]

def cl (hcl : Closed1 F = ⊤) : Glob1 F →ₗ[R] cechDeRhamTotalCocyclesOne F :=
  formZZ F ∘ₗ LinearMap.codRestrict (Closed1 F) LinearMap.id (fun w ↦ by rw [hcl]; trivial)

theorem cl_coe (hcl : Closed1 F = ⊤) (w : Glob1 F) : (cl hcl w).1 = (0, w.1) := rfl

def Lc (hcl : Closed1 F = ⊤) (τ : H1 F →ₗ[R] cechDeRhamTotalCocyclesOne F) : H1 F ⊗[R] Glob1 F →ₗ[R] cechDeRhamTotalCocyclesTwo F :=
  TensorProduct.lift ((cupZZ F).compl₁₂ τ (cl hcl))

theorem cup_cl_self (hcl : Closed1 F = ⊤) (w : Glob1 F) : cupZZ F (cl hcl w) (cl hcl w) = 0 := by
  refine Subtype.ext (Tot2.ext (fun T T' T'' φ ψ ↦ ?_) (fun T T' φ ↦ ?_) fun T ↦ ?_)
  · simp [coe_cupZZ, cupTot_apply, cl_coe]
  · simp [coe_cupZZ, cupTot_a, cl_coe]
  · simp [coe_cupZZ, cupTot_η, cl_coe]

def Nc (hcl : Closed1 F = ⊤) : ⋀[R]^2 (Glob1 F) →ₗ[R] cechDeRhamTotalCocyclesTwo F :=
  ext2 ((cupZZ F).compl₁₂ (cl hcl) (cl hcl)) (cup_cl_self hcl)

theorem Nc_apply (hcl : Closed1 F = ⊤) (a b : Glob1 F) :
    Nc hcl (exteriorPower.ιMulti R 2 ![a, b]) = cupZZ F (cl hcl a) (cl hcl b) :=
  characterExtensionRep_apply _ _ a b

theorem Nc_spec (hcl : Closed1 F = ⊤) (nu : ⋀[R]^2 (Glob1 F) →ₗ[R] W0 F 2)
    (hnu : ∀ (a b : Glob1 F) (T : C), nu (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (x : ⋀[R]^2 (Glob1 F)) : (Nc hcl x).1 = (0, 0, nu x) := by
  have e : (cechDeRhamTotalCocyclesTwo F).subtype ∘ₗ Nc hcl =
      LinearMap.inr R _ _ ∘ₗ LinearMap.inr R _ _ ∘ₗ nu := by
    refine grpScheme_square_hom_ext_fst_snd fun a b ↦ ?_
    simp only [LinearMap.comp_apply, Nc_apply, Submodule.subtype_apply, LinearMap.inr_apply]
    refine Tot2.ext (fun T T' T'' φ ψ ↦ ?_) (fun T T' φ ↦ ?_) fun T ↦ ?_
    · simp [coe_cupZZ, cupTot_apply, cl_coe]
    · simp [coe_cupZZ, cupTot_a, cl_coe]
    · simp [coe_cupZZ, cupTot_η, cl_coe, hnu]
  exact LinearMap.congr_fun e x

abbrev sR (τ : H1 F →ₗ[R] cechDeRhamTotalCocyclesOne F) : H1 F ⊗[R] Glob1 F →ₗ[R] Z1 F ⊗[R] Glob1 F :=
  LinearMap.rTensor (Glob1 F) (cechDeRhamTotalCocyclesOne.fn F ∘ₗ τ)

theorem rT_sR (τ : H1 F →ₗ[R] cechDeRhamTotalCocyclesOne F) (hτ : ∀ v, H1.mk F (cechDeRhamTotalCocyclesOne.fn F (τ v)) = v) (u : H1 F ⊗[R] Glob1 F) :
    LinearMap.rTensor (Glob1 F) (H1.mk F) (sR τ u) = u := by
  rw [sR, ← LinearMap.rTensor_comp_apply]
  have : H1.mk F ∘ₗ cechDeRhamTotalCocyclesOne.fn F ∘ₗ τ = LinearMap.id := LinearMap.ext hτ
  rw [this, LinearMap.rTensor_id]
  rfl

theorem Lc_spec (hcl : Closed1 F = ⊤) (τ : H1 F →ₗ[R] cechDeRhamTotalCocyclesOne F) (mu : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F)
    (hmu : ∀ (f : Z1 F) (w : Glob1 F) (T T' : C) (φ : T ⟶ T'), mu (f ⊗ₜ w) T T' φ = f.1 T T' φ • w.1 T')
    (u : H1 F ⊗[R] Glob1 F) :
    (Lc hcl τ u).1.1 = 0 ∧ (Lc hcl τ u).1.2.1 = mu (sR τ u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    constructor
    · rw [map_add (f := _)]
      change (Lc hcl τ a).1.1 + (Lc hcl τ b).1.1 = 0
      rw [ha.1, hb.1, add_zero]
    · rw [map_add (f := _), map_add (f := _), map_add (f := _)]
      change (Lc hcl τ a).1.2.1 + (Lc hcl τ b).1.2.1 = _
      rw [ha.2, hb.2]
  | tmul v w =>
    constructor
    · funext T T' T'' φ ψ
      change (cupTot F (τ v).1 (cl hcl w).1).1 T T' T'' φ ψ = 0
      simp [cupTot_apply, cl_coe]
    · funext T T' φ
      change (cupTot F (τ v).1 (cl hcl w).1).2.1 T T' φ = mu ((cechDeRhamTotalCocyclesOne.fn F (τ v)) ⊗ₜ w) T T' φ
      rw [hmu, cupTot_a]
      simp [cl_coe]
      rfl

theorem beta_of (τ : H1 F →ₗ[R] cechDeRhamTotalCocyclesOne F) (hτ : ∀ v, H1.mk F (cechDeRhamTotalCocyclesOne.fn F (τ v)) = v)
    (mu : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F)
    (hmu : ∀ (f : Z1 F) (w : Glob1 F) (T T' : C) (φ : T ⟶ T'), mu (f ⊗ₜ w) T T' φ = f.1 T T' φ • w.1 T')
    (t : Z1 F ⊗[R] Glob1 F) :
    ∃ β : A0 F, ∀ (T T' : C) (φ : T ⟶ T'),
      mu t T T' φ - mu (sR τ (LinearMap.rTensor (Glob1 F) (H1.mk F) t)) T T' φ = β T' - p1 F φ (β T) := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add a b ha hb =>
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hb
    refine ⟨x + y, fun T T' φ ↦ ?_⟩
    have h1 := hx T T' φ
    have h2 := hy T T' φ
    simp only [map_add (f := _), Pi.add_apply]
    rw [add_sub_add_comm, h1, h2]
    abel
  | tmul f w =>
    obtain ⟨g, hg⟩ := H1.mk_eq_mk.1 (hτ (H1.mk F f)).symm
    refine ⟨fun T ↦ g T • w.1 T, fun T T' φ ↦ ?_⟩
    have hg' : g T' - mp F φ (g T) = f.1 T T' φ - (cechDeRhamTotalCocyclesOne.fn F (τ (H1.mk F f))).1 T T' φ :=
      congrFun (congrFun (congrFun hg T) T') φ
    simp only [LinearMap.rTensor_tmul, hmu, LinearMap.comp_apply]
    rw [oneFormsMapOfFunctorMorphism_smul, ← w.2 φ, ← sub_smul, ← sub_smul, hg']

end Coh

theorem add_rearr {A : Type} [AddCommGroup A] (a b l d : A) : a = a - b - l - d + l + b + d := by
  abel

section Main

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}

theorem form_component_of_cup_class_zero (hcl : Closed1 F = ⊤) (τ : H1 F →ₗ[R] cechDeRhamTotalCocyclesOne F) (mu : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F)
    (hmu : ∀ (f : Z1 F) (w : Glob1 F) (T T' : C) (φ : T ⟶ T'), mu (f ⊗ₜ w) T T' φ = f.1 T T' φ • w.1 T')
    (u : H1 F ⊗[R] Glob1 F) : fn2 F (Lc hcl τ u) = 0 :=
  Subtype.ext (Lc_spec hcl τ mu hmu u).1

theorem form_component_of_wedge_class_zero (hcl : Closed1 F = ⊤) (nu : ⋀[R]^2 (Glob1 F) →ₗ[R] W0 F 2)
    (hnu : ∀ (a b : Glob1 F) (T : C), nu (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (x : ⋀[R]^2 (Glob1 F)) : fn2 F (Nc hcl x) = 0 :=
  Subtype.ext (congrArg Prod.fst (Nc_spec hcl nu hnu x))

theorem inj_L (hs : Function.Surjective (toO F)) (hcl : Closed1 F = ⊤) (τ : H1 F →ₗ[R] cechDeRhamTotalCocyclesOne F)
    (hτ : ∀ v, H1.mk F (cechDeRhamTotalCocyclesOne.fn F (τ v)) = v) (mu : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F)
    (hmu : ∀ (f : Z1 F) (w : Glob1 F) (T T' : C) (φ : T ⟶ T'), mu (f ⊗ₜ w) T T' φ = f.1 T T' φ • w.1 T')
    (hmu3 : ∀ (t : Z1 F ⊗[R] Glob1 F) (β : A0 F),
      (∀ (T T' : C) (φ : T ⟶ T'), mu t T T' φ = β T' - p1 F φ (β T)) →
        (H1.mk F).rTensor (Glob1 F) t = 0)
    (nu : ⋀[R]^2 (Glob1 F) →ₗ[R] W0 F 2)
    (hnu : ∀ (a b : Glob1 F) (T : C), nu (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (u : H1 F ⊗[R] Glob1 F) (x : ⋀[R]^2 (Glob1 F)) (c : Tot1 F)
    (hc : dTot1 F c = (Lc hcl τ u + Nc hcl x).1) : u = 0 := by
  have hL := Lc_spec hcl τ mu hmu u
  have hN := Nc_spec hcl nu hnu x
  have hz : d1 F c.1 = 0 := by
    have h : d1 F c.1 = (Lc hcl τ u).1.1 + (Nc hcl x).1.1 := congrArg Prod.fst hc
    rw [h, hL.1, hN, add_zero]
  have hf : c.1 ∈ Z1 F := by rw [commAlgFunctorCocyclesOne_eq_ker]; exact hz
  obtain ⟨β, hβ, -⟩ := key_D hs c.1 hf
  have ha : ∀ (T T' : C) (φ : T ⟶ T'), mu (sR τ u) T T' φ = (c.2 - β) T' - p1 F φ ((c.2 - β) T) := by
    intro T T' φ
    have h : c.2 T' - p1 F φ (c.2 T) - D R _ (c.1 T T' φ) =
        (Lc hcl τ u).1.2.1 T T' φ + (Nc hcl x).1.2.1 T T' φ :=
      congrArg (fun y : Tot2 F ↦ y.2.1 T T' φ) hc
    rw [hL.2, hN, hβ] at h
    have h' : mu (sR τ u) T T' φ = c.2 T' - p1 F φ (c.2 T) - (β T' - p1 F φ (β T)) := by
      rw [h]; exact (add_zero _).symm
    rw [h']
    simp only [Pi.sub_apply, map_sub]
    abel
  have := hmu3 _ _ ha
  rwa [rT_sR τ hτ] at this

theorem inj_N (hs : Function.Surjective (toO F)) (hcl : Closed1 F = ⊤) (c : Tot1 F) (w : W0 F 2)
    (hc : dTot1 F c = (0, 0, w)) : w = 0 := by
  have hz : d1 F c.1 = 0 := congrArg Prod.fst hc
  have hf : c.1 ∈ Z1 F := by rw [commAlgFunctorCocyclesOne_eq_ker]; exact hz
  obtain ⟨β, hβ, hβc⟩ := key_D hs c.1 hf
  let g0 : Glob1 F := ⟨c.2 - β, fun T T' φ ↦ by
    have h : c.2 T' - p1 F φ (c.2 T) - D R _ (c.1 T T' φ) = 0 :=
      congrArg (fun y : Tot2 F ↦ y.2.1 T T' φ) hc
    rw [hβ] at h
    simp only [Pi.sub_apply, map_sub]
    rw [← sub_eq_zero, ← h]
    abel⟩
  have hg0 : g0 ∈ Closed1 F := hcl ▸ Submodule.mem_top
  funext T
  have h : dOne R _ (c.2 T) = w T := congrArg (fun y : Tot2 F ↦ y.2.2 T) hc
  have h2 : dOne R _ (c.2 T - β T) = 0 := hg0 T
  rw [map_sub, hβc, sub_zero, h] at h2
  exact h2


set_option maxHeartbeats 1000000 in
theorem surj_step (hcl : Closed1 F = ⊤) (τ : H1 F →ₗ[R] cechDeRhamTotalCocyclesOne F)
    (hτ : ∀ v, H1.mk F (cechDeRhamTotalCocyclesOne.fn F (τ v)) = v) (mu : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F)
    (hmu : ∀ (f : Z1 F) (w : Glob1 F) (T T' : C) (φ : T ⟶ T'), mu (f ⊗ₜ w) T T' φ = f.1 T T' φ • w.1 T')
    (hmu2 : ∀ a : A1 F, (∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''),
      a T T'' (φ ≫ ψ) = p1 F ψ (a T T' φ) + a T' T'' ψ) → ∃ t, mu t = a)
    (nu : ⋀[R]^2 (Glob1 F) →ₗ[R] W0 F 2)
    (hnu : ∀ (a b : Glob1 F) (T : C), nu (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (hnus : ∀ w : W0 F 2, (∀ (T T' : C) (φ : T ⟶ T'), w T' = pOm F 2 φ (w T)) → ∃ t, nu t = w)
    (c : cechDeRhamTotalCocyclesTwo F) (hc : H2.mk F (fn2 F c) = 0) :
    ∃ u x, Hyp2.mk F c = Hyp2.mk F (Lc hcl τ u) + Hyp2.mk F (Nc hcl x) := by
  obtain ⟨f, hf⟩ := H2.mk_eq_zero.1 hc
  have hf' : d1 F f = c.1.1 := hf
  let b1 : cechDeRhamTotalCocyclesTwo F := ⟨dTot1 F (f, 0), dTot1_mem F _⟩
  let c1 : cechDeRhamTotalCocyclesTwo F := c - b1
  have z1 : ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''), c1.1.1 T T' T'' φ ψ = 0 := fun T T' T'' φ ψ ↦ by
    change c.1.1 T T' T'' φ ψ - d1 F f T T' T'' φ ψ = 0
    rw [hf']; exact sub_self _
  have ha : ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''),
      c1.1.2.1 T T'' (φ ≫ ψ) = p1 F ψ (c1.1.2.1 T T' φ) + c1.1.2.1 T' T'' ψ := fun T T' T'' φ ψ ↦ by
    have := cechDeRhamTotalCocyclesTwo.one c1 φ ψ
    rwa [z1, map_zero, add_zero] at this
  obtain ⟨t, ht⟩ := hmu2 _ ha
  obtain ⟨β, hβ⟩ := beta_of τ hτ mu hmu t
  obtain ⟨u, hu⟩ : ∃ u, u = LinearMap.rTensor (Glob1 F) (H1.mk F) t := ⟨_, rfl⟩
  rw [← hu] at hβ
  let b2 : cechDeRhamTotalCocyclesTwo F := ⟨dTot1 F (0, β), dTot1_mem F _⟩
  let c2 : cechDeRhamTotalCocyclesTwo F := c1 - Lc hcl τ u - b2
  have hL := Lc_spec hcl τ mu hmu u
  have z2 : ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''), c2.1.1 T T' T'' φ ψ = 0 := fun T T' T'' φ ψ ↦ by
    change c1.1.1 T T' T'' φ ψ - (Lc hcl τ u).1.1 T T' T'' φ ψ - d1 F 0 T T' T'' φ ψ = 0
    rw [z1, hL.1, map_zero]
    simp
  have a2 : ∀ (T T' : C) (φ : T ⟶ T'), c2.1.2.1 T T' φ = 0 := fun T T' φ ↦ by
    change c1.1.2.1 T T' φ - (Lc hcl τ u).1.2.1 T T' φ -
      (β T' - p1 F φ (β T) - D R _ ((0 : C1 F) T T' φ)) = 0
    rw [hL.2, ← ht, hβ]
    simp
  have g : ∀ (T T' : C) (φ : T ⟶ T'), c2.1.2.2 T' = pOm F 2 φ (c2.1.2.2 T) := fun T T' φ ↦ by
    have := cechDeRhamTotalCocyclesTwo.two c2 φ
    rwa [a2, map_zero, add_zero] at this
  obtain ⟨x, hx⟩ := hnus _ g
  have e : c2 = Nc hcl x := by
    refine Subtype.ext ?_
    rw [Nc_spec hcl nu hnu x, hx]
    exact Tot2.ext z2 a2 fun _ ↦ rfl
  refine ⟨u, x, ?_⟩
  have e1 : Hyp2.mk F b1 = 0 := Hyp2.mk_eq_zero.2 ⟨_, rfl⟩
  have e2 : Hyp2.mk F b2 = 0 := Hyp2.mk_eq_zero.2 ⟨_, rfl⟩
  have e3 : c = Nc hcl x + Lc hcl τ u + b1 + b2 := by
    rw [← e]
    exact add_rearr c b1 _ b2
  rw [e3, map_add (f := _), map_add (f := _), map_add (f := _), e1, e2, add_zero, add_zero, add_comm]


set_option maxHeartbeats 1000000 in
theorem wedgeHyp_of (hproj : Module.Projective R (H1 F)) (hcl : Closed1 F = ⊤)
    (hs : Function.Surjective (toO F)) (hW : Wedge F) (halt : ∀ c, cupHyp F c c = 0)
    (mu : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F)
    (hmu : ∀ (f : Z1 F) (w : Glob1 F) (T T' : C) (φ : T ⟶ T'), mu (f ⊗ₜ w) T T' φ = f.1 T T' φ • w.1 T')
    (hmu2 : ∀ a : A1 F, (∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''),
      a T T'' (φ ≫ ψ) = p1 F ψ (a T T' φ) + a T' T'' ψ) → ∃ t, mu t = a)
    (hmu3 : ∀ (t : Z1 F ⊗[R] Glob1 F) (β : A0 F),
      (∀ (T T' : C) (φ : T ⟶ T'), mu t T T' φ = β T' - p1 F φ (β T)) →
        (H1.mk F).rTensor (Glob1 F) t = 0)
    (nu : ⋀[R]^2 (Glob1 F) →ₗ[R] W0 F 2)
    (hnu : ∀ (a b : Glob1 F) (T : C), nu (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (hnui : Function.Injective nu)
    (hnus : ∀ w : W0 F 2, (∀ (T T' : C) (φ : T ⟶ T'), w T' = pOm F 2 φ (w T)) → ∃ t, nu t = w) :
    WedgeHyp F := by
  obtain ⟨E, hE⟩ := hW
  obtain ⟨τ, hτ'⟩ := Module.projective_lifting_property (toO F ∘ₗ Hyp1.mk F)
    (LinearMap.id : H1 F →ₗ[R] H1 F) (hs.comp (Hyp1.mk_surjective F))
  have hτ : ∀ v, H1.mk F (cechDeRhamTotalCocyclesOne.fn F (τ v)) = v := fun v ↦ LinearMap.congr_fun hτ' v
  let e : ⋀[R]^2 (Hyp1 F) →ₗ[R] Hyp2 F := ext2 (cupHyp F) halt
  let σ : H1 F →ₗ[R] Hyp1 F := Hyp1.mk F ∘ₗ τ
  let k : Glob1 F →ₗ[R] Hyp1 F := Hyp1.mk F ∘ₗ cl hcl
  have he : ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cupHyp F a b := characterExtensionRep_apply _ _
  have he' : ∀ a b, e (wB R _ a b) = cupHyp F a b := he
  have hσ : ∀ v, toO F (σ v) = v := hτ
  have hs2 : ∀ y, rho F (e (exteriorPower.map 2 σ y)) = E y := by
    have h : rho F ∘ₗ e ∘ₗ exteriorPower.map 2 σ = E.toLinearMap := grpScheme_square_hom_ext_fst_snd fun a b ↦ by
      simp only [LinearMap.comp_apply, exterior_square_map_apply, LinearEquiv.coe_coe, he', rho_cup, hE, hσ]
    exact LinearMap.congr_fun h
  have hs1 : ∀ u, e (mix σ k u) = Hyp2.mk F (Lc hcl τ u) := by
    have h : e ∘ₗ mix σ k = Hyp2.mk F ∘ₗ Lc hcl τ := TensorProduct.ext' fun v w ↦ he' _ _
    exact LinearMap.congr_fun h
  have hs0 : ∀ x, e (exteriorPower.map 2 k x) = Hyp2.mk F (Nc hcl x) := by
    have h : e ∘ₗ exteriorPower.map 2 k = Hyp2.mk F ∘ₗ Nc hcl := grpScheme_square_hom_ext_fst_snd fun a b ↦ by
      simp only [LinearMap.comp_apply, exterior_square_map_apply, he', Nc_apply]
      exact cupHyp_mk F _ _
    exact LinearMap.congr_fun h
  have hspan : ∀ a, ∃ v w, a = σ v + k w := by
    intro a
    have h : a - σ (toO F a) ∈ Fil1 F := by
      change toO F _ = 0
      rw [map_sub, hσ, sub_self]
    rw [Fil1_eq_range] at h
    obtain ⟨c, hc⟩ := h
    refine ⟨toO F a, c.1, ?_⟩
    have hk : k c.1 = ofForm F c := rfl
    rw [hk, hc]
    abel
  have hinj : Function.Injective e := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, u, z, rfl⟩ := decomp σ k hspan x
    rw [map_add (f := _), map_add (f := _), hs1, hs0] at hx
    have hy : y = 0 := by
      have h : rho F (e (exteriorPower.map 2 σ y) + Hyp2.mk F (Lc hcl τ u) + Hyp2.mk F (Nc hcl z)) = 0 := by
        rw [hx, map_zero]
      rw [map_add (f := _), map_add (f := _), hs2, rho_mk, rho_mk, form_component_of_cup_class_zero hcl τ mu hmu, form_component_of_wedge_class_zero hcl nu hnu, map_zero,
        add_zero, add_zero] at h
      exact E.map_eq_zero_iff.1 h
    subst hy
    rw [map_zero, map_zero, zero_add, ← map_add (f := _), Hyp2.mk_eq_zero] at hx
    obtain ⟨c, hc⟩ := hx
    have hu := inj_L hs hcl τ hτ mu hmu hmu3 nu hnu u z c hc
    subst hu
    have hc2 : dTot1 F c = (0, 0, nu z) := by
      rw [hc, map_zero, zero_add, Nc_spec hcl nu hnu z]
    have hz : z = 0 := hnui ((inj_N hs hcl c _ hc2).trans (map_zero nu).symm)
    subst hz
    simp
  have hsurj : Function.Surjective e := by
    intro h
    obtain ⟨c, rfl⟩ := Hyp2.mk_surjective F h
    obtain ⟨y, hy⟩ : ∃ y, E y = rho F (Hyp2.mk F c) := E.surjective _
    obtain ⟨c', hc'⟩ := Hyp2.mk_surjective F (Hyp2.mk F c - e (exteriorPower.map 2 σ y))
    have h0 : H2.mk F (fn2 F c') = 0 := by
      rw [← rho_mk, hc', map_sub, hs2, hy, sub_self]
    obtain ⟨u, x, hux⟩ := surj_step hcl τ hτ mu hmu hmu2 nu hnu hnus c' h0
    refine ⟨exteriorPower.map 2 σ y + mix σ k u + exteriorPower.map 2 k x, ?_⟩
    rw [map_add (f := _), map_add (f := _), hs1, hs0, add_assoc, ← hux, hc']
    exact add_sub_cancel _ _
  exact ⟨LinearEquiv.ofBijective e ⟨hinj, hsurj⟩, he⟩

theorem hyp2St : OneFormCohSt → TwoFormCohSt → H2FieldHypothesis := by
  intro h1 h2 R _ C _ F hF _ hproj hcl hs hW halt
  obtain ⟨mu, hmu, hmu2, hmu3⟩ := h1 R C F hF
  obtain ⟨nu, hnu, hnui, hnus⟩ := h2 R C F hF
  exact wedgeHyp_of hproj hcl hs hW halt mu hmu hmu2 hmu3 nu hnu hnui hnus

end Main

end GlobalTheory.CompanionTheory.HypWedge
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.AbelianHodgeDeRham
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.Development
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

namespace MainStatements.Hodge.Free

structure Chapters : Prop where
  dict : DictSt
  cx : CxSt
  low : DictSt → LowSt
  htpy : CxSt → HtpySt
  qcalc : CxSt → QCalcSt
  fubini : CxSt → FubiniSt
  affacyc : CxSt → HtpySt → AffAcycSt
  descent : CxSt → HtpySt → QCalcSt → FubiniSt → AffAcycSt → DescentSt
  sysbc : DescentSt → LowSt → SysBCSt
  stein : SteinSt
  cot : CotSt
  par : CotSt → SteinSt → ParSt
  axo : DescentSt → LowSt → SysBCSt → SteinSt → AxOSt
  axform : CotSt → SteinSt → ParSt → AxFormSt
  cmp : CxSt → CmpSt
  fincoh : CmpSt → FinCohSt
  van : CxSt → CmpSt → VanSt
  perfnoeth : CxSt → DictSt → PerfNoethSt
  perfbase : PerfBaseSt
  perfh1 : PerfectH1BaseChange
  perfh2 : PerfectH2FromFibres
  wedgeof : LowSt → WedgeOfSt
  hopffield : CxSt → DictSt → LowSt → HopfFieldSt
  oneform : OneFormCohSt
  twoform : TwoFormCohSt
  closed : TwoFormCohSt → ClosedSt
  lift : OneFormCohSt → TwoFormCohSt → LiftSt
  alt : OneFormCohSt → TwoFormCohSt → AltSt
  hyp2 : OneFormCohSt → TwoFormCohSt → H2FieldHypothesis
  hopf : HtpySt → QCalcSt → FubiniSt → AffAcycSt → DescentSt → LowSt → AxOSt → HopfSt
  bi : DescentSt → LowSt → SteinSt → ParSt → AxOSt → AxFormSt → BiSt
  formbc : SteinSt → ParSt → FormBCSt
  oside : DescentSt → LowSt → SysBCSt → PerfSt → SteinSt → H1StructureBundle → WedgeFieldSt → HopfSt → PerfectH1BaseChange → PerfectH2FromFibres → WedgeOfSt → OBCSt ∧ WedgeSt
  perf : GlobalTheory.SpreadingModels.SchemeModels → GlobalTheory.SpreadingModels.Spreads (fun _ _ f => Smooth f) → GlobalTheory.SpreadingModels.Spreads (fun _ _ f => IsProper f) → DescentSt → LowSt → SysBCSt → FinCohSt → PerfNoethSt → PerfBaseSt → PerfSt
  hopfle : CxSt → DictSt → LowSt → HopfLeSt
  h1le : DescentSt → LowSt → SteinSt → VanSt → HopfSt → HopfLeSt → PositivityTheory.ObstructionTrivialLocus.H1StructureDimLe
  wedgefield2 : DescentSt → LowSt → SteinSt → H1StructureFieldDim → VanSt → HopfSt → HopfFieldSt → WedgeFieldSt
  noprim : DescentSt → LowSt → SteinSt → AxOSt → WedgeFieldSt → NoPrimSt
  smalllift : DescentSt → LowSt → SysBCSt → AxOSt → NoPrimSt → SmallLiftSt
  perfvb : PerfVBSt
  h1all : DescentSt → LowSt → SysBCSt → PerfSt → SteinSt → H1StructureFieldDim → SmallLiftSt → PerfVBSt → H1StructureBundle
  flatbc : DescentSt → LowSt → SysBCSt → FlatBCSt
  feweqn : FewEqSt
  stalkdim : StalkDimSt
  h1ge : PositivityTheory.ObstructionTrivialLocus.TrivLocus → PositivityTheory.ObstructionTrivialLocus.KFinite → FlatBCSt → FewEqSt → StalkDimSt → H1DimGeAbelianDim
  h1field : FlatBCSt → PositivityTheory.ObstructionTrivialLocus.H1StructureDimLe → H1DimGeAbelianDim → H1StructureFieldDim
  final : SteinSt → ParSt → H1StructureBundle → DegenSt → WedgeHypSt → OBCSt → FormBCSt → GlobalTheory.Published.AbelianHodgeDeRham

theorem wedge_alt {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R} (h : Wedge F)
    (c : H1 F) : cup F c c = 0 := by
  obtain ⟨e, he⟩ := h
  rw [← he, (exteriorPower.ιMulti R 2).map_eq_zero_of_eq ![c, c] (i := 0) (j := 1) rfl (by decide), map_zero]

theorem Chapters.print (h : Chapters) (h₁ : GlobalTheory.SpreadingModels.SchemeModels)
    (h₂ : GlobalTheory.SpreadingModels.Spreads (fun _ _ f => Smooth f)) (h₃ : GlobalTheory.SpreadingModels.Spreads (fun _ _ f => IsProper f))
    (ht : PositivityTheory.ObstructionTrivialLocus.TrivLocus) (hk : PositivityTheory.ObstructionTrivialLocus.KFinite) : GlobalTheory.Published.AbelianHodgeDeRham := by
  have low := h.low h.dict
  have htpy := h.htpy h.cx
  have qc := h.qcalc h.cx
  have fub := h.fubini h.cx
  have aff := h.affacyc h.cx htpy
  have des := h.descent h.cx htpy qc fub aff
  have sbc := h.sysbc des low
  have par := h.par h.cot h.stein
  have axo := h.axo des low sbc h.stein
  have axf := h.axform h.cot h.stein par
  have cmp := h.cmp h.cx
  have hopf := h.hopf htpy qc fub aff des low axo
  have perf := h.perf h₁ h₂ h₃ des low sbc (h.fincoh cmp) (h.perfnoeth h.cx h.dict) h.perfbase
  have van := h.van h.cx cmp
  have fbc := h.flatbc des low sbc
  have h1f := h.h1field fbc (h.h1le des low h.stein van hopf (h.hopfle h.cx h.dict low))
    (h.h1ge ht hk fbc h.feweqn h.stalkdim)
  have wf := h.wedgefield2 des low h.stein h1f van hopf (h.hopffield h.cx h.dict low)
  have h1 := h.h1all des low sbc perf h.stein h1f
    (h.smalllift des low sbc axo (h.noprim des low h.stein axo wf)) h.perfvb
  obtain ⟨obc, w⟩ := h.oside des low sbc perf h.stein h1 wf hopf h.perfh1 h.perfh2 (h.wedgeof low)
  have bi := h.bi des low h.stein par axo axf
  have fr : AllAb fun _ _ A _ _ ↦ Framed (OAff A.hom) := fun R _ A _ g hA hg ↦
    ⟨h.stein R A g hA hg, (par R A g hA hg).1, (par R A g hA hg).2.1, (par R A g hA hg).2.2.1⟩
  have deg : DegenSt := fun R _ A _ g hA hg ↦
    have c := h.closed h.twoform R _ _ (fr R A g hA hg) (bi R A g hA hg)
    ⟨c, h.lift h.oneform h.twoform R _ _ (fr R A g hA hg) (bi R A g hA hg) c⟩
  have wh : WedgeHypSt := fun R _ A _ g hA hg ↦
    h.hyp2 h.oneform h.twoform R _ _ (fr R A g hA hg) (h1 R A g hA hg).1 (h1 R A g hA hg).2.1 (deg R A g hA hg).1
      (deg R A g hA hg).2 (w R A g hA hg)
      (h.alt h.oneform h.twoform R _ _ (fr R A g hA hg) (bi R A g hA hg) (deg R A g hA hg).1 (deg R A g hA hg).2
        (wedge_alt (w R A g hA hg)))
  exact h.final h.stein par h1 deg wh obc (h.formbc h.stein par)

end MainStatements.Hodge.Free
end

namespace MainStatements.Hodge.Free

theorem abelianHodgeDeRham' : Chapters := by
  exact {
    dict := GlobalTheory.CompanionTheory.Dict.dictSt
    cx := GlobalTheory.CompanionTheory.HodgeCx.cxSt
    low := GlobalTheory.CompanionTheory.HodgeLow.lowSt_of_dictSt
    htpy := GlobalTheory.CompanionTheory.Hodge.htpySt_of_cxSt
    qcalc := GlobalTheory.CompanionTheory.QCalc.qCalcSt
    fubini := GlobalTheory.CompanionTheory.NerveCoh.fubiniSt
    affacyc := GlobalTheory.CompanionTheory.AffAcyc.main
    descent := GlobalTheory.CompanionTheory.Descent.descentSt
    sysbc := GlobalTheory.CompanionTheory.SysBC.sysBCSt
    stein := GlobalTheory.CompanionTheory.Hodge.stein_holds
    cot := GlobalTheory.CompanionTheory.Cot.cotSt
    par := GlobalTheory.CompanionTheory.AbForms.parSt
    axo := GlobalTheory.CompanionTheory.Axis.axOSt
    axform := GlobalTheory.CompanionTheory.AxForm.axFormSt
    cmp := GlobalTheory.CompanionTheory.Hodge.Nerve.cmpSt_of_cxSt
    fincoh := GlobalTheory.CompanionTheory.Hodge.finCohSt_of_cmpSt
    van := GlobalTheory.CompanionTheory.Hodge.vanSt
    perfnoeth := GlobalTheory.CompanionTheory.PerfN.perfNoeth
    perfbase := GlobalTheory.CompanionTheory.PerfExt.main
    perfh1 := GlobalTheory.CompanionTheory.PerfectFirstCohomology.perfect_first_cohomology_base_change
    perfh2 := GlobalTheory.CompanionTheory.PerfectSecondCohomology.perfect_second_cohomology_from_fibres
    wedgeof := GlobalTheory.CompanionTheory.WedgeOf.wedgeOf_of_low
    hopffield := GlobalTheory.CompanionTheory.HopfC.hopfFieldSt
    oneform := GlobalTheory.CompanionTheory.OneFormCoh.oneFormCohSt
    twoform := GlobalTheory.CompanionTheory.HodgeTwoForm.twoFormCohSt
    closed := GlobalTheory.CompanionTheory.HodgeClosed.closedSt_of_twoFormCohSt
    lift := GlobalTheory.CompanionTheory.Hodge.LiftO.lift_of_forms
    alt := GlobalTheory.CompanionTheory.HodgeAlt.altSt
    hyp2 := GlobalTheory.CompanionTheory.HypWedge.hyp2St
    hopf := GlobalTheory.CompanionTheory.HopfSys.hopfSt
    bi := GlobalTheory.CompanionTheory.GroupLaw.bilinear_statement_with_descent_hypotheses
    formbc := GlobalTheory.CompanionTheory.Hodge.FormBC.formBC
    oside := GlobalTheory.CompanionTheory.HodgeO.oBC_wedge
    perf := GlobalTheory.CompanionTheory.PerfModels.perfSt_of_spreads
    final := GlobalTheory.CompanionTheory.HodgeAssembly.abelianHodgeDeRham_of_statements
    hopfle := GlobalTheory.CompanionTheory.HopfLe.hopfLeSt
    h1le := GlobalTheory.CompanionTheory.Hodge.FirstCohomologyUpperBounds.h1Le
    wedgefield2 := GlobalTheory.CompanionTheory.Hodge.WedgeFieldGeo.wedgeField_of_field
    noprim := MainStatements.Hodge.Pf.noprim
    smalllift := GlobalTheory.CompanionTheory.SmallLift.main
    perfvb := GlobalTheory.CompanionTheory.PerfVB.perfVB
    h1all := GlobalTheory.CompanionTheory.Hodge.FirstCohomologyVectorBundle.first_cohomology_vector_bundle_rank
    flatbc := GlobalTheory.CompanionTheory.Hodge.FlatBase.flatBC
    feweqn := GlobalTheory.CompanionTheory.FewEq.fewEq
    stalkdim := MainStatements.Hodge.Pf.stalkdim
    h1ge := GlobalTheory.CompanionTheory.FirstCohomologyLowerBound.first_cohomology_dimension_lower_bound
    h1field := GlobalTheory.CompanionTheory.AbelianFirstCohomologyOverField.first_cohomology_rank_over_field
  }

theorem abelianHodgeDeRham : GlobalTheory.Published.AbelianHodgeDeRham :=
  abelianHodgeDeRham'.print GlobalTheory.CompanionTheory.NoethApprox.schemeModels GlobalTheory.CompanionTheory.SmoothSpread.smooth_spreads GlobalTheory.CompanionTheory.SpreadingModels.properSpreads
    GlobalTheory.CompanionTheory.TrivLoc.trivLocus GlobalTheory.CompanionTheory.KLFinite.kFinite

end MainStatements.Hodge.Free
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.PageOf
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR FubiniStudyChowHeightFormula₂.Hdr

attribute [local instance] Over.cartesianMonoidalCategory

namespace MainStatements.Hodge.Free

theorem page_of_hodge (H : GlobalTheory.Published.AbelianHodgeDeRham) : AbelianDeRhamPage := by
  intro R _ A _ g hA hg
  obtain ⟨⟨a1, a2, a3⟩, hw, ⟨f1, f2, f3⟩, ⟨o1, o2, -⟩, ⟨hcl, hinj, hsurj⟩, hbc⟩ := H R A g hA hg
  let i := formEquiv A.hom hcl hinj
  have hk : Hodge1 A.hom = LinearMap.ker (toHO1 A.hom) := (cechHodgeFiltration_eq_range A.hom).symm
  let q : (HH1 A.hom ⧸ Hodge1 A.hom) ≃ₗ[R] HO1 A.hom :=
    (Submodule.quotEquivOfEq _ _ hk).trans ((toHO1 A.hom).quotKerEquivOfSurjective hsurj)
  refine ⟨hw, ⟨⟨a1, a2⟩, a3⟩, ⟨hcl, hinj, ⟨⟨Module.Finite.equiv i, Module.Projective.of_equiv i⟩,
      fun p ↦ by rw [← Module.rankAtStalk_eq_of_equiv i, f3]⟩,
      Module.Finite.equiv q.symm, Module.Projective.of_equiv q.symm⟩,
    ⟨by rw [hk]; exact LinearMap.exact_subtype_ker_map _, hsurj⟩, fun R' _ _ X' s' φ h ↦ ?_⟩
  obtain ⟨b1, ⟨e, he⟩, b3⟩ := hbc R' X' s' φ h
  refine ⟨b1, ?_, b3⟩
  obtain ⟨_, hA'⟩ := exists_abelian A hA h
  have hg' : SmoothOfRelativeDimension g (Over.mk s').hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback h hg
  obtain ⟨-, -, -, -, ⟨hcl', hinj', -⟩, -⟩ := H R' (Over.mk s') g hA' hg'
  let i' := formEquiv s' hcl' hinj'
  refine ⟨(LinearEquiv.baseChange R R' _ _ i.symm).trans (e.trans i'), fun c ↦ ?_⟩
  obtain ⟨c, rfl⟩ := i.surjective c
  have k : ((LinearEquiv.baseChange R R' _ _ i.symm).trans (e.trans i')) (1 ⊗ₜ i c) = i' (e (1 ⊗ₜ c)) := by
    simp
  rw [k]
  exact IsPullForm.cl (ω := ⟨c, hcl ▸ trivial⟩) (ω' := ⟨e (1 ⊗ₜ c), hcl' ▸ trivial⟩) (he c)

end MainStatements.Hodge.Free
end
end

namespace MainStatements.Hodge.Free

theorem abelianDeRhamPage : FubiniStudyChowHeightFormula₂.Hdr.AbelianDeRhamPage := page_of_hodge abelianHodgeDeRham

end MainStatements.Hodge.Free
