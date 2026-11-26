module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetNeZeroOfImHermFormIntegralRealBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramSmoothOfHolomorphicFrames
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LargeFor
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TwDatPsiValuesInLL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CubicalStructureSquareTransport
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousLatticeVectorsAlongArc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.UnitHmE
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilPairingExpModelFiberEqAlternatingForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivativesSeparateLieBasisCoeffsCartesian
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivativesSeparateLieBasisCoeffsCartesian
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
open MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace GlobalTheory.ArcLieCoord

attribute [local instance] Over.cartesianMonoidalCategory

theorem zeroPt_sc {S : Type} [CommRing S] (c : S) : GlobalTheory.PowLie.zeroPt S ≫ GlobalTheory.PowLie.sc c = GlobalTheory.PowLie.zeroPt S := by
  ext1
  simp only [Over.comp_left, GlobalTheory.PowLie.zeroPt, GlobalTheory.PowLie.sc, Over.homMk_left]
  rw [← spMap_comp]
  congr 1
  refine RingHom.ext fun r => ?_
  simp [epsScaleR]

theorem isTangent_prod {S : Type} [CommRing S] {G' : Over (Sp S)} [GrpObj G'] [IsCommMonObj G'] {n : ℕ}
    (v : Fin n → (epsR S ⟶ G')) (hv : ∀ k, IsTangent (v k)) (c : Fin n → S) :
    IsTangent (∏ k, GlobalTheory.PowLie.sc (c k) ≫ v k) := by
  rw [GlobalTheory.PowLie.isTangent_iff]
  have e := map_prod (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom (G := G') (GlobalTheory.PowLie.zeroPt S)) (fun k => GlobalTheory.PowLie.sc (c k) ≫ v k) Finset.univ
  refine (e.trans ?_)
  refine (Finset.prod_eq_one fun k _ => ?_).trans rfl
  change GlobalTheory.PowLie.zeroPt S ≫ GlobalTheory.PowLie.sc (c k) ≫ v k = 1
  rw [← Category.assoc, zeroPt_sc, (GlobalTheory.PowLie.isTangent_iff _).1 (hv k)]
  rfl

theorem sep : ∀ {S : Type} [CommRing S] {X : Scheme.{0}} {x : Sp S ⟶ X} {G : Over X} {G' : Over (Sp S)} [GrpObj G] [GrpObj G'] [IsCommMonObj G'] {φ : G'.left ⟶ G.left}, IsGrpPullback G' G x φ → ∀ {n : ℕ} (v : Fin n → (epsR S ⟶ G')), IsLieBasis v → ∀ {V : G.left.Opens}, IsAffineOpen V → ⊤ ≤ ((η[G']).left ≫ φ) ⁻¹ᵁ V → ∀ (b : Fin n → S), (∀ f : Γ(G.left, V), ∑ k, b k * (valR ((v k).left ≫ φ) V f).snd = 0) → b = 0 := by
  intro S _ X x G G' _ _ _ φ h n v hv V hA hV b hb
  set w₀ : epsR S ⟶ G' := ∏ k, GlobalTheory.PowLie.sc (b k) ≫ v k with hw₀
  set w₁ : epsR S ⟶ G' := ∏ k, GlobalTheory.PowLie.sc ((0 : Fin n → S) k) ≫ v k with hw₁
  have c₀ : IsLieComb b v w₀ := (GlobalTheory.PowLie.isLieComb_iff_prod b v w₀).2 rfl
  have c₁ : IsLieComb 0 v w₁ := (GlobalTheory.PowLie.isLieComb_iff_prod 0 v w₁).2 rfl
  have t₀ : IsTangent w₀ := isTangent_prod v hv.1 b
  have t₁ : IsTangent w₁ := isTangent_prod v hv.1 0
  have l₀ := tan_le h w₀ t₀ V hV
  have l₁ := tan_le h w₁ t₁ V hV
  have fst_eq : ∀ (w : epsR S ⟶ G'), IsTangent w → ∀ f : Γ(G.left, V),
      (valR (w.left ≫ φ) V f).fst = valR ((η[G']).left ≫ φ) V f := by
    intro w hw f
    have e1 := GlobalTheory.HolHom.valR_spMap (TrivSqZeroExt.fstHom S S S).toRingHom (w.left ≫ φ) V (tan_le h w hw V hV) f
    have e2 : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w.left ≫ φ = (η[G']).left ≫ φ := by
      rw [← Category.assoc]
      exact congrArg (· ≫ φ) hw
    rw [e2] at e1
    rw [e1]
    rfl
  have e : w₀.left ≫ φ = w₁.left ≫ φ := by
    refine GlobalTheory.HolHom.point_ext hA l₀ l₁ fun f => ?_
    refine TrivSqZeroExt.ext ((fst_eq w₀ t₀ f).trans (fst_eq w₁ t₁ f).symm) ?_
    rw [comb_snd h v hv.1 b w₀ c₀ V hV f, comb_snd h v hv.1 0 w₁ c₁ V hV f, hb f]
    simp
  have hw : w₀ = w₁ := ReciprocityTheory.ChartRestriction.G.Chart.inj_over h e
  exact (hv.2 w₀ t₀).unique c₀ (hw ▸ c₁)

end GlobalTheory.ArcLieCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivativesSeparateLieBasisCoeffsCartesianStatement
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivatives_separate_lieBasis_coeffs_cartesian : ∀ {S : Type} [CommRing S] {X : Scheme.{0}} {x : Sp S ⟶ X} {G : Over X} {G' : Over (Sp S)} [GrpObj G] [GrpObj G'] [IsCommMonObj G'] {φ : G'.left ⟶ G.left}, IsGrpPullback G' G x φ → ∀ {n : ℕ} (v : Fin n → (epsR S ⟶ G')), IsLieBasis v → ∀ {V : G.left.Opens}, IsAffineOpen V → ⊤ ≤ ((η[G']).left ≫ φ) ⁻¹ᵁ V → ∀ (b : Fin n → S), (∀ f : Γ(G.left, V), ∑ k, b k * (valR ((v k).left ≫ φ) V f).snd = 0) → b = 0 := by
  first | exact @GlobalTheory.ArcLieCoord.sep | exact GlobalTheory.ArcLieCoord.sep | (intros; apply GlobalTheory.ArcLieCoord.sep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearFormFromFinsupp
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

noncomputable section

namespace GlobalTheory.PolCell

variable {X : Type} [AddCommGroup X]

theorem linW_single_apply (p : X × X) (k : ℤ) (β : LinearMap.BilinForm ℤ X) :
    linW (Finsupp.single p k) β = k * β p.1 p.2 := by
  rw [linW_apply, Finsupp.sum_single_index (by simp)]

theorem linW_add_apply (w v : (X × X) →₀ ℤ) (β : LinearMap.BilinForm ℤ X) :
    linW (w + v) β = linW w β + linW v β := by
  simp only [linW_apply]
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)

theorem linW_finset_sum_apply {ι : Type} (s : Finset ι) (g : ι → (X × X) →₀ ℤ) (β : LinearMap.BilinForm ℤ X) :
    linW (∑ i ∈ s, g i) β = ∑ i ∈ s, linW (g i) β := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [linW_apply]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, linW_add_apply, ih]

theorem bilin_eq_zero_of_mem_torsion_left (β : LinearMap.BilinForm ℤ X) {t : X}
    (ht : t ∈ Submodule.torsion ℤ X) (y : X) : β t y = 0 := by
  obtain ⟨n, hn⟩ := (Submodule.mem_torsion_iff t).mp ht
  rw [Submonoid.smul_def] at hn
  have h := LinearMap.map_smul₂ β (n : ℤ) t y
  rw [hn, map_zero, LinearMap.zero_apply, eq_comm, smul_eq_zero] at h
  exact h.resolve_left (nonZeroDivisors.coe_ne_zero n)

theorem bilin_eq_zero_of_mem_torsion_right (β : LinearMap.BilinForm ℤ X) (x : X) {t : X}
    (ht : t ∈ Submodule.torsion ℤ X) : β x t = 0 := by
  obtain ⟨n, hn⟩ := (Submodule.mem_torsion_iff t).mp ht
  rw [Submonoid.smul_def] at hn
  have h := (β x).map_smul (n : ℤ) t
  rw [hn, map_zero, eq_comm, smul_eq_zero] at h
  exact h.resolve_left (nonZeroDivisors.coe_ne_zero n)

theorem exists_linW_eq : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
    ∃ w : (X × X) →₀ ℤ, linW w = ℓ := by
  intro X _ _ ℓ
  classical
  let T := Submodule.torsion ℤ X
  let b := Module.Free.chooseBasis ℤ (X ⧸ T)
  let e : Module.Free.ChooseBasisIndex ℤ (X ⧸ T) → X := fun i => (T.mkQ_surjective (b i)).choose
  have he : ∀ i, T.mkQ (e i) = b i := fun i => (T.mkQ_surjective (b i)).choose_spec
  let c : Module.Free.ChooseBasisIndex ℤ (X ⧸ T) → X →ₗ[ℤ] ℤ := fun i => (b.coord i).comp T.mkQ
  have hdec : ∀ x, x - ∑ i, c i x • e i ∈ T := by
    intro x
    refine (Submodule.Quotient.mk_eq_zero T).mp ?_
    change T.mkQ _ = 0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum]
    simp only [map_smul, he, c, LinearMap.comp_apply, Module.Basis.coord_apply]
    rw [b.sum_repr, sub_self]
  have hβ : ∀ β : LinearMap.BilinForm ℤ X,
      β = ∑ i, ∑ j, β (e i) (e j) • (c i).smulRight (c j) := by
    intro β
    ext x y
    have h1 : β x y = β (∑ i, c i x • e i) y := by
      have := bilin_eq_zero_of_mem_torsion_left β (hdec x) y
      rwa [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    have h2 : ∀ x', β x' y = β x' (∑ j, c j y • e j) := by
      intro x'
      have := bilin_eq_zero_of_mem_torsion_right β x' (hdec y)
      rwa [map_sub, sub_eq_zero] at this
    rw [h1, h2]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, smul_eq_mul]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  refine ⟨∑ i, ∑ j, Finsupp.single (e i, e j) (ℓ ((c i).smulRight (c j))), ?_⟩
  ext β
  rw [linW_finset_sum_apply]
  conv_rhs => rw [hβ β]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, smul_eq_mul, linW_finset_sum_apply, linW_single_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.PolCell
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIndexBoundCoreOverExactSmallField
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetOfKer
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RefCharValues

theorem sign_zpow_even (z : ℂ) (h : z ≠ 0) (k : ℤ) :
    (z / ((‖z‖ : ℝ) : ℂ)) ^ (2 * k) = (z / starRingEnd ℂ z) ^ k := by
  rw [zpow_mul]
  congr 1
  have h1 : (‖z‖ : ℂ) ^ 2 = z * starRingEnd ℂ z := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
  have h2 : starRingEnd ℂ z ≠ 0 := by simpa using h
  rw [zpow_ofNat, div_pow, h1]
  field_simp

end GlobalTheory.RefCharValues
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIndexBoundCoreOverExactSmallField
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.AtMember
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoreExact

theorem locK_mem_of_values : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (M : IntermediateField ℚ ℂ), GlobalTheory.Mem.Fld.valueField χ 0 ≤ M → (∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) ∈ M) → ∀ (P : HeightOneSpectrum (𝓞 L)) (k : Lˣ), ((χ.locK P k : ℂˣ) : ℂ) ∈ M :=
  fun _ _ _ χ _ hv hi P _ => GlobalTheory.HeckeValField.mem_unitsIn.1 (GlobalTheory.HeckeValField.loc_mem χ hv hi P _)

theorem char_mem_of_values : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), Formalism.IndefR.Links.ChrEq c χ → ∀ M : IntermediateField ℚ ℂ, GlobalTheory.Mem.Fld.valueField χ 0 ≤ M → (∀ k : D.host.Eˣ, ((χ.inf k : ℂˣ) : ℂ) ∈ M) → ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ((c x : Circle) : ℂ) ∈ M := by
  intro D c χ hc M hv hi x hx
  obtain ⟨j, j1, j2, j3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D j j1 j2
    (GlobalTheory.PlaceIdem.exists_isPlIdem D j j1 j2 j3) c χ hc
  obtain ⟨S, k, hS, hS'⟩ := finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((j : _ →+* _).comp (finPart D)).toMonoidHom x)
  rw [hprod x hx S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS']
  exact prod_mem fun P _ => locK_mem_of_values D.host.E χ M hv hi P (k P)

theorem KsC_eq (X : Stages) : X.B.KsC = FO X.toD7 := by
  ext z
  rw [Base.mem_KsC, mem_FO_assembled_iff]

theorem exists_core_exact : ∀ (X : Stages) (f : Fr X.B.toPre), Fld.charField f ≤ X.B.KsC → Formalism.L2.Host.ValLL0 X.toD7 (Fr.at X f) → VolTieG X.toD7 → ∃ (C : CoreJ X.toD7) (_ : Algebra C.Q.c.F X.toD7.what₂.LL), CorePin C.toCore (Fr.at X f).P.pb ∧ (∀ y : C.Q.c.F, X.B.embLL (algebraMap C.Q.c.F X.toD7.what₂.LL y) = (y : ℂ)) ∧ (∀ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y ∈ X.B.LL0) ∧ (∀ x ∈ X.B.Ks, ∃ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y = x) ∧ (∀ x : X.toD7.host.E, ∃ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y = X.toD7.embE x) ∧ LawsJ C ∧ Formalism.IndefR.FWT.AlgTie C ∧ Formalism.L2.Host.ValLL X.toD7 (Fr.at X f) ∧ ∀ (T' : Type) (L : Formalism.IndefR.Links.LevCh X.toD7 T') (μ : T'), L.Is μ → L.C = Fr.at X f → ∀ (i : Fin X.toD7.R.m) (x : (AE X.toD7)ˣ), infPart X.toD7 (x : AE X.toD7) = 1 → ∃ y : C.Q.c.F, ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = X.toD7.what₂.embLL (algebraMap C.Q.c.F X.toD7.what₂.LL y) := by
  intro X f hch hv _
  obtain ⟨J, hJ, hC, hCan, hp, hpq, -⟩ := GlobalTheory.FinalJoin2.exists_coreJ_of_chiOK_noVol X.toD7 (hermitianCodeWordStages_ringOfIntegers_full X)
    (hermitianCodeWordStages_has_rootOfUnity X) f.P.pb f.P.pb_over _ (GlobalTheory.FinalJoin.chiOK_one X.toD7)
  have hP : J.Q.PinField := hJ.pins.2.2.1
  letI := Formalism.IndefR.FWT.algTop J hP
  have ha : Formalism.IndefR.FWT.AlgTie J := Formalism.IndefR.FWT.algTie_algTop J hP

  have hemb : ∀ y : J.Q.c.F, X.toD7.what₂.embLL (algebraMap J.Q.c.F X.toD7.what₂.LL y) = (y : ℂ) := by
    have h : X.toD7.what₂.embLL.comp (algebraMap J.Q.c.F X.toD7.what₂.LL) = J.Q.c.F.val.toRingHom :=
      IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 J.Q.c.F)) (RingHom.ext fun x =>
        (congrArg X.toD7.what₂.embLL (ha x)).trans (hP x))
    exact fun y => RingHom.congr_fun h y

  have hle : ∀ y : J.Q.c.F, (y : ℂ) ∈ FO X.toD7 := by
    intro y
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 J.Q.c.F) y
    have hi : ∀ a : 𝓞 J.Q.c.F, ((a : J.Q.c.F) : ℂ) ∈ FO X.toD7 := fun a => by
      rw [← hP a]
      exact phiO_mem_FO _ _
    rw [IntermediateField.coe_div]
    exact div_mem (hi a) (hi b)
  have hge : ∀ z ∈ FO X.toD7, ∃ y : J.Q.c.F, (y : ℂ) = z := by
    intro z hz
    have hle' : FO X.toD7 ≤ J.Q.c.F := by
      rw [FO, IntermediateField.adjoin_le_iff]
      rintro _ ⟨w, rfl⟩
      obtain ⟨x, rfl⟩ := J.Q.eO.surjective w
      have h : X.toD7.what₂.phiO (J.Q.eO x) = ((x : J.Q.c.F) : ℂ) := hP x
      rw [h]
      exact (x : J.Q.c.F).2
    exact ⟨⟨z, hle' hz⟩, rfl⟩

  have hback : ∀ z : X.toD7.what₂.LL, X.toD7.what₂.embLL z ∈ FO X.toD7 →
      ∃ y : J.Q.c.F, algebraMap J.Q.c.F X.toD7.what₂.LL y = z := by
    intro z hz
    obtain ⟨y, hy⟩ := hge _ hz
    exact ⟨y, X.toD7.what₂.embLL.injective ((hemb y).trans hy)⟩
  refine ⟨J, inferInstance, ⟨hC, hCan, hpq, hp⟩, hemb, fun y => ?_, fun x hx => hback x ?_, fun x => hback _ ?_,
    hJ, ha, hv.toLL, ?_⟩
  · obtain ⟨x, hx, hx'⟩ := (mem_FO_assembled_iff X _).1 (hle y)
    have : algebraMap J.Q.c.F X.toD7.what₂.LL y = x := X.toD7.what₂.embLL.injective (((hemb y).trans hx'.symm))
    rw [this]
    exact X.B.Ks_le hx
  · exact (mem_FO_assembled_iff X _).2 ⟨x, hx, rfl⟩
  · rw [show X.toD7.what₂.embLL (X.toD7.embE x) = X.toD7.host.φ₀ x from RingHom.congr_fun X.toD7.embE_φ₀ x]
    exact phi0_mem_coeff_field _ x
  · intro T' L μ hL hLC i x hx
    have hmem : ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) ∈ FO X.toD7 := by
      refine char_mem_of_values X.toD7 _ _ (hL.mu0 i) (FO X.toD7) ?_ ?_ x hx
      · rw [hLC, ← KsC_eq]
        exact (le_iSup (fun j => Fld.valueField (f.mu0 j) 0) i).trans
          (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans hch))))
      · intro k
        obtain ⟨n, hn, hi⟩ := (L.C.isMu0 i).inf
        choose z hz using fun g => (X.toD7.hc (X.toD7.eTau.symm g)).e_int i
        have hnz : n = fun g => 2 * -z g := funext fun g => by
          have h1 := hn g
          simp only [Formalism.L2.Host.eExp, hz] at h1
          exact_mod_cast h1
        rw [hnz] at hi
        rw [hi k]
        refine prod_mem fun g _ => ?_
        rw [GlobalTheory.RefCharValues.sign_zpow_even _ ((map_ne_zero _).2 k.ne_zero)]
        exact zpow_mem (div_mem (conj_mem_FO _ _ _) (conj_mem_FO _ ((starRingEnd ℂ).comp _) _)) _
    obtain ⟨y, hy⟩ := hge _ hmem
    exact ⟨y, by rw [hemb, hy]⟩

end GlobalTheory.CoreExact
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIndexBoundCoreOverExactSmallFieldStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.AtMember
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_value_mem_smallField_of_infPart_eq_one : ∀ (X : Stages) (f : Fr X.B.toPre), Fld.charField f ≤ X.B.KsC → Formalism.L2.Host.ValLL0 X.toD7 (Fr.at X f) → VolTieG X.toD7 → ∃ (C : CoreJ X.toD7) (_ : Algebra C.Q.c.F X.toD7.what₂.LL), CorePin C.toCore (Fr.at X f).P.pb ∧ (∀ y : C.Q.c.F, X.B.embLL (algebraMap C.Q.c.F X.toD7.what₂.LL y) = (y : ℂ)) ∧ (∀ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y ∈ X.B.LL0) ∧ (∀ x ∈ X.B.Ks, ∃ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y = x) ∧ (∀ x : X.toD7.host.E, ∃ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y = X.toD7.embE x) ∧ LawsJ C ∧ Formalism.IndefR.FWT.AlgTie C ∧ Formalism.L2.Host.ValLL X.toD7 (Fr.at X f) ∧ ∀ (T' : Type) (L : Formalism.IndefR.Links.LevCh X.toD7 T') (μ : T'), L.Is μ → L.C = Fr.at X f → ∀ (i : Fin X.toD7.R.m) (x : (AE X.toD7)ˣ), infPart X.toD7 (x : AE X.toD7) = 1 → ∃ y : C.Q.c.F, ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = X.toD7.what₂.embLL (algebraMap C.Q.c.F X.toD7.what₂.LL y) := by
  first | exact @GlobalTheory.CoreExact.exists_core_exact | exact GlobalTheory.CoreExact.exists_core_exact | (intros; apply GlobalTheory.CoreExact.exists_core_exact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadingCoordinatewiseImageEqExtendedData
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadingCoordinatewiseImageEqExtendedData
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.LiftRead

theorem read_of_span {L L' : Type} [Field L] [Field L'] (φ : L →+* L') (σ : L →+* ℂ) (σ' : L' →+* ℂ) (hφ : ∀ x, σ' (φ x) = σ x)
    {n n' : ℕ} (hn : n = n') {H H' : Type} (nH : NormedAddCommGroup H) (nH' : NormedAddCommGroup H')
    (iH : InnerProductSpace ℂ H) (iH' : InnerProductSpace ℂ H') (hH : H' = H) (h1 : HEq nH' nH) (h2 : HEq iH' iH)
    (j : (Fin n → L) →ₛₗ[σ] H) (j' : (Fin n' → L') →ₛₗ[σ'] H') (S : Set (Fin n → L)) (hS : Submodule.span L S = ⊤)
    (hj : ∀ y ∈ S, ∃ y' : Fin n' → L', (∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → σ' (y' k') = σ (y k)) ∧ HEq (j' y') (j y))
    (x : Fin n → L) (x' : Fin n' → L') (hx : ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)) :
    HEq (j' x') (j x) := by
  subst hn hH
  cases h1
  cases h2
  have e : x' = fun k => φ (x k) := funext fun k => hx k k rfl
  subst e
  clear hx
  refine heq_of_eq ?_
  have hx : x ∈ Submodule.span L S := hS ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨y', a, b⟩ := hj y hy
    have e : (fun k => φ (y k)) = y' := funext fun k => σ'.injective ((hφ _).trans (a k k rfl).symm)
    rw [e]
    exact eq_of_heq b
  | zero =>
    have e : (fun k => φ ((0 : Fin n → L) k)) = 0 := by funext k; simp
    rw [e, map_zero, map_zero]
  | add y z _ _ hy hz =>
    have e : (fun k => φ ((y + z) k)) = (fun k => φ (y k)) + fun k => φ (z k) := by funext k; simp
    rw [e, map_add (f := _), map_add (f := _), hy, hz]
  | smul a y _ hy =>
    have e : (fun k => φ ((a • y) k)) = φ a • fun k => φ (y k) := by funext k; simp
    rw [e, map_smulₛₗ, map_smulₛₗ, hy, hφ]


set_option maxHeartbeats 4000000 in
theorem hmod_fields {B B' : Base} (q : B'.toPre = B.toPre) {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'}
    {w : ColW B f T} {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt}
    (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i')
    {S : (w.st Z).toD7.what₂.Tau → SPar} {S' : (w'.st Z').toD7.what₂.Tau → SPar}
    (M : Formalism.IndefR.Mult.DSModel (Wc (w.st Z).toD7 i) S) (M' : Formalism.IndefR.Mult.DSModel (Wc (w'.st Z').toD7 i') S')
    (a : HEq M'.H M.H) (b : HEq M'.nacg M.nacg) (c : HEq M'.ips M.ips) (d : HEq M'.σ M.σ) (l : HEq M'.lam M.lam) (e : HEq M'.ε M.ε)
    (g : HEq M'.fr M.fr) (X : HMod (Formalism.IndefR.Mult.MMap M)) (X' : HMod (Formalism.IndefR.Mult.MMap M')) (hX : HEq X' X) :
    X'.H = X.H ∧ HEq X'.nH X.nH ∧ HEq X'.iH X.iH := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  cases M
  cases M'
  dsimp only at a b c d l e g
  cases a; cases b; cases c; cases d; cases l; cases e; cases g
  have e' : X' = X := eq_of_heq hX
  subst e'
  exact ⟨rfl, HEq.rfl, HEq.rfl⟩


set_option maxHeartbeats 4000000 in
theorem read_extN {B B' : Base} (q : B'.toPre = B.toPre) {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'}
    {w : ColW B f T} {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok}
    {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl} {z : Dat (w.st Z) w.I hX T Wt} {z' : Dat (w'.st Z') w'.I hX' T' Wt'}
    (hE : ExtN z z') (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m) (hj : (j : ℕ) = j')
    (φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL)
    (hφ : ∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x)
    (x : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) (x' : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL)
    (hx : ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)) :
    HEq ((z'.R.FW j').j (w'.st Z').toD7.what₂.embLL x') ((z.R.FW j).j (w.st Z).toD7.what₂.embLL x) := by
  have hk := hE.κ j j' hj
  have hc : ↥(z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n) =
      ↥(z.core.cuspA ((j : ℕ) + 1) (Formalism.L2.Pj.wtA (z.geo.κ j)) (z.geo.κ j).n) := (by with_unfolding_all exact ((cusp_type_congr (P₁ := B.toPre) (P₂ := B'.toPre) q (congrArg (· + 1) hj) hk.2.2
      hE.H hE.l hE.c hE.Dw hE.Xo hE.U hk.1 hk.2.1) :))
  have hm : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := congrArg (fun P : Pre => P.R.m) q
  have hn : z.R.nW j = z'.R.nW j' := GlobalTheory.Mem.R3.LiftForms.nat_eq_of_heq hm hE.nW j j' hj
  obtain ⟨a, b, c, d, l, e, g, -, hW, -, hr⟩ := hE.MW j j' hj
  obtain ⟨h0, h1, h2⟩ := hmod_fields q j j' hj _ _ a b c d l e g _ _ hW
  obtain ⟨m, bs, hb, -, -, -, hsp⟩ := z.geo.fw.ks j
  refine read_of_span φ _ _ hφ hn _ _ _ _ h0 h1 h2 _ _ (Set.range bs) hsp ?_ x x' hx
  rintro _ ⟨i, rfl⟩
  obtain ⟨u, hu⟩ := (z.geo.fw.e j).surjective ⟨bs i, hb i⟩
  have hu' : bs i = (z.geo.fw.e j u : (z.R.FW j).WK).1 := (congrArg Subtype.val hu).symm
  rw [hu']
  exact ⟨(z'.geo.fw.e j' (cast hc.symm u) : (z'.R.FW j').WK).1, hE.forms j j' hj u _ (cast_heq _ _), hr u _ (cast_heq _ _)⟩


set_option maxHeartbeats 2000000 in
theorem read_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (x : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) (x' : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL), (∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)) → HEq ((z'.R.FW j').j (w'.st Z').toD7.what₂.embLL x') ((z.R.FW j).j (w.st Z).toD7.what₂.embLL x)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE _ _ _ Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ hExt j j' hj φ hφ x x' hx => ?_
  exact read_extN hE.1 hExt j j' hj φ hφ x x' hx

end GlobalTheory.Mem.R3.LiftRead

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadingCoordinatewiseImageEqExtendedDataStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reading_coordinatewiseImage_eq_extendedData : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (x : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) (x' : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL), (∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)) → HEq ((z'.R.FW j').j (w'.st Z').toD7.what₂.embLL x') ((z.R.FW j).j (w.st Z).toD7.what₂.embLL x)) := by
  first | exact @GlobalTheory.Mem.R3.LiftRead.read_ext | exact GlobalTheory.Mem.R3.LiftRead.read_ext | (intros; apply GlobalTheory.Mem.R3.LiftRead.read_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArcLiftPeriodsTendstoSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArcLiftPeriodsTendstoSpan
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.PerLim


open scoped CategoryTheory.MonObj in
theorem exists_transfer {S S' S0 : Scheme.{0}} {G : Over S} {G' : Over S'} {G0 : Over S0} [GrpObj G] [GrpObj G']
    [GrpObj G0] {f : S' ⟶ S} {f0 : S' ⟶ S0} {φ : G'.left ⟶ G.left} {φ0 : G'.left ⟶ G0.left}
    (h : IsGrpPullback G' G f φ) (h0 : IsGrpPullback G' G0 f0 φ0) (q : Sp ℂ ⟶ S') {y : Sp ℂ ⟶ S} {y0 : Sp ℂ ⟶ S0}
    (hy : q ≫ f = y) (hy0 : q ≫ f0 = y0) {g : ℕ} (ex0 : (Fin g → ℂ) → (Over.mk y0 ⟶ G0))
    (hadd : ∀ z w, ex0 (z + w) = ex0 z * ex0 w)
    (hol : IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ G0.left from (ex0 z).left))) :
    ∃ ex : (Fin g → ℂ) → (Over.mk y ⟶ G), (∀ z w, ex (z + w) = ex z * ex w) ∧
      IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ G.left from (ex z).left)) ∧
      (∀ (d : Fin g → ℂ) (w : Sp (DualNumber ℂ) ⟶ G'.left),
        w ≫ G'.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ q →
        IsDerivAt0 (fun z => (ex0 z).left) d (w ≫ φ0) → IsDerivAt0 (fun z => (ex z).left) d (w ≫ φ)) ∧
      ∀ z, ex z = 1 → ex0 z = 1 := by
  subst hy hy0
  let ex' : (Fin g → ℂ) → (Over.mk q ⟶ G') := fun z =>
    Over.homMk (h0.1.lift (ex0 z).left q (Over.w (ex0 z))) (h0.1.lift_snd _ _ _)
  have e0 : ∀ z, pushHom h0 (Over.mk q) (ex' z) = ex0 z := fun z =>
    Over.OverMorphism.ext (h0.1.lift_fst _ _ _)
  have e0' : ∀ z, (ex' z).left ≫ φ0 = (ex0 z).left := fun z => h0.1.lift_fst _ _ _
  have e1 : ∀ z, (ex' z).left ≫ G'.hom = q := fun z => Over.w (ex' z)
  have inj0 : Function.Injective (pushHom h0 (Over.mk q)) := fun a b hab =>
    Over.OverMorphism.ext (h0.1.hom_ext (congrArg (·.left) hab) ((Over.w a).trans (Over.w b).symm))
  have inj : Function.Injective (pushHom h (Over.mk q)) := fun a b hab =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg (·.left) hab) ((Over.w a).trans (Over.w b).symm))
  have hA : ∀ t, HolHom.HolAt (fun z => (show Sp ℂ ⟶ G'.left from (ex' z).left)) t := fun t =>
    HolHom.holAt_of_isPullback h0.1
      (by simp only [e0']; exact HolHom.holAt_of_isHolTo hol (Set.mem_univ t))
      (by simp only [e1]; exact HolHom.holAt_const _ _)
  refine ⟨fun z => pushHom h (Over.mk q) (ex' z), fun z w => ?_, ?_, fun d w hw hd => ?_, fun z hz => ?_⟩
  · have : ex' (z + w) = ex' z * ex' w := inj0 (by rw [map_mul, e0, e0, e0]; exact hadd z w)
    exact (congrArg _ this).trans (map_mul _ _ _)
  · exact HolHom.isHolTo_of_holAt isOpen_univ fun t _ => (hA t).comp φ
  · obtain ⟨v, hv⟩ := (hA 0).exists_isDerivAt d
    have h1 := hv.comp φ0
    simp only [e0'] at h1
    have h2 : v = w := h0.1.hom_ext (h1.unique ((HolHom.isDerivAt0_iff _ _ _).1 hd))
      ((HolHom.IsDerivAt.over (a := ex') hv).trans hw.symm)
    subst h2
    exact (HolHom.isDerivAt0_iff _ _ _).2 (hv.comp φ)
  · have : ex' z = 1 := inj (hz.trans (map_one _).symm)
    rw [← e0, this]
    exact map_one _

theorem eventually_eq_of_lattice {B La V : Type} [TopologicalSpace B] [AddCommGroup La] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (P : B → (La →+ V)) (hP : ∀ a, Continuous fun b => P b a)
    (b₀ : B) (hinj : Function.Injective (P b₀)) (hd : DiscreteTopology (P b₀).range)
    (hs : Submodule.span ℝ (Set.range (P b₀)) = ⊤) (a : B → La) (ha : Continuous fun b => P b (a b)) :
    ∀ᶠ b in 𝓝 b₀, a b = a b₀ := by
  classical
  let L : Submodule ℤ V := (P b₀).range.toIntSubmodule
  haveI : DiscreteTopology L := hd
  haveI : IsZLattice ℝ L := ⟨hs⟩
  let bz := Module.Free.chooseBasis ℤ L
  let bR := bz.ofZLatticeBasis ℝ L
  have hc : ∀ i, ∃ c, P b₀ c = bR i := fun i => by
    rw [Module.Basis.ofZLatticeBasis_apply]; exact (bz i).2
  choose c hc using hc
  let T : B → V →L[ℝ] V := fun b => ∑ i, (LinearMap.toContinuousLinearMap (bR.coord i)).smulRight (P b (c i))
  have hT : ∀ b x, T b x = ∑ i, bR.repr x i • P b (c i) := fun b x => by simp [T]
  have hTc : Continuous T := continuous_finsetSum _ fun i _ =>
    (ContinuousLinearMap.smulRightL ℝ V V (LinearMap.toContinuousLinearMap (bR.coord i))).continuous.comp (hP _)
  have hT0 : T b₀ = ContinuousLinearMap.id ℝ V := by
    ext x
    rw [hT]
    simp only [hc]
    exact bR.sum_repr x
  have hTP : ∀ b x, T b (P b₀ x) = P b x := fun b x => by
    let xl : L := ⟨P b₀ x, x, rfl⟩
    have h1 : ∀ i, bR.repr (P b₀ x) i = (bz.repr xl i : ℝ) := fun i => bz.ofZLatticeBasis_repr_apply ℝ L xl i
    have h2 : x = ∑ i, bz.repr xl i • c i := hinj (by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [map_zsmul, hc]
      rw [← bR.sum_repr (P b₀ x)]
      exact Finset.sum_congr rfl fun i _ => by rw [h1, Int.cast_smul_eq_zsmul])
    rw [hT]
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [h2, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [h1, Int.cast_smul_eq_zsmul, map_zsmul]
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.1 (isOpen_discrete ({0} : Set L)) 0 rfl
  have h1 : ∀ᶠ b in 𝓝 b₀, ‖T b - T b₀‖ < 1 / 2 := by
    have : Tendsto (fun b => ‖T b - T b₀‖) (𝓝 b₀) (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 (hTc.tendsto b₀)
    exact this.eventually (gt_mem_nhds (by norm_num))
  have h2 : ∀ᶠ b in 𝓝 b₀, ‖P b (a b) - P b (a b₀)‖ < ε / 2 := by
    have : Tendsto (fun b => ‖P b (a b) - P b (a b₀)‖) (𝓝 b₀) (𝓝 ‖P b₀ (a b₀) - P b₀ (a b₀)‖) :=
      ((ha.sub (hP _)).norm.tendsto b₀)
    rw [sub_self, norm_zero] at this
    exact this.eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [h1, h2] with b h1 h2
  rw [← map_sub, ← hTP] at h2
  set x := P b₀ (a b - a b₀) with hx
  have h3 : ‖T b x - x‖ ≤ 1 / 2 * ‖x‖ := by
    have := (T b - T b₀).le_of_opNorm_le h1.le x
    rwa [hT0] at this
  have h4 : ‖x‖ ≤ ‖T b x‖ + ‖T b x - x‖ := by
    have := norm_sub_le (T b x) (T b x - x)
    rwa [sub_sub_cancel] at this
  have h5 : (⟨x, _, rfl⟩ : L) ∈ Metric.ball (0 : L) ε := by
    rw [mem_ball_zero_iff]
    show ‖x‖ < ε
    linarith
  have h6 : x = 0 := congrArg Subtype.val (hb h5)
  exact sub_eq_zero.1 (hinj (h6.trans (map_zero _).symm))

theorem tendsto_eTwoPi : Tendsto eTwoPi imTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h : (fun w => ‖eTwoPi w‖) = fun w : ℂ => Real.exp (-(2 * Real.pi * w.im)) := funext fun w => by
    rw [eTwoPi, Complex.norm_exp]
    simp
  rw [h]
  exact Real.tendsto_exp_neg_atTop_nhds_zero.comp
    ((tendsto_comap (f := Complex.im) (x := atTop)).const_mul_atTop (by positivity))

theorem span_proj {n g m : ℕ} (lam : Fin n → Fin g → ℂ) (h : Submodule.span ℂ (Set.range lam) = ⊤) (s : Fin m → Fin g)
    (hs : Function.Injective s) : Submodule.span ℂ (Set.range fun j i => lam j (s i)) = ⊤ := by
  have : (fun j i => lam j (s i)) = LinearMap.funLeft ℂ ℂ s ∘ lam := rfl
  rw [this, Set.range_comp, ← Submodule.map_span, h, Submodule.map_top, LinearMap.range_eq_top]
  exact LinearMap.funLeft_surjective_of_injective ℂ ℂ s hs

theorem continuous_perFr {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {B : Type}
    [TopologicalSpace B] {x : B → Frame X.Ψ r} (hx : ∀ b, x b ∈ X.dom) (hc : Continuous x) (v : Fin r → E)
    (τ : E →+* ℂ) (i : ℕ) : Continuous fun b => perFr X (x b) v τ i := by
  have hm : ∀ t, Continuous fun b => mat (x b) t := fun t => (continuous_apply t).comp hc
  unfold perFr
  split_ifs with h1 h2 h3 h4
  · refine (continuous_apply (⟨X.p0 + i, h2⟩ : Fin r)).comp
      (Continuous.matrix_mulVec (A := fun b => (mat (x b) ⟨τ, h1⟩)⁻¹) ?_ continuous_const)
    refine continuous_iff_continuousAt.2 fun b => (continuousAt_matrix_inv _ ?_).comp (hm _).continuousAt
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (hx b _).1
  · exact continuous_const
  · simp only [ReciprocityTheory.ChartRestriction.G.FD.hermC]
    exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun c _ =>
      (((hm _).matrix_elem _ _).mul continuous_const).mul continuous_const
  · exact continuous_const
  · exact continuous_const

theorem exists_periods_tendsto_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsOrbit (U.X k) T M γ xx → IsLift U k y T xx → ∃ (n : ℕ) (v : Fin n → Fin N → E) (Lp : Fin n → (U.X k).Ψ → Fin (N - (U.X k).p0) → ℂ) (Lm : Fin n → (U.X k).Ψ → Fin (U.X k).p0 → ℂ), (∀ j (τ : (U.X k).Ψ) (i : Fin (N - (U.X k).p0)), Tendsto (fun w => perFr (U.X k) (xx w) (v j) τ.1 i) imTop (𝓝 (Lp j τ i))) ∧ (∀ j (τ : (U.X k).Ψ) (i : Fin (U.X k).p0), Tendsto (fun w => perFr (U.X k) (xx w) (v j) (conjEmb τ.1) i) imTop (𝓝 (Lm j τ i))) ∧ ∀ τ : (U.X k).Ψ, Submodule.span ℂ (Set.range fun j => Lp j τ) = ⊤ ∧ Submodule.span ℂ (Set.range fun j => Lm j τ) = ⊤ := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ N U A _ φ x fr ψ r y k T M γ xx hσ hU harc hm horb hlift
  obtain ⟨hN, hX, -, -, -, g, e, F, ik, φL, -, hfr⟩ := hU
  obtain ⟨ρ, n, lam, hρ, hρr, hcont, hspan, hker⟩ := GlobalTheory.T.exists_continuous_lattice_vectors_along_arc E H Dw l Xo c O β Z σ A φ x fr ψ r g e harc
  obtain ⟨-, -, hxd, hxm, -⟩ := horb
  obtain ⟨T₁, hT₁⟩ : ∃ T₁ : ℝ, ∀ w : ℂ, T₁ < w.im → T < w.im ∧ eTwoPi w ∈ Metric.ball (0 : ℂ) ρ := by
    have h1 : ∀ᶠ w in imTop, eTwoPi w ∈ Metric.ball (0 : ℂ) ρ := tendsto_eTwoPi.eventually (Metric.ball_mem_nhds 0 hρ)
    obtain ⟨a, ha⟩ := eventually_atTop.1 (eventually_comap.1 h1)
    exact ⟨max a T, fun w hw => ⟨(le_max_right _ _).trans_lt hw, ha _ ((le_max_left _ _).trans hw.le) w rfl⟩⟩
  let B := {w : ℂ // w ∈ {w : ℂ | T₁ < w.im}}
  haveI : PreconnectedSpace B := Subtype.preconnectedSpace (convex_halfSpace_im_gt T₁).isPreconnected
  have hdom : ∀ b : B, xx b ∈ (U.X k).dom := fun b => hxm b (hT₁ b b.2).1
  choose Pm hPm hper hpt hder hrest using fun b : B => hfr k ⟨xx b, hdom b⟩
  clear hrest
  have key : ∀ (b : B) j, lam j (eTwoPi b) ∈ (Pm b).range := fun b j => by
    have hb := (hT₁ b b.2).2
    obtain ⟨_, hx1, hx2⟩ := hlift b (hT₁ b b.2).1
    obtain ⟨hm1, hm2⟩ := hm _ (Metric.ball_subset_ball hρr hb) (Complex.exp_ne_zero _)
    have h0 : GlobalTheory.AllWt.ptF (y (eTwoPi b)) ≫ pullback.fst _ _ = (y (eTwoPi b)).x := pullback.lift_fst _ _ _
    obtain ⟨ex, a1, a2, a3, a4⟩ := exists_transfer Z.m.cart Z.m0.toSABMap.cart
      (GlobalTheory.AllWt.ptF (S := CAt σ) (y (eTwoPi b)) :)
      (y := spMap (ψ (eTwoPi b)) ≫ x ≫ genι Z) (y0 := F.u (ik k) (Pm b))
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ genι Z) hm1).trans (Category.assoc _ _ _)))
      (h0.trans (hx1.symm.trans (hpt b))) (F.ex (ik k) (Pm b)) (F.ex_add _ _ (hper b))
      (HolHom.isHolTo_ex F _ (hper b))
    refine (F.ex_ker _ _ (hper b) _).1 (a4 _ (hker _ hb ex a1 a2 (fun jj => ?_) j))
    obtain ⟨w, w1, w2, w3⟩ := hm2 (e jj).1 (e jj).2
    have hd := hder b (e jj).1 (e jj).2
    rw [hx2, ← w2, Sigma.eta, Equiv.symm_apply_apply] at hd
    exact w3 ▸ a3 _ w w1 hd
  choose a ha using key
  have hxc : Continuous fun b : B => xx b :=
    (hxd.continuousOn.mono fun w hw => (hT₁ w hw).1).restrict
  have hPc : ∀ z, Continuous fun b : B => Pm b z := fun z => continuous_pi fun jj => by
    simp only [hPm]
    exact continuous_perFr _ hdom hxc _ _ _
  have hec : Continuous eTwoPi := by unfold eTwoPi; fun_prop
  let b₀ : B := ⟨(T₁ + 1 : ℝ) * Complex.I, by simp⟩
  have hconst : ∀ j b, a b j = a b₀ j := fun j b => by
    refine IsLocallyConstant.apply_eq_of_preconnectedSpace (f := fun b => a b j)
      ((IsLocallyConstant.iff_eventually_eq _).2 fun b' => ?_) b b₀
    refine eventually_eq_of_lattice Pm hPc b' (hper b').2.1 (hper b').2.2.1 (hper b').2.2.2.1 (fun b => a b j) ?_
    simp only [ha]
    exact (hcont j).comp_continuous (hec.comp continuous_subtype_val) fun b => (hT₁ b b.2).2
  have hlim : ∀ j jj, Tendsto (fun w => perFr (U.X k) (xx w) (φL k (a b₀ j) : Fin N → E) (relab c σ (e jj).1) (e jj).2)
      imTop (𝓝 (lam j 0 jj)) := fun j jj => by
    have h1 : Tendsto (fun w => lam j (eTwoPi w) jj) imTop (𝓝 (lam j 0 jj)) :=
      ((continuous_apply jj).tendsto _).comp
        ((((hcont j).continuousAt (Metric.ball_mem_nhds 0 hρ)).tendsto).comp tendsto_eTwoPi)
    refine h1.congr' ?_
    filter_upwards [(tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_gt_atTop T₁)] with w hw
    rw [← ha ⟨w, hw⟩ j, hconst, hPm]
  have hidx : ∀ (τ : E →+* ℂ) (m : ℕ), m = (if τ (H.rt : E) = H.rt0 then Dw.p else Dw.q) →
      ∃ s : Fin m → Fin g, Function.Injective s ∧ ∀ i, relab c σ (e (s i)).1 = τ ∧ ((e (s i)).2 : ℕ) = i := by
    intro τ m hmτ
    obtain ⟨τ', rfl⟩ := Finite.injective_iff_surjective.1 (ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.relab_injective c σ) τ
    have h1 : m = Dw.mult τ' := by
      rw [hmτ, Datum.mult]
      exact if_congr (ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.relab_rt c σ hσ τ') rfl rfl
    subst h1
    refine ⟨fun i => e.symm ⟨τ', i⟩, fun i i' h => ?_, fun i => ?_⟩
    · exact eq_of_heq (Sigma.mk.inj (e.symm.injective h)).2
    · rw [Equiv.apply_symm_apply]
      exact ⟨rfl, rfl⟩
  choose sp hsp hsp' using fun τ : (U.X k).Ψ => hidx τ.1 (N - (U.X k).p0) (by
    rw [if_pos (((hX k).2 _).1 τ.2), (hX k).1, hN, Nat.add_sub_cancel])
  choose sm hsm hsm' using fun τ : (U.X k).Ψ => hidx (conjEmb τ.1) (U.X k).p0 (by
    rw [if_neg fun h => ((U.X k).cmType τ.1).1 τ.2 (((hX k).2 (conjEmb τ.1)).2 h), (hX k).1])
  refine ⟨n, fun j => φL k (a b₀ j), fun j τ i => lam j 0 (sp τ i), fun j τ i => lam j 0 (sm τ i), fun j τ i => ?_,
    fun j τ i => ?_, fun τ => ⟨span_proj _ hspan _ (hsp τ), span_proj _ hspan _ (hsm τ)⟩⟩
  · have := hlim j (sp τ i)
    rwa [(hsp' τ i).1, (hsp' τ i).2] at this
  · have := hlim j (sm τ i)
    rwa [(hsm' τ i).1, (hsm' τ i).2] at this

end GlobalTheory.ShFam.PerLim
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArcLiftPeriodsTendstoSpanStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_arcLift_periods_tendsto_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsOrbit (U.X k) T M γ xx → IsLift U k y T xx → ∃ (n : ℕ) (v : Fin n → Fin N → E) (Lp : Fin n → (U.X k).Ψ → Fin (N - (U.X k).p0) → ℂ) (Lm : Fin n → (U.X k).Ψ → Fin (U.X k).p0 → ℂ), (∀ j (τ : (U.X k).Ψ) (i : Fin (N - (U.X k).p0)), Tendsto (fun w => perFr (U.X k) (xx w) (v j) τ.1 i) imTop (𝓝 (Lp j τ i))) ∧ (∀ j (τ : (U.X k).Ψ) (i : Fin (U.X k).p0), Tendsto (fun w => perFr (U.X k) (xx w) (v j) (conjEmb τ.1) i) imTop (𝓝 (Lm j τ i))) ∧ ∀ τ : (U.X k).Ψ, Submodule.span ℂ (Set.range fun j => Lp j τ) = ⊤ ∧ Submodule.span ℂ (Set.range fun j => Lm j τ) = ⊤ := by
  first | exact @GlobalTheory.ShFam.PerLim.exists_periods_tendsto_span | exact GlobalTheory.ShFam.PerLim.exists_periods_tendsto_span | (intros; apply GlobalTheory.ShFam.PerLim.exists_periods_tendsto_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitCoefOpen
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.KeyOpen

theorem glue_units {Z : Scheme.{0}} [IsReduced Z] (V : Z.Opens) (P : Z.Opens → Prop)
    (hP : ∀ p ∈ V, ∃ W : Z.Opens, IsAffineOpen W ∧ W ≤ V ∧ P W ∧ p ∈ W)
    (R : ∀ (L : Type) [Field L], (Sp L ⟶ Z) → L → Prop)
    (uniq : ∀ (L : Type) [Field L] (z : Sp L ⟶ Z), ⊤ ≤ z ⁻¹ᵁ V → ∀ x y, R L z x → R L z y → x = y)
    (loc : ∀ W : Z.Opens, IsAffineOpen W → W ≤ V → P W → ∃ a : Γ(Z, W)ˣ,
      ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ W), R L z (ev z W hz a.val)) :
    ∃ a : Γ(Z, V)ˣ, ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ V), R L z (ev z V hz a.val) := by
  let I := {W : Z.Opens // IsAffineOpen W ∧ W ≤ V ∧ P W}
  choose a ha using fun i : I => loc i.1 i.2.1 i.2.2.1 i.2.2.2
  have hc : ∀ p ∈ V, ∃ i : I, p ∈ i.1 := fun p hp => by
    obtain ⟨W, hW, hWV, hPW, hpW⟩ := hP p hp
    exact ⟨⟨W, hW, hWV, hPW⟩, hpW⟩
  have hcov : V ≤ iSup fun i : I => i.1 := fun p hp => TopologicalSpace.Opens.mem_iSup.2 (hc p hp)
  have key : ∀ (i j : I) (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ (i.1 ⊓ j.1)),
      ev z _ hz (resG Z inf_le_left (a i).val) = ev z _ hz (resG Z inf_le_right (a j).val) := by
    intro i j L _ z hz
    have hi := GlobalTheory.FlagMod.le_preimage_mono inf_le_left hz
    have hj := GlobalTheory.FlagMod.le_preimage_mono inf_le_right hz
    rw [GlobalTheory.FlagMod.ev_res z _ hz hi, GlobalTheory.FlagMod.ev_res z _ hz hj]
    exact uniq L z (GlobalTheory.FlagMod.le_preimage_mono i.2.2.1 hi) _ _ (ha i L z hi) (ha j L z hj)
  obtain ⟨s, hs, -⟩ := Z.sheaf.existsUnique_gluing' (fun i : I => i.1) V (fun i => homOfLE i.2.2.1)
    hcov (fun i => (a i).val) (fun i j =>
      GlobalTheory.FlagMod.ext_ev_field (a := resG Z inf_le_left (a i).val) (b := resG Z inf_le_right (a j).val)
        fun L _ z hz => key i j L z hz)
  obtain ⟨t, ht, -⟩ := Z.sheaf.existsUnique_gluing' (fun i : I => i.1) V (fun i => homOfLE i.2.2.1)
    hcov (fun i => (a i)⁻¹.val) (fun i j =>
      GlobalTheory.FlagMod.ext_ev_field (a := resG Z inf_le_left (a i)⁻¹.val) (b := resG Z inf_le_right (a j)⁻¹.val)
        fun L _ z hz => by
          have e := key i j L z hz
          have e₁ := map_units_inv (((ev z _ hz).comp (resG Z inf_le_left)) : Γ(Z, i.1) →+* L) (a i)
          have e₂ := map_units_inv (((ev z _ hz).comp (resG Z inf_le_right)) : Γ(Z, j.1) →+* L) (a j)
          simp only [RingHom.coe_comp, Function.comp_apply] at e₁ e₂
          rw [e₁, e₂, e])
  obtain ⟨s, t, hs, ht⟩ : ∃ s t : Γ(Z, V), (∀ i : I, resG Z i.2.2.1 s = (a i).val) ∧
      ∀ i : I, resG Z i.2.2.1 t = (a i)⁻¹.val := ⟨s, t, hs, ht⟩
  have hval : ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ V), ∃ i : I, ∃ hi : ⊤ ≤ z ⁻¹ᵁ i.1,
      ev z V hz s = ev z i.1 hi (a i).val ∧ ev z V hz t = ev z i.1 hi (a i)⁻¹.val := by
    intro L _ z hz
    obtain ⟨i, hi⟩ := hc (z (IsLocalRing.closedPoint L)) (hz (Set.mem_univ _))
    have hi' : ⊤ ≤ z ⁻¹ᵁ i.1 := ((IsLocalRing.closed_point_mem_iff (U := z ⁻¹ᵁ i.1)).1 hi).ge
    exact ⟨i, hi', (GlobalTheory.FlagMod.ev_res z i.2.2.1 hi' hz s).symm.trans (congrArg _ (hs i)),
      (GlobalTheory.FlagMod.ev_res z i.2.2.1 hi' hz t).symm.trans (congrArg _ (ht i))⟩
  have hst : s * t = 1 := GlobalTheory.FlagMod.ext_ev_field fun L _ z hz => by
    obtain ⟨i, hi, e₁, e₂⟩ := hval L z hz
    rw [map_mul, map_one, e₁, e₂, ← map_mul, Units.mul_inv, map_one]
  refine ⟨⟨s, t, hst, by rw [mul_comm, hst]⟩, fun L _ z hz => ?_⟩
  obtain ⟨i, hi, e₁, -⟩ := hval L z hz
  show R L z (ev z V hz s)
  rw [e₁]
  exact ha i L z hi

end GlobalTheory.KeyOpen

namespace GlobalTheory.KeyOpen

end GlobalTheory.KeyOpen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjGeneratorsMemFramePrimesTrueColumns
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjGeneratorsMemFramePrimesTrueColumns
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.AtMember
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AtMember


set_option synthInstance.maxHeartbeats 400000 in
theorem conj_gen_mem_frame : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : Bl.ColW B f T) (Z : w.Lt) (t : Bl.ColT w Z), HalfAt (Formalism.L2.Herm.toErrXS t.full.1) (Fr.at (w.st Z) f) := by
  intro B f T w Z t k
  have hpi : (Formalism.L2.Herm.toErrXS t.full.1).piG = w.px.piG := by
    have h5 : (t.full.1.cols.levelZeroCompatibility (w.D Z).u₀).piG = (t.C.herm.levelZeroCompatibility (w.D Z).u₀).piG :=
      congrArg (fun X : Formalism.L2.Herm.ColsHermS (w.D Z) => (X.levelZeroCompatibility (w.D Z).u₀).piG) t.full.2
    exact h5.trans ((t.C.piG (w.D Z).u₀).symm.trans (t.std (w.D Z).u₀).gl.piG)
  show barE (w.D Z) ((Formalism.L2.Herm.toErrXS t.full.1).piG k) ∈
    Ideal.map (algebraMap (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E)) ((Fr.at (w.st Z) f).P.pb k).asIdeal
  rw [hpi]
  have hP : (Fr.at (w.st Z) f).P = w.I.C.P := by rw [w.C_eq]; rfl
  rw [hP]
  have hdiv := w.ok.pibar k
  set π : 𝓞 (w.D Z).host.E := w.px.piG k with hπdef
  set b : 𝓞 (w.D Z).host.E := barE (w.D Z) π with hbdef
  have hbc : ((b : 𝓞 (w.D Z).host.E) : (w.D Z).host.E) = (w.D Z).host.conj (π : (w.D Z).host.E) := barE_eq_conj _ _
  have hprod : π * b = (((w.D Z).host.g k : ℕ) : 𝓞 (w.D Z).host.E) := by
    apply RingOfIntegers.ext
    show ((π : (w.D Z).host.E) * (b : (w.D Z).host.E)) = algebraMap (𝓞 (w.D Z).host.E) (w.D Z).host.E (((w.D Z).host.g k : ℕ) : 𝓞 (w.D Z).host.E)
    rw [map_natCast, hbc]
    exact w.px.piG_norm k
  have hg0 : (((w.D Z).host.g k : ℕ) : 𝓞 (w.D Z).host.E) ≠ 0 := by
    intro h
    have h' := congrArg (algebraMap (𝓞 (w.D Z).host.E) (w.D Z).host.E) h
    rw [map_natCast, map_zero, Nat.cast_eq_zero] at h'
    exact ((w.D Z).host.g_prime k).ne_zero h'
  have hπ0 : π ≠ 0 := fun h => hg0 (by rw [← hprod, h, zero_mul])
  have hb0 : b ≠ 0 := fun h => hg0 (by rw [← hprod, h, mul_zero])
  have hbK : ((b : 𝓞 (w.D Z).host.E) : (w.D Z).host.E) ∈ (w.D Z).host.K := by
    have hπE : ((π : 𝓞 (w.D Z).host.E) : (w.D Z).host.E) ≠ 0 := fun h => hπ0 (RingOfIntegers.ext (h.trans (map_zero (algebraMap (𝓞 (w.D Z).host.E) (w.D Z).host.E)).symm))
    have e : ((b : 𝓞 (w.D Z).host.E) : (w.D Z).host.E) =
        ((w.D Z).host.g k : (w.D Z).host.E) / ((π : 𝓞 (w.D Z).host.E) : (w.D Z).host.E) := by
      rw [eq_div_iff hπE, mul_comm, hbc]
      exact w.px.piG_norm k
    rw [e]
    exact div_mem (natCast_mem _ _) (w.px.piG_K k)
  set y : 𝓞 (w.D Z).host.K := toOK b hbK with hydef
  have hy : algebraMap (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E) y = b := algebraMap_toOK b hbK
  rw [← hy]
  apply Ideal.mem_map_of_mem

  have iI : Algebra.IsIntegral (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E) :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral (R := ℤ) x).tower_top⟩
  have hPk : ((w.I.C.P.pb k).asIdeal : Ideal (𝓞 (w.D Z).host.K)).IsPrime := (w.I.C.P.pb k).isPrime
  obtain ⟨Q, -, hQp, hQ⟩ := @Ideal.exists_ideal_over_prime_of_isIntegral (𝓞 (w.D Z).host.K) _ (𝓞 (w.D Z).host.E) _
    (algebraMap (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E)).toAlgebra iI
    ((w.I.C.P.pb k).asIdeal : Ideal (𝓞 (w.D Z).host.K)) hPk ⊥ (by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot] at hx
      have : x = 0 := FaithfulSMul.algebraMap_injective (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E) (hx.trans (map_zero _).symm)
      rw [this]; exact Ideal.zero_mem _)
  have hgQ : π * b ∈ Q := by
    rw [hprod, ← map_natCast (algebraMap (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E)), ← Ideal.mem_comap]
    change _ ∈ Ideal.under (𝓞 (w.D Z).host.K) Q
    rw [hQ]
    exact w.I.C.P.pb_over k
  rcases hQp.mem_or_mem hgQ with hπQ | hbQ
  ·
    have hQ'p : (Q.comap (barE (w.D Z) : 𝓞 (w.D Z).host.E →+* 𝓞 (w.D Z).host.E)).IsPrime := Ideal.comap_isPrime _ _
    have hbQ' : b ∈ Q.comap (barE (w.D Z) : 𝓞 (w.D Z).host.E →+* 𝓞 (w.D Z).host.E) := by
      rw [Ideal.mem_comap]
      show barE (w.D Z) (barE (w.D Z) π) ∈ Q
      rw [barE_barE]; exact hπQ
    let Q' : HeightOneSpectrum (𝓞 (w.D Z).host.E) :=
      ⟨Q.comap (barE (w.D Z) : 𝓞 (w.D Z).host.E →+* 𝓞 (w.D Z).host.E), hQ'p, fun h => hb0 (by rw [h] at hbQ'; exact (Ideal.mem_bot).1 hbQ')⟩
    have hmem : Q' ∈ (B.primes w.px).vG k := (Formalism.L2.Col.mem_divs hb0 Q').2 hbQ'
    have hd := (hdiv Q').1 hmem
    have hu : y ∈ (HeightOneSpectrum.under (𝓞 (w.D Z).host.K) Q').asIdeal := by
      show algebraMap (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E) y ∈ Q'.asIdeal
      rw [hy]; exact hbQ'
    have hd' : HeightOneSpectrum.under (𝓞 (w.D Z).host.K) Q' = w.I.C.P.pb k := hd
    rw [hd'] at hu
    exact hu
  · rw [← hQ]
    have h' : algebraMap (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E) y ∈ Q := hy.symm ▸ hbQ
    exact h'

end GlobalTheory.AtMember
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjGeneratorsMemFramePrimesTrueColumnsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.AtMember
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjGenerators_mem_framePrimes_trueColumns : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : Bl.ColW B f T) (Z : w.Lt) (t : Bl.ColT w Z), HalfAt (Formalism.L2.Herm.toErrXS t.full.1) (Fr.at (w.st Z) f) := by
  first | exact @GlobalTheory.AtMember.conj_gen_mem_frame | exact GlobalTheory.AtMember.conj_gen_mem_frame | (intros; apply GlobalTheory.AtMember.conj_gen_mem_frame <;> assumption)
end
end
