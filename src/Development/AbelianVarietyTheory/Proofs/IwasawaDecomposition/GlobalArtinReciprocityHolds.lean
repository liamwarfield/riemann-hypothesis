module

public import CompanionTheory.AutomorphicTheory.PlaceSeparation.IsOpenQuotientMapArt0
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSelfDualAdelicFrameLevelOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
theorem GlobalTheory.globalArtinReciprocity_holds : GlobalTheory.Published.GlobalArtinReciprocity := CompanionTheory.FamInh.globalArtin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapRef

variable {D : D7} {S T : HSp D} {r g : ℕ}

def IsSet (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (hr : T.rank = r) (X : Data D.host.E r)
    (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) : Prop :=
  IsStdChar D ψ (-1) ∧ IsInfFam θ ∧ S.gram = 1 ∧ Even S.rank ∧ ModelW T hr X ∧ X.κ0 = -(2 * D.host.xi0) ∧
    (∀ ρ, (eT ρ).1 = tauE D ρ) ∧ IsSympl X bas

abbrev Fam (T : HSp D) : Type := D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ

def negM (T : HSp D) (q : ℕ) : Matrix (Fin T.rank) (Fin T.rank) ℂ :=
  Matrix.diagonal fun a : Fin T.rank => ((-(sgn q (a : ℕ)) : ℝ) : ℂ)

def IsONeg (T : HSp D) (q : ℕ) (Z : Fam T) : Prop := ∀ ρ, (Z ρ)ᴴ * gramAt D T ρ * Z ρ = negM T q

def cartZ (T : HSp D) (q : ℕ) (Z : Fam T) : Fam T := fun ρ => Z ρ * negM T q * (Z ρ)⁻¹

def mvZ (θ : InfFam D) (h : GA D T) (Z : Fam T) : Fam T := fun ρ => compAt θ ρ (Formalism.L2.Theta.mt T h) * Z ρ

def frOf (hr : T.rank = r) {X : Data D.host.E r} (eT : D.what₂.Tau ≃ X.Ψ) (Z : Fam T) : Frame X.Ψ r :=
  fun τ a b => Z (eT.symm τ) (Fin.cast hr.symm a) (Fin.cast hr.symm b)

def rePt (θ : InfFam D) (hr : T.rank = r) {X : Data D.host.E r} (eT : D.what₂.Tau ≃ X.Ψ) (w : WO S T) :
    Ker.WR X S.rank :=
  fun τ k a => compAt θ (eT.symm τ) w (Fin.cast hr.symm a) k

def Zak (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hr : T.rank = r) {X : Data D.host.E r}
    (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r)
    (φ : TF S.rank g) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ ∀ w, Ker.IsRealPt w → f w = Ker.thR X bas idx φ x (rePt θ hr eT w)

def finR (S : HSp D) (hr : T.rank = r) (y : Matrix (Fin S.rank) (Fin r) D.host.E) : WO S T :=
  Ker.finW S T (y.submatrix id (Fin.cast hr))

def latW (hr : T.rank = r) (L : Lt D.host.E r) : Lt D.host.E T.rank :=
  L.comap (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr.symm))

def toP (S : HSp D) (hr : T.rank = r) {X : Data D.host.E r} (eT : D.what₂.Tau ≃ X.Ψ) {q0 : ℕ} (hq : X.p0 + q0 = r) :
    MvPolynomial (FVar D T.rank S.rank) ℂ →ₐ[ℂ] Harm.Poly ℂ X.Ψ q0 X.p0 (Fin S.rank) :=
  MvPolynomial.aeval fun v => MvPolynomial.C (((2 / fockScale D v.1 : ℝ) : ℂ)) *
    MvPolynomial.X (eT v.1, (rowIdx hq).symm (Fin.cast hr v.2.1), v.2.2)

def fv (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (q : ℕ) (Z : Fam T) (f : WO S T → ℂ)
    (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) : WO S T → ℂ :=
  pureTensorO ψ θ S T (fun _ => 1) (cartZ T q Z) (fun _ => 1) Z f Q

def ctxOf {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hn : Even S.rank)
    (X' : Data D.host.E T.rank) (m : Ker.Match S T X') {q : ℕ} (hq : X'.p0 + q = T.rank)
    (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X'.Λ) (idx' : Fin g ≃ X'.Ψ × Fin T.rank) (hs : IsSympl X' bas') : Ker.Ctx S T :=
  ⟨ψ, hψ, θ, hθ, X', m, g, q, hq, bas', idx', hs, hn⟩

section Geo

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

def MarkAd (hr : T.rank = r) (l : Level H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin T.rank → D.host.E)) (h : GA D T)
    (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) : Prop :=
  ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat T h,
    finVec T (mk a ∘ Fin.cast hr) - (finHom T h).1.mulVec (finVec T (ι a)) = (l.M : ℕ) • w

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

def Matched (c : Coeff l) (σ : c.F →+* ℂ) (X : Data D.host.E r) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) : Prop :=
  (∀ x v j, pv X idx x v j = perFr X x v (relab c σ (e j).1) (e j).2) ∧ ∀ j, rowType X (idx j) = relab c σ (e j).1

abbrev ptC (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) : @FrPt D.host.E _ _ _ H Dw l Xo c ℂ _ σ.toAlgebra :=
  unC (Formalism.L2.PjFree.Unf.ofPj U) k x

def FrConst (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S : HSp D) (hr : T.rank = r)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (f₀ : WO S T → ℂ) (U : Unf Xo c σ r)
    (dict : GA D T → Σ k, Frame (U.X k).Ψ r) (mu : GA D T → ℂ) (Z₀ : Fam T) (cc : U.Comp → ℂ) : Prop :=
  ∀ (h γ : GA D T), γ ∈ GQ T → ∀ (g : ℕ) (eT : D.what₂.Tau ≃ (U.X (dict h).1).Ψ)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X (dict h).1).Λ) (idx : Fin g ≃ (U.X (dict h).1).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw),
    IsSet ψ θ S T hr (U.X (dict h).1) eT bas → Matched c σ (U.X (dict h).1) idx e →
    (dict h).2 = frOf hr eT (mvZ θ (γ * h) Z₀) → ∀ (hx : (dict h).2 ∈ (U.X (dict h).1).dom),
    letI : Algebra c.F ℂ := σ.toAlgebra
    ∀ (A : AnFib (U.X (dict h).1) bas idx e (dict h).2 (U.X (dict h).1).Λ (ptC U (dict h).1 ⟨(dict h).2, hx⟩))
      (th : (Fin g → ℂ) → ℂ), A.Reads 1 (ptC U (dict h).1 ⟨(dict h).2, hx⟩).s th →
      ∀ w : WO S T, Ker.IsRealPt w →
        om (1, γ * h) f₀ w = cc (dict h).1 * mu h *
          (Ker.gaussR (U.X (dict h).1) bas idx (dict h).2 (Ker.zR (U.X (dict h).1) idx (dict h).2 (rePt θ hr eT w)) *
            ∏ b, th (Ker.zR (U.X (dict h).1) idx (dict h).2 (rePt θ hr eT w) b))

section Field

variable {c' : Coeff l} {hle : c.F ≤ c'.F} [Algebra c.F ℂ] [Algebra c'.F ℂ] (hA : AlgOver c c' hle ℂ) {X : Data D.host.E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r}
  {L : Lt D.host.E r} {y : FrPt Xo c ℂ}

def fibExt (A : AnFib X bas idx e x L y) : AnFib X bas idx e x L (y.ext hle hA) :=
  ⟨A.ex, A.ex_add, A.ex_onto, A.ex_ker, A.ex_lin, A.hol, A.der, A.fr, A.fr_hol, A.fr_ne, A.fr_g, A.fr_0, A.χ, A.χ_norm,
    A.fr_per⟩

end Field

end Geo

section Rec

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

abbrev baseZ {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) :
    Fam (Wc D i) := x0Mat (R.MW i (sg0 D A))

end Rec

end GlobalTheory.OneMapRef

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.QCoh

theorem exists_isIrreducible_inter_open_subset {α : Type*} [TopologicalSpace α] [NoetherianSpace α]
    {T : Set α} (hT : IsClosed T) (hne : T.Nonempty) :
    ∃ Z : Set α, IsClosed Z ∧ IsIrreducible Z ∧ Z ⊆ T ∧
      ∃ U : Set α, IsOpen U ∧ (∃ x ∈ T, x ∈ U) ∧ T ∩ U ⊆ Z := by
  classical
  obtain ⟨S, hS, hc, hi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hT
  have hSne : S.Nonempty := by
    obtain ⟨x, t, ht, -⟩ := hne
    exact ⟨t, ht⟩
  obtain ⟨Z, hZ⟩ := hS.exists_maximal hSne
  have hfin : (S \ {Z}).Finite := hS.diff
  refine ⟨Z, hc Z hZ.1, hi Z hZ.1, Set.subset_sUnion_of_mem hZ.1, (⋃₀ (S \ {Z}))ᶜ, ?_, ?_, ?_⟩
  · rw [isOpen_compl_iff, Set.sUnion_eq_biUnion]
    exact hfin.isClosed_biUnion fun t ht => hc t ht.1
  · by_contra h
    have hsub : Z ⊆ ⋃₀ (hfin.toFinset : Set (Set α)) := fun x hx => by
      rw [hfin.coe_toFinset]
      by_contra hx'
      exact h ⟨x, Set.subset_sUnion_of_mem hZ.1 hx, hx'⟩
    obtain ⟨z, hz, hZz⟩ := isIrreducible_iff_sUnion_isClosed.1 (hi Z hZ.1) hfin.toFinset
      (fun z hz => hc z (hfin.mem_toFinset.1 hz).1) hsub
    have hz' := hfin.mem_toFinset.1 hz
    exact hz'.2 (le_antisymm (hZ.2 hz'.1 hZz) hZz)
  · rintro x ⟨⟨t, ht, hxt⟩, hx⟩
    by_contra hxZ
    exact hx ⟨t, ⟨ht, fun e => hxZ ((show t = Z from e) ▸ hxt)⟩, hxt⟩

variable {X : Scheme.{0}}

theorem exists_pow_vanishingIdeal_le_annihilator [IsLocallyNoetherian X] (F : X.Modules)
    [IsFiniteQC F] (Z : Closeds X) (W : X.affineOpens) (h : support F ∩ W.1 ⊆ Z) :
    ∃ k : ℕ, (Scheme.IdealSheafData.vanishingIdeal Z).ideal W ^ k ≤
      Module.annihilator Γ(X, W.1) Γ(F, W.1) := by
  have := finite_sections F W.2
  have : IsNoetherianRing Γ(X, W.1) := IsLocallyNoetherian.component_noetherian W
  refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (IsNoetherian.noetherian _)
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal, ← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical,
    ← Module.support_eq_zeroLocus, ← fromSpec_preimage_support F W.2]
  refine PrimeSpectrum.vanishingIdeal_anti_mono fun p hp => h ⟨hp, ?_⟩
  exact W.2.range_fromSpec.le ⟨p, rfl⟩

theorem pow_le_annihilator_kernel_unit (I : X.IdealSheafData) (E : X.Modules) [E.IsQuasicoherent]
    (W : X.affineOpens) {k : ℕ}
    (h : I.ideal W ^ (k + 1) ≤ Module.annihilator Γ(X, W.1) Γ(E, W.1)) :
    I.ideal W ^ k ≤ Module.annihilator Γ(X, W.1)
      Γ(kernel ((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app E), W.1) := by
  set φ := (Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app E with hφ
  intro a ha
  refine Module.mem_annihilator.2 fun t => ?_
  have h₁ : appLinear (kernel.ι φ) W.1 t ∈ (I.ideal W • ⊤ : Submodule Γ(X, W.1) Γ(E, W.1)) := by
    have := (surjective_and_ker_unit_subschemeι I E W).2
    rw [← hφ, ← range_kernel_ι_app] at this
    exact this.le ⟨t, rfl⟩
  have h₂ : ∀ u ∈ (I.ideal W • ⊤ : Submodule Γ(X, W.1) Γ(E, W.1)), a • u = 0 := fun u hu => by
    refine Submodule.smul_induction_on hu (fun r hr n _ => ?_) fun x y hx hy => ?_
    · rw [smul_smul]
      exact Module.mem_annihilator.1 (h (pow_succ (I.ideal W) k ▸ Ideal.mul_mem_mul ha hr)) n
    · rw [smul_add, hx, hy, add_zero]
  refine injective_kernel_ι_app φ W.1 ?_
  change appLinear (kernel.ι φ) W.1 (a • t) = appLinear (kernel.ι φ) W.1 0
  rw [map_smul, map_zero]
  exact h₂ _ h₁

theorem devissage : ∀ (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X] (P : X.Modules → Prop), (∀ F : X.Modules, IsZero F → P F) → (∀ S : ShortComplex X.Modules, S.ShortExact → IsFiniteQC S.X₁ → IsFiniteQC S.X₃ → P S.X₁ → P S.X₃ → P S.X₂) → (∀ (Z : Closeds X), IsIrreducible (Z : Set X) → (∀ F : X.Modules, IsFiniteQC F → GlobalTheory.QCoh.support F ⊂ (Z : Set X) → P F) → ∀ G : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Modules, IsFiniteQC G → P ((Scheme.Modules.pushforward (redι Z)).obj G)) → ∀ F : X.Modules, IsFiniteQC F → P F := by
  intro X _ P h0 hext hZ
  suffices H : ∀ T : Closeds X, ∀ F : X.Modules, IsFiniteQC F → support F = T → P F from
    fun F hF => H ⟨support F, isClosed_support F⟩ F hF rfl
  intro T
  induction T using WellFoundedLT.induction with
  | ind T ih =>
  intro F hF hT
  have ih' : ∀ E : X.Modules, IsFiniteQC E → support E ⊂ (T : Set X) → P E := fun E hE h =>
    ih ⟨support E, isClosed_support E⟩ h E hE rfl
  rcases (T : Set X).eq_empty_or_nonempty with he | hne
  · exact h0 F (support_eq_empty_iff.1 (hT.trans he))
  obtain ⟨Z, hZc, hZi, hZT, U, hU, ⟨x, hxT, hxU⟩, hUZ⟩ :=
    exists_isIrreducible_inter_open_subset T.isClosed hne
  obtain ⟨W, hW, hxW, hWU⟩ := exists_affine_mem_le (U := ⟨U, hU⟩) x hxU
  let Z' : Closeds X := ⟨Z, hZc⟩
  have hP := hZ Z' hZi fun E hE h => ih' E hE (h.trans_subset hZT)
  obtain ⟨k, hk⟩ := exists_pow_vanishingIdeal_le_annihilator F Z' ⟨W, hW⟩
    fun y hy => hUZ ⟨hT ▸ hy.1, hWU hy.2⟩
  have key : ∀ (k : ℕ) (E : X.Modules), IsFiniteQC E → support E ⊆ T →
      (Scheme.IdealSheafData.vanishingIdeal Z').ideal ⟨W, hW⟩ ^ k ≤
        Module.annihilator Γ(X, W) Γ(E, W) → P E := by
    intro k
    induction k with
    | zero =>
      intro E hE hET h
      refine ih' E hE ⟨hET, fun hle => ?_⟩
      have h₁ := (mem_support_iff_annihilator_le (F := E) hW ⟨x, hxW⟩).1 (hle hxT)
      rw [pow_zero, Ideal.one_eq_top] at h
      exact (hW.primeIdealOf ⟨x, hxW⟩).isPrime.ne_top (top_le_iff.1 (h.trans h₁))
    | succ k ihk =>
      intro E hE hET h
      let G := (Scheme.Modules.pullback (redι Z')).obj E
      let φ : E ⟶ (Scheme.Modules.pushforward (redι Z')).obj G :=
        (Scheme.Modules.pullbackPushforwardAdjunction (redι Z')).unit.app E
      have hepi : Epi φ := (epi_iff_forall_affine φ).2 fun V hV =>
        (surjective_and_ker_unit_subschemeι _ E ⟨V, hV⟩).1
      have hS : (ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)).ShortExact :=
        { exact := ShortComplex.exact_kernel φ }
      have hK : IsFiniteQC (kernel φ) := inferInstance
      exact hext _ hS hK (IsFiniteQC.of_epi φ)
        (ihk _ hK ((support_subset_of_mono (kernel.ι φ)).trans hET)
          (pow_le_annihilator_kernel_unit _ E ⟨W, hW⟩ h)) (hP G inferInstance)
  exact key k F hF hT.le hk

end GlobalTheory.QCoh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeSum.GrowthAtPlace

open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.AutSpace

variable {n : ℕ} {ε : Fin n → Bool} {P G : Mx n}

theorem norm_entry_le (A : Mx n) (i j : Fin n) : ‖A i j‖ ≤ 1 + hs A := by
  have h : ‖A i j‖ ^ 2 ≤ hs A :=
    (Finset.single_le_sum (f := fun b => ‖A i b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun a => ∑ b, ‖A a b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i))
  nlinarith [norm_nonneg (A i j)]

theorem one_add_hs_conj_le (Q y P : Mx n) : 1 + hs (Q * y * P) ≤ (1 + hs Q) * (1 + hs P) * (1 + hs y) := by
  have h1 := one_add_hs_mul_le (Q * y) P
  have h2 := mul_le_mul_of_nonneg_right (one_add_hs_mul_le Q y) (show 0 ≤ 1 + hs P by linarith [hs_nonneg P])
  nlinarith

theorem conj_mul (hP : IsUnit P) (a b : Mx n) : P⁻¹ * (a * b) * P = (P⁻¹ * a * P) * (P⁻¹ * b * P) := by
  have hd := (isUnit_iff_isUnit_det _).1 hP
  calc P⁻¹ * (a * b) * P = P⁻¹ * a * (P * P⁻¹) * b * P := by
        rw [Matrix.mul_nonsing_inv _ hd]; simp only [Matrix.mul_assoc, Matrix.one_mul]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem conj_exp (hP : IsUnit P) (X : Mx n) (t : ℝ) :
    P⁻¹ * NormedSpace.exp (t • X) * P = NormedSpace.exp (t • (P⁻¹ * X * P)) := by
  have hd := (isUnit_iff_isUnit_det _).1 hP
  rw [Matrix.mul_assoc, exp_mul_eq hP, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]

theorem conj_lie (hP : IsUnit P) (h : Pᴴ * Jm ε * P = G) {X : Mx n} (hX : X ∈ lieSet ε) :
    (P⁻¹ * X * P)ᴴ * G + G * (P⁻¹ * X * P) = 0 := by
  have hd := (isUnit_iff_isUnit_det _).1 hP
  have h1 : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  calc (P⁻¹ * X * P)ᴴ * G + G * (P⁻¹ * X * P)
      = Pᴴ * Xᴴ * (P * P⁻¹)ᴴ * Jm ε * P + Pᴴ * Jm ε * (P * P⁻¹) * X * P := by
        rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Pᴴ * (Xᴴ * Jm ε + Jm ε * X) * P := by
        rw [Matrix.mul_nonsing_inv _ hd]
        simp only [conjTranspose_one, Matrix.mul_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [h1, Matrix.mul_zero, Matrix.zero_mul]

theorem normInf_atTau_le {D : D7} {θ : InfF D} (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    {ε : Fin V.rank → Bool} {P : Mx V.rank} (hP : IsUnit P) (h : Pᴴ * Jm ε * P = gramAt D V τ) :
    ∃ c : ℝ, ∀ y ∈ UJset ε, normInf θ V (atTau θ V τ (P⁻¹ * y * P)) ≤ c * (1 + hs y) := by
  have hd := (isUnit_iff_isUnit_det _).1 hP
  set K : ℝ := (1 + hs P⁻¹) * (1 + hs P) + (1 + hs (1 : Mx V.rank)) with hK
  refine ⟨∑ _τ : D.what₂.Tau, ∑ _i : Fin V.rank, ∑ _j : Fin V.rank, (K + K), fun y hy => ?_⟩
  have hs1 := hs_nonneg (1 : Mx V.rank)
  have hsy := hs_nonneg y
  have hPP : 0 ≤ (1 + hs P⁻¹) * (1 + hs P) := mul_nonneg (by linarith [hs_nonneg P⁻¹]) (by linarith [hs_nonneg P])
  have b1 : ∀ z : Mx V.rank, hs z = hs y → 1 + hs (P⁻¹ * z * P) ≤ K * (1 + hs y) := fun z hz => by
    have := one_add_hs_conj_le P⁻¹ z P
    rw [hz] at this
    nlinarith
  have b2 : 1 + hs (1 : Mx V.rank) ≤ K * (1 + hs y) := by nlinarith
  have sp := atTau_spec hθ V τ (conj_inv_mem hP h hy)
  unfold normInf
  simp only [Finset.sum_mul]
  refine Finset.sum_le_sum fun τ' _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have e := infMat_mul_inv θ V τ' (atTau θ V τ (P⁻¹ * y * P))
  rw [add_mul]
  refine add_le_add ((norm_entry_le _ i j).trans ?_) ((norm_entry_le _ i j).trans ?_)
  · by_cases c : τ' = τ
    · subst c
      rw [sp.2.1]
      exact b1 y rfl
    · rw [sp.2.2 τ' c]
      exact b2
  · by_cases c : τ' = τ
    · subst c
      rw [sp.2.1] at e
      have e2 : (P⁻¹ * y⁻¹ * P) * (P⁻¹ * y * P) = 1 := by
        rw [← conj_mul hP, inv_mul_UJ hy, Matrix.mul_one, Matrix.nonsing_inv_mul _ hd]
      rw [← left_inv_eq_right_inv e2 e]
      exact b1 _ (hs_inv hy)
    · rw [sp.2.2 τ' c, Matrix.one_mul] at e
      rw [e]
      exact b2

theorem umg_atTau : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (φ : GA D V → ℂ), IsAutFunSm θ V φ → ∀ (ε : Fin V.rank → Bool) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ → ∀ x : GA D V, GlobalTheory.TypeSum.UMG ε (fun y => φ (x * atTau θ V τ (P⁻¹ * y * P))) := by
  intro D θ hθ V τ φ hφ ε P hP h x
  obtain ⟨N, hN⟩ := hφ.growth
  obtain ⟨c, hc⟩ := normInf_atTau_le hθ V τ hP h
  have hl : ∀ l : List (Mx V.rank), (∀ Y ∈ l, Y ∈ lieSet ε) →
      ∀ p ∈ l.map fun X => (τ, P⁻¹ * X * P), p.2 ∈ lieAt V p.1 := fun l hl p hp => by
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hp
    exact conj_lie hP h (hl Y hY)
  refine ⟨N, fun l y => ((l.map fun X => (τ, P⁻¹ * X * P)).foldr (fun p f => Rder θ V p.1 p.2 f) φ)
    (x * atTau θ V τ (P⁻¹ * y * P)), fun _ _ => rfl, fun l hl' X hX g hg => ?_, fun l hl' => ?_⟩
  · have hs := (linOnSm_foldr (θ := θ) (fun p : D.what₂.Tau × Mx V.rank => Rder θ V p.1 p.2) _
      fun p hp => linOnSm_Rder (hl l hl' p hp)).mem φ hφ.smooth
    have hd := (differentiable_oneP hs (τ := τ) (conj_lie hP h hX) (x * atTau θ V τ (P⁻¹ * g * P)) 0).hasDerivAt
    refine HasDerivAt.congr_of_eventuallyEq hd (Filter.Eventually.of_forall fun t => ?_)
    beta_reduce
    rw [conj_mul hP, atTau_mul hθ V τ (conj_inv_mem hP h hg) (conj_inv_mem hP h (exp_mem_UJ hX t)), conj_exp hP,
      ← mul_assoc]
    rfl
  · obtain ⟨C, hC⟩ := hN _ (hl l hl') x
    refine ⟨|C| * c ^ N, fun g hg => (hC _ (atTau_mem V τ _)).trans ?_⟩
    have h0 := normInf_nonneg (θ := θ) (atTau θ V τ (P⁻¹ * g * P))
    rw [mul_assoc |C|, ← mul_pow]
    exact mul_le_mul (le_abs_self _) (pow_le_pow_left₀ h0 (hc g hg) N) (pow_nonneg h0 _) (abs_nonneg _)

end GlobalTheory.TypeSum.GrowthAtPlace

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

namespace SerreCriterion

variable {X : Scheme.{0}}

theorem exists_germ_eq_of_support_subset {F : X.Modules} {y : X} (hy : IsClosed ({y} : Set X))
    (hF : support F ⊆ {y}) (t : (F.presheaf.stalk y :)) :
    ∃ s : Γ(F, ⊤), F.presheaf.germ ⊤ y trivial s = t := by
  classical
  by_cases h : y ∈ support F
  · obtain ⟨s, hs⟩ := (germ_support_bijective (F := F) ((Set.finite_singleton y).subset hF)
      fun x hx => by rw [show x = y from hF hx]; exact hy).2
      (Function.update (fun _ => 0) ⟨y, h⟩ t)
    refine ⟨s, (congrFun hs ⟨y, h⟩).trans ?_⟩
    simp
  · exact ⟨0, (notMem_support_iff.1 h).elim _ _⟩

theorem support_pushforward_subscheme_subset (Y : X.IdealSheafData) :
    support ((Scheme.Modules.pushforward Y.subschemeι).obj (structureModule Y.subscheme)) ⊆
      Y.support := by
  intro x hx
  by_contra h
  refine notMem_support_iff.2 (subsingleton_of_forall_eq 0 fun t => ?_) hx
  obtain ⟨V, hV, hxV, s, rfl⟩ := exists_germ_eq_of_mem (U := Y.support.compl) h t
  have e : Y.subschemeι ⁻¹ᵁ V = ⊥ :=
    eq_bot_iff.2 fun z hz => (hV hz (Y.range_subschemeι.le ⟨z, rfl⟩)).elim
  have : Subsingleton Γ(Y.subscheme, Y.subschemeι ⁻¹ᵁ V) := by
    rw [e]
    infer_instance
  have hs : s = 0 := this.elim s 0
  rw [hs, map_zero]

theorem not_isUnit_of_toSubscheme_eq_zero (Y : X.IdealSheafData) {y : X} (hy : y ∈ Y.support)
    (g : ((structureModule X).presheaf.stalk y :)) (hg : stalkLinear (toSubscheme Y) y g = 0) :
    ¬ IsUnit (structureModuleStalkEquiv y g) := by
  have hex := (exact_iff_stalkLinear (ShortComplex.mk (kernel.ι (toSubscheme Y)) (toSubscheme Y)
    (kernel.condition _))).1 (ShortComplex.exact_kernel _) y
  obtain ⟨u, rfl⟩ := (hex g).1 hg
  obtain ⟨V, hV, u, rfl⟩ := (idealModule Y).presheaf.exists_germ_eq u
  intro hu
  refine notMem_support_of_mem_basicOpen Y u ((X.mem_basicOpen _ y hV).2 ?_) hy
  rw [← structureModuleStalkEquiv_germ, ← stalkLinear_germ]
  exact hu

theorem exists_mem_nonzeroLocus {M : LB X} (hM : M.IsLB) {J : X.Modules}
    (j : J ⟶ structureModule X) (Y : X.IdealSheafData) {y : X} (hY : (Y.support : Set X) = {y})
    (h : Subsingleton (coh (twist (kernel (j ≫ toSubscheme Y)) M) 1))
    {U : X.Opens} (hU : y ∈ U) (t : Γ(J, U))
    (ht : structureModuleSectionsEquiv U (j.app U t) = 1) :
    ∃ a : Γ(twist J M, ⊤), y ∈ nonzeroLocus (secOfTwist j a) := by
  set φ := j ≫ toSubscheme Y with hφ
  let S : ShortComplex X.Modules :=
    ShortComplex.mk (kernel.ι φ) (cokernel.π (kernel.ι φ)) (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  have hS' : (S.map (twistFunctor M)).ShortExact := Twist.shortExact_map hM hS
  have hsurj := cohOn.app_surjective hS' ⊤ h
  have hyc : IsClosed ({y} : Set X) := hY ▸ Y.support.isClosed
  have hQ : support (twist S.X₃ M) ⊆ {y} := by
    rw [support_twist hM, ← hY]
    refine fun x hx => support_pushforward_subscheme_subset Y ?_
    have := mem_support_iff.1 hx
    exact mem_support_iff.2 (stalkLinear_injective (Abelian.factorThruCoimage φ) x).nontrivial
  obtain ⟨c, hc⟩ := exists_chart hM y
  obtain ⟨b, hb⟩ := exists_germ_eq_of_support_subset hyc hQ
    ((stalkEquiv S.X₃ hM c hc).symm (stalkLinear S.g y (J.presheaf.germ U y hU t)))
  obtain ⟨a, rfl⟩ := hsurj b
  refine ⟨a, basicOpen_le_nonzeroLocus _ c ((X.mem_basicOpen _ y hc).2 ?_)⟩
  have hm : y ∈ ⊤ ⊓ M.U c := ⟨trivial, hc⟩
  replace hb := (stalkEquiv_germ hM c hc (V := ⊤) trivial _).symm.trans
    ((LinearEquiv.eq_symm_apply _).1 hb)
  have h₁ : stalkLinear S.g y (J.presheaf.germ _ y hm (coord (F := J) a c)) =
      stalkLinear S.g y (J.presheaf.germ U y hU t) :=
    (stalkLinear_germ S.g y hm _).trans hb
  have h₂ : stalkLinear φ y (J.presheaf.germ U y hU t -
      J.presheaf.germ _ y hm (coord (F := J) a c)) = 0 := by
    rw [← Abelian.coimage.fac φ, stalkLinear_comp, LinearMap.comp_apply, map_sub]
    exact (congrArg _ (sub_eq_zero.2 h₁.symm)).trans (map_zero _)
  rw [hφ, stalkLinear_comp, LinearMap.comp_apply] at h₂
  have h₃ := not_isUnit_of_toSubscheme_eq_zero Y (y := y) (hY.ge rfl) _ h₂
  rw [map_sub, map_sub, stalkLinear_germ, stalkLinear_germ, structureModuleStalkEquiv_germ,
    structureModuleStalkEquiv_germ, ht, map_one] at h₃
  have hu := (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_right h₃
  exact (congrArg IsUnit (X.presheaf.germ_res_apply (homOfLE _) y hc _)).mpr hu

end SerreCriterion


open SerreCriterion in
theorem isAmpleLB_of_subsingleton_coh_one (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X]
    (L : LB X) (hL : L.IsLB)
    (h : ∀ F : X.Modules, IsFiniteQC F →
      ∃ n : ℕ, 1 ≤ n ∧ Subsingleton (coh (twist F (lbPow L n)) 1)) : IsAmpleLB L := by
  refine ⟨hL, inferInstance, fun x => ?_⟩
  obtain ⟨y, hxy, hy⟩ := (isClosed_closure (s := ({x} : Set X))).exists_closed_singleton
    ⟨x, subset_closure rfl⟩
  obtain ⟨W, hW, hyW⟩ := exists_affine_mem y
  let I := Scheme.IdealSheafData.vanishingIdeal W.compl
  have hI : ∀ z, z ∉ I.support ↔ z ∈ W := fun z => by
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact not_not
  let Y := Scheme.IdealSheafData.vanishingIdeal (X := X) ⟨{y}, hy⟩
  have hY : (Y.support : Set X) = {y} := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  obtain ⟨n, hn, hz⟩ := h (kernel (idealModuleι I ≫ toSubscheme Y)) (.of_mono (kernel.ι _))
  obtain ⟨t, ht⟩ := exists_idealModuleι_app_eq_one I fun z => (hI z).2
  have hM := isLB_lbPow hL n
  obtain ⟨a, ha⟩ := exists_mem_nonzeroLocus hM _ Y hY hz hyW t ht
  have hle : nonzeroLocus (secOfTwist (idealModuleι I) a) ≤ W := iSup_le fun c z hz => (hI z).1 <| by
    rw [secOfTwist_f] at hz
    exact notMem_support_of_mem_basicOpen I _ ((X.basicOpen_res _ (homOfLE _).op).le hz).2
  refine ⟨n, hn, _, (specializes_iff_mem_closure.2 hxy).mem_open (Opens.isOpen _) ha, ?_⟩
  exact inf_eq_left.2 hle ▸ isAffineOpen_nonzeroLocus_inf hM _ hW

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfOrderDvd
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelChoices

open Formalism.L2.Host Formalism.L2.Herm

variable {D : D7}

theorem mem_crdLat (V : HSp D) (x : Fin V.rank → D.host.E) : x ∈ crdLat V V.L0 ↔ (crd V).symm x ∈ V.L0 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    show (crd V).symm (crd V y) ∈ V.L0
    rwa [LinearEquiv.symm_apply_apply]
  · intro h
    exact ⟨_, h, (crd V).apply_symm_apply x⟩

theorem coe_crdLat (V : HSp D) : (crdLat V V.L0 : Set (Fin V.rank → D.host.E)) = L0c D V := by
  ext x
  rw [SetLike.mem_coe, mem_crdLat]
  show V.frame.equivFun.symm x ∈ V.L0 ↔ _
  rw [Module.Basis.equivFun_symm_apply]
  rfl

theorem dualL_crdLat (V : HSp D) : dualL D.sp.cm V (crdLat V V.L0) = crdLat V V.L0 := by
  unfold dualL
  conv_rhs => rw [← Submodule.span_eq (crdLat V V.L0)]
  congr 1
  ext x
  rw [SetLike.mem_coe, mem_crdLat]
  conv_rhs => rw [← V.baseLattice_isUnimodular]
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply,
    Submodule.mem_one]
  constructor
  · intro h y hy
    have := h (crd V y) ⟨y, hy, rfl⟩
    rw [hT_crd D.sp.cm, LinearEquiv.apply_symm_apply]
    exact this
  · rintro h _ ⟨y, hy, rfl⟩
    have := h y hy
    rw [hT_crd D.sp.cm, LinearEquiv.apply_symm_apply] at this
    exact this

theorem isSDFrame_of_one {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (h : IsSDFrame V β Λ 1) (N : ℕ) : IsSDFrame V β Λ N := by
  obtain ⟨c, hc⟩ := h
  refine ⟨0, ?_⟩
  rw [one_pow] at hc
  rwa [pow_zero]

theorem isUnitary_of_orderDvd {L : Type} [Field L] [NumberField L] {χ : HChar L} {n : ℕ} (hn : 0 < n) (h : χ.OrderDvd n) :
    χ.IsUnitary := by
  intro x
  have h1 : (χ.1 x) ^ n = 1 := by
    have : (χ ^ n).1 x = 1 := by rw [h]; rfl
    rw [← this]; rfl
  have h2 : ‖((χ.1 x : ℂˣ) : ℂ)‖ ^ n = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2

theorem exists_levCh (D : D7) (C : CharFrame D) (T : Type) (μ0 : T) (ξ : T → HChar D.host.E)
    (Q : T → Finset (Pl D.host.E)) (hinj : Function.Injective ξ) (hbase : ξ μ0 = 1)
    (hfin : ∀ t, ∃ n : ℕ, 0 < n ∧ (ξ t).OrderDvd n) (htriv : ∀ t, (ξ t).TrivOn D.host.F)
    (htame : ∀ t v, (ξ t).TameAt v) (hpl : ∀ t, Lev.IsTwistPlaces D.host.g (Q t))
    (hoff : ∀ t, ∀ PP ∈ Q t, ((D.host.QS * D.host.q * D.host.d * D.sp.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ∧
      ∀ u : D.what₂.Word, (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (hde : ∀ p ∈ ({D.host.pde, D.host.pde'} : Set ℕ), ∃ 𝔭 : HeightOneSpectrum (𝓞 D.host.K),
      ∀ t, ∀ PP ∈ Q t, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP.under (𝓞 D.host.K) = 𝔭)
    (hram : ∀ t PP, ¬ (ξ t).UnrAt PP ↔ PP ∈ Q t ∨ ∃ PP' ∈ Q t, Lev.IsConjPl PP' PP) :
    ∃ L : LevCh D T, L.C = C ∧ L.xiH = ξ ∧ L.Q = Q ∧ (∀ j, L.ΛY j = crdLat _ (Yc D j).L0) ∧ L.Is μ0 := by
  classical
  choose m hm using fun j : Fin D.R.m => GlobalTheory.T.exists_cmAdeleUnitCharacter_reading_heckeChar D (C.mu0 j) (C.isMu0 j).unitary
  obtain ⟨η, hη⟩ := GlobalTheory.T.exists_cmAdeleUnitCharacter_reading_heckeChar D C.eta C.isEta.unitary
  choose x hx using fun t => GlobalTheory.T.exists_cmAdeleUnitCharacter_reading_heckeChar D (ξ t) (by obtain ⟨n, hn, h⟩ := hfin t; exact isUnitary_of_orderDvd hn h)
  choose r hr using fun (j : Fin D.R.m) PP => GlobalTheory.exists_isRes_of_tameAt D (C.mu0 j) PP ((C.isMu0 j).tame PP)
  choose s hs using fun t PP => GlobalTheory.exists_isRes_of_tameAt D (ξ t) PP (htame t PP)
  choose β hβ using fun V : HSp D => GlobalTheory.T.exists_selfDual_adelic_frame_level_one D V (crdLat V V.L0) (coe_crdLat V) (dualL_crdLat V)
  refine ⟨{ C := C, xiH := ξ
            mu0 := fun j => if h : j - 1 < D.R.m then m ⟨j - 1, h⟩ else 1
            eta := η, xi := x
            Pg := Finset.univ.biUnion fun k => aboveF (L := D.host.E) D.host.K (C.P.pb k)
            Q := Q
            chi := fun j PP => if h : j - 1 < D.R.m then (r ⟨j - 1, h⟩ PP)⁻¹ else 1
            xiR := s
            ΛY := fun _ => crdLat _ (HSpace.L0 _), ΛX := crdLat _ (HSpace.L0 _)
            ΛV := fun _ => crdLat _ (HSpace.L0 _), ΛW := fun _ => crdLat _ (HSpace.L0 _)
            βY := fun _ => β _, βX := β _, βV := fun _ => β _, βW := fun _ => β _ }, rfl, rfl, rfl, fun _ => rfl, ?_⟩
  exact
    { mu0 := fun j => by
        have h : (j : ℕ) + 1 - 1 < D.R.m := j.2
        simp only [dif_pos h]
        exact hm j
      eta := hη, xi := hx, xi_inj := hinj, xi_base := hbase, xi_fin := hfin, xi_triv := htriv, xi_tame := htame
      Pg := fun PP => by
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, aboveF, Set.Finite.mem_toFinset]
        rfl
      Q_pl := hpl, Q_off := hoff, Q_de := hde, Q_ram := hram
      chi := fun j PP _ => by
        have h : (j : ℕ) + 1 - 1 < D.R.m := j.2
        simp only [dif_pos h, inv_inv]
        exact hr j PP
      xiR := fun t PP _ => hs t PP
      βY := fun j _ => isSDFrame_of_one (hβ _) _
      βX := hβ _, βV := fun _ => hβ _, βW := fun _ => hβ _ }

theorem exists_levCh_unit : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D), ∃ L : LevCh D Unit, L.C = C ∧ L.Is () := by
  intro D C
  obtain ⟨L, h1, -, -, -, h2⟩ := exists_levCh D C Unit () (fun _ => 1) (fun _ => ∅) (fun _ _ _ => rfl) rfl
    (fun _ => ⟨1, one_pos, one_pow 1⟩) (fun _ => (isPsi_one (H := D.host) 2).triv) (fun _ _ _ _ _ => rfl)
    (fun _ _ h => absurd h (Finset.notMem_empty _)) (fun _ _ h => absurd h (Finset.notMem_empty _))
    (fun _ _ => ⟨C.P.pb 0, fun _ _ h => absurd h (Finset.notMem_empty _)⟩)
    (fun _ _ => iff_of_false (fun h => h fun _ _ => rfl) (by simp))
  exact ⟨L, h1, h2⟩

end GlobalTheory.LevelChoices
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAndHasSumKAvg
noncomputable section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.ExpansionAverage

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem integrable_K {E : Type} [NormedAddCommGroup E] {F : KG ε → E} (hF : Continuous F) : Integrable F (muK ε) :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

theorem toMK_mem (k : KG ε) : toMK k ∈ UJset ε := K_le_UJ (toMK_mem_K k)

theorem integrable_Dw (h : Std ε σ) {e : KG ε → ℂ} (he : Continuous e) {l : List (Mx n)}
    (hl : ∀ X ∈ l, X ∈ lieSet ε) {w : H} (hw : Sm ε σ w) :
    Integrable (fun k : KG ε => e k • Dw σ l (σ (toMK k) w)) (muK ε) :=
  integrable_K (he.smul ((h.continuousOn_Dw hl hw).comp_continuous (continuous_toMK ε) toMK_mem))

theorem Dw_kAvg (h : Std ε σ) {e : KG ε → ℂ} (he : Continuous e) {l : List (Mx n)}
    (hl : ∀ X ∈ l, X ∈ lieSet ε) {w : H} (hw : Sm ε σ w) (hw' : Sm ε σ (kAvg ε σ e w)) :
    Dw σ l (kAvg ε σ e w) = ∫ k, e k • Dw σ l (σ (toMK k) w) ∂(muK ε) := by
  refine h.dense_smooth.eq_of_inner_right ℂ fun y hy => ?_
  have h0 : Integrable (fun k : KG ε => e k • σ (toMK k) w) (muK ε) := integrable_Dw h he (l := []) (by simp) hw
  rw [inner_Dw h.1 hl hy hw', kAvg, ← integral_inner h0, ← integral_inner (integrable_Dw h he hl hw),
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [inner_smul_right]
  rw [inner_Dw h.1 hl hy (hw.translate h.1 (toMK_mem k))]
  ring

theorem form_kAvg (h : Std ε σ) {e : KG ε → ℂ} (he : Continuous e) {ℓ : H →ₗ[ℂ] ℂ} (hℓ : Sobolev₂ (lieSet ε) σ ℓ)
    {w : H} (hw : Sm ε σ w) (hw' : Sm ε σ (kAvg ε σ e w)) :
    ℓ (kAvg ε σ e w) = ∫ k, e k * ℓ (σ (toMK k) w) ∂(muK ε) := by
  obtain ⟨m, S, Λ, hS, hΛ⟩ := exists_factor (isUnit_Jm ε) h.1 hℓ
  have hΛ' : ∀ w, Sm ε σ w → ℓ w = ∑ i, Λ i (Dw σ (S i) w) := hΛ
  rw [hΛ' _ hw']
  simp only [fun i => Dw_kAvg h he (hS i) hw hw',
    fun i => ((Λ i).integral_comp_comm (integrable_Dw h he (hS i) hw)).symm]
  rw [← integral_finsetSum _ fun i _ => (Λ i).integrable_comp (integrable_Dw h he (hS i) hw)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [hΛ' _ (hw.translate h.1 (toMK_mem k)), Finset.mul_sum, map_smul, smul_eq_mul]

theorem continuousOn_and_hasSum_kAvg : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ →
    ∀ (S : List (List (Mx n))) (v : ℕ → H) (ℓ : ℕ → (H →ₗ[ℂ] ℂ)) (C : ℕ → ℝ) (f : Mx n → ℂ),
      Words (lieSet ε) S → Ctrl (lieSet ε) (UJset ε) σ S → IsExpn (lieSet ε) (UJset ε) σ S v ℓ C f →
      ContinuousOn f (UJset ε) ∧ ∀ e : KG ε → ℂ, Continuous e → (∀ w, Sm ε σ (kAvg ε σ e w)) → ∀ g ∈ UJset ε,
        HasSum (fun i => ℓ i (σ g (kAvg ε σ e (v i)))) (∫ k, e k * f (g * toMK k) ∂(muK ε)) := by
  intro n ε H _ _ _ σ h S v ℓ C f hS ⟨B, hB, hBd⟩ hE
  have hsc := hE.sobCont hS
  obtain ⟨hv, hC, hb, hsum, hf⟩ := hE
  have hc : ∀ i, ContinuousOn (fun g => ℓ i (σ g (v i))) (UJset ε) := fun i => h.continuousOn_coef (hsc i) (hv i)
  have hbd : ∀ (M : ℝ) i, ∀ g ∈ UJset ε, B g ≤ M → ‖ℓ i (σ g (v i))‖ ≤ M * (C i * sobNorm σ S (v i)) := by
    intro M i g hg hM
    calc ‖ℓ i (σ g (v i))‖ ≤ C i * sobNorm σ S (σ g (v i)) := hb i _ (Sm.translate h.1 (hv i) hg)
      _ ≤ C i * (M * sobNorm σ S (v i)) := mul_le_mul_of_nonneg_left
          ((hBd g hg _ (hv i)).trans (mul_le_mul_of_nonneg_right hM (sobNorm_nonneg _ _ _))) (hC i)
      _ = _ := by ring
  refine ⟨fun g₀ hg₀ => ?_, fun e he hs g hg => ?_⟩
  · have ho : {g | B g < B g₀ + 1} ∈ 𝓝 g₀ := (isOpen_lt hB continuous_const).mem_nhds (lt_add_one (B g₀))
    have h1 : ContinuousOn (fun g => ∑' i, ℓ i (σ g (v i))) (UJset ε ∩ {g | B g < B g₀ + 1}) :=
      continuousOn_tsum (fun i => (hc i).mono Set.inter_subset_left) (hsum.mul_left (B g₀ + 1))
        fun i g hg => hbd _ i g hg.1 (le_of_lt hg.2)
    have h2 : ContinuousOn f (UJset ε ∩ {g | B g < B g₀ + 1}) := h1.congr fun g hg => (hf g hg.1).tsum_eq.symm
    exact (continuousWithinAt_inter ho).1 (h2 g₀ ⟨hg₀, lt_add_one (B g₀)⟩)
  · have hm : ∀ k : KG ε, g * toMK k ∈ UJset ε := fun k => mul_mem_UJ hg (toMK_mem k)
    have hcm : Continuous fun k : KG ε => g * toMK k := continuous_const.mul (continuous_toMK ε)
    obtain ⟨M, hM⟩ := (isCompact_range (hB.comp hcm)).bddAbove
    have hM' : ∀ k : KG ε, B (g * toMK k) ≤ M := fun k => hM ⟨k, rfl⟩
    have hF : ∀ i, Integrable (fun k : KG ε => e k * ℓ i (σ (g * toMK k) (v i))) (muK ε) := fun i =>
      integrable_K (he.mul ((hc i).comp_continuous hcm hm))
    have hS' : Summable fun i => ∫ k, ‖e k * ℓ i (σ (g * toMK k) (v i))‖ ∂(muK ε) := by
      refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun k => norm_nonneg _) (fun i => ?_)
        ((hsum.mul_left M).mul_left (∫ k, ‖e k‖ ∂(muK ε)))
      rw [← integral_mul_const]
      refine integral_mono (hF i).norm ((integrable_K he.norm).mul_const _) fun k => ?_
      simp only [norm_mul]
      exact mul_le_mul_of_nonneg_left (hbd M i _ (hm k) (hM' k)) (norm_nonneg _)
    have key := hasSum_integral_of_summable_integral_norm hF hS'
    simp only [fun k => ((hf _ (hm k)).mul_left (e k)).tsum_eq] at key
    refine Eq.mpr (congrArg (HasSum · _) (funext fun i => ?_)) key
    have := form_kAvg h he (sobCont_translate h.1 (hsc i) hg) (hv i) (hs (v i))
    simp only [fun k => sigma_mul h.1 hg (toMK_mem k)]
    exact this

end GlobalTheory.ExpansionAverage

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsKFinDRep
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

theorem isKFin_dRep : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ v, IsKFin ε σ v → ∀ X ∈ lieSet ε,
      IsKFin ε σ (dRep σ X v) := by
  intro n ε H _ _ _ σ h v hv X hX
  obtain ⟨S, h1, h2, h3⟩ := hv
  have hS : S ≤ smooth (Jm ε) σ := fun s hs => h.2.2.1 s ⟨S, h1, hs, h3⟩
  let b := Module.finBasis ℝ (lie (Jm ε))
  let L : Fin (Module.finrank ℝ (lie (Jm ε))) → (S →ₗ[ℂ] H) := fun i =>
    (smooth (Jm ε) σ).subtype ∘ₗ dOp (isUnit_Jm ε) h.1 (b i).2 ∘ₗ Submodule.inclusion hS
  have hL : ∀ i (s : S), L i s = dRep σ (b i) s := fun _ _ => rfl
  let T : Submodule ℂ H := ⨆ i, LinearMap.range (L i)
  have hT : ∀ Y ∈ lieSet ε, ∀ s ∈ S, dRep σ Y s ∈ T := by
    intro Y hY s hs
    have e : Y = ∑ i, b.repr ⟨Y, hY⟩ i • (b i : Mx n) := by
      have := congrArg Subtype.val (b.sum_repr ⟨Y, hY⟩)
      simpa only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] using this.symm
    rw [e, h.dRep_sum (fun i => (b i).2) (hS hs)]
    refine T.sum_mem fun i _ => T.smul_mem _ ?_
    exact Submodule.mem_iSup_of_mem i ⟨⟨s, hs⟩, rfl⟩
  refine ⟨T, inferInstance, hT X hX v h2, fun k hk w hw => ?_⟩
  have hg := K_le_UJ hk
  have : T ≤ T.comap (σ k : H →ₗ[ℂ] H) := by
    refine iSup_le fun i => ?_
    rintro _ ⟨s, rfl⟩
    have hinv : (k⁻¹)⁻¹ = k := Matrix.inv_eq_left_inv (mul_inv_UJ hg)
    have hY : k * (b i : Mx n) * k⁻¹ ∈ lieSet ε := by
      have := conj_mem_lie (isUnit_Jm ε) (inv_mem_UJ hg) (b i).2
      rwa [hinv] at this
    have e := Dw_translate h.1 hg (hS s.2) (l := [k * (b i : Mx n) * k⁻¹]) (by simpa using hY)
    have e2 : k⁻¹ * (k * (b i : Mx n) * k⁻¹) * k = b i := by
      rw [← mul_assoc, ← mul_assoc, inv_mul_UJ hg, one_mul, mul_assoc, inv_mul_UJ hg, mul_one]
    simp only [Dw, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, e2] at e
    show σ k (dRep σ (b i) s) ∈ T
    rw [← e]
    exact hT _ hY _ (h3 k hk s s.2)
  exact this hw

end GlobalTheory.TypeSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMtTieCoord
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.DivisionValues
open scoped InnerProductSpace Matrix

namespace GlobalTheory.Mem.LiftForms

section Main

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem jMt_injective (μ : D.what₂.Tup) (j : ℕ) : Function.Injective (D.what₂.jMt μ j) := by
  have hli := (D.what₂.jMt_basis μ j (Module.Free.chooseBasis _ _)).1
  have := hli.finite
  have := Fintype.ofFinite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL μ j))
  exact inj_of_li D.what₂.embLL (D.what₂.jMt μ j) (Module.Free.chooseBasis _ _) hli

theorem carrier_subset (μ : D.what₂.Tup) (j : ℕ) : ∀ m ∈ (D.what₂.MtLat μ j).carrier, m ∈ Set.range (D.what₂.jMt μ j) := by
  rintro _ ⟨c, rfl⟩
  refine Finset.sum_induction _ (fun m => m ∈ Set.range (D.what₂.jMt μ j)) ?_ ⟨0, map_zero _⟩ fun v hv => ?_
  · rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, map_add _ _ _⟩
  · obtain ⟨x, rfl⟩ := D.what₂.MtLat_sub μ j v hv
    exact ⟨D.what₂.OtoLL (c (D.what₂.jMt μ j x)) • x, map_smulₛₗ _ _ _⟩

variable {R : RealDat D A Ks} {F : Face D A}


end Main

section Comparison₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

end Comparison₂

end GlobalTheory.Mem.LiftForms

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMeasDef
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.DefiniteMeasure

open Formalism.IndefR.Lev GlobalTheory.Mem.VolExists

theorem exists_probHaar (P Q : ℕ) (h : P = 0 ∨ Q = 0) : ∃ ν : Measure (UpqT P Q), ν.IsHaarMeasure ∧
    ∀ m : Measure (UpqT P Q), (m.IsHaarMeasure ∧ IsProbabilityMeasure m) ↔ m = ν := by
  haveI : CompactSpace (UpqT P Q) := by
    rcases h with rfl | rfl
    exacts [(GlobalTheory.compactSpace_UpqT_definite Q).2, (GlobalTheory.compactSpace_UpqT_definite P).1]
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  let ν : Measure (UpqT P Q) := Measure.haarMeasure ⊤
  haveI hν : ν.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure ⊤
  haveI hp : IsProbabilityMeasure ν := ⟨Measure.haarMeasure_self (K₀ := ⊤)⟩
  refine ⟨ν, hν, fun m => ⟨fun ⟨h1, h2⟩ => ?_, fun e => e ▸ ⟨hν, hp⟩⟩⟩
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure m ν

end GlobalTheory.Mem.DefiniteMeasure
end
