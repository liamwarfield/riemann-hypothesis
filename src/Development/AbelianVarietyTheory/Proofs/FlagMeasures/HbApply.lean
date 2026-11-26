module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatsDiscStable
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensAll
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfUnimodular
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.PtMatIsUnit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HbApply
noncomputable section
open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full

namespace GlobalTheory.RowsOrb

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

def Wb : Submodule D.host.E (VS D).V where
  carrier := {v | ∀ a, (VS D).hT (X.eX a) v = 0 ∧ (VS D).hT (X.fY a) v = 0}
  add_mem' := by
    intro x y hx hy a
    exact ⟨by rw [map_add (f := _), (hx a).1, (hy a).1, add_zero], by rw [map_add (f := _), (hx a).2, (hy a).2, add_zero]⟩
  zero_mem' := fun a => ⟨map_zero _, map_zero _⟩
  smul_mem' := by
    intro c x hx a
    exact ⟨by rw [map_smul, (hx a).1, smul_zero], by rw [map_smul, (hx a).2, smul_zero]⟩

theorem mem_Wb (v : (VS D).V) : v ∈ Wb X ↔ ∀ a, (VS D).hT (X.eX a) v = 0 ∧ (VS D).hT (X.fY a) v = 0 := Iff.rfl

def hb : Wb X →ₗ⋆[D.host.E] Wb X →ₗ[D.host.E] D.host.E := GlobalTheory.Mass.hRes (VS D).hT (Wb X)

def zb (u : D.what₂.Word) : Wb X := ⟨X.zu u, fun a => X.zu_orth u a⟩

def Ub (u : D.what₂.Word) : Submodule D.host.E (Wb X) :=
  GlobalTheory.Mass.perp (hb X) (Submodule.span D.host.E {zb X u})

def hU (u : D.what₂.Word) : Ub X u →ₗ⋆[D.host.E] Ub X u →ₗ[D.host.E] D.host.E := GlobalTheory.Mass.hRes (hb X) (Ub X u)

def Lmap (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Submodule (𝓞 D.host.E) (Wb X) :=
  GlobalTheory.Mass.latIn (Wb X) (Λ ⊔ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X)

abbrev Gz (u : D.what₂.Word) : Subgroup (Formalism.HermitianLatticesTheory.isom (hb X)) :=
  MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom (hb X)) (zb X u)

theorem hb_apply (x y : Wb X) : hb X x y = (VS D).hT (x : (VS D).V) (y : (VS D).V) := rfl

theorem zb_coe (u : D.what₂.Word) : ((zb X u : Wb X) : (VS D).V) = X.zu u := rfl

theorem hU_apply (u : D.what₂.Word) (x y : Ub X u) :
    hU X u x y = (VS D).hT ((x : Wb X) : (VS D).V) ((y : Wb X) : (VS D).V) := rfl

theorem mem_Ub (u : D.what₂.Word) (x : Wb X) : x ∈ Ub X u ↔ (VS D).hT (X.zu u) (x : (VS D).V) = 0 := by
  unfold Ub GlobalTheory.Mass.perp
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro H
    exact H (zb X u) (Submodule.mem_span_singleton_self _)
  · intro H y hy
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply]
    change _ • (VS D).hT (X.zu u) (x : (VS D).V) = 0
    rw [H, smul_zero]

theorem mem_Lmap (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (w : Wb X) :
    w ∈ Lmap X u Λ ↔ (w : (VS D).V) ∈ Λ ⊔ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X := Iff.rfl

end GlobalTheory.RowsOrb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PureFiniteAdelicTestFunctionContinuousCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PureFiniteAdelicTestFunctionContinuousCompact
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory.PureFinite

open PI.VolStabS.PositiveNearLattice PI.VolStabS.AdmissibleCompactSupport GlobalTheory.GaugeEx Set

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) {n M : ℕ}

include b in
theorem continuous_projV_fin (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (fun X : Fin n → Fin M → Af F ⊗[F] E => projV v X) := by
  have h : Continuous (evalV F v) :=
    RestrictedProduct.continuous_eval (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v
  haveI : IsTopologicalRing (Af F) := inferInstance
  have h2 : Continuous (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)) :=
    continuous_map_tens b (evalV F v) h
  exact continuous_pi fun a => continuous_pi fun i =>
    h2.comp ((continuous_apply i).comp (continuous_apply a))

theorem projV_add (v : HeightOneSpectrum (𝓞 F)) (X Y : Fin n → Fin M → Af F ⊗[F] E) :
    projV v (X + Y) = projV v X + projV v Y := by
  funext a i
  simp [projV, map_add (f := _)]

theorem latV_add (v : HeightOneSpectrum (𝓞 F)) {Y Z : Fin n → Fin M → Fv F v ⊗[F] E}
    (hY : Y ∈ latV b v) (hZ : Z ∈ latV b v) : Y + Z ∈ latV b v := by
  intro a i k
  simp only [Pi.add_apply, map_add (f := _), Finsupp.add_apply]
  exact add_mem (hY a i k) (hZ a i k)

variable (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ)

theorem continuous_finprod (hSB : ∀ v, IsSB (Φv v))
    (hae : ∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1) :
    Continuous (fun X : Fin n → Fin M → Af F ⊗[F] E => ∏ᶠ v, Φv v (projV v X)) := by
  classical
  rw [continuous_iff_continuousAt]
  intro X
  have hS := Filter.eventually_cofinite.1 (hae.and (eventually_mem_latV b X))
  let O : Set (Af F) := {x | ∀ v, x v ∈ v.adicCompletionIntegers F}
  have hOo : IsOpen O :=
    RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun v => Valued.isOpen_valuationSubring _)
  let U : Set (Fin n → Fin M → Af F ⊗[F] E) := {Y | ∀ a i k, crd b (Af F) ((Y - X) a i) k ∈ O}
  have hUo : IsOpen U := by
    have e : U = ⋂ a, ⋂ i, ⋂ k, (fun Y : Fin n → Fin M → Af F ⊗[F] E =>
        crd b (Af F) ((Y - X) a i) k) ⁻¹' O := by
      ext Y; simp [U]
    rw [e]
    exact isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun i =>
      isOpen_iInter_of_finite fun k => hOo.preimage ((continuous_crd b (Af F) k).comp
        ((continuous_apply i).comp ((continuous_apply a).comp (continuous_id.sub continuous_const))))
  have hXU : X ∈ U := by
    intro a i k v
    simp only [sub_self, crd, Pi.zero_apply, map_zero, Finsupp.zero_apply]
    exact zero_mem (v.adicCompletionIntegers F)
  have hev : (fun Y : Fin n → Fin M → Af F ⊗[F] E => ∏ᶠ v, Φv v (projV v Y)) =ᶠ[nhds X]
      fun Y => ∏ v ∈ hS.toFinset, Φv v (projV v Y) := by
    filter_upwards [hUo.mem_nhds hXU] with Y hY
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    rw [Set.Finite.coe_toFinset]
    intro h
    apply hv
    have hYX : projV v (Y - X) ∈ latV b v := by
      intro a i k
      have := crd_projV b (Y - X) v a i k
      simp only [crd] at this
      rw [this]
      exact hY a i k v
    have hmem : projV v Y ∈ latV b v := by
      have e : projV v Y = projV v (Y - X) + projV v X := by
        rw [← projV_add]; simp
      rw [e]
      exact latV_add b v hYX h.2
    show Φv v (projV v Y) = 1
    rw [h.1, Set.indicator_of_mem hmem]
    rfl
  refine ContinuousAt.congr ?_ hev.symm
  exact (continuous_finsetProd _ fun v _ =>
    (hSB v).1.continuous.comp (continuous_projV_fin b v)).continuousAt

theorem hasCompactSupport_finprod (hSB : ∀ v, IsSB (Φv v))
    (hae : ∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1) :
    HasCompactSupport (fun X : Fin n → Fin M → Af F ⊗[F] E => ∏ᶠ v, Φv v (projV v X)) := by
  classical
  let D : Fin n → Fin M → Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v) :=
    fun i j k v =>
      ((fun Z : Fin n → Fin M → Fv F v ⊗[F] E => crd b (Fv F v) (Z i j) k) '' tsupport (Φv v)) ∪
        (v.adicCompletionIntegers F : Set (Fv F v))
  have hD : ∀ i j k v, IsCompact (D i j k v) := fun i j k v =>
    ((hSB v).2.isCompact.image ((continuous_crd b (Fv F v) k).comp
      ((continuous_apply j).comp (continuous_apply i)))).union
      (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v)
  have hDe : ∀ i j k, ∀ᶠ v in Filter.cofinite,
      D i j k v = (v.adicCompletionIntegers F : Set (Fv F v)) := by
    intro i j k
    filter_upwards [hae] with v hv
    refine Set.union_eq_right.2 ?_
    rintro _ ⟨Z, hZ, rfl⟩
    have hsub : tsupport (Φv v) ⊆ latV b v := by
      rw [hv]
      exact closure_minimal Set.support_indicator_subset (isClopen_latV b v n M).isClosed
    exact hsub hZ i j k
  let Bf : Fin n → Fin M → Fin d → Set (Af F) := fun i j k => {x | ∀ v, x v ∈ D i j k v}
  have hBf : ∀ i j k, IsCompact (Bf i j k) := fun i j k => isCompact_finBox (hD i j k) (hDe i j k)
  let Box : Set (Fin n → Fin M → Fin d → Af F) :=
    Set.pi univ fun i => Set.pi univ fun j => Set.pi univ fun k => Bf i j k
  have hbox : IsCompact Box := isCompact_univ_pi fun i => isCompact_univ_pi fun j =>
    isCompact_univ_pi fun k => hBf i j k
  let L : (Fin n → Fin M → Fin d → Af F) → (Fin n → Fin M → Af F ⊗[F] E) :=
    fun c x i => ∑ k, c x i k • ((1 : Af F) ⊗ₜ[F] b k)
  have hL : Continuous L := by
    refine continuous_pi fun x => continuous_pi fun i => continuous_finsetSum _ fun k _ => ?_
    exact continuous_smul.comp
      (((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply x))).prodMk
        continuous_const)
  refine HasCompactSupport.intro (hbox.image hL) fun X hX => ?_
  by_contra h
  apply hX
  have hv := factor_ne_zero b Φv hae X h
  refine ⟨fun i j k => crd b (Af F) (X i j) k, ?_, ?_⟩
  · simp only [Box, Set.mem_pi, Set.mem_univ, true_implies]
    intro i j k v
    refine Or.inl ⟨projV v X, subset_tsupport _ (hv v), ?_⟩
    exact crd_projV b X v i j k
  · funext i j
    exact (eq_sum_crd b (Af F) (X i j)).symm

end GlobalTheory.PureFinite

namespace GlobalTheory

theorem isPureFin_continuous_hasCompactSupport : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (d M n : ℕ) (b : Module.Basis (Fin d) F E)
    (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ),
    IsPureFin b Φf Φv → Continuous Φf ∧ HasCompactSupport Φf := by
  intro F E _ _ _ _ _ d M n b Φf Φv h
  obtain ⟨hSB, hae, hprod⟩ := h
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have e : Φf = fun X => ∏ᶠ v, Φv v (projV v X) := funext hprod
  subst e
  exact ⟨PureFinite.continuous_finprod b Φv hSB hae, PureFinite.hasCompactSupport_finprod b Φv hSB hae⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PureFiniteAdelicTestFunctionContinuousCompactStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pureFiniteAdelicTestFunction_continuous_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d M n : ℕ) (b : Module.Basis (Fin d) F E) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ) (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ), IsPureFin b Φf Φv → Continuous Φf ∧ HasCompactSupport Φf := by
  first | exact @GlobalTheory.isPureFin_continuous_hasCompactSupport | exact GlobalTheory.isPureFin_continuous_hasCompactSupport | (intros; apply GlobalTheory.isPureFin_continuous_hasCompactSupport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TotallyPositiveOrthogonalOfTwoFlagExtendedSpaces
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TotallyPositiveOrthogonalOfTwoFlagExtendedSpaces
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ComplPos

theorem mem_orth_left {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {U U' : Submodule E S.V}
    {x : S.V} (hx : x ∈ orth S (U ⊔ U')) : x ∈ orth S U := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  exact fun y hy => hx y (Submodule.mem_sup_left hy)

theorem mem_orth_right {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {U U' : Submodule E S.V}
    {x : S.V} (hx : x ∈ orth S (U ⊔ U')) : x ∈ orth S U' := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  exact fun y hy => hx y (Submodule.mem_sup_right hy)

theorem fvec_mem_Xplus {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (F : FlagG S r T) (b : Fin (r + 1)) : F.fvec b ∈ F.Xplus := by
  refine Fin.lastCases ?_ (fun a => ?_) b
  · simp only [FlagG.fvec, Fin.snoc_last]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · simp only [FlagG.fvec, Fin.snoc_castSucc]
    exact Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩)

theorem eq_zero_of_mem_X {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
    (F : FlagG S r T) (F' : FlagG S r T') (hdet : (ZhatOM (Zhat F F')).det ≠ 0) {x : S.V}
    (hxX : x ∈ F.X) (hx : x ∈ orth S F'.Xplus) : x = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hxX
  have hx' : ∀ y ∈ F'.Xplus, S.hT y (∑ i, c i • F.e i) = 0 := by
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx
    exact hx
  have hrow : ∀ b, ∑ a : Fin r, star (c a) * Zhat F F' a.castSucc b = 0 := by
    intro b
    have h1 := hx' _ (fvec_mem_Xplus F' b)
    have h2 : S.hT (∑ i, c i • F.e i) (F'.fvec b) = 0 := by
      rw [← S.herm.eq, h1, map_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Zhat, brS, FlagG.fvec, Fin.snoc_castSucc, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, starRingEnd_apply]
  set v : Fin (r + 1) → E := Fin.snoc (α := fun _ => E) (fun a => star (c a)) 0 with hv
  have hvZ : Matrix.vecMul v (ZhatOM (Zhat F F')) = 0 := by
    funext b
    simp only [Matrix.vecMul, dotProduct, ZhatOM, Pi.zero_apply]
    rw [Fin.sum_univ_castSucc]
    simp only [hv, Fin.snoc_castSucc, Fin.snoc_last, zero_mul, add_zero]
    have := hrow b
    calc ∑ a : Fin r, star (c a) * ((-1) ^ (r - b.val) * Zhat F F' a.castSucc b)
        = (-1) ^ (r - b.val) * ∑ a : Fin r, star (c a) * Zhat F F' a.castSucc b := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => ?_; ring
      _ = 0 := by rw [this, mul_zero]
  have hv0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hvZ
  have hc : ∀ a, c a = 0 := by
    intro a
    have := congrFun hv0 a.castSucc
    simp only [hv, Fin.snoc_castSucc, Pi.zero_apply, star_eq_zero] at this
    exact this
  simp [hc]

end GlobalTheory.ComplPos

theorem GlobalTheory.ComplPos.complement_totPos : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ x ∈ orth (VS D) (Xplus F ⊔ Xplus F'), x ≠ 0 → 0 < Algebra.trace ℚ D.host.E ((VS D).hT x x) := by
  intro D X Y u u' F F' w hZ _ x hx hx0
  have hdet : (ZhatOM (Zhat F.fl F'.fl)).det ≠ 0 := by
    have e : ZhatOM (Zhat F.fl F'.fl) = ptMat w := hZ
    rw [e]
    exact Formalism.L2.SG.Pf.StabilizerIndexVolumes.ptMat_det w
  by_cases hxX : x ∈ Xsp F
  · exact absurd (GlobalTheory.ComplPos.eq_zero_of_mem_X F.fl F'.fl hdet hxX (GlobalTheory.ComplPos.mem_orth_right hx)) hx0
  · have hT : 0 < Tu D u := (D.mem u).A.T_prime.pos
    exact GlobalTheory.LoopC.PerpPos.trace_pos_perp D (Tu D u) F hT x (GlobalTheory.ComplPos.mem_orth_left hx) hxX
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TotallyPositiveOrthogonalOfTwoFlagExtendedSpacesStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totallyPositive_orthogonal_of_two_flagExtendedSpaces : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ x ∈ orth (VS D) (Xplus F ⊔ Xplus F'), x ≠ 0 → 0 < Algebra.trace ℚ D.host.E ((VS D).hT x x) := by
  first | exact @GlobalTheory.ComplPos.complement_totPos | exact GlobalTheory.ComplPos.complement_totPos | (intros; apply GlobalTheory.ComplPos.complement_totPos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutomorphicInstanceExistsFundamentalDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableFundamentalDomain
namespace GlobalTheory.MeasurableFundamentalDomain

open Set Topology

theorem exists_small_open {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (Γ : Subgroup G)
    (hΓ : ∀ C : Set G, IsCompact C → Set.Finite (C ∩ (↑Γ : Set G))) :
    ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧ ∀ a ∈ V, ∀ b ∈ V, a * b⁻¹ ∈ Γ → a * b⁻¹ = 1 := by
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hfin : ((K ∩ (↑Γ : Set G)) \ {1}).Finite := (hΓ K hK).subset sdiff_subset
  have hcl : IsClosed ((K ∩ (↑Γ : Set G)) \ {1}) := hfin.isClosed
  have h1 : ((K ∩ (↑Γ : Set G)) \ {1})ᶜ ∈ 𝓝 (1 : G) :=
    hcl.isOpen_compl.mem_nhds (by simp)
  have hW : K ∩ ((K ∩ (↑Γ : Set G)) \ {1})ᶜ ∈ 𝓝 (1 : G) := Filter.inter_mem hK1 h1
  obtain ⟨V, hV, hVW⟩ := exists_nhds_split_inv hW
  refine ⟨interior V, isOpen_interior, mem_interior_iff_mem_nhds.2 hV, ?_⟩
  intro a ha b hb hab
  have h := hVW a (interior_subset ha) b (interior_subset hb)
  rw [div_eq_mul_inv] at h
  by_contra hne
  exact h.2 ⟨⟨h.1, hab⟩, hne⟩

theorem exists_measurable_fundamental_domain {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [OpensMeasurableSpace G] (Γ : Subgroup G) [Countable ↥Γ]
    (hΓ : ∀ C : Set G, IsCompact C → Set.Finite (C ∩ (↑Γ : Set G))) :
    ∃ D : Set G, MeasurableSet D ∧ (∀ y : G, ∃ γ ∈ Γ, γ * y ∈ D) ∧
      ∀ γ ∈ Γ, ∀ y ∈ D, γ * y ∈ D → γ = (1 : G) := by
  classical
  obtain ⟨V, hVo, hV1, hV⟩ := exists_small_open Γ hΓ
  obtain ⟨g, hg⟩ := TopologicalSpace.exists_dense_seq G
  let U : ℕ → Set G := fun n => {y | y * (g n)⁻¹ ∈ V}
  let S : ℕ → Set G := fun n => ⋃ γ ∈ Γ, {y | γ * y ∈ U n}
  have hUo : ∀ n, IsOpen (U n) := fun n => hVo.preimage (continuous_id.mul continuous_const)
  have hSo : ∀ n, IsOpen (S n) := fun n =>
    isOpen_biUnion fun γ _ => (hUo n).preimage (continuous_const.mul continuous_id)
  have hS : ∀ n y, y ∈ S n ↔ ∃ γ ∈ Γ, γ * y ∈ U n := by
    intro n y
    simp [S]
  have hSinv : ∀ n, ∀ γ ∈ Γ, ∀ y, γ * y ∈ S n → y ∈ S n := by
    intro n γ hγ y hy
    obtain ⟨δ, hδ, h⟩ := (hS _ _).1 hy
    exact (hS _ _).2 ⟨δ * γ, Γ.mul_mem hδ hγ, by rwa [mul_assoc]⟩
  refine ⟨⋃ n, (U n \ ⋃ m ∈ Set.Iio n, S m), ?_, ?_, ?_⟩
  · exact MeasurableSet.iUnion fun n =>
      (hUo n).measurableSet.diff (isOpen_biUnion fun m _ => hSo m).measurableSet
  · intro y
    have hex : ∃ n, y ∈ S n := by
      have ho : IsOpen {x : G | y * x⁻¹ ∈ V} :=
        hVo.preimage (continuous_const.mul continuous_inv)
      obtain ⟨n, hn⟩ := hg.exists_mem_open ho ⟨y, by simpa using hV1⟩
      exact ⟨n, (hS _ _).2 ⟨1, Γ.one_mem, by rw [one_mul]; exact hn⟩⟩
    obtain ⟨γ, hγ, h⟩ := (hS _ _).1 (Nat.find_spec hex)
    refine ⟨γ, hγ, mem_iUnion.2 ⟨Nat.find hex, h, ?_⟩⟩
    intro hm
    obtain ⟨m, hm, hy⟩ := mem_iUnion₂.1 hm
    exact Nat.find_min hex hm (hSinv m γ hγ y hy)
  · intro γ hγ y hy hγy
    obtain ⟨n, hn, hn'⟩ := mem_iUnion.1 hy
    obtain ⟨m, hm, hm'⟩ := mem_iUnion.1 hγy
    have hnm : n = m := by
      rcases lt_trichotomy n m with h | h | h
      · exact absurd (mem_iUnion₂.2 ⟨n, h, (hS _ _).2
          ⟨γ⁻¹, Γ.inv_mem hγ, by rwa [inv_mul_cancel_left]⟩⟩) hm'
      · exact h
      · exact absurd (mem_iUnion₂.2 ⟨m, h, (hS _ _).2 ⟨γ, hγ, hm⟩⟩) hn'
    subst hnm
    have e : (γ * y * (g n)⁻¹) * (y * (g n)⁻¹)⁻¹ = γ := by group
    have := hV _ hm _ hn (by rw [e]; exact hγ)
    rwa [e] at this

end GlobalTheory.MeasurableFundamentalDomain
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutomorphicInstanceExistsFundamentalDomain
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace
open Topology Filter

namespace GlobalTheory.FundExists

theorem exists_strict_domain {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
    [OpensMeasurableSpace G] (Γ : Subgroup G) [Countable Γ]
    (hfin : ∀ C : Set G, IsCompact C → (C ∩ Γ).Finite) :
    ∃ D : Set G, MeasurableSet D ∧ (∀ y, ∃ γ ∈ Γ, γ * y ∈ D) ∧
      ∀ γ ∈ Γ, ∀ y ∈ D, γ * y ∈ D → γ = 1 := by
  first
  | exact @_root_.GlobalTheory.MeasurableFundamentalDomain.exists_measurable_fundamental_domain
  | exact _root_.GlobalTheory.MeasurableFundamentalDomain.exists_measurable_fundamental_domain
  | (apply _root_.GlobalTheory.MeasurableFundamentalDomain.exists_measurable_fundamental_domain <;> assumption)
  | (intros; apply _root_.GlobalTheory.MeasurableFundamentalDomain.exists_measurable_fundamental_domain <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MeasurableFundamentalDomain.exists_measurable_fundamental_domain <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MeasurableFundamentalDomain.exists_measurable_fundamental_domain ..)

theorem exists_isFundDom : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf],
    ∃ fund, I.IsFundDom (I.muA μf) fund := by
  intro I μf _ _
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.CongTop.adelic_topology I
  obtain ⟨Γ, hΓ, hc, hfin, -⟩ := GlobalTheory.RatDiscrete.rational_points I
  rw [← hΓ] at hfin
  obtain ⟨D, hD, hcov, hinj⟩ := exists_strict_domain Γ hfin
  refine ⟨D, hD, ?_, ?_⟩
  · rw [← hΓ]
    exact hcov
  · rw [← hΓ]
    intro γ hγ hne
    have : (fun y => γ * y) '' D ∩ D = ∅ := by
      refine Set.eq_empty_of_forall_notMem ?_
      rintro _ ⟨⟨y, hy, rfl⟩, hγy⟩
      exact hne (hinj γ hγ y hy hγy)
    rw [this, measure_empty]

end GlobalTheory.FundExists
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutomorphicInstanceExistsFundamentalDomainStatement
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphicInstance_exists_fundamental_domain : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf], ∃ fund, I.IsFundDom (I.muA μf) fund := by
  first | exact @GlobalTheory.FundExists.exists_isFundDom | exact GlobalTheory.FundExists.exists_isFundDom | (intros; apply GlobalTheory.FundExists.exists_isFundDom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiVNeOneOfTrace
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.StdCharTotReal

section Local

variable {F : Type} [Field F] [NumberField F]

theorem trace_int_iff (a : F) : (∀ r : 𝓞 F, ∃ k : ℤ, Algebra.trace ℚ F (a * r) = k) ↔
    ∀ d ∈ differentIdeal ℤ (𝓞 F), ∃ r : 𝓞 F, (r : F) = a * d := by
  have h1 : (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := one_ne_zero
  have hD := FractionalIdeal.dual_ne_zero ℤ ℚ h1
  have hd : (∀ r : 𝓞 F, ∃ k : ℤ, Algebra.trace ℚ F (a * r) = k) ↔
      a ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [FractionalIdeal.mem_dual h1]
    constructor
    · intro h x hx
      obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hx
      obtain ⟨k, hk⟩ := h b
      exact ⟨k, by rw [Algebra.traceForm_apply]; simpa using hk.symm⟩
    · intro h r
      obtain ⟨k, hk⟩ := h (algebraMap _ F r) ((FractionalIdeal.mem_one_iff _).mpr ⟨r, rfl⟩)
      exact ⟨k, by rw [Algebra.traceForm_apply] at hk; simpa using hk.symm⟩
  rw [hd, ← inv_inv (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)),
    FractionalIdeal.mem_inv_iff (inv_ne_zero hD), ← coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)]
  constructor
  · intro h d hd
    exact (FractionalIdeal.mem_one_iff _).mp (h _ (FractionalIdeal.mem_coeIdeal_of_mem _ hd))
  · intro h y hy
    obtain ⟨d, hd, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
    exact (FractionalIdeal.mem_one_iff _).mpr (h d hd)

theorem integral_iff (x : F) : (∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (Af F) x v ∈ v.adicCompletionIntegers F) ↔
    ∃ r : 𝓞 F, (r : F) = x := by
  constructor
  · intro h
    have hx := (GlobalTheory.AdLat.mem_adelicIdeal_one_iff_integral F _).2 h
    rwa [GlobalTheory.Idele.algebraMap_mem_adelicIdeal (GlobalTheory.AdLat.one_ne_zero_fracIdeal F),
      FractionalIdeal.mem_one_iff] at hx
  · rintro ⟨r, rfl⟩ v
    exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v r

theorem fin_conductor (χ : Af F → ℂ) (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y)
    (hrat : ∀ a : F, χ (algebraMap F (Af F) a) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F (-a) : ℚ) : ℂ))) (z : Af F) :
    (∀ t : Af F, (∀ v : HeightOneSpectrum (𝓞 F), t v ∈ v.adicCompletionIntegers F) → χ (z * t) = 1) ↔
      ∀ d ∈ differentIdeal ℤ (𝓞 F), ∀ v : HeightOneSpectrum (𝓞 F), (z * algebraMap F (Af F) (d : F)) v ∈ v.adicCompletionIntegers F := by
  have hone : ∀ a : F, χ (algebraMap F (Af F) a) = 1 ↔ ∃ k : ℤ, Algebra.trace ℚ F a = k := by
    intro a
    rw [hrat, Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨-n, ?_⟩
      rw [mul_comm (n : ℂ), mul_right_inj' Complex.two_pi_I_ne_zero, map_neg] at hn
      have : -Algebra.trace ℚ F a = (n : ℚ) := by exact_mod_cast hn
      push_cast
      linarith
    · rintro ⟨k, hk⟩
      refine ⟨-k, ?_⟩
      rw [map_neg, hk]
      push_cast
      ring
  have hO : ∀ r : 𝓞 F, ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (Af F) (r : F) v ∈ v.adicCompletionIntegers F :=
    fun r => (integral_iff _).2 ⟨r, rfl⟩
  have hint : ∀ t : Af F, (∀ v : HeightOneSpectrum (𝓞 F), t v ∈ v.adicCompletionIntegers F) → χ t = 1 := fun t ht =>
    GlobalTheory.IntDense.mem_of_isClosed F (C := {y | χ y = 1}) (isClosed_eq hc continuous_const)
      (fun r => (hone _).2 (by simpa using (trace_int_iff (1 : F)).2 (fun d _ => ⟨d, (one_mul _).symm⟩) r)) t ht
  obtain ⟨a, s, hs, hz⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F 1 one_pos z
  rw [one_smul] at hz
  have hmul : ∀ t : Af F, (∀ v : HeightOneSpectrum (𝓞 F), t v ∈ v.adicCompletionIntegers F) → χ (z * t) = χ (algebraMap F (Af F) a * t) := by
    intro t ht
    rw [hz, add_mul, hadd, hint (s * t) (fun v => mul_mem (hs v) (ht v)), mul_one]
  have h1 : (∀ t : Af F, (∀ v : HeightOneSpectrum (𝓞 F), t v ∈ v.adicCompletionIntegers F) → χ (z * t) = 1) ↔
      ∀ r : 𝓞 F, ∃ k : ℤ, Algebra.trace ℚ F (a * r) = k := by
    constructor
    · intro h r
      rw [← hone, map_mul, ← hmul _ (hO r)]
      exact h _ (hO r)
    · intro h t ht
      rw [hmul t ht]
      exact GlobalTheory.IntDense.mem_of_isClosed F (C := {y | χ (algebraMap F (Af F) a * y) = 1})
        (isClosed_eq (hc.comp (continuous_const.mul continuous_id)) continuous_const)
        (fun r => by
          show χ _ = 1
          rw [← map_mul, hone]
          exact h r) t ht
  rw [h1, trace_int_iff]
  refine forall₂_congr fun d _ => ?_
  rw [← integral_iff, hz, add_mul, map_mul]
  refine forall_congr' fun v => ?_
  have h2 : (s * algebraMap F (Af F) (d : F)) v ∈ v.adicCompletionIntegers F := mul_mem (hs v) (hO d v)
  exact ⟨fun h => add_mem h h2, fun h => (add_mem_cancel_right h2).1 h⟩

theorem single_same (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) : singleV F v y v = y := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v y

theorem single_ne (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) :
    singleV F v y w = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) y hw

theorem single_mul (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) (t : Af F) :
    singleV F v y * t = singleV F v (y * t v) := by
  refine RestrictedProduct.ext _ _ fun w => ?_
  change singleV F v y w * t w = singleV F v (y * t v) w
  by_cases hw : w = v
  · subst hw; rw [single_same, single_same]
  · rw [single_ne v _ hw, single_ne v _ hw, zero_mul]

theorem psiV_ne_one_of_trace {ψ : AddChar (AF F) ℂ} (h : IsCharAF F ψ)
    (hinf : ∀ a : F, psiInf F ψ (algebraMap F (Ainf F) a) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F a : ℚ) : ℂ))) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ y, psiV F ψ v y ≠ 1 := by
  by_contra hn
  push Not at hn
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))
  have hd1 : algebraMap F (Fv F v) (d : F) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact_mod_cast hd0
  obtain ⟨z, hz⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp 1)
  have key := (fin_conductor (fun y => ψ (pairA F 0 y))
    (h.1.comp (Continuous.prodMk continuous_const continuous_id))
    (fun a b => by
      rw [← AddChar.map_add_eq_mul]
      exact congrArg ψ (Prod.ext (add_zero _).symm rfl))
    (fun a => by rw [GlobalTheory.StdRat.char_fin_rat ψ h, hinf]) (singleV F v (z * (algebraMap F (Fv F v) (d : F))⁻¹))).1
    (fun t _ => by rw [single_mul]; exact hn _) d hd v
  have h1 : (singleV F v (z * (algebraMap F (Fv F v) (d : F))⁻¹) * algebraMap F (Af F) (d : F)) v = z := by
    rw [single_mul, single_same]
    show z * (algebraMap F (Fv F v) (d : F))⁻¹ * algebraMap F (Fv F v) (d : F) = z
    rw [inv_mul_cancel_right₀ hd1]
  rw [h1, HeightOneSpectrum.mem_adicCompletionIntegers, hz, ← WithZero.exp_zero, WithZero.exp_le_exp] at key
  omega

theorem sum_places_eq_trace [IsTotallyReal F] (x : F) :
    (((∑ w : InfinitePlace F, (w.embedding x).re : ℝ)) : ℂ) = ((Algebra.trace ℚ F x : ℚ) : ℂ) := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := x)
  rw [eq_ratCast] at h
  rw [h, ← Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun τ => τ x) _ fun τ => rfl]
  have hr : ∀ τ : F →+* ℂ, (InfinitePlace.mk τ).embedding = τ := fun τ =>
    InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))
  push_cast
  refine Fintype.sum_bijective (fun w : InfinitePlace F => w.embedding) ⟨fun a b hab => ?_, fun τ => ⟨_, hr τ⟩⟩ _ _
    fun w => ?_
  · rw [← InfinitePlace.mk_embedding a, ← InfinitePlace.mk_embedding b]
    exact congrArg InfinitePlace.mk hab
  · have := InfinitePlace.isReal_iff.1 (IsTotallyReal.isReal w)
    exact Complex.conj_eq_iff_re.1 (RingHom.congr_fun this x)

end Local

theorem exists_psiV_ne_one : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → (∀ x : Ainf F, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I * ((∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ))) → ∀ v : HeightOneSpectrum (𝓞 F), ∃ r, psiV F ψ v r ≠ 1 := by
  intro F _ _ hF ψ hψ hinf v
  refine psiV_ne_one_of_trace hψ (fun a => ?_) v
  rw [hinf, ← sum_places_eq_trace]
  refine congrArg (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)))
    (Finset.sum_congr rfl fun w _ => congrArg Complex.re ?_)
  rw [InfiniteAdeleRing.algebraMap_apply, InfinitePlace.Completion.extensionEmbedding_coe]
  simp

end GlobalTheory.StdCharTotReal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselTransportIsometryFrameAdapted
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselTransportIsometryFrameAdapted
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovDom.ModelIso

variable {D : D7} (X : HidaSetting D)

theorem pl_vOf (τ : D.what₂.Tau) : X.pl (vOf X τ) = τ := by
  simp [vOf]

theorem qi_gram {θ : ℝ} (C : Choice X θ) (τ : D.what₂.Tau) :
    (C.Qi τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.Qi τ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
  obtain ⟨-, h2, h3, -⟩ := C.isT τ
  rw [← h3]
  calc (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * C.Qi τ
      = (C.Q τ * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.Qi τ) := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [h2, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem pinv_gram (v : InfinitePlace X.B.I.F) :
    ((X.B.I.P v)⁻¹)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * (X.B.I.P v)⁻¹ = X.B.I.J.map (X.B.I.φ v) := by
  have hu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  have h1 : X.B.I.P v * (X.B.I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  rw [← X.B.I.P_spec v]
  calc ((X.B.I.P v)⁻¹)ᴴ * ((X.B.I.P v)ᴴ * X.B.I.J.map (X.B.I.φ v) * X.B.I.P v) * (X.B.I.P v)⁻¹
      = (X.B.I.P v * (X.B.I.P v)⁻¹)ᴴ * X.B.I.J.map (X.B.I.φ v) * (X.B.I.P v * (X.B.I.P v)⁻¹) := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem besselModelTransportMatrix_gram_eq {θ : ℝ} (C : Choice X θ) (w : InfinitePlace D.host.E) :
    (A0 X C w)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * A0 X C w = (Jc X).map (embS D (tauOf D w)) := by
  set τ := tauOf D w
  set B := C.Qi τ * (X.B.I.P (vOf X τ))⁻¹ with hBdef
  have hB : Bᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * B = X.B.I.J.map (X.B.I.φ (vOf X τ)) := by
    rw [← pinv_gram X (vOf X τ), ← qi_gram X C τ, hBdef, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have hA : A0 X C w = B.submatrix id (ci X) := rfl
  have hAt : (A0 X C w)ᴴ = Bᴴ.submatrix (ci X) id := by rw [hA, conjTranspose_submatrix]
  have hprod : Bᴴ.submatrix (ci X) id * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * B.submatrix id (ci X) =
      (Bᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * B).submatrix (ci X) (ci X) := by
    symm
    rw [submatrix_mul (Bᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) B (ci X) id (ci X) Function.bijective_id,
      submatrix_mul Bᴴ (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) (ci X) id id Function.bijective_id, submatrix_id_id]
  rw [hAt, hA, hprod, hB]
  ext i j
  simp only [submatrix_apply, map_apply, Jc, X.φ_eq, X.J_eq, pl_vOf]

theorem embedding_of_not_direct (w : InfinitePlace D.host.E) (h : ¬ Direct D w) :
    w.embedding = ComplexEmbedding.conjugate (embS D (tauOf D w)) := by
  have hw : InfinitePlace.mk (embS D (tauOf D w)) = w := (GlobalTheory.RealPlaces.existsUnique_place D w).exists.choose_spec
  rcases InfinitePlace.embedding_mk_eq (embS D (tauOf D w)) with h1 | h1
  · rw [hw] at h1; exact (h h1).elim
  · rwa [hw] at h1

theorem isModel {θ : ℝ} (C : Choice X θ) : GlobalTheory.SnMass.IsModelAt (Jc X) (Ac X C) := by
  intro w
  unfold Ac
  split_ifs with h
  · rw [besselModelTransportMatrix_gram_eq, show w.embedding = embS D (tauOf D w) from h]
  · rw [embedding_of_not_direct w h]
    have hH : (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS).map (starRingEnd ℂ) = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := by
      ext i j; simp only [map_apply, Formalism.QuantumDeterminants.Hpk]; split_ifs <;> simp
    have hc : ((A0 X C w).map (starRingEnd ℂ))ᴴ = ((A0 X C w)ᴴ).map (starRingEnd ℂ) := by
      ext i j; simp [conjTranspose_apply]
    show ((A0 X C w).map (starRingEnd ℂ))ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (A0 X C w).map (starRingEnd ℂ) = _
    rw [hc, ← hH, ← Matrix.map_mul, ← Matrix.map_mul, besselModelTransportMatrix_gram_eq]
    ext i j
    simp [ComplexEmbedding.conjugate_coe_eq]

end GlobalTheory.CovDom.ModelIso

namespace GlobalTheory.CovDom.ModelIso

variable {D : D7} (X : HidaSetting D)

theorem v_pos : 0 < D.host.v := by
  have := GlobalTheory.RealPlaces.one_le_rdE D
  unfold Host.v; linarith

theorem frS_ne_zero : frS D ≠ 0 := by
  have hv := v_pos (D := D)
  unfold frS Host.ka
  have : Real.pi / D.host.v / (2 * Real.pi) ≠ 0 := by positivity
  exact_mod_cast this

theorem frS_pow_inv (m : ℕ) : ((frS D) ^ m)⁻¹ = (((2 * D.host.v) ^ m : ℝ) : ℂ) := by
  have hv := v_pos (D := D)
  have h : D.host.ka / (2 * Real.pi) = (2 * D.host.v)⁻¹ := by
    unfold Host.ka; field_simp
  rw [frS, h]; push_cast; rw [inv_pow, inv_inv]

theorem star_frS : star (frS D) = frS D := by
  unfold frS; exact Complex.conj_ofReal _

theorem besselModelTransportMatrix_mulVec_coordinates {θ : ℝ} (C : Choice X θ) (w : InfinitePlace D.host.E) (y : (VS D).V) :
    (A0 X C w *ᵥ fun i => embS D (tauOf D w) (crdH X y i)) =
      C.Qi (tauOf D w) *ᵥ rv X.B.I (vOf X (tauOf D w)) (X.crd y) := by
  have hx : (fun i => embS D (tauOf D w) (crdH X y i)) =
      (fun j => embS D (tauOf D w) (X.bas.repr y j)) ∘ (ci X) := rfl
  have hx2 : ((fun j => embS D (tauOf D w) (X.bas.repr y j)) ∘ (ci X)) ∘ (ci X).symm =
      fun j => embS D (tauOf D w) (X.bas.repr y j) := by
    funext j; simp
  rw [hx, A0, submatrix_mulVec_equiv, hx2, Function.comp_id, ← mulVec_mulVec]
  congr 1
  unfold rv
  congr 1
  funext i
  rw [X.φ_eq, pl_vOf]
  simp [HidaSetting.crd, crdOf]

theorem qi_e {θ : ℝ} (C : Choice X θ) (τ : D.what₂.Tau) (a : Fin D.R.rS) :
    C.Qi τ *ᵥ rv X.B.I (vOf X τ) (X.eR a) =
      (((2 * D.host.v) ^ (D.R.rS - (a : ℕ)) : ℝ) : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) := by
  obtain ⟨h1, -, -, h4⟩ := C.isT τ
  have he := congrArg (fun x => C.Qi τ *ᵥ x) (h4 a a rfl).1
  simp only [mulVec_mulVec, h1, one_mulVec, mulVec_smul] at he
  rw [← frS_pow_inv, Formalism.QuantumDeterminants.bvec, he, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ frS_ne_zero), one_smul]

theorem qi_f {θ : ℝ} (C : Choice X θ) (τ : D.what₂.Tau) (a : Fin D.R.rS) :
    C.Qi τ *ᵥ rv X.B.I (vOf X τ) (X.fR a) =
      ((((2 * D.host.v) ^ (D.R.rS - (a : ℕ)) : ℝ) : ℂ))⁻¹ • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) := by
  obtain ⟨h1, -, -, h4⟩ := C.isT τ
  have he := congrArg (fun x => C.Qi τ *ᵥ x) (h4 a a rfl).2
  simp only [mulVec_mulVec, h1, one_mulVec, mulVec_smul] at he
  have hs : star (frS D ^ (D.R.rS - (a : ℕ))) = frS D ^ (D.R.rS - (a : ℕ)) := by
    rw [star_pow, star_frS]
  rw [hs] at he
  rw [← frS_pow_inv, inv_inv, Formalism.QuantumDeterminants.bvec, he, smul_smul,
    mul_inv_cancel₀ (pow_ne_zero _ frS_ne_zero), one_smul]

theorem Ac_mulVec {θ : ℝ} (C : Choice X θ) (w : InfinitePlace D.host.E) (y : (VS D).V) (c : ℝ)
    (j' : Fin (2 * D.R.rS + D.R.k + 1))
    (h : (A0 X C w *ᵥ fun i => embS D (tauOf D w) (crdH X y i)) = (c : ℂ) • Formalism.QuantumDeterminants.bvec j') :
    (Ac X C w *ᵥ fun i => w.embedding (crdH X y i)) = (c : ℂ) • Formalism.QuantumDeterminants.bvec j' := by
  unfold Ac
  split_ifs with hd
  · rw [show w.embedding = embS D (tauOf D w) from hd]; exact h
  · rw [embedding_of_not_direct w hd]
    have e1 : (fun i => (ComplexEmbedding.conjugate (embS D (tauOf D w))) (crdH X y i)) =
        ⇑(starRingEnd ℂ) ∘ (fun i => embS D (tauOf D w) (crdH X y i)) := by
      funext i; simp [ComplexEmbedding.conjugate_coe_eq]
    rw [e1]
    funext i
    rw [show (A0 X C w).map star = (A0 X C w).map (starRingEnd ℂ) from rfl, ← RingHom.map_mulVec, h]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal, Formalism.QuantumDeterminants.bvec]
    congr 1
    rcases eq_or_ne i j' with rfl | hij
    · simp
    · simp [hij]

end GlobalTheory.CovDom.ModelIso

namespace GlobalTheory.CovDom.ModelIso

theorem model_adapted : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word),
    GlobalTheory.SnMass.IsModelAt (Jc X) (Ac X C) ∧ GlobalTheory.SnMass.Adapted (Ac X C) (Pc X u) (fc X) (sc D) := by
  intro D X θ C u
  refine ⟨isModel X C, fun w a => ⟨?_, ?_⟩⟩
  · have hP : (fun i => w.embedding (Pc X u i a.castSucc)) = fun i => w.embedding (crdH X (X.eX a) i) := by
      funext i; simp [Pc]
    rw [hP]
    exact Ac_mulVec X C w _ _ _ (by rw [besselModelTransportMatrix_mulVec_coordinates]; exact qi_e X C _ a)
  · have hf : (fun i => w.embedding (fc X i a)) = fun i => w.embedding (crdH X (X.fY a) i) := rfl
    rw [hf]
    have := Ac_mulVec X C w (X.fY a) ((2 * D.host.v) ^ (D.R.rS - (a : ℕ)))⁻¹ (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a)
      (by rw [besselModelTransportMatrix_mulVec_coordinates]; have := qi_f X C (tauOf D w) a; push_cast at this ⊢; exact this)
    unfold sc; push_cast at this ⊢; exact this

end GlobalTheory.CovDom.ModelIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselTransportIsometryFrameAdaptedStatement
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_transport_isometry_frame_adapted : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word), GlobalTheory.SnMass.IsModelAt (Jc X) (Ac X C) ∧ GlobalTheory.SnMass.Adapted (Ac X C) (Pc X u) (fc X) (sc D) := by
  first | exact @GlobalTheory.CovDom.ModelIso.model_adapted | exact GlobalTheory.CovDom.ModelIso.model_adapted | (intros; apply GlobalTheory.CovDom.ModelIso.model_adapted <;> assumption)
end
end
