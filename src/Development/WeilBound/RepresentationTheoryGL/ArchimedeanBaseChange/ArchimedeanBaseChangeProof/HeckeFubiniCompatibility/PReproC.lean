module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.CompatFub
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.BridgeSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelUniqueness

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PReproB
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace PositivityTheory.Rg.BcB.CG.ReproL

open Classical

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

abbrev UN (N : ℕ) : Type := Matrix.unitaryGroup (Fin N) ℂ

instance msUN (N : ℕ) : MeasurableSpace (UN N) := borel _
instance bsUN (N : ℕ) : BorelSpace (UN N) := ⟨rfl⟩
instance csUN (N : ℕ) : CompactSpace (UN N) := GlobalTheory.compactSpace_unitaryGroup (Fin N) ℂ

def nuN (N : ℕ) : Measure (UN N) := Measure.haar

instance (N : ℕ) : (nuN N).IsHaarMeasure := by unfold nuN; infer_instance

instance (N : ℕ) : IsFiniteMeasure (nuN N) := CompactSpace.isFiniteMeasure


open Classical in
def jvMat (v : InfinitePlace E) (u : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) (Cinf E) :=
  Matrix.of fun i j w => if w = v then u i j else (1 : Matrix (Fin N) (Fin N) ℂ) i j

theorem jvMat_mem (v : InfinitePlace E) (u : UN N) : jvMat v u.1 ∈ Matrix.unitaryGroup (Fin N) (Cinf E) := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hu := Matrix.mem_unitaryGroup_iff.mp u.2
  ext i j w
  have hij := congrFun (congrFun hu i) j
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at hij
  simp only [Matrix.mul_apply, Matrix.star_apply, jvMat, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply,
    Pi.star_apply, Matrix.one_apply]
  by_cases hw : w = v
  · simp only [hw, if_true]
    rw [hij]
    split_ifs <;> rfl
  · simp only [hw, if_false]
    by_cases h : i = j
    · subst h; simp
    · simp [h]

def jv (v : InfinitePlace E) (u : UN N) : Kinf E N := ⟨jvMat v u.1, jvMat_mem v u⟩

def Yv (v : InfinitePlace E) (t : G N) : GL (Fin N) (Cinf E) :=
  Units.map (Matrix.piRingEquiv (n := Fin N) (β := fun _ : InfinitePlace E => ℂ)).symm.toMonoidHom
    (MulEquiv.piUnits.symm (Pi.mulSingle v t))

theorem Yv_apply (v : InfinitePlace E) (t : G N) (i j : Fin N) (w : InfinitePlace E) :
    (Yv v t).val i j w = if w = v then t.val i j else (1 : Matrix (Fin N) (Fin N) ℂ) i j := by
  have e : (Yv v t).val i j w = ((Pi.mulSingle v t : InfinitePlace E → G N) w).val i j := rfl
  rw [e]
  by_cases hw : w = v
  · subst hw; simp
  · simp [Pi.mulSingle_eq_of_ne hw, hw]

theorem infinitePart_mulSingle (v : InfinitePlace E) (t : G N) : infP N (Pi.mulSingle v t) = infGL E N (Yv v t) := rfl

theorem toUnits_jv (v : InfinitePlace E) (u : UN N) : Unitary.toUnits (jv v u) = Yv v (Unitary.toUnits u) := by
  ext i j w
  rw [Yv_apply]
  rfl

theorem infGL_jv (v : InfinitePlace E) (u : UN N) :
    infGL E N (Unitary.toUnits (jv v u)) = infP N (Pi.mulSingle v (Unitary.toUnits u)) := by
  rw [toUnits_jv, infinitePart_mulSingle]

theorem atW_eq (v : InfinitePlace E) (t : G N) : Bridge.atW v t.val = toL (Yv v t).val := by
  funext i j w
  show Bridge.atW v t.val i j w = (Yv v t).val i j w
  rw [Yv_apply]
  unfold Bridge.atW
  split_ifs <;> rfl

def Wv (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) : Submodule ℂ (UN N → ℂ) :=
  W.map (LinearMap.funLeft ℂ ℂ (jv v))

def S0 (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) : Submodule ℂ (UN N → ℂ) where
  carrier := {w | Continuous w ∧ ∀ u', (fun u => w (u' * u)) ∈ Wv W v}
  add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun u' => (Wv W v).add_mem (ha.2 u') (hb.2 u')⟩
  zero_mem' := ⟨continuous_const, fun _ => (Wv W v).zero_mem⟩
  smul_mem' := fun c w hw => ⟨hw.1.const_smul c, fun u' => (Wv W v).smul_mem c (hw.2 u')⟩

def V0 (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) : Type := S0 W v

instance (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) : AddCommGroup (V0 W v) :=
  inferInstanceAs (AddCommGroup (S0 W v))
instance (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) : Module ℂ (V0 W v) :=
  inferInstanceAs (Module ℂ (S0 W v))

def toFun (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) : V0 W v →ₗ[ℂ] (UN N → ℂ) := (S0 W v).subtype

theorem serre_vanishing_zero_trans {W : Submodule ℂ (Kinf E N → ℂ)} {v : InfinitePlace E} {w w' : V0 W v}
    (h : ∀ u, toFun W v w u = toFun W v w' u) : w = w' :=
  Subtype.ext (funext h)

theorem toFun_mem (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) (w : V0 W v) :
    toFun W v w ∈ S0 W v := (w : S0 W v).2

theorem continuous_toFun' (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) (w : V0 W v) :
    Continuous (toFun W v w) := (toFun_mem W v w).1

theorem integrable_toFun (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) (b w : V0 W v) :
    Integrable (fun u => conj (toFun W v b u) * toFun W v w u) (nuN N) :=
  (((continuous_toFun' W v b).star).mul (continuous_toFun' W v w)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

abbrev core (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) : InnerProductSpace.Core ℂ (V0 W v) where
  inner b w := ∫ u, conj (toFun W v b u) * toFun W v w u ∂nuN N
  conj_inner_symm b w := by
    rw [← integral_conj]
    congr 1; funext u
    simp [mul_comm]
  re_inner_nonneg w := by
    have e : (fun u => conj (toFun W v w u) * toFun W v w u) = fun u => ((‖toFun W v w u‖ ^ 2 : ℝ) : ℂ) := by
      funext u; rw [Complex.conj_mul']; norm_cast
    show 0 ≤ RCLike.re (∫ u, conj (toFun W v w u) * toFun W v w u ∂nuN N)
    rw [e, integral_complex_ofReal]
    exact integral_nonneg fun u => by positivity
  add_left a b w := by
    show ∫ u, conj (toFun W v (a + b) u) * toFun W v w u ∂nuN N = _
    simp only [map_add (f := _), Pi.add_apply, add_mul]
    exact integral_add (integrable_toFun W v a w) (integrable_toFun W v b w)
  smul_left a w c := by
    show ∫ u, conj (toFun W v (c • a) u) * toFun W v w u ∂nuN N = _
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
    exact integral_const_mul _ _
  definite w h := by
    have e : (fun u => conj (toFun W v w u) * toFun W v w u) = fun u => ((‖toFun W v w u‖ ^ 2 : ℝ) : ℂ) := by
      funext u; rw [Complex.conj_mul']; norm_cast
    change ∫ u, conj (toFun W v w u) * toFun W v w u ∂nuN N = 0 at h
    rw [e, integral_complex_ofReal] at h
    have h0 : ∫ u, ‖toFun W v w u‖ ^ 2 ∂nuN N = 0 := by exact_mod_cast h
    have hc : Continuous fun u => ‖toFun W v w u‖ ^ 2 := ((continuous_toFun' W v w).norm).pow 2
    have hae := (integral_eq_zero_iff_of_nonneg (fun u => by positivity)
      (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).1 h0
    have hz : (fun u => ‖toFun W v w u‖ ^ 2) = 0 := (Continuous.ae_eq_iff_eq (nuN N) hc continuous_const).1 hae
    exact serre_vanishing_zero_trans fun u => by
      have := congrFun hz u
      simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, norm_eq_zero] at this
      simpa using this

instance nacg (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) : NormedAddCommGroup (V0 W v) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (core W v)
instance ips (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) : InnerProductSpace ℂ (V0 W v) where
  toNormedSpace := { toModule := (inferInstance : Module ℂ (V0 W v))
                     norm_smul_le := (InnerProductSpace.ofCore (core W v).toCore).norm_smul_le }
  inner := (core W v).inner
  norm_sq_eq_re_inner := (InnerProductSpace.ofCore (core W v).toCore).norm_sq_eq_re_inner
  conj_inner_symm := (core W v).conj_inner_symm
  add_left := (core W v).add_left
  smul_left := (core W v).smul_left

theorem rootsOfUnityRing_le_wittIntegers (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) : S0 W v ≤ Wv W v := fun w hw => by
  simpa using hw.2 1

theorem fd (W : Submodule ℂ (Kinf E N → ℂ)) (hW : FiniteDimensional ℂ W) (v : InfinitePlace E) :
    FiniteDimensional ℂ (V0 W v) := by
  have : FiniteDimensional ℂ (Wv W v) := by unfold Wv; infer_instance
  exact Submodule.finiteDimensional_of_le (rootsOfUnityRing_le_wittIntegers W v)

theorem inner_eq (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) (b w : V0 W v) :
    ⟪b, w⟫_ℂ = ∫ u, conj (toFun W v b u) * toFun W v w u ∂nuN N := rfl

theorem exists_finset_eval (W : Submodule ℂ (Kinf E N → ℂ)) (hW : FiniteDimensional ℂ W) (v : InfinitePlace E) :
    ∃ s : Finset (UN N), ∀ w : V0 W v, (∀ x ∈ s, toFun W v w x = 0) → w = 0 := by
  have := fd W hW v
  suffices H : ∀ n : ℕ, ∀ M : Submodule ℂ (V0 W v), Module.finrank ℂ M ≤ n →
      ∃ s : Finset (UN N), ∀ w ∈ M, (∀ x ∈ s, toFun W v w x = 0) → w = 0 by
    obtain ⟨s, hs⟩ := H _ ⊤ le_rfl
    exact ⟨s, fun w hw => hs w Submodule.mem_top hw⟩
  intro n
  induction n with
  | zero =>
    intro M hM
    have hb : M = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hM)
    exact ⟨∅, fun w hw _ => by rw [hb] at hw; exact (Submodule.mem_bot ℂ).mp hw⟩
  | succ n ih =>
    intro M hM
    by_cases hb : M = ⊥
    · exact ⟨∅, fun w hw _ => by rw [hb] at hw; exact (Submodule.mem_bot ℂ).mp hw⟩
    obtain ⟨w0, hw0M, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    have hx : ∃ x, toFun W v w0 x ≠ 0 := by
      by_contra h
      push Not at h
      exact hw0 (serre_vanishing_zero_trans fun u => by rw [h u]; rfl)
    obtain ⟨x0, hx0⟩ := hx
    set M' := M ⊓ LinearMap.ker ((LinearMap.proj x0).comp (toFun W v)) with hM'
    have hlt : M' < M := by
      refine lt_of_le_of_ne inf_le_left fun h => hx0 ?_
      have : w0 ∈ M' := h ▸ hw0M
      exact (Submodule.mem_inf.mp this).2
    have hr := Submodule.finrank_lt_finrank_of_lt hlt
    obtain ⟨s', hs'⟩ := ih M' (by omega)
    refine ⟨insert x0 s', fun w hw hz => hs' w (Submodule.mem_inf.mpr ⟨hw, ?_⟩)
      fun x hx => hz x (Finset.mem_insert_of_mem hx)⟩
    exact hz x0 (Finset.mem_insert_self _ _)

theorem exists_linv (W : Submodule ℂ (Kinf E N → ℂ)) (hW : FiniteDimensional ℂ W) (v : InfinitePlace E) :
    ∃ (s : Finset (UN N)) (L : (s → ℂ) →L[ℂ] V0 W v), ∀ w : V0 W v, L (fun x => toFun W v w x) = w := by
  have := fd W hW v
  obtain ⟨s, hs⟩ := exists_finset_eval W hW v
  let Ev : V0 W v →ₗ[ℂ] (s → ℂ) := LinearMap.pi fun x : s => (LinearMap.proj (x : UN N)).comp (toFun W v)
  have hk : LinearMap.ker Ev = ⊥ :=
    LinearMap.ker_eq_bot'.2 fun w hw => hs w fun x hx => congrFun hw ⟨x, hx⟩
  obtain ⟨g, hg⟩ := Ev.exists_leftInverse_of_injective hk
  exact ⟨s, LinearMap.toContinuousLinearMap g, fun w => LinearMap.congr_fun hg w⟩

theorem continuous_of_toFun (W : Submodule ℂ (Kinf E N → ℂ)) (hW : FiniteDimensional ℂ W) (v : InfinitePlace E)
    {X : Type} [TopologicalSpace X] (F : X → V0 W v) (h : ∀ u, Continuous fun a => toFun W v (F a) u) :
    Continuous F := by
  obtain ⟨s, L, hL⟩ := exists_linv W hW v
  have e : F = fun a => L (fun x => toFun W v (F a) x) := funext fun a => (hL (F a)).symm
  rw [e]
  exact L.continuous.comp (continuous_pi fun x => h x)

def rhoL (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) (u' : UN N) : V0 W v →ₗ[ℂ] V0 W v where
  toFun w := (⟨fun u => toFun W v w (u'⁻¹ * u), (continuous_toFun' W v w).comp (continuous_const.mul continuous_id),
    fun u'' => by simpa only [mul_assoc] using (toFun_mem W v w).2 (u'⁻¹ * u'')⟩ : S0 W v)
  map_add' a b := rfl
  map_smul' c a := rfl

def Mv (W : Submodule ℂ (Kinf E N → ℂ)) (hW : FiniteDimensional ℂ W) (v : InfinitePlace E) : KMod N :=
  haveI := fd W hW v
  { V := V0 W v
    ρ := { toFun := fun u' => LinearMap.toContinuousLinearMap (rhoL W v u')
           map_one' := ContinuousLinearMap.ext fun w => serre_vanishing_zero_trans fun u => by
             show toFun W v w (1⁻¹ * u) = toFun W v w u
             rw [inv_one, one_mul]
           map_mul' := fun a b => ContinuousLinearMap.ext fun w => serre_vanishing_zero_trans fun u => by
             show toFun W v w ((a * b)⁻¹ * u) = toFun W v w (b⁻¹ * (a⁻¹ * u))
             rw [mul_inv_rev, mul_assoc] }
    iso := fun k w => by
      show ‖rhoL W v k w‖ = ‖w‖
      rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_eq, inner_eq]
      congr 2
      exact integral_mul_left_eq_self (fun u => conj (toFun W v w u) * toFun W v w u) k⁻¹
    cont := continuous_clm_apply.2 fun w =>
      continuous_of_toFun W hW v _ fun u => (continuous_toFun' W v w).comp (continuous_inv.mul continuous_const) }

theorem toFun_rho (W : Submodule ℂ (Kinf E N → ℂ)) (hW : FiniteDimensional ℂ W) (v : InfinitePlace E) (u' : UN N)
    (w : (Mv W hW v).V) (u : UN N) : toFun W v ((Mv W hW v).ρ u' w) u = toFun W v w (u'⁻¹ * u) := rfl

def evL (W : Submodule ℂ (Kinf E N → ℂ)) (hW : FiniteDimensional ℂ W) (v : InfinitePlace E) (u : UN N) :
    (Mv W hW v).V →L[ℂ] ℂ :=
  haveI := fd W hW v
  LinearMap.toContinuousLinearMap ((LinearMap.proj u).comp (toFun W v))

theorem evL_apply (W : Submodule ℂ (Kinf E N → ℂ)) (hW : FiniteDimensional ℂ W) (v : InfinitePlace E) (u : UN N)
    (w : (Mv W hW v).V) : evL W hW v u w = toFun W v w u := rfl

theorem continuous_toFun₂ (W : Submodule ℂ (Kinf E N → ℂ)) (hW : FiniteDimensional ℂ W) (v : InfinitePlace E) :
    Continuous fun p : (Mv W hW v).V × UN N => toFun W v p.1 p.2 := by
  have := fd W hW v
  obtain ⟨s, L, hL⟩ := exists_linv W hW v
  have key : ∀ (w : V0 W v) (u : UN N), toFun W v w u =
      ∑ x : s, toFun W v w x • toFun W v (L fun j => if x = j then 1 else 0) u := by
    intro w u
    have := LinearMap.pi_apply_eq_sum_univ
      ((LinearMap.proj u).comp ((toFun W v).comp (L : (s → ℂ) →ₗ[ℂ] V0 W v))) (fun x => toFun W v w x)
    simpa [hL w] using this
  have e : (fun p : (Mv W hW v).V × UN N => toFun W v p.1 p.2) =
      fun p => ∑ x : s, toFun W v p.1 x • toFun W v (L fun j => if x = j then 1 else 0) p.2 :=
    funext fun p => key p.1 p.2
  rw [e]
  refine continuous_finsetSum _ fun x _ => ?_
  exact ((LinearMap.continuous_of_finiteDimensional ((LinearMap.proj (x : UN N)).comp (toFun W v))).comp
    continuous_fst).smul ((continuous_toFun' W v _).comp continuous_snd)

theorem along_val (v : InfinitePlace E) (g : GA E N) (φ : GA E N → ℂ) (t : G N) :
    Bridge.along v g φ t.val = φ (g * infP N (Pi.mulSingle v t)) := by
  rw [infinitePart_mulSingle, ← chart_val φ g (Yv v t)]
  show chart φ g (Bridge.atW v t.val) = _
  rw [atW_eq]

theorem along_one' (v : InfinitePlace E) (g : GA E N) (φ : GA E N → ℂ) : Bridge.along v g φ 1 = φ g := by
  have := along_val v g φ 1
  simp only [Units.val_one, Pi.mulSingle_one] at this
  rw [this]
  simp [infP]

theorem atW_mem_invSet (v : InfinitePlace E) {x : Mat N} (hx : x ∈ GLs N) : Bridge.atW v x ∈ invSet E N := by
  have := atW_eq v (Matrix.GeneralLinearGroup.mkOfDetNeZero x hx)
  have e : (Matrix.GeneralLinearGroup.mkOfDetNeZero x hx).val = x := rfl
  rw [e] at this
  rw [this]
  exact val_mem_invSet _

theorem contDiff_atW (v : InfinitePlace E) : ContDiff ℝ ∞ (Bridge.atW (E := E) (a := N) v) := by
  unfold Bridge.atW
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => contDiff_pi.2 fun w => ?_
  split_ifs
  · exact (contDiff_apply ℝ (fun _ => ℂ) j).comp (contDiff_apply ℝ (fun _ => (Fin N → ℂ)) i)
  · exact contDiff_const

theorem contDiffOn_along (v : InfinitePlace E) {φ : GA E N → ℂ} (hs : φ ∈ Sm E N) (g : GA E N) :
    ContDiffOn ℝ ∞ (Bridge.along v g φ) (GLs N) :=
  ((show ∀ g, ContDiffOn ℝ ∞ (chart φ g) (invSet E N) from hs) g).comp (contDiff_atW v).contDiffOn
    fun _ hx => atW_mem_invSet v hx

theorem mem_ktype_space_along_chart (W : Submodule ℂ (Kinf E N → ℂ)) (v : InfinitePlace E) {φ : GA E N → ℂ}
    (hs : φ ∈ Sm E N) (hφ : ∀ g, (fun k : Kinf E N => φ (g * infGL E N (Unitary.toUnits k))) ∈ W) (g : GA E N)
    {y : Mat N} (hy : y ∈ GLs N) : (fun u : UN N => Bridge.along v g φ (y * u.1)) ∈ S0 W v := by
  refine ⟨(contDiffOn_along v hs g).continuousOn.comp_continuous
    ((GlobalTheory.CompanionTheory.RCalc.mulL y).continuous.comp continuous_subtype_val : Continuous fun u : UN N => y * u.1)
    fun u => GlobalTheory.CompanionTheory.RCalc.mul_mem_GLs hy (GlobalTheory.CompanionTheory.RCalc.unitary_mem_GLs u), fun u' => ?_⟩
  set Y := Matrix.GeneralLinearGroup.mkOfDetNeZero y hy
  refine ⟨fun k => φ ((g * infP N (Pi.mulSingle v (Y * Unitary.toUnits u'))) * infGL E N (Unitary.toUnits k)),
    hφ _, ?_⟩
  funext u
  simp only [LinearMap.funLeft_apply]
  have e : y * (u' * u).1 = (Y * Unitary.toUnits u' * Unitary.toUnits u).val := by
    simp only [Units.val_mul, mul_assoc]
    rfl
  rw [e, along_val, infGL_jv]
  simp only [Pi.mulSingle_mul, infinitePart_mul, mul_assoc]

section GelClm

variable {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V'] [NormedSpace ℂ V']

theorem Rd_clm (L : V →L[ℂ] V') (X : Mat N) {f : Mat N → V} {y : Mat N} (hf : DifferentiableAt ℝ f y) :
    Rd X (fun z => L (f z)) y = L (Rd X f y) := by
  unfold Rd
  have h := ((L.restrictScalars ℝ).hasFDerivAt.comp y hf.hasFDerivAt).fderiv
  have e : (fun z => L (f z)) = (L.restrictScalars ℝ) ∘ f := rfl
  rw [e]
  exact (DFunLike.congr_fun h (y * X)).trans rfl

theorem Eu_clm (L : V →L[ℂ] V') (s : Bool) (a b : Fin N) {f : Mat N → V} {y : Mat N}
    (hf : DifferentiableAt ℝ f y) : Eu s a b (fun z => L (f z)) y = L (Eu s a b f y) := by
  simp only [Eu, Pi.smul_apply, Pi.add_apply, Rd_clm L _ hf, map_add (f := _), map_smul]

theorem Epow_clm (L : V →L[ℂ] V') (s : Bool) {f : Mat N → V} (hf : ContDiffOn ℝ ∞ f (GLs N)) (m : ℕ) :
    ∀ a b : Fin N, Set.EqOn (Epow s m a b (fun z => L (f z))) (fun z => L (Epow s m a b f z)) (GLs N) := by
  induction m with
  | zero =>
    intro a b y _
    by_cases hab : a = b <;> simp [Epow, hab]
  | succ m ih =>
    intro a b y hy
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Epow, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [GlobalTheory.CompanionTheory.WaveAll.Eu_congr GlobalTheory.CompanionTheory.RCalc.isOpen_GLs (ih c b) s a c hy]
    exact Eu_clm L s a c (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth
      (GlobalTheory.CompanionTheory.WaveAll.Epow_smooth GlobalTheory.CompanionTheory.RCalc.rcalc hf s m c b) hy)

theorem gel_clm (L : V →L[ℂ] V') (s : Bool) (m : ℕ) {f : Mat N → V} (hf : ContDiffOn ℝ ∞ f (GLs N)) {y : Mat N}
    (hy : y ∈ GLs N) : gel s m (fun z => L (f z)) y = L (gel s m f y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gel, Finset.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun a _ => Epow_clm L s hf m a a hy

end GelClm

theorem exists_linv' (W : Submodule ℂ (Kinf E N → ℂ)) (hW : FiniteDimensional ℂ W) (v : InfinitePlace E) :
    ∃ (s : Finset (UN N)) (L : (s → ℂ) →L[ℂ] (Mv W hW v).V), ∀ w : (Mv W hW v).V,
      L (fun x => toFun W v w x) = w := by
  obtain ⟨s, L, hL⟩ := exists_linv W hW v
  exact ⟨s, L, hL⟩

def ofKTypeVector (W : Submodule ℂ (Kinf E N → ℂ)) (hW : FiniteDimensional ℂ W) (v : InfinitePlace E) (w : S0 W v) :
    (Mv W hW v).V := w

def sec (W : Submodule ℂ (Kinf E N → ℂ)) (hW : FiniteDimensional ℂ W) (v : InfinitePlace E) (φ : GA E N → ℂ)
    (hs : φ ∈ Sm E N) (hφ : ∀ g, (fun k : Kinf E N => φ (g * infGL E N (Unitary.toUnits k))) ∈ W) (g : GA E N) :
    Mat N → (Mv W hW v).V :=
  fun y => if hy : y ∈ GLs N then ofKTypeVector W hW v ⟨fun u => Bridge.along v g φ (y * u.1), mem_ktype_space_along_chart W v hs hφ g hy⟩
    else 0

theorem toFun_sec (W : Submodule ℂ (Kinf E N → ℂ)) (hW : FiniteDimensional ℂ W) (v : InfinitePlace E)
    (φ : GA E N → ℂ) (hs : φ ∈ Sm E N) (hφ : ∀ g, (fun k : Kinf E N => φ (g * infGL E N (Unitary.toUnits k))) ∈ W)
    (g : GA E N) {y : Mat N} (hy : y ∈ GLs N) (u : UN N) :
    toFun W v (sec W hW v φ hs hφ g y) u = Bridge.along v g φ (y * u.1) := by
  unfold sec
  rw [dite_eq_left hy]
  rfl

theorem sec_mem_CE (W : Submodule ℂ (Kinf E N → ℂ)) (hW : FiniteDimensional ℂ W) (v : InfinitePlace E)
    (φ : GA E N → ℂ) (hs : φ ∈ Sm E N) (hφ : ∀ g, (fun k : Kinf E N => φ (g * infGL E N (Unitary.toUnits k))) ∈ W)
    (g : GA E N) : sec W hW v φ hs hφ g ∈ CE (Mv W hW v) := by
  obtain ⟨s, L, hL⟩ := exists_linv' W hW v
  refine ⟨?_, fun y hy k => ?_⟩
  · have e : ∀ y ∈ GLs N, sec W hW v φ hs hφ g y = L (fun x : s => Bridge.along v g φ (y * (x : UN N).1)) := by
      intro y hy
      conv_lhs => rw [← hL (sec W hW v φ hs hφ g y)]
      congr 1
      funext x
      exact toFun_sec W hW v φ hs hφ g hy x
    refine ContDiffOn.congr ?_ e
    refine (L.restrictScalars ℝ).contDiff.comp_contDiffOn (contDiffOn_pi.2 fun x => ?_)
    exact (contDiffOn_along v hs g).comp (GlobalTheory.CompanionTheory.RCalc.mulR (x : UN N).1).contDiff.contDiffOn
      fun z hz => GlobalTheory.CompanionTheory.RCalc.mul_mem_GLs hz (GlobalTheory.CompanionTheory.RCalc.unitary_mem_GLs _)
  · have hyk : y * k.1 ∈ GLs N := GlobalTheory.CompanionTheory.RCalc.mul_mem_GLs hy (GlobalTheory.CompanionTheory.RCalc.unitary_mem_GLs k)
    apply serre_vanishing_zero_trans
    intro u
    rw [toFun_rho, toFun_sec W hW v φ hs hφ g hyk, toFun_sec W hW v φ hs hφ g hy, inv_inv]
    congr 1
    show y * k.1 * u.1 = y * (k.1 * u.1)
    rw [mul_assoc]

theorem sec_isEig (W : Submodule ℂ (Kinf E N → ℂ)) (hW : FiniteDimensional ℂ W) (v : InfinitePlace E)
    (φ : GA E N → ℂ) (hs : φ ∈ Sm E N) (hφ : ∀ g, (fun k : Kinf E N => φ (g * infGL E N (Unitary.toUnits k))) ∈ W)
    (g : GA E N) (χ : Inf N) (h : IsEig χ (Bridge.along v g φ)) : IsEig χ (sec W hW v φ hs hφ g) := by
  obtain ⟨s, L, hL⟩ := exists_linv' W hW v
  intro sb m y hy
  set G' : Mat N → (s → ℂ) := fun z x => Bridge.along v g φ (z * (x : UN N).1) with hG'd
  have hG' : ContDiffOn ℝ ∞ G' (GLs N) := contDiffOn_pi.2 fun x =>
    (contDiffOn_along v hs g).comp (GlobalTheory.CompanionTheory.RCalc.mulR (x : UN N).1).contDiff.contDiffOn
      fun z hz => GlobalTheory.CompanionTheory.RCalc.mul_mem_GLs hz (GlobalTheory.CompanionTheory.RCalc.unitary_mem_GLs _)
  have e : Set.EqOn (sec W hW v φ hs hφ g) (fun z => L (G' z)) (GLs N) := by
    intro z hz
    conv_lhs => rw [← hL (sec W hW v φ hs hφ g z)]
    congr 1
    funext x
    exact toFun_sec W hW v φ hs hφ g hz x
  rw [GlobalTheory.CompanionTheory.WaveAll.gel_congr GlobalTheory.CompanionTheory.RCalc.isOpen_GLs e sb m hy, gel_clm L sb m hG' hy, e hy, ← L.map_smul]
  congr 1
  funext x
  have h1 := gel_clm (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : s => ℂ) x) sb m hG' hy
  simp only [ContinuousLinearMap.proj_apply] at h1
  rw [Pi.smul_apply, ← h1]
  show gel sb m (fun z => Bridge.along v g φ (z * (x : UN N).1)) y = _
  rw [GlobalTheory.CompanionTheory.RCalc.gel_right sb m (GlobalTheory.CompanionTheory.RCalc.unitary_mem_GLs _) (contDiffOn_along v hs g) hy]
  exact h sb m _ (GlobalTheory.CompanionTheory.RCalc.mul_mem_GLs hy (GlobalTheory.CompanionTheory.RCalc.unitary_mem_GLs _))

end PositivityTheory.Rg.BcB.CG.ReproL
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PReproCb
noncomputable section

open MeasureTheory NumberField GlobalTheory.CuspRep
open scoped Pointwise
open PositivityTheory.RgTw (G)

namespace PositivityTheory.Rg.BcB.CG.ReproL

open Classical

section Gen

variable {G U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  [TopologicalSpace U] [CompactSpace U] [T2Space U] [SecondCountableTopology U] [MeasurableSpace U] [BorelSpace U]
  (ν : Measure U) [IsFiniteMeasure ν]
  (K : Subgroup G) (hK : IsCompact (K : Set G)) (ι : U → G) (hι : Continuous ι) (hιK : ∀ u, ι u ∈ K)

include hK in
theorem integral_mul_mem (k : G) (hk : k ∈ K) (F : G → ℂ) : ∫ y, F (y * k) ∂μ = ∫ y, F y ∂μ := by
  have e : Measure.map (⇑(MeasurableEquiv.mulRight k)) μ = μ :=
    GlobalTheory.CompactRight.map_mul_right_eq_of_mem_compact μ K hK k hk
  conv_rhs => rw [← e]
  rw [(MeasurableEquiv.mulRight k).measurableEmbedding.integral_map]
  rfl

include hK hι hιK in
theorem swap_right (c : G → U → ℂ) (hc : Continuous (Function.uncurry c)) (Kc : Set G) (hKc : IsCompact Kc)
    (hcK : ∀ y u, y ∉ Kc → c y u = 0) (h : G → ℂ) (hh : Continuous h) :
    ∫ y, (∫ u, c y u * h (y * ι u) ∂ν) ∂μ = ∫ y, (∫ u, c (y * (ι u)⁻¹) u ∂ν) * h y ∂μ := by
  have hKK : IsCompact (Kc * (K : Set G)) := hKc.mul hK
  have i1 : Integrable (Function.uncurry fun y u => c y u * h (y * ι u)) (μ.prod ν) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hc.mul (hh.comp (continuous_fst.mul (hι.comp continuous_snd)))
    · refine HasCompactSupport.intro (hKc.prod isCompact_univ) fun p hp => ?_
      have : p.1 ∉ Kc := fun h1 => hp ⟨h1, Set.mem_univ _⟩
      simp [Function.uncurry, hcK _ _ this]
  have i2 : Integrable (Function.uncurry fun y u => c (y * (ι u)⁻¹) u * h y) (μ.prod ν) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (hc.comp ((continuous_fst.mul (hι.comp continuous_snd).inv).prodMk continuous_snd)).mul
        (hh.comp continuous_fst)
    · refine HasCompactSupport.intro (hKK.prod isCompact_univ) fun p hp => ?_
      have : p.1 * (ι p.2)⁻¹ ∉ Kc := fun h1 =>
        hp ⟨⟨p.1 * (ι p.2)⁻¹, h1, ι p.2, hιK p.2, by simp⟩, Set.mem_univ _⟩
      simp [Function.uncurry, hcK _ _ this]
  rw [integral_integral_swap i1]
  have e : ∀ u, ∫ y, c y u * h (y * ι u) ∂μ = ∫ y, c (y * (ι u)⁻¹) u * h y ∂μ := by
    intro u
    have := integral_mul_mem μ K hK (ι u) (hιK u) (fun y => c (y * (ι u)⁻¹) u * h y)
    simpa using this
  simp_rw [e]
  rw [← integral_integral_swap i2]
  congr 1
  funext y
  rw [integral_mul_const]

include hK hι hιK in
theorem avg_cont_supp (c : G → U → ℂ) (hc : Continuous (Function.uncurry c)) (Kc : Set G) (hKc : IsCompact Kc)
    (hcK : ∀ y u, y ∉ Kc → c y u = 0) :
    Continuous (fun y => ∫ u, c (y * (ι u)⁻¹) u ∂ν) ∧ HasCompactSupport (fun y => ∫ u, c (y * (ι u)⁻¹) u ∂ν) := by
  constructor
  · have := continuous_parametric_integral_of_continuous (μ := ν) (f := fun y u => c (y * (ι u)⁻¹) u)
      (hc.comp ((continuous_fst.mul (hι.comp continuous_snd).inv).prodMk continuous_snd)) isCompact_univ
    simpa [Measure.restrict_univ] using this
  · refine HasCompactSupport.intro (hKc.mul hK) fun y hy => ?_
    have : ∀ u, c (y * (ι u)⁻¹) u = 0 := fun u => hcK _ _ fun h1 => hy ⟨_, h1, ι u, hιK u, by simp⟩
    simp [this]

end Gen

theorem continuous_toUnitsU (N : ℕ) :
    Continuous (fun u : Matrix.unitaryGroup (Fin N) ℂ => (Unitary.toUnits u : G N)) := by
  rw [Units.continuous_iff]
  constructor
  · exact continuous_subtype_val
  · exact continuous_star.comp continuous_subtype_val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem continuous_along_infP (v : InfinitePlace E) (g : GA E N) (φ : GA E N → ℂ) (hs : φ ∈ Sm E N) :
    Continuous fun t : G N => φ (g * infP N (Pi.mulSingle v t)) := by
  let Mt : (InfinitePlace E → G N) → GL (Fin N) (Cinf E) := fun y =>
    Units.map (Matrix.piRingEquiv (n := Fin N) (β := fun _ : InfinitePlace E => ℂ)).symm.toMonoidHom
      (MulEquiv.piUnits.symm y)
  have hM : Continuous Mt := by
    refine Continuous.units_map _ ?_ |>.comp (ContinuousMulEquiv.piUnits (M := fun _ : InfinitePlace E =>
      Matrix (Fin N) (Fin N) ℂ)).symm.continuous
    exact continuous_pi fun i => continuous_pi fun j => continuous_pi fun v => (continuous_apply v).matrix_elem i j
  have hL : Continuous fun x : Matrix (Fin N) (Fin N) (Cinf E) => (toL x : Lie E N) := continuous_id
  have e : (fun t : G N => φ (g * infP N (Pi.mulSingle v t))) =
      fun t => chart φ g (toL (Mt (Pi.mulSingle v t)).val) := by
    funext t
    rw [chart_val]
    rfl
  rw [e]
  exact (hs g).continuousOn.comp_continuous
    (hL.comp ((Units.continuous_val (M := Matrix (Fin N) (Fin N) (Cinf E))).comp (hM.comp (continuous_mulSingle (A := fun _ : InfinitePlace E => G N) v))))
    fun t => val_mem_invSet _

end PositivityTheory.Rg.BcB.CG.ReproL
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PReproCa
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.RgBcC

namespace PositivityTheory.Rg.BcB.CG.ReproL

theorem norm_cosh_sub_one_le {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖Complex.cosh z - 1‖ ≤ 2 * ‖z‖ := by
  have h1 := Complex.norm_exp_sub_one_le hz
  have h2 := Complex.norm_exp_sub_one_le (x := -z) (by rwa [norm_neg])
  rw [norm_neg] at h2
  have e : Complex.cosh z - 1 = ((Complex.exp z - 1) + (Complex.exp (-z) - 1)) / 2 := by
    rw [show Complex.cosh z = (Complex.exp z + Complex.exp (-z)) / 2 from rfl]; ring
  rw [e, norm_div]
  have h3 := norm_add_le (Complex.exp z - 1) (Complex.exp (-z) - 1)
  have h4 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h4]
  linarith

theorem continuous_cas (N : ℕ) : Continuous fun χ : Inf N => cas χ := by
  have hA : ∀ f : Inf N → Fin N → ℂ, Continuous f → Continuous fun χ => Formalism.REAL.Amat (f χ) := by
    intro f hf
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Formalism.REAL.Amat, Matrix.of_apply]
    split_ifs
    · exact (continuous_apply a).comp hf
    · exact continuous_const
    · exact continuous_const
  have hg : ∀ s : Bool, Continuous fun χ : Inf N => GlobalTheory.Dec.gelfVal (χ s) 2 := by
    intro s
    unfold GlobalTheory.Dec.gelfVal
    refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
    have hf : Continuous fun χ : Inf N => fun c : Fin N => χ s c + ((N : ℂ) - 1) / 2 :=
      continuous_pi fun c => (continuous_apply_apply s c).add continuous_const
    exact ((hA _ hf).pow 2).matrix_elem a b
  unfold cas
  exact continuous_const.mul ((hg true).add (hg false))

theorem exists_bump (N : ℕ) (R : ℝ) : ∃ (g : ℝ → ℝ) (T : ℝ), 0 < T ∧ IsBump g T ∧
    ∀ χ : Inf N, (∀ s i, ‖χ s i‖ ≤ R) → 1 / 2 ≤ ‖coshT g (cas χ)‖ := by
  have hS : IsCompact {χ : Inf N | ∀ s i, ‖χ s i‖ ≤ R} := by
    have e : {χ : Inf N | ∀ s i, ‖χ s i‖ ≤ R} =
        Set.univ.pi fun _ => Set.univ.pi fun _ => Metric.closedBall (0 : ℂ) R := by
      ext χ; simp [Set.mem_pi]
    rw [e]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn (continuous_cas N).continuousOn
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set s := Real.sqrt C' with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set T : ℝ := 1 / (4 * (s + 1)) with hT
  have hT0 : 0 < T := by positivity
  have hTs : T * s ≤ 1 / 4 := by
    rw [hT, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  let f : ContDiffBump (0 : ℝ) := ⟨T / 2, T, by positivity, by linarith⟩
  set g : ℝ → ℝ := f.normed volume with hg
  have hsupp : ∀ t, g t ≠ 0 → |t| < T := by
    intro t ht
    have : t ∈ Function.support g := ht
    rw [hg, ContDiffBump.support_normed_eq] at this
    simpa [Metric.mem_ball, Real.dist_eq] using this
  refine ⟨g, T, hT0, ⟨ContDiffBump.contDiff_normed f, fun t => ?_, fun t ht => ?_⟩, ?_⟩
  · have := ContDiffBump.normed_neg f (μ := volume) t
    simpa [hg] using this
  · by_contra h
    exact absurd (hsupp t h) (not_lt.2 ht.le)
  intro χ hχ
  set c := cas χ with hc
  have hcC : ‖c‖ ≤ C' := (hC χ hχ).trans (le_max_left _ _)
  have hroot : ‖c ^ (1 / 2 : ℂ)‖ ≤ s := by
    have e : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_cpow_real, ← Real.sqrt_eq_rpow, hs]
    exact Real.sqrt_le_sqrt hcC
  have hgc : Continuous g := (ContDiffBump.contDiff_normed f (n := 0)).continuous
  have hgcs : HasCompactSupport g := ContDiffBump.hasCompactSupport_normed f
  have hgC : HasCompactSupport fun t => (g t : ℂ) := hgcs.comp_left Complex.ofReal_zero
  have hcont1 : Continuous fun t : ℝ => Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) :=
    Complex.continuous_cosh.comp (Complex.continuous_ofReal.mul continuous_const)
  have hi1 : Integrable fun t : ℝ => (g t : ℂ) * Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) :=
    ((Complex.continuous_ofReal.comp hgc).mul hcont1).integrable_of_hasCompactSupport (hgC.mul_right)
  have hi2 : Integrable fun t : ℝ => (g t : ℂ) :=
    (Complex.continuous_ofReal.comp hgc).integrable_of_hasCompactSupport hgC
  have hone : ∫ t, (g t : ℂ) = 1 := by
    rw [integral_complex_ofReal, hg, ContDiffBump.integral_normed]; simp
  have h3 : ∫ t, (g t : ℂ) * (Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) - 1) =
      (∫ t, (g t : ℂ) * Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ))) - ∫ t, (g t : ℂ) := by
    rw [← integral_sub hi1 hi2]; congr 1; funext t; ring
  have hdiff : coshT g c - 1 = ∫ t, (g t : ℂ) * (Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) - 1) := by
    rw [h3, hone]; rfl
  have hbound : ∀ t, ‖(g t : ℂ) * (Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) - 1)‖ ≤ g t * (1 / 2) := by
    intro t
    by_cases h0 : g t = 0
    · simp [h0]
    have ht := hsupp t h0
    have hz : ‖(t : ℂ) * c ^ (1 / 2 : ℂ)‖ ≤ 1 / 4 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |t| * ‖c ^ (1 / 2 : ℂ)‖ ≤ T * s := mul_le_mul ht.le hroot (norm_nonneg _) hT0.le
        _ ≤ 1 / 4 := hTs
    have hgt : 0 ≤ g t := ContDiffBump.nonneg_normed f t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgt]
    refine mul_le_mul_of_nonneg_left ?_ hgt
    calc ‖Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) - 1‖ ≤ 2 * ‖(t : ℂ) * c ^ (1 / 2 : ℂ)‖ :=
          norm_cosh_sub_one_le (hz.trans (by norm_num))
      _ ≤ 1 / 2 := by linarith
  have hle : ‖coshT g c - 1‖ ≤ 1 / 2 := by
    rw [hdiff]
    calc ‖∫ t, (g t : ℂ) * (Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) - 1)‖ ≤ ∫ t, g t * (1 / 2) :=
          norm_integral_le_of_norm_le ((hgc.mul continuous_const).integrable_of_hasCompactSupport hgcs.mul_right)
            (Filter.Eventually.of_forall hbound)
      _ = 1 / 2 := by rw [integral_mul_const, hg, ContDiffBump.integral_normed]; ring
  have := norm_sub_norm_le (1 : ℂ) (1 - coshT g c)
  rw [sub_sub_cancel, norm_one, norm_sub_rev] at this
  linarith

theorem exists_enum {N : ℕ} (m : Multiset ℂ) (h : Multiset.card m = N) :
    ∃ e : Fin N → ℂ, Multiset.map e Finset.univ.val = m := by
  subst h
  refine ⟨fun i => m.toList.get (Fin.cast (by simp) i), ?_⟩
  rw [Fin.univ_val_map]
  have e : List.ofFn (fun i : Fin (Multiset.card m) => m.toList.get (Fin.cast (by simp) i)) = m.toList :=
    List.ext_get (by simp) (by simp)
  rw [e, Multiset.coe_toList]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem exists_chi (hB : Bridge.BridgeSt) (R : ℝ) (v : InfinitePlace E) (φ : Sm E N)
    (hR : PositivityTheory.Rg.BcB.SpectralAccumulation.InfBdd R (Submodule.span ℂ {φ})) :
    ∃ χ : Inf N, (∀ s i, ‖χ s i‖ ≤ R) ∧ ∀ g : GA E N, IsEig χ (Bridge.along v g φ.1) := by
  obtain ⟨m1, h1, b1⟩ := hR v.embedding
  obtain ⟨m2, h2, b2⟩ := hR (ComplexEmbedding.conjugate v.embedding)
  obtain ⟨e1, he1⟩ := exists_enum m1 h1.1
  obtain ⟨e2, he2⟩ := exists_enum m2 h2.1
  refine ⟨fun s => if s then e1 else e2, ?_, ?_⟩
  · intro s i
    cases s
    · exact b2 _ (he2 ▸ Multiset.mem_map_of_mem e2 (Finset.mem_univ_val i))
    · exact b1 _ (he1 ▸ Multiset.mem_map_of_mem e1 (Finset.mem_univ_val i))
  · intro g
    have key := (hB E N (Submodule.span ℂ {φ}) v (fun s => if s then e1 else e2)).2
      ⟨by simpa [he1] using h1, by simpa [he2] using h2⟩
    exact key φ (Submodule.mem_span_singleton_self φ) g

end PositivityTheory.Rg.BcB.CG.ReproL
end
end

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open scoped ContDiff ComplexConjugate InnerProductSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace PositivityTheory.Rg.BcB.CG.ReproL

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

instance scUN (N : ℕ) : SecondCountableTopology (UN N) :=
  (Topology.IsEmbedding.subtypeVal (p := fun x => x ∈ Matrix.unitaryGroup (Fin N) ℂ)).secondCountableTopology

theorem one_mem_GLs' : (1 : Mat N) ∈ GLs N := by simp [GLs]

theorem local_repro (hK : KerEx) (hM : MultAlg) (hB : Bridge.BridgeSt) (W : Submodule ℂ (Kinf E N → ℂ))
    (hW : FiniteDimensional ℂ W) (R : ℝ) (v : InfinitePlace E) [MeasurableSpace (G N)] [BorelSpace (G N)]
    (μ0 : Measure (G N)) [μ0.IsHaarMeasure] :
    ∃ a : G N → ℂ, Continuous a ∧ HasCompactSupport a ∧ ∀ φ : Sm E N,
      (∀ g, (fun k : Kinf E N => φ.1 (g * infGL E N (Unitary.toUnits k))) ∈ W) →
      PositivityTheory.Rg.BcB.SpectralAccumulation.InfBdd R (Submodule.span ℂ {φ}) →
      ∃ s : ℂ, 1 / 2 ≤ ‖s‖ ∧ ∀ g : GA E N, ∫ t, a t * φ.1 (g * infP N (Pi.mulSingle v t)) ∂μ0 = s * φ.1 g := by
  obtain ⟨g, T, hT, hg, hval⟩ := exists_bump N R
  obtain ⟨c0, hc0⟩ := hK N
  obtain ⟨k, hk⟩ := (hc0 μ0 (Mv W hW v)).1 [] g T hg
  have hmult : IsMult μ0 (Mv W hW v) k (fun χ => coshT g (cas χ)) T :=
    ⟨1, fun _ => 1, fun _ => [], fun _ => g, fun _ => k, fun _ => ⟨hg, hk⟩, fun y _ => by simp,
      fun χ => by simp [zVal]⟩
  have hact := (hM N μ0 (Mv W hW v) k k _ _ T T hmult hmult).2.2.2
  have : CompleteSpace (Mv W hW v).V := FiniteDimensional.complete ℂ _
  set b : G N → (Mv W hW v).V := fun y =>
    (InnerProductSpace.toDual ℂ (Mv W hW v).V).symm ((evL W hW v 1).comp (k y.val)) with hbdef
  have hb : ∀ y w, ⟪b y, w⟫_ℂ = toFun W v (k y.val w) 1 := fun y w => by
    rw [hbdef, InnerProductSpace.toDual_symm_apply]; rfl
  have hbc : Continuous b :=
    (InnerProductSpace.toDual ℂ (Mv W hW v).V).symm.continuous.comp
      ((ContinuousLinearMap.compL ℂ _ _ ℂ (evL W hW v 1)).continuous.comp (mult_continuous hmult))
  set c : G N → UN N → ℂ := fun y u => conj (toFun W v (b y) u) with hcdef
  have hcc : Continuous (Function.uncurry c) :=
    Complex.continuous_conj.comp ((continuous_toFun₂ W hW v).comp ((hbc.comp continuous_fst).prodMk continuous_snd))
  set Kc := tsupport fun y : G N => k y.val with hKcdef
  have hKc : IsCompact Kc := mult_hasCompactSupport hmult
  have hk0 : ∀ y, y ∉ Kc → k y.val = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport (f := fun y : G N => k y.val) hy
  have hcK : ∀ y u, y ∉ Kc → c y u = 0 := by
    intro y u hy
    have hb0 : b y = 0 := by simp [hbdef, hk0 y hy]
    have ht : toFun W v (b y) = 0 := by rw [hb0]; exact (toFun W v).map_zero
    simp [hcdef, ht]
  set ι : UN N → G N := fun u => Unitary.toUnits u with hιdef
  have hι : Continuous ι := continuous_toUnitsU N
  set Ku : Subgroup (G N) := (Unitary.toUnits (R := Mat N)).range with hKudef
  have hKu : IsCompact (Ku : Set (G N)) := by
    have : (Ku : Set (G N)) = Set.range ι := by ext x; simp [Ku, ι]
    rw [this]; exact isCompact_range hι
  have hιK : ∀ u, ι u ∈ Ku := fun u => ⟨u, rfl⟩
  obtain ⟨ha1, ha2⟩ := avg_cont_supp (nuN N) Ku hKu ι hι hιK c hcc Kc hKc hcK
  refine ⟨_, ha1, ha2, ?_⟩
  intro φ hφ hR
  obtain ⟨χ, hχb, hχ⟩ := exists_chi hB R v φ hR
  refine ⟨coshT g (cas χ), hval χ hχb, fun g0 => ?_⟩
  set F := sec W hW v φ.1 φ.2 hφ g0 with hFdef
  have hF := sec_mem_CE W hW v φ.1 φ.2 hφ g0
  have hE := sec_isEig W hW v φ.1 φ.2 hφ g0 χ (hχ g0)
  have h1 := hact χ F hF hE 1 one_mem_GLs'
  set h : G N → ℂ := fun t => φ.1 (g0 * infP N (Pi.mulSingle v t)) with hhdef
  have hh : Continuous h := continuous_along_infP v g0 φ.1 φ.2
  have hFc : Continuous fun y : G N => F y.val :=
    hF.1.continuousOn.comp_continuous Units.continuous_val val_mem_GLs
  have hint : Integrable (fun y : G N => k y.val (F (1 * y.val))) μ0 := by
    simp only [one_mul]
    refine Continuous.integrable_of_hasCompactSupport ((mult_continuous hmult).clm_apply hFc) ?_
    exact HasCompactSupport.intro hKc fun y hy => by simp [hk0 y hy]
  have h2 := congrArg (evL W hW v 1) h1
  simp only [PositivityTheory.RgBcC.act] at h2
  rw [← ContinuousLinearMap.integral_comp_comm _ hint] at h2
  have hL : ∀ y : G N, evL W hW v 1 (k y.val (F (1 * y.val))) = ∫ u, c y u * h (y * ι u) ∂nuN N := by
    intro y
    rw [one_mul, evL_apply, ← hb]
    refine (inner_eq W v (b y) (F y.val)).trans (integral_congr_ae (Filter.Eventually.of_forall fun u => ?_))
    simp only [hcdef, hhdef]
    rw [toFun_sec W hW v φ.1 φ.2 hφ g0 (val_mem_GLs y) u]
    congr 1
    rw [show y.val * u.1 = (y * ι u).val from rfl, along_val]
  have hRHS : evL W hW v 1 (coshT g (cas χ) • F 1) = coshT g (cas χ) * φ.1 g0 := by
    rw [map_smul, evL_apply, toFun_sec W hW v φ.1 φ.2 hφ g0 one_mem_GLs' 1, smul_eq_mul]
    congr 1
    simpa using along_one' v g0 φ.1
  simp_rw [hL] at h2
  rw [hRHS] at h2
  rw [← h2, swap_right μ0 (nuN N) Ku hKu ι hι hιK c hcc Kc hKc hcK h hh]

end PositivityTheory.Rg.BcB.CG.ReproL
