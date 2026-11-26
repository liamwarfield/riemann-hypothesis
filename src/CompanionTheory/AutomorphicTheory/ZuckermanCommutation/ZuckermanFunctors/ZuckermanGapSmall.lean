module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DerivedSeriesDerivation
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorDifferentialSignRuleQuadratic
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorPowerIntegral
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CasimirSplitting
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CasimirDiagonalSum
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WordLengthBoundOfLinear
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TruncatedDerivationLimit
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.MultOne
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.OrbitDerivatives.LieAlgebraHomomorphism
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.FormalDegreeConstantDiscrete
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.HarishChandraMultiplicityBound
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundOfCompact
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SnTens2Statement

@[expose] public section

section -- merged from CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ShiftApply
open Matrix Finset
open scoped Kronecker

noncomputable section

namespace CompanionTheory.Zuck

open BranchingSupport Formalism.FourierDecayAlt.ThreeDimData
open PI.UpqRep (IsHCParam)
open PI.ZuckTensor (GapAtLeast)

structure Lib (t : ∀ n : ℕ, (Fin n → Bool) → ℝ) : Prop where
  zg : ZG t
  dec : ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (μ : Fin (2 * r + k + 1) → ℝ) (U : URep k r) (h : ℝ) (m : ℕ),
    U.R.IsDS ε μ → GapAtLeast ε μ h → t _ ε + m < h → Decay U m
  uniq : ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (μ : Fin (2 * r + k + 1) → ℝ) (R R' : Rep k r) (h : ℝ),
    R.IsDS ε μ → R'.IsDS ε μ → GapAtLeast ε μ h → t _ ε < h →
    ∃ e : R.H ≃ₗᵢ[ℂ] R'.H, ∀ g ∈ GG k r, ∀ x, e (R.σ g x) = R'.σ g (e x)
  exist : ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (μ μ' : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (h : ℝ),
    R.IsDS ε μ → IsHCParam μ' → GapAtLeast ε μ' h → t _ ε < h → ∃ R' : Rep k r, R'.IsDS ε μ'

structure Steps : Prop where
  infChar : PI.DSInfCharCap.DSInfCharCap
  decOfInj : DecOfInj
  decOfTrace : DecOfTrace
  homCat : HomCat
  okTriv : OKTriv
  okVr : OKVr
  okWedge : OKWedge
  okTens : OKTens
  matHom : MatHom
  uIso : UIso
  homLie : HomLie
  casSplit : CasSplit
  casDS : CasDS
  wedgeInt : WedgeInt
  wedgeQ : WedgeQ
  schur : Schur
  adj : Adj
  multOne : MultOne
  inj : InjStep
  occ : OccStep
  zuckH : ZuckH
  decTens : DecTens
  toRaw : ToRaw
  count : Count

section lin

variable {O : Type 1} {N : O → Type} [∀ o, AddCommGroup (N o)] [∀ o, Module ℂ (N o)]
  {Hom : ∀ a b, (N a →ₗ[ℂ] N b) → Prop}

theorem dec_iso (C : IsLinCat N Hom) {κ : Type} [Fintype κ] {X : O} {T T' : κ → O}
    (h : ∃ io pr, IsDec Hom X T io pr) (e : ∀ s, IsIso Hom (T s) (T' s)) : ∃ io pr, IsDec Hom X T' io pr := by
  obtain ⟨io, pr, h⟩ := h
  choose f g hf hg hgf hfg using e
  have a1 : ∀ s y, g s (f s y) = y := fun s y => LinearMap.congr_fun (hgf s) y
  have a2 : ∀ s y, f s (g s y) = y := fun s y => LinearMap.congr_fun (hfg s) y
  refine ⟨fun s => io s ∘ₗ g s, fun s => f s ∘ₗ pr s, fun s => C.comp _ _ _ _ _ (hg s) (h.io_hom s),
    fun s => C.comp _ _ _ _ _ (h.pr_hom s) (hf s), ?_, fun s => ?_, fun s s' hs => ?_⟩
  · rw [← h.sum]
    exact Finset.sum_congr rfl fun s _ => LinearMap.ext fun x => by simp [a1]
  · refine LinearMap.ext fun y => ?_
    have := LinearMap.congr_fun (h.pr_io s) (g s y)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this ⊢
    rw [this, a2]
  · refine LinearMap.ext fun y => ?_
    have := LinearMap.congr_fun (h.pr_io_ne s s' hs) (g s' y)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at this ⊢
    rw [this, map_zero]

end lin

section num

variable {n : ℕ}

theorem shift_shift (b : Bool) (μ : Fin n → ℝ) (s : Fin n) : shift (!b) (shift b μ s) s = μ := by
  cases b <;> simp [shift]

theorem shift_apply (b : Bool) (μ : Fin n → ℝ) (s a : Fin n) :
    shift b μ s a = μ a + if a = s then (if b then -1 else 1) else 0 := by
  cases b <;> by_cases h : a = s <;> simp [shift, h, Pi.single_apply, sub_eq_add_neg]

theorem gap_shift {ε : Fin n → Bool} {μ : Fin n → ℝ} {h : ℝ} (hg : GapAtLeast ε μ h) (b : Bool) (s : Fin n) :
    GapAtLeast ε (shift b μ s) (h - 1) := by
  intro a c hac
  have h1 := hg a c hac
  have hne : a ≠ c := fun e => hac (by rw [e])
  rw [shift_apply, shift_apply]
  rw [le_abs] at h1 ⊢
  by_cases e1 : a = s <;> by_cases e2 : c = s
  · exact absurd (e1.trans e2.symm) hne
  all_goals cases b <;> simp only [e1, e2, if_true, if_false, Bool.false_eq_true] at h1 ⊢ <;>
    rcases h1 with h1 | h1 <;> first | (left; linarith) | (right; linarith)

theorem casG_shift (b : Bool) (μ : Fin n → ℝ) (s : Fin n) :
    casG (shift b μ s) = casG μ + 2 * (if b then -1 else 1) * μ s + 1 := by
  have : ∑ a, shift b μ s a ^ 2 = ∑ a, (μ a ^ 2 + if a = s then 2 * (if b then -1 else 1) * μ s + 1 else 0) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [shift_apply]
    by_cases h : a = s
    · subst h; cases b <;> simp <;> ring
    · simp [h]
  unfold casG
  rw [this, Finset.sum_add_distrib]
  simp
  ring

theorem cas_ne {μ : Fin n → ℝ} (hμ : StrictAnti μ) (b : Bool) (s t : Fin n) :
    (casG (shift b (shift b μ s) t) : ℂ) ≠ 2 * (casG (shift b μ s) : ℂ) - (casG μ : ℂ) := by
  intro h
  have h' : casG (shift b (shift b μ s) t) = 2 * casG (shift b μ s) - casG μ := by exact_mod_cast h
  rw [casG_shift b (shift b μ s) t, casG_shift b μ s, shift_apply] at h'
  by_cases e : t = s
  · subst e
    cases b <;> simp at h' <;> linarith
  · apply e
    apply hμ.injective
    cases b <;> simp [e] at h' <;> linarith

theorem shift_inj (b : Bool) (μ : Fin n → ℝ) : Function.Injective (shift b μ) := by
  intro s t h
  have := congrFun h s
  rw [shift_apply, shift_apply] at this
  by_contra e
  cases b <;> simp [e] at this

theorem near {ε : Fin n → Bool} {μ : Fin n → ℝ} {h D : ℝ} (hμ : IsHCParam μ) (hg : GapAtLeast ε μ h)
    (hD : ∀ a c, a < c → D ≤ μ a - μ c) {ν : Fin n → ℝ} (j : ℕ) (hj : (j : ℝ) < D)
    (hx : ∀ a, ∃ x : ℕ, x ≤ j ∧ ν a = μ a + x) :
    IsHCParam ν ∧ GapAtLeast ε ν (h - j) ∧ ∀ a c, a < c → D - j ≤ ν a - ν c := by
  choose x hxj hx using hx
  have hx0 : ∀ a, (0 : ℝ) ≤ x a := fun a => Nat.cast_nonneg _
  have hx1 : ∀ a, (x a : ℝ) ≤ j := fun a => by exact_mod_cast hxj a
  have h3 : ∀ a c, a < c → D - j ≤ ν a - ν c := fun a c hac => by
    have := hD a c hac
    rw [hx, hx]; linarith [hx0 a, hx1 c]
  refine ⟨⟨fun a c hac => by linarith [h3 a c hac], fun a => ?_⟩, fun a c hac => ?_, h3⟩
  · obtain ⟨m, hm⟩ := hμ.2 a
    exact ⟨m + x a, by rw [hx]; push_cast; linarith⟩
  · have h1 := hg a c hac
    rw [le_abs] at h1 ⊢
    rw [hx, hx]
    rcases h1 with h1 | h1
    · left; linarith [hx0 a, hx1 c]
    · right; linarith [hx0 c, hx1 a]

theorem ind_le {m : ℕ} (J : Sub n m) (a : Fin n) : (if a ∈ J.1 then 1 else 0 : ℕ) ≤ m := by
  split_ifs with h
  · rw [← J.2]; exact Finset.card_pos.2 ⟨a, h⟩
  · exact Nat.zero_le _

theorem addSet_inj {l : ℕ} (μ : Fin n → ℝ) : Function.Injective fun I : Sub n l => addSet μ I.1 := by
  intro I J h
  refine Subtype.ext (Finset.ext fun a => ?_)
  have := congrFun h a
  simp only [addSet, add_right_inj] at this
  by_cases h1 : a ∈ I.1 <;> by_cases h2 : a ∈ J.1 <;> simp_all

end num

variable {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

def mkU {μ : Fin (2 * r + k + 1) → ℝ} (R : Rep k r) (h : R.IsDS ε μ) : URep k r :=
  ⟨R, CompanionTheory.LimBd.SchurHpk.isURepOn_of_ds h.2⟩

theorem iso_of (S : Steps) (Lb : Lib t) {μ : Fin (2 * r + k + 1) → ℝ} {U U' : URep k r} {h : ℝ}
    (hU : U.R.IsDS ε μ) (hU' : U'.R.IsDS ε μ) (hg : GapAtLeast ε μ h) (ht : t _ ε < h) :
    IsIso (N := M) IsHom (one U) (one U') :=
  S.uIso k r _ U U' (Lb.uniq k r ε μ U.R U'.R h hU hU' hg ht)

theorem injV (S : Steps) (Lb : Lib t) (b : Bool) {μ : Fin (2 * r + k + 1) → ℝ} {U : URep k r} {h : ℝ}
    (hU : U.R.IsDS ε μ) (hg : GapAtLeast ε μ h) (ht : t _ ε + (((2 * r + k + 1) ^ 2 + 2 : ℕ) : ℝ) < h) :
    ∃ T : {s // IsHCParam (shift b μ s)} → URep k r, (∀ s, (T s).R.IsDS ε (shift b μ s)) ∧
      JInj (N := M) IsHom (vr k r b, U) (fun s => one (T s)) ∧
      ∀ s, ∃ p, IsHom (vr k r b, U) (one (T s)) p ∧ p ≠ 0 := by
  have h1 : (1 : ℝ) ≤ (((2 * r + k + 1) ^ 2 + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  obtain ⟨T, hT, hin, hof⟩ := S.zuckH t Lb.zg k r ε μ U b h hU hg (by linarith)
  have hd := Lb.dec k r ε μ U h _ hU hg ht
  exact ⟨T, hT, S.inj k r _ _ T _ (S.okVr k r b) ⟨_, _, hU⟩ (fun s => ⟨_, _, hT s⟩) hd (by show 1 + _ + 1 ≤ _; omega) hin,
    fun s => S.occ k r _ _ _ (S.okVr k r b) ⟨_, _, hU⟩ ⟨_, _, hT s⟩ hd (by show 1 + _ + 1 ≤ _; omega) (hof s)⟩

theorem decV (S : Steps) (Lb : Lib t) (hk : 1 ≤ k) (b : Bool) {μ : Fin (2 * r + k + 1) → ℝ} {U : URep k r} {h : ℝ}
    (hU : U.R.IsDS ε μ) (hg : GapAtLeast ε μ h) (ht : t _ ε + (((2 * r + k + 1) ^ 2 + 2 : ℕ) : ℝ) + 1 < h)
    (T : Fin (2 * r + k + 1) → URep k r) (hT : ∀ s, (T s).R.IsDS ε (shift b μ s)) :
    ∃ io pr, IsDec (N := M) IsHom (vr k r b, U) (fun s => one (T s)) io pr := by
  have C := S.homCat k r
  have h1 : (1 : ℝ) ≤ (((2 * r + k + 1) ^ 2 + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have hsimp := S.schur S.infChar k r ε _ _ T (shift_inj b μ) hT
  have adj' : ∀ U U' : URep k r, ∃ e : (M (vr k r (!b), U) →ₗ[ℂ] M (one U')) ≃ₗ[ℂ] (M (one U) →ₗ[ℂ] M (vr k r b, U')),
      ∀ p, IsHom (vr k r (!b), U) (one U') p ↔ IsHom (one U) (vr k r b, U') (e p) := by
    cases b
    · exact S.adj k r true
    · exact S.adj k r false
  have occ : ∀ s, ∃ i, IsHom (one (T s)) (vr k r b, U) i ∧ i ≠ 0 := by
    intro s
    obtain ⟨T', hT', -, hp⟩ := injV S Lb (!b) (hT s) (gap_shift hg b s) (by linarith)
    have hs : IsHCParam (shift (!b) (shift b μ s) s) := by rw [shift_shift]; exact hU.1
    obtain ⟨p, hp, hp0⟩ := hp ⟨s, hs⟩
    have hd : (T' ⟨s, hs⟩).R.IsDS ε μ := by simpa only [shift_shift] using hT' ⟨s, hs⟩
    obtain ⟨f, g, hf, -, hgf, -⟩ := iso_of S Lb hd hU hg (by linarith)
    obtain ⟨e, he⟩ := adj' (T s) U
    refine ⟨e (f ∘ₗ p), (he _).1 (C.comp _ _ _ _ _ hp hf), fun h0 => hp0 ?_⟩
    have h2 : f ∘ₗ p = 0 := e.map_eq_zero_iff.1 h0
    calc p = (g ∘ₗ f) ∘ₗ p := by rw [hgf, LinearMap.id_comp]
      _ = 0 := by rw [LinearMap.comp_assoc, h2, LinearMap.comp_zero]
  refine S.decOfInj _ _ _ C _ _ _ hsimp ?_ (fun s => ?_) occ
  · obtain ⟨T', hT', hi, -⟩ := injV S Lb b hU hg (by linarith)
    intro x hx
    refine hi x fun s p hp => ?_
    obtain ⟨f, g, hf, -, hgf, -⟩ := iso_of S Lb (hT' s) (hT s.1) (gap_shift hg b s.1) (by linarith)
    have h2 := hx s.1 _ (C.comp _ _ _ _ _ hp hf)
    have h3 := LinearMap.congr_fun hgf (p x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h2 h3
    rw [← h3, h2, map_zero]
  · obtain ⟨T', hT', hi, -⟩ := injV S Lb b (hT s) (gap_shift hg b s) (by linarith)
    have cB := S.casDS S.infChar k r ε _ (T s) hk (hT s)
    have m1 : AtMostOne (N := M) IsHom (one U) (vr k r (!b), T s) := by
      have := fun hi' ho' => S.multOne k r (!b) (T s) U _ T' _ _ _ (fun F => (cB F).1) (cB (triv k r)).2
        (S.casDS S.infChar k r ε _ U hk hU (triv k r)).2
        (fun u => (S.casDS S.infChar k r ε _ (T' u) hk (hT' u) (triv k r)).2)
        (fun u => cas_ne hU.1.1 b s u.1) hi' (hsimp.2.1 s) ⟨_, _, hU⟩ ho'
      cases b
      · exact this hi (occ s)
      · exact this hi (occ s)
    obtain ⟨e, he⟩ := S.adj k r b U (T s)
    intro f g hf hg'
    obtain ⟨α, β, hab, h0⟩ := m1 _ _ ((he f).1 hf) ((he g).1 hg')
    refine ⟨α, β, hab, e.map_eq_zero_iff.1 ?_⟩
    rw [map_add (f := _), map_smul, map_smul, h0]

theorem decW (S : Steps) (Lb : Lib t) (hk : 1 ≤ k) : ∀ (l : ℕ) {μ : Fin (2 * r + k + 1) → ℝ} {U : URep k r} {h : ℝ},
    U.R.IsDS ε μ → GapAtLeast ε μ h → t _ ε + (((2 * r + k + 1) ^ 2 + 2 : ℕ) : ℝ) + 1 + l < h →
    (∀ a c, a < c → (l : ℝ) + 1 ≤ μ a - μ c) →
    ∀ T : Sub (2 * r + k + 1) l → URep k r, (∀ I, (T I).R.IsDS ε (addSet μ I.1)) →
    ∃ io pr, IsDec (N := M) IsHom (wedge k r l, U) (fun I => one (T I)) io pr := by
  intro l
  induction l with
  | zero =>
    intro μ U h hU hg ht _ T hT
    have C := S.homCat k r
    have h1 : (1 : ℝ) ≤ (((2 * r + k + 1) ^ 2 + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    have hI : ∀ I : Sub (2 * r + k + 1) 0, I = ⟨∅, rfl⟩ := fun I => Subtype.ext (Finset.card_eq_zero.1 I.2)
    have : Unique (Sub (2 * r + k + 1) 0) := ⟨⟨⟨∅, rfl⟩⟩, hI⟩
    have hc : ∀ (g : Mx k r) I J, cmp 0 g I J = 1 := fun g I J => Matrix.det_isEmpty
    refine dec_iso C (T := fun _ => one U) ⟨fun _ => mAct (Matrix.of fun _ _ => 1), fun _ => mAct (Matrix.of fun _ _ => 1),
      fun _ => S.matHom k r _ _ U _ fun g _ => ?_, fun _ => S.matHom k r _ _ U _ fun g _ => ?_, ?_, fun _ => ?_,
      fun I J hIJ => absurd (Subsingleton.elim I J) hIJ⟩ fun I => iso_of S Lb hU ?_ hg (by rw [Nat.cast_zero] at ht; linarith)
    · ext I u; simp [Matrix.mul_apply, hc]
    · ext u I; simp [Matrix.mul_apply, hc]
    · refine LinearMap.ext fun x => funext fun I => ?_
      simp [mAct_apply, Subsingleton.elim default I]
    · refine LinearMap.ext fun x => funext fun u => ?_
      simp [mAct_apply]
    · have e : addSet μ I.1 = μ := by rw [hI I]; funext a; simp [addSet]
      simpa only [e] using hT I
  | succ m ih =>
    intro μ U h hU hg ht hD T hT
    classical
    have C := S.homCat k r
    have h1 : (1 : ℝ) ≤ (((2 * r + k + 1) ^ 2 + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rw [Nat.cast_succ m] at ht hD
    let P := {ν : Fin (2 * r + k + 1) → ℝ // IsHCParam ν ∧ GapAtLeast ε ν (h - ((m + 1 : ℕ) : ℝ))}
    have hex : ∀ ν : P, ∃ V : URep k r, V.R.IsDS ε ν.1 := fun ν => by
      have ht' : t _ ε < h - ((m + 1 : ℕ) : ℝ) := by
        push_cast
        linarith
      have hRep : ∃ R' : Rep k r, R'.IsDS ε ν.1 :=
        Lb.exist k r ε μ ν.1 U.R (h - ((m + 1 : ℕ) : ℝ)) hU ν.2.1 ν.2.2 ht'
      exact hRep.elim fun R' hR' => ⟨mkU R' hR', hR'⟩
    choose V hV using hex
    have nr : ∀ {ν : Fin (2 * r + k + 1) → ℝ}, (∀ a, ∃ x : ℕ, x ≤ m + 1 ∧ ν a = μ a + x) →
        IsHCParam ν ∧ GapAtLeast ε ν (h - ((m + 1 : ℕ) : ℝ)) := fun hx =>
      have := near hU.1 hg hD (m + 1) (by push_cast; linarith) hx
      ⟨this.1, this.2.1⟩
    have hJ : ∀ (J : Sub (2 * r + k + 1) m) a, ∃ x : ℕ, x ≤ m ∧ addSet μ J.1 a = μ a + x := fun J a =>
      ⟨_, ind_le J a, by simp [addSet]⟩
    have hs : ∀ (s a : Fin (2 * r + k + 1)), ∃ x : ℕ, x ≤ 1 ∧ shift false μ s a = μ a + x := fun s a =>
      ⟨if a = s then 1 else 0, by split_ifs <;> simp, by rw [shift_apply]; simp⟩
    let pJ : Sub (2 * r + k + 1) m → P := fun J => ⟨addSet μ J.1, nr fun a =>
      let ⟨x, h1, h2⟩ := hJ J a; ⟨x, by omega, h2⟩⟩
    let ps : Fin (2 * r + k + 1) → P := fun s => ⟨shift false μ s, nr fun a =>
      let ⟨x, h1, h2⟩ := hs s a; ⟨x, by omega, h2⟩⟩
    let par : Sub (2 * r + k + 1) m × Fin (2 * r + k + 1) → P := fun p =>
      ⟨addSet μ p.1.1 + Pi.single p.2 1, nr fun a =>
        ⟨(if a ∈ p.1.1 then 1 else 0) + (if a = p.2 then 1 else 0),
          add_le_add (ind_le p.1 a) (by split_ifs <;> simp), by simp [addSet, Pi.single_apply, add_assoc]⟩⟩
    let e : Sub (2 * r + k + 1) (m + 1) → P := fun I => ⟨addSet μ I.1, nr fun a => ⟨_, ind_le I a, by simp [addSet]⟩⟩
    have cs := fun ν : P => (S.casDS S.infChar k r ε _ (V ν) hk (hV ν) (triv k r)).2
    have hDecTens := S.decTens
    unfold DecTens at hDecTens
    have hTensor := hDecTens k r (wedge k r m) (vr k r false) U (S.okWedge k r m) (S.okVr k r false)
    rcases hTensor with ⟨hd1, hd2⟩
    let X : Obj k r := ((wedge k r m).tens (vr k r false), U)
    have hLeft : ∃ io pr, IsDec (N := M) IsHom X (fun p => one (V (par p))) io pr ∧
        ∀ p, cas1 (wedge k r m) (vr k r false) U ∘ₗ io p = (casG (pJ p.1).1 : ℂ) • io p := by
      refine hd1 (Sub (2 * r + k + 1) m) (Fin (2 * r + k + 1))
        (fun J => V (pJ J)) (fun p => V (par p)) (fun J => (casG (pJ J).1 : ℂ)) ?_ ?_ (fun J => cs (pJ J))
      · exact ih (μ := μ) (U := U) (h := h) hU hg (by linarith)
          (fun a c hac => by linarith [hD a c hac]) _ (fun J => hV (pJ J))
      · intro J
        have hGap := (near hU.1 hg hD m (by linarith) (hJ J)).2.1
        exact decV S Lb hk false (μ := (pJ J).1) (U := V (pJ J)) (h := h - m)
          (hV (pJ J)) hGap (by linarith) _ (fun s => hV (par (J, s)))
    obtain ⟨io₁, pr₁, D₁, e₁⟩ := hLeft
    have hRight : ∃ io pr, IsDec (N := M) IsHom X (fun p => one (V (par p))) io pr ∧
        ∀ p, cas2 (wedge k r m) (vr k r false) U ∘ₗ io p = (casG (ps p.2).1 : ℂ) • io p := by
      refine hd2 (Sub (2 * r + k + 1) m) (Fin (2 * r + k + 1))
        (fun s => V (ps s)) (fun p => V (par p)) (fun s => (casG (ps s).1 : ℂ)) ?_ ?_ (fun s => cs (ps s))
      · exact decV S Lb hk false (μ := μ) (U := U) (h := h) hU hg (by linarith) _ (fun s => hV (ps s))
      · intro s
        refine ih (μ := (ps s).1) (U := V (ps s)) (h := h - 1)
          (hV (ps s)) (gap_shift hg false s) (by linarith) ?_ _ ?_
        · intro a c hac
          have := (near hU.1 hg hD 1 (by push_cast; linarith) (hs s)).2.2 a c hac
          push_cast at this
          show _ ≤ shift false μ s a - shift false μ s c
          linarith
        · intro J
          have e' : addSet (ps s).1 J.1 = (par (J, s)).1 := by
            funext a; simp [ps, par, addSet, shift]; ring
          rw [e']
          exact hV (par (J, s))
    obtain ⟨io₂, pr₂, D₂, e₂⟩ := hRight
    obtain ⟨hint, hjj⟩ := S.wedgeInt (2 * r + k + 1) m
    have hm1 : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    obtain ⟨c1, c2⟩ := S.count (2 * r + k + 1) m μ fun a c hac => by linarith [hD a c hac]
    have okX := S.okTens k r _ _ (S.okWedge k r m) (S.okVr k r false)
    refine dec_iso C (S.decOfTrace _ _ _ C P (fun ν => one (V ν))
      (S.schur S.infChar k r ε P (fun ν => ν.1) V Subtype.val_injective hV) _ par
      X (wedge k r (m + 1), U) io₁ io₂ pr₁ pr₂ D₁ D₂
      (cas _) (cas1 _ _ U) (cas2 _ _ U) _ _ (fun ν => (casG ν.1 : ℂ)) (2 - (casG μ : ℂ)) (2 * ((m : ℂ) + 1)) e₁ e₂
      (fun ν i hi => LinearMap.ext fun x => ?_)
      (mAct (jW _ m)) (mAct (((m : ℂ) + 1)⁻¹ • (jW _ m)ᵀ))
      (S.matHom k r _ _ U _ fun g _ => (hint g).1)
      (S.matHom k r _ _ U _ fun g _ => ?_) ?_ (mul_ne_zero two_ne_zero hm1) ?_ _ e
      (fun I J hIJ => addSet_inj μ (congrArg Subtype.val hIJ)) (fun I => ?_) (fun ν hν => ?_))
      fun I => iso_of S Lb (hV (e I)) (hT I) (e I).2.2 (by push_cast; linarith)
    · rw [LinearMap.comp_apply, ← hom_cas S.homLie (S.okTriv k r) okX hi, cs ν]
      simp
    · rw [Matrix.smul_mul, Matrix.mul_smul]
      exact congrArg _ (hint g).2
    · rw [← mAct_mul, Matrix.smul_mul, hjj, smul_smul, inv_mul_cancel₀ hm1, one_smul, mAct_one]
    · rw [S.casSplit k r _ _ U (S.okWedge k r m) (S.okVr k r false),
        (S.casDS S.infChar k r ε _ U hk hU _).1, S.wedgeQ, mAct_sub, mAct_one, mAct_mul, mAct_smul,
        LinearMap.comp_smul, smul_smul, mul_assoc, mul_inv_cancel₀ hm1, mul_one, sub_smul, smul_sub]
      abel
    · rw [← c1 I]
      refine Finset.sum_congr (Finset.filter_congr fun p _ => Subtype.ext_iff) fun p _ => ?_
      simp [pJ, ps, e, shift]
    · rw [← c2 ν.1 fun I h0 => hν I (Subtype.ext h0)]
      refine Finset.sum_congr (Finset.filter_congr fun p _ => Subtype.ext_iff) fun p _ => ?_
      simp [pJ, ps, shift]

def ZuckSm (t : ∀ n : ℕ, (Fin n → Bool) → ℝ) : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (h : ℝ), 1 ≤ k →
    R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h →
    (∀ (l : ℕ) (RI : Sub (2 * r + k + 1) l → Rep k r), t _ ε + ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 3 + l < h →
      (∀ a c, a < c → (l : ℝ) + 1 ≤ mu a - mu c) → (∀ I, (RI I).IsDS ε (addSet mu I.1)) →
      ∃ io pr, TensRaw (cmp l) R RI io pr) ∧
    ∀ RI : Fin (2 * r + k + 1) → Rep k r, t _ ε + ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 3 < h →
      (∀ s, (RI s).IsDS ε (mu - Pi.single s 1)) → ∃ io pr, TensRaw dualM R RI io pr

theorem zuckSm_of (S : Steps) (Lb : Lib t) : ZuckSm t := by
  intro k r ε mu R h hk hR hg
  refine ⟨fun l RI ht hD hI => ?_, fun RI ht hI => ?_⟩
  · exact S.toRaw k r (wedge k r l) (mkU R hR) _ (fun I => mkU (RI I) (hI I))
      (decW S Lb hk l (U := mkU R hR) hR hg (by push_cast at ht ⊢; linarith) hD _ hI)
  · exact S.toRaw k r (vr k r true) (mkU R hR) _ (fun s => mkU (RI s) (hI s))
      (decV S Lb hk true (U := mkU R hR) hR hg (by push_cast at ht ⊢; linarith) _ hI)

end CompanionTheory.Zuck

end
end

section -- merged from CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ZuckermanLibraryBounds
open Matrix

noncomputable section

namespace CompanionTheory.Zuck

open BranchingSupport Formalism.FourierDecayAlt.ThreeDimData ReciprocityTheory.ChartRestriction.DS

def thr (n : ℕ) (ε : Fin n → Bool) : ℝ := max (thrStar ε) (G2.thrS ε)

theorem thr_le {n : ℕ} (hn : 1 ≤ n) (ε : Fin n → Bool) : thr n ε ≤ 43 * (n : ℝ) ^ 3 := by
  have hp : pOf ε ≤ n := (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  have hq : qOf ε ≤ n := (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  have h0 : S7.q0 ε ≤ n := by unfold S7.q0; omega
  have hp' : (pOf ε : ℝ) ≤ n := by exact_mod_cast hp
  have hq' : (qOf ε : ℝ) ≤ n := by exact_mod_cast hq
  have h0' : (S7.q0 ε : ℝ) ≤ n := by exact_mod_cast h0
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (n : ℝ) ≤ n ^ 3 := le_self_pow₀ h1 (by norm_num)
  have h3 : (n : ℝ) ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ h1 (by norm_num)
  have h4 : Real.sqrt (2 * (S7.q0 ε : ℝ)) ≤ 2 * n := Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
  have h5 : 16 * (n : ℝ) * S7.q0 ε ≤ 16 * n * n := by gcongr
  have h6 : (n : ℝ) * pOf ε * qOf ε ≤ n * n * n := by gcongr
  refine max_le (max_le ?_ ?_) (max_le ?_ ?_) <;> nlinarith

theorem dsigW_SK {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mx k r → (H →L[ℂ] H)) : ∀ (W : List (Mx k r)) (v : H),
    Formalism.MainNotions.S.dsigW (k := k) (r := r) σ W v = PI.UpqRep.dsigW (k := k) (r := r) σ W v
  | [], _ => rfl
  | X :: W, v => by
    change Formalism.MainNotions.S.dsig σ X (Formalism.MainNotions.S.dsigW σ W v) = PI.UpqRep.dsig σ X (PI.UpqRep.dsigW σ W v)
    rw [dsigW_SK σ W v]; rfl

theorem zuckerman_library_bounds : Lib thr := by
  refine { zg := ?_, dec := ?_, uniq := ?_, exist := ?_ }
  · intro n ε μ H _ _ _ σ hμ hσ h hg ht
    have ht' : G2.thrS ε + 1 < h := lt_of_le_of_lt (by unfold thr; linarith [le_max_right (thrStar ε) (G2.thrS ε)]) ht
    exact ⟨G2.zuckerman_tensor_exists n ε μ H σ hμ hσ h hg ht', G2.zuckerman_dual_tensor_exists n ε μ H σ hμ hσ h hg ht'⟩
  · intro k r ε μ U h m hU hg ht
    obtain ⟨C, Ws, hWs, hC⟩ := DecInf.decSm hU.1 hg m
      (lt_of_le_of_lt (by unfold thr; linarith [le_max_left (thrStar ε) (G2.thrS ε)]) ht) (σ := U.R.σ) hU.2
    refine ⟨C, Ws, fun W hW => (hWs W hW).2, fun u hu v hv g hg' => ?_⟩
    have h1 := hC u hu v hv g hg'
    simp only [dsigW_SK] at h1
    exact h1
  · intro k r ε μ R R' h hR hR' hg ht
    have h2 : 2 * ((2 * r + k + 1 : ℕ) : ℝ) < h :=
      lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right (thrStar ε) (G2.thrS ε))) ht
    obtain ⟨P, hP, hd⟩ := hR.2
    obtain ⟨P', hP', hd'⟩ := hR'.2
    have hU' := CompanionTheory.LimBd.SchurHpk.isURepOn_of_ds hR'.2
    obtain ⟨e, he⟩ := (G2.discrete_series_props_large_gap _ ε μ hR.1 h hg h2 R.H (fun g => R.σ (P⁻¹ * g * P)) hd).2.2.2.2 R'.H
      (fun g => R'.σ (P'⁻¹ * g * P')) hd'
    have hPu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
    have hPu' : IsUnit P'.det := (Matrix.isUnit_iff_isUnit_det _).1 hP'.1.1
    have hb : P⁻¹ * P' ∈ GG k r := by
      have h1 : P⁻¹ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, Matrix.mul_nonsing_inv _ hPu, conjTranspose_one]
      show (P⁻¹ * P')ᴴ * PI.UpqRep.Hpk k r * (P⁻¹ * P') = PI.UpqRep.Hpk k r
      calc (P⁻¹ * P')ᴴ * PI.UpqRep.Hpk k r * (P⁻¹ * P')
          = P'ᴴ * (P⁻¹ᴴ * Pᴴ) * PI.UpqRep.Jm ε * (P * P⁻¹) * P' := by
            rw [← hP.1.2]; simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [h1, Matrix.mul_nonsing_inv _ hPu, Matrix.mul_one, Matrix.mul_one, hP'.1.2]
    obtain ⟨-, ha, hmul⟩ := PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r _ hb
    have hab : (P⁻¹ * P')⁻¹ = P'⁻¹ * P := by rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hPu]
    rw [hab] at ha
    have hba : P⁻¹ * P' * (P'⁻¹ * P) = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hPu', Matrix.nonsing_inv_mul _ hPu]
    have hab' : P'⁻¹ * P * (P⁻¹ * P') = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hPu, Matrix.nonsing_inv_mul _ hPu']
    have hm : ∀ a ∈ GG k r, ∀ b ∈ GG k r, ∀ x, R'.σ (a * b) x = R'.σ a (R'.σ b x) := fun a ha b hb x => by
      rw [hU'.1.2 a ha b hb]; rfl
    let f : R'.H ≃ₗᵢ[ℂ] R'.H := LinearIsometryEquiv.ofSurjective
      ⟨(R'.σ (P⁻¹ * P') : R'.H →ₗ[ℂ] R'.H), hU'.2.1 _ hb⟩ fun y => ⟨R'.σ (P'⁻¹ * P) y, by
        show R'.σ (P⁻¹ * P') (R'.σ (P'⁻¹ * P) y) = y
        rw [← hm _ hb _ ha, hba, hU'.1.1]; rfl⟩
    refine ⟨e.trans f, fun g hg x => ?_⟩
    have h3 := he _ (CompanionTheory.LimBd.SchurHpk.forth_mem hP.1 hg) x
    simp only [CompanionTheory.LimBd.SchurHpk.back_forth hP.1] at h3
    show R'.σ (P⁻¹ * P') (e (R.σ g x)) = R'.σ g (R'.σ (P⁻¹ * P') (e x))
    have hag := (PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r _ ha).2.2 _ hg
    have e1 : P'⁻¹ * (P * g * P⁻¹) * P' = P'⁻¹ * P * g * (P⁻¹ * P') := by simp only [Matrix.mul_assoc]
    rw [h3, e1, ← hm _ hb _ ((PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r _ hag).2.2 _ hb), ← hm _ hg _ hb,
      ← Matrix.mul_assoc (P⁻¹ * P') (P'⁻¹ * P * g), ← Matrix.mul_assoc (P⁻¹ * P') (P'⁻¹ * P), hba, Matrix.one_mul]
  · intro k r ε μ μ' R h hR hμ' hg ht
    obtain ⟨P, hP, -⟩ := hR.2
    have h1 : G2.thrS ε < h := lt_of_le_of_lt (le_max_right (thrStar ε) (G2.thrS ε)) ht
    have h2 : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ) := by positivity
    have h3 := Real.sqrt_nonneg (2 * (S7.q0 ε : ℝ))
    obtain ⟨H, _, _, σ, hσ⟩ := G2.discrete_series_exists_large_gap _ ε μ' hμ' h hg (Or.inr (max_lt ((le_max_left _ _).trans_lt h1)
      (by have := (le_max_right _ _).trans_lt h1; linarith)))
    have := hσ.1
    refine ⟨{ H := H, σ := fun g => σ (P * g * P⁻¹) }, hμ', P, hP, ?_⟩
    have e : (fun g => σ (P * (P⁻¹ * g * P) * P⁻¹)) = σ :=
      funext fun g => congrArg σ (CompanionTheory.LimBd.SchurHpk.forth_back hP.1 g)
    show PI.UpqRep.IsDS ε μ' fun g => σ (P * (P⁻¹ * g * P) * P⁻¹)
    rw [e]
    exact hσ

end CompanionTheory.Zuck

end
end

section -- merged from CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ZuckermanIngredients
section -- merged from CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.DecompositionOfInjective
open Matrix Finset
open scoped ContDiff

noncomputable section

namespace CompanionTheory.Zuck

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

theorem decomposition_of_injective : DecOfInj := by
  intro O N _ _ Hom C S _ X T hs hj hm hi
  classical
  choose i hi hi0 using hi
  have hp : ∀ s, ∃ p, Hom X (T s) p ∧ p ∘ₗ i s = LinearMap.id ∧ p ≠ 0 := by
    intro s
    obtain ⟨y, hy⟩ : ∃ y, i s y ≠ 0 := by
      by_contra hn
      exact hi0 s (LinearMap.ext fun y => not_not.1 fun h => hn ⟨y, h⟩)
    obtain ⟨t, p, hp, hpy⟩ : ∃ t p, Hom X (T t) p ∧ p (i s y) ≠ 0 := by
      by_contra hn
      exact hy (hj _ fun t p hp => not_not.1 fun h => hn ⟨t, p, hp, h⟩)
    obtain rfl : s = t := by
      by_contra hst
      exact hpy (LinearMap.congr_fun (hs.2.2 s t hst _ (C.comp _ _ _ _ _ (hi s) hp)) y)
    obtain ⟨c, hc⟩ := hs.2.1 s _ (C.comp _ _ _ _ _ (hi s) hp)
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hpy (by simpa using LinearMap.congr_fun hc y)
    refine ⟨c⁻¹ • p, C.smul _ _ _ _ hp, ?_, fun h0 => hpy ?_⟩
    · rw [LinearMap.smul_comp, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    · rw [(smul_eq_zero.1 h0).resolve_left (inv_ne_zero hc0)]; rfl
  choose p hp hpi hp0 using hp
  have hne : ∀ s t, s ≠ t → p s ∘ₗ i t = 0 := fun s t hst =>
    hs.2.2 t s (Ne.symm hst) _ (C.comp _ _ _ _ _ (hi t) (hp s))
  refine ⟨i, p, hi, hp, LinearMap.ext fun x => ?_, hpi, hne⟩
  rw [LinearMap.id_apply, eq_comm, ← sub_eq_zero]
  refine hj _ fun t q hq => ?_
  have h0 : p t (x - (∑ s, i s ∘ₗ p s) x) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, LinearMap.sum_apply, map_sum, Finset.sum_eq_single t]
    · exact sub_eq_zero.2 (LinearMap.congr_fun (hpi t) (p t x)).symm
    · intro s _ hst
      exact LinearMap.congr_fun (hne t s (Ne.symm hst)) (p s x)
    · simp
  obtain ⟨α, β, hab, h1⟩ := hm t q (p t) hq (hp t)
  have hα : α ≠ 0 := by
    rintro rfl
    rw [zero_smul, zero_add] at h1
    exact hp0 t ((smul_eq_zero.1 h1).resolve_left (hab.resolve_left (not_not.2 rfl)))
  have h2 := LinearMap.congr_fun h1 (x - (∑ s, i s ∘ₗ p s) x)
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, h0, smul_zero, add_zero] at h2
  exact (smul_eq_zero.1 h2).resolve_left hα

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem trivial_rep_admissible : OKTriv := fun _ _ =>
  ⟨rfl, fun _ _ _ _ => (Matrix.one_mul _).symm,
    fun _ _ _ _ => ⟨Set.univ, _, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩,
    ⟨1, fun _ _ _ _ => by simp⟩⟩

theorem vector_rep_admissible : OKVr := by
  intro k r b
  cases b
  · refine ⟨rfl, fun _ _ _ _ => rfl, fun c d _ _ => ?_, ⟨1, fun g _ c d => ?_⟩⟩
    · exact ⟨Set.univ, fun g => g c d, isOpen_univ, trivial,
        (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ c d)).contDiff.contDiffOn, fun _ _ _ => rfl⟩
    · simpa using GlobalTheory.DualFRep.entry_le g c d
  · obtain ⟨-, -, h1, h2, -, -, h3, -⟩ := GlobalTheory.isFRep_dualM k r
    refine ⟨h1, h2, fun c d _ _ => ?_, h3⟩
    let A : Mx k r →ₗ[ℝ] ℂ :=
      { toFun := fun x => (PI.UpqRep.Hpk k r * xᴴ * PI.UpqRep.Hpk k r) d c
        map_add' := fun a b => by rw [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]; rfl
        map_smul' := fun t a => by
          rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, star_trivial]; rfl }
    refine ⟨Set.univ, A, isOpen_univ, trivial, (LinearMap.toContinuousLinearMap A).contDiff.contDiffOn,
      fun g _ hg => ?_⟩
    show g⁻¹ d c = _
    rw [PI.HwUniqW.inv_eq_UH hg]; rfl

end CompanionTheory.Zuck

end
end

section -- merged from CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.AdjFromApply
open Matrix Finset
open scoped Kronecker

noncomputable section

namespace CompanionTheory.Zuck

open BranchingSupport Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem cMT_mul {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} (h : A * Bᵀ = 1) :
    (cM n)ᵀ * (1 : Matrix Unit Unit ℂ) = (A ⊗ₖ B) * (cM n)ᵀ := by
  ext ⟨i, j⟩ u
  rw [Matrix.mul_one]
  have hij := congrFun (congrFun h i) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at hij
  simp only [Matrix.mul_apply, Matrix.transpose_apply, cM, Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  rw [← hij]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

private theorem hpk_apply_lemma (k r : ℕ) (i l : Fin (2 * r + k + 1)) :
    Formalism.QuantumDeterminants.Hpk k r i l = if (l : ℕ) = (if (i : ℕ) < r ∨ r + k < i then 2 * r + k - i else i) then
      (if (i : ℕ) = r + k then -1 else 1) else 0 := by
  have hi := i.2
  have hl := l.2
  simp only [Formalism.QuantumDeterminants.Hpk]
  split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | rfl | omega | norm_num

private theorem hpk_mul_self_lemma_2 (k r : ℕ) : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := by
  ext i j
  have hi := i.2
  have hj := j.2
  rw [Matrix.mul_apply]
  simp only [hpk_apply_lemma]
  rw [Finset.sum_eq_single ⟨if (i : ℕ) < r ∨ r + k < i then 2 * r + k - i else i, by split_ifs <;> omega⟩]
  · simp only [Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> first | rfl | omega | norm_num
  · intro l _ hl
    rw [if_neg (fun h => hl (Fin.ext h)), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem isUnit_det_lemma_3 {k r : ℕ} {g : Formalism.FourierDecayAlt.ThreeDimData.Mx k r} (hg : g ∈ BranchingSupport.GG k r) : IsUnit g.det := by
  have hH : (Formalism.QuantumDeterminants.Hpk k r).det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det (hpk_mul_self_lemma_2 k r)
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  have hg' : g.conjTranspose * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  rw [isUnit_iff_ne_zero]
  intro h0
  apply hH
  rw [← hg', Matrix.det_mul, h0, mul_zero]

theorem cMT_hom (hM : MatHom) (b : Bool) (B : URep k r) :
    IsHom (one B) ((vr k r b).tens (vr k r (!b)), B) (mAct (cM _)ᵀ) := by
  refine hM k r (triv k r) ((vr k r b).tens (vr k r (!b))) B (cM _)ᵀ (fun g hg => ?_)
  have hinv : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g (isUnit_det_lemma_3 hg)
  have hAB : (vr k r b).ρ g * ((vr k r (!b)).ρ g)ᵀ = 1 := by
    cases b <;> simp [vr, BranchingSupport.dualM, hinv, ← Matrix.transpose_mul]
  exact cMT_mul hAB

def uR (ι : Type) [DecidableEq ι] : Matrix (ι × Unit) ι ℂ := fun p d => if p.1 = d then 1 else 0

theorem uR_int (F : FRep k r) (g : Mx k r) : uR F.ι * F.ρ g = (F.tens (triv k r)).ρ g * uR F.ι := by
  ext ⟨i, u⟩ d
  cases u
  simp [Matrix.mul_apply, uR, FRep.tens, triv, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply]

theorem uMT_int (F : FRep k r) (g : Mx k r) : (uM F.ι)ᵀ * ((triv k r).tens F).ρ g = F.ρ g * (uM F.ι)ᵀ := by
  ext d ⟨u, e⟩
  cases u
  simp [Matrix.mul_apply, uM, FRep.tens, triv, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply]

section

variable {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

def adjTo (p : (Fin n → V) →ₗ[ℂ] (Unit → V')) : (Unit → V) →ₗ[ℂ] (Fin n → V') :=
  mAct (uM (Fin n))ᵀ ∘ₗ (on1 p ∘ₗ mAct (cM n)ᵀ)

def adjFrom (i : (Unit → V) →ₗ[ℂ] (Fin n → V')) : (Fin n → V) →ₗ[ℂ] (Unit → V') :=
  mAct (cM n) ∘ₗ (on2 i ∘ₗ mAct (uR (Fin n)))

theorem adjTo_apply (p : (Fin n → V) →ₗ[ℂ] (Unit → V')) (x : Unit → V) (d : Fin n) :
    adjTo p x d = p (Pi.single d (x ())) () := by
  simp [adjTo, mAct_apply, uM, cM, on1, Fintype.sum_prod_type]
  have e : (LinearMap.funLeft ℂ V fun c => (c, d)) ((mAct (cM n)ᵀ) x) = Pi.single d (x ()) := by
    funext c
    simp [LinearMap.funLeft_apply, mAct_apply, cM, Matrix.transpose_apply, Pi.single_apply]
  rw [e]

theorem adjFrom_apply (i : (Unit → V) →ₗ[ℂ] (Fin n → V')) (y : Fin n → V) (u : Unit) :
    adjFrom i y u = ∑ c, i (fun _ => y c) c := by
  simp [adjFrom, mAct_apply, uR, cM, on2, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _
  have e : (LinearMap.funLeft ℂ V fun d => (c, d)) ((mAct (uR (Fin n))) y) = fun _ => y c := by
    funext u
    simp [LinearMap.funLeft_apply, mAct_apply, uR]
  rw [e]

def adjEquiv : ((Fin n → V) →ₗ[ℂ] (Unit → V')) ≃ₗ[ℂ] ((Unit → V) →ₗ[ℂ] (Fin n → V')) where
  toFun := adjTo
  invFun := adjFrom
  map_add' p q := LinearMap.ext fun x => funext fun d => by simp [adjTo_apply]
  map_smul' a p := LinearMap.ext fun x => funext fun d => by simp [adjTo_apply]
  left_inv p := LinearMap.ext fun y => funext fun u => by
    rw [adjFrom_apply]
    simp only [adjTo_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.sum_apply, ← map_sum, Finset.univ_sum_single]
  right_inv i := LinearMap.ext fun x => funext fun d => by
    rw [adjTo_apply, adjFrom_apply, Finset.sum_eq_single d]
    · simp
    · intro c _ hc
      rw [Pi.single_eq_of_ne hc]
      exact congrFun (map_zero i) c
    · simp

end

theorem adj_of (hC : HomCat) (hM : MatHom) (hT : TensHom) : Adj := by
  intro k r b U U'
  refine ⟨adjEquiv, fun p => ⟨fun hp => ?_, fun hq => ?_⟩⟩
  · have h1 := cMT_hom hM b U
    have h2 := (hT k r (vr k r b) (triv k r) (vr k r (!b)) U U' p hp).1
    have h3 : IsHom ((triv k r).tens (vr k r (!b)), U') (vr k r (!b), U') (mAct (uM (vr k r (!b)).ι)ᵀ) :=
      hM k r _ _ U' _ (fun g _ => uMT_int (vr k r (!b)) g)
    exact (hC k r).comp _ _ _ _ _ ((hC k r).comp _ _ _ _ _ h1 h2) h3
  · have h1 : IsHom (vr k r b, U) ((vr k r b).tens (triv k r), U) (mAct (uR (vr k r b).ι)) :=
      hM k r _ _ U _ (fun g _ => uR_int (vr k r b) g)
    have h2 := (hT k r (triv k r) (vr k r (!b)) (vr k r b) U U' (adjEquiv p) hq).2
    have h3 := cM_hom hM b U'
    have h4 := (hC k r).comp _ _ _ _ _ ((hC k r).comp _ _ _ _ _ h1 h2) h3
    rw [← adjEquiv.left_inv p]
    exact h4

end CompanionTheory.Zuck

end
end

namespace CompanionTheory.Zuck

theorem zuckerman_ingredients : Steps := by
  exact {
    infChar := CompanionTheory.D.DSIC.discrete_series_infinitesimal_character
    decOfInj := decomposition_of_injective
    decOfTrace := GlobalTheory.T.DecompositionOfTrace
    homCat := GlobalTheory.T.HomCategory
    okTriv := trivial_rep_admissible
    okVr := vector_rep_admissible
    okWedge := GlobalTheory.T.ExteriorPowerIntegral
    okTens := GlobalTheory.T.TensorPowerIntegral
    matHom := GlobalTheory.T.MatrixHom
    uIso := GlobalTheory.T.UnitaryIso
    homLie := CompanionTheory.D.gk.FinalFormK.lie_algebra_homomorphism
    casSplit := GlobalTheory.T.CasimirSplitting
    casDS := GlobalTheory.T.CasimirDiagonalSum
    wedgeInt := GlobalTheory.T.ExteriorIntegrality
    wedgeQ := GlobalTheory.T.exterior_differential_sign_rule_quadratic GlobalTheory.T.StandardDifferential GlobalTheory.T.exterior_differential_matrix_unit_formula
    schur := CompanionTheory.D.gk.FinalFormK.schur'
    adj := adj_of GlobalTheory.T.HomCategory GlobalTheory.T.MatrixHom GlobalTheory.T.tensHom'
    multOne := multOne_of GlobalTheory.T.HomCategory GlobalTheory.T.MatrixHom GlobalTheory.T.tensHom' CompanionTheory.D.gk.FinalFormK.lie_algebra_homomorphism GlobalTheory.T.CasimirSplitting GlobalTheory.T.StandardDifferential
      CompanionTheory.D.gk.FinalFormK.kerZero' trivial_rep_admissible vector_rep_admissible GlobalTheory.T.TensorPowerIntegral
    inj := CompanionTheory.D.gk.FinalFormK.injectivity_induction
    occ := CompanionTheory.D.gk.FinalFormK.occurrence_induction
    zuckH := GlobalTheory.T.zuckerman_hypothesis
    decTens := GlobalTheory.T.decomposition_of_tensor_from_hom_laws GlobalTheory.T.HomCategory GlobalTheory.T.MatrixHom GlobalTheory.T.tensHom' CompanionTheory.D.gk.FinalFormK.lie_algebra_homomorphism trivial_rep_admissible
    toRaw := GlobalTheory.T.ToRawComplex
    count := GlobalTheory.T.CountingBound
  }

end CompanionTheory.Zuck
end

section -- merged from CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.Bridge
open Matrix Finset

noncomputable section

namespace CompanionTheory.Zuck

open BranchingSupport Formalism.FourierDecayAlt.ThreeDimData

theorem n1_add_le' {n : ℕ} (x y : Fin n → ℤ) : n1 (x + y) ≤ n1 x + n1 y := by
  unfold n1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Int.natAbs_add_le _ _

theorem n1_single_eq_natAbs {n : ℕ} (s : Fin n) (m : ℤ) : n1 (Pi.single s m) = m.natAbs := by
  unfold n1
  rw [Finset.sum_eq_single s]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem n1_eZ_eq_card_finset {n : ℕ} (I : Finset (Fin n)) : n1 (eZ I) = I.card := by
  unfold n1 eZ
  have : ∀ i : Fin n, (if i ∈ I then (1 : ℤ) else 0).natAbs = if i ∈ I then 1 else 0 := by
    intro i; split_ifs <;> rfl
  simp [this]

theorem zuckG_of_sm {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} (ht : ∀ n, 1 ≤ n → ∀ ε, t n ε ≤ 43 * (n : ℝ) ^ 3)
    (hZ : ZuckSm t) : BranchingSupport.ZuckG := by
  intro k r ε lam q0 R hF ν
  have hn1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
  have h2 : ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := pow_le_pow_right₀ hn1 (by norm_num)
  have h3 : ((2 * r + k + 1 : ℕ) : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := le_self_pow₀ hn1 (by norm_num)
  have h4 := ht (2 * r + k + 1) (by omega) ε
  constructor
  · intro l hl
    by_cases hln : l ≤ 2 * r + k + 1
    · have hR := hF ν (by omega)
      obtain ⟨h, hg, hok⟩ := hR.gap
      have hl' : (l : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast hln
      refine (hZ k r ε _ (R ν) h hok.1 ⟨hR.hc, hR.ds⟩ hg).1 l _ (by linarith [hok.2.1]) (fun a c hac => ?_) fun I => ?_
      · have h5 := (hF (ν + Pi.single c (l : ℤ)) (by
          have := n1_add_le' ν (Pi.single c (l : ℤ))
          rw [n1_single_eq_natAbs, Int.natAbs_natCast] at this
          omega)).hc.1 hac
        simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hac.ne, add_zero, Int.cast_add,
          Int.cast_natCast] at h5
        obtain ⟨x, hx⟩ := hR.hc.2 a
        obtain ⟨y, hy⟩ := hR.hc.2 c
        have h6 : (l : ℝ) < (x : ℝ) - y := by linarith
        have h7 : (l : ℤ) + 1 ≤ x - y := by exact_mod_cast h6
        have h8 : (l : ℝ) + 1 ≤ (x : ℝ) - y := by exact_mod_cast h7
        linarith
      · have h5 := hF (ν + eZ I.1) (by
          have := n1_add_le' ν (eZ I.1)
          rw [n1_eZ_eq_card_finset, I.2] at this
          omega)
        have e : (fun a => lam a + (((ν + eZ I.1) a : ℤ) : ℝ)) = addSet (fun a => lam a + (ν a : ℝ)) I.1 := by
          funext a
          simp only [addSet, eZ, Pi.add_apply]
          split_ifs <;> push_cast <;> ring
        rw [e] at h5
        exact ⟨h5.hc, h5.ds⟩
    · have : IsEmpty (Sub (2 * r + k + 1) l) := ⟨fun I => hln (by
        rw [← I.2]; exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin _))⟩
      exact ⟨fun I => isEmptyElim I, fun I => isEmptyElim I, fun I => isEmptyElim I, fun I => isEmptyElim I,
        fun I => isEmptyElim I, fun I => isEmptyElim I, fun _ _ I => isEmptyElim I, fun I => isEmptyElim I,
        fun I => isEmptyElim I⟩
  · intro hl
    have hR := hF ν (by omega)
    obtain ⟨h, hg, hok⟩ := hR.gap
    refine (hZ k r ε _ (R ν) h hok.1 ⟨hR.hc, hR.ds⟩ hg).2 _ (by linarith [hok.2.1]) fun s => ?_
    have h5 := hF (ν - Pi.single s 1) (by
      have := n1_add_le' ν (Pi.single s (-1))
      rw [n1_single_eq_natAbs, Pi.single_neg, ← sub_eq_add_neg] at this
      exact this.trans hl)
    have e : (fun a => lam a + (((ν - Pi.single s 1 : Fin (2 * r + k + 1) → ℤ) a : ℤ) : ℝ)) =
        (fun a => lam a + (ν a : ℝ)) - Pi.single s 1 := by
      funext a
      simp only [Pi.sub_apply, Pi.single_apply]
      split_ifs <;> push_cast <;> ring
    rw [e] at h5
    exact ⟨h5.hc, h5.ds⟩

end CompanionTheory.Zuck

end
end

namespace CompanionTheory.Zuck

theorem zuckerman_gap_small : ZuckSm thr := zuckSm_of zuckerman_ingredients zuckerman_library_bounds

theorem zuckerman_gap : BranchingSupport.ZuckG := zuckG_of_sm (fun _ hn ε => thr_le hn ε) zuckerman_gap_small

end CompanionTheory.Zuck
