module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinBaseChangeP
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.GammaIndependence.PeriodMapZEqCast
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdmissibleMinors.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.DualOf
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.Geo
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.Bock
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.SecMapZero
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.TranscendentalPeriodUnits.IsUOfIsUnit
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.TranscendentalPeriodUnits.CrystallineSemistableComparison
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTailAlt

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.TranscendentalPeriodUnits.CharZeroBdR
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Formalism.Per6 GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}


variable (l) in
abbrev Fr : Subfield (BdR l) :=
  ACris.fracBCris (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one

end CrystallineSemistableComparison
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.GammaIndependence.PhiMain
set_option backward.isDefEq.respectTransparency false

namespace CrystallineSemistableComparison

theorem phi : FrobeniusComparison := phi_of inj

end CrystallineSemistableComparison
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.EqZeroOfCast
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace CrystallineSemistableComparison

open GlobalTheory.EtC

namespace RootOfUnityLemmas

theorem pick_neg {α : Type*} [Zero α] {P : α → Prop} (h : ¬ ∃ a, P a) : pick P = 0 := by
  unfold pick
  rw [dite_eq_right h]

theorem cast_zero' {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') :
    (0 : Ht q E n i).cast hn hi = 0 := by
  subst hn; subst hi; rfl

theorem eq_zero_of_cast {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E n i)
    (h : x.cast hn hi = 0) : x = 0 := by
  subst hn; subst hi; exact h

theorem res_id {R : Type} [CommRing R] {F : Shv R} {X : Scheme.{0}} (a : Sec F X) : Sec.res (𝟙 X) a = a := by
  simp [Sec.res]

theorem resGen_closed (hF : FormalIn) (q : ℕ) (s : ℤ) {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) :
    Sec.map ((res _ (tw q s)).d 0 1) (resGen s ζ) = 0 := by
  obtain ⟨-, e, -, he⟩ := hF.a9 (ZMod q) (tw q s)
  obtain ⟨α, -, hα⟩ := he X (twGen s ζ)
  have h := ((hF.et.sch (ZMod q) X (res _ (tw q s)) (-1) 0 1 (by norm_num) (by norm_num)).2 α).1
  rw [hα] at h
  exact h

theorem ev_vanish {R : Type} [CommRing R] {X : Scheme.{0}} {I : GlobalTheory.EtC.Cx R} {n : ℤ}
    (α : Cochain ((chains R).obj (sch.obj X)) I n)
    (h : ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (x : U ⟶ X), ev α (p + 1) s h U x = 0) :
    ∀ (p : ℕ), p ≠ 0 → ∀ (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx (sch.obj X) p U), ev α p s h U x = 0 := by
  intro p hp
  obtain ⟨p', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
  exact fun s h' U x => h p' s h' U x

theorem isAW_conc {R : Type} [CommRing R] {I J K : GlobalTheory.EtC.Cx R} (μ : Pair I J K) {X : Scheme.{0}}
    (α : Cochain ((chains R).obj (sch.obj X)) I 0) (β : Cochain ((chains R).obj (sch.obj X)) J 0)
    (γ : Cochain ((chains R).obj (sch.obj X)) K (0 + 0)) (a : Sec (I.X 0) X) (b : Sec (J.X 0) X) (c : Sec (K.X 0) X)
    (hc : μ.mul X 0 0 0 (add_zero 0) a b = c)
    (hα0 : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev α 0 0 (by simp) U x = Sec.res x a)
    (hα1 : ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + 0 = s) (U : Scheme.{0}) (x : U ⟶ X), ev α (p + 1) s h U x = 0)
    (hβ0 : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev β 0 0 (by simp) U x = Sec.res x b)
    (hβ1 : ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + 0 = s) (U : Scheme.{0}) (x : U ⟶ X), ev β (p + 1) s h U x = 0)
    (hγ0 : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ 0 (0 + 0) (by simp) U x = Sec.res x c)
    (hγ1 : ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + (0 + 0) = s) (U : Scheme.{0}) (x : U ⟶ X), ev γ (p + 1) s h U x = 0) :
    μ.IsAW rfl α β γ := by
  intro N w h U x
  cases N with
  | zero =>
    subst h
    rw [Fin.sum_univ_one]
    have e1 : ev γ 0 (-((0 : ℕ) : ℤ) + (0 + 0)) rfl U x = μ.mul U 0 0 0 (add_zero 0) (ev α 0 0 (by simp) U x)
        (ev β 0 0 (by simp) U x) := by
      rw [hα0, hβ0, ← μ.nat, hc]
      exact hγ0 U x
    rw [e1]
    simp only [Fin.val_zero, Nat.cast_zero, mul_zero, Int.negOnePow_zero, one_smul]
    rfl
  | succ N =>
    rw [hγ1 N w h U x]
    refine (Finset.sum_eq_zero fun p _ => ?_).symm
    by_cases hp : (p : ℕ) = 0
    · rw [ev_vanish β hβ1 (N + 1 - p) (by omega)]
      simp
    · rw [ev_vanish α hα1 p hp]
      simp

theorem conc_eq_one (hF : FormalIn) (q : ℕ) [NeZero q] (X : Scheme.{0}) (ζ : Prim q Γ(X, ⊤)) (t : ℤ) (ht : (0 : ℤ) = t)
    (c : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q t)) (0 + 0))
    (hc : ev c.1 0 (0 + 0) (by simp) X (𝟙 X) = resGen t ζ) (hn : (0 : ℤ) = 0 + 0) :
    CohomologyClass.mk c = (one q (sch.obj X)).cast hn ht := by
  subst ht
  by_cases hw : ∃ c' : Ht q (sch.obj X) 0 0, ∃ α : Cocycle _ _ 0, CohomologyClass.mk α = c' ∧
      ∀ (U : Scheme.{0}) (x : Sx (sch.obj X) 0 U) (ζ' : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ'
  · obtain ⟨α, hα, hα'⟩ : ∃ α : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 0)) 0,
        CohomologyClass.mk α = one q (sch.obj X) ∧
        ∀ (U : Scheme.{0}) (x : Sx (sch.obj X) 0 U) (ζ' : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ' :=
      pick_spec hw
    rw [← hα]
    change CohomologyClass.mk c = CohomologyClass.mk α
    exact WeightedPowerFormIntegrability.mk_eq_of_ev hF.et.sch c α (hc.trans (hα' X (𝟙 X) ζ).symm)
  · have h1 : one q (sch.obj X) = 0 := pick_neg hw
    have hinv : Inv q (sch.obj X) := fun U ⟨x⟩ => (Prim.map (show U ⟶ X from x).appTop.hom ζ).2.1
    have h2 := (hF.a6ring q (sch.obj X)).1 hinv (CohomologyClass.mk c)
    rw [h1, map_zero, AddMonoidHom.zero_apply] at h2
    rw [h1, cast_zero', eq_zero_of_cast _ _ _ h2.symm]

end RootOfUnityLemmas


open RootOfUnityLemmas in
theorem root : RootsOfUnityFormal := by
  intro hF q _ X ⟨ζ⟩ i
  have hS := hF.et.sch
  obtain ⟨v, hv0, hv1⟩ := (hS (ZMod q) X (res _ (tw q (-i))) (-1) 0 1 (by norm_num) (by norm_num)).1
    (resGen (-i) ζ) (resGen_closed hF q (-i) ζ)
  obtain ⟨u, hu0, hu1⟩ := (hS (ZMod q) X (res _ (tw q i)) (-1) 0 1 (by norm_num) (by norm_num)).1
    (resGen i ζ) (resGen_closed hF q i ζ)
  obtain ⟨c, hc0, hc1⟩ := (hS (ZMod q) X (res _ (tw q (-i + i))) (-1) (0 + 0) 1 (by norm_num) (by norm_num)).1
    (resGen (-i + i) ζ) (resGen_closed hF q (-i + i) ζ)
  refine ⟨CohomologyClass.mk u, CohomologyClass.mk v, ?_⟩
  have hcup : cup q (CohomologyClass.mk v) (CohomologyClass.mk u) = CohomologyClass.mk c :=
    Pair.cup_spec (twPair q (-i) i) (sch.obj X) rfl v u c
      (isAW_conc (twPair q (-i) i) v.1 u.1 c.1 (resGen (-i) ζ) (resGen i ζ) (resGen (-i + i) ζ)
        (hF.et.tw q (-i) i X ζ) hv0 hv1 hu0 hu1 hc0 hc1)
  rw [hcup]
  exact conc_eq_one hF q X ζ (-i + i) (by ring) c ((hc0 X (𝟙 X)).trans (res_id _)) (by ring)

end CrystallineSemistableComparison
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdmissibleMinors.admitted
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdmissibleMinors.AdmAbs
noncomputable section

open Matrix

namespace CrystallineSemistableComparison.AdmAbs

variable {F : Type*} [Field F] {Γ : Type*} (σ : Γ → F →+* F) (S : Subring F) {X : Type*}

def Indep {r : ℕ} (w : Fin r → X → F) : Prop :=
  ∀ μ : Fin r → F, (∀ i, μ i ∈ S) → (∀ i g, σ g (μ i) = μ i) → (∀ x, ∑ i, μ i * w i x = 0) → μ = 0

theorem reduce (hfrac : ∀ x ∈ S, ∀ y ∈ S, ∀ w : F, w * y = x → y ≠ 0 → (∀ g, σ g w = w) → w ∈ S) :
    ∀ (r : ℕ) (w : Fin r → X → F), (∀ i x g, σ g (w i x) = w i x) →
    ∃ (r' : ℕ) (w' : Fin r' → X → F), (∀ i x g, σ g (w' i x) = w' i x) ∧ Indep σ S w' ∧
      ∀ β : Fin r → F, (∀ i, β i ∈ S) → ∃ β' : Fin r' → F, (∀ i, β' i ∈ S) ∧
        ∀ x, ∑ i, β i * w i x = ∑ i, β' i * w' i x := by
  intro r
  induction r with
  | zero =>
    intro w hw
    exact ⟨0, w, hw, fun μ _ _ _ => funext fun i => i.elim0, fun β hβ => ⟨β, hβ, fun _ => rfl⟩⟩
  | succ r ih =>
    intro w hw
    by_cases hI : Indep σ S w
    · exact ⟨r + 1, w, hw, hI, fun β hβ => ⟨β, hβ, fun _ => rfl⟩⟩
    · simp only [Indep, not_forall] at hI
      obtain ⟨μ, hμS, hμσ, hμw, hμ0⟩ := hI
      obtain ⟨i0, hi0⟩ : ∃ i0, μ i0 ≠ 0 := by
        by_contra h
        push Not at h
        exact hμ0 (funext h)
      obtain ⟨lam, hlamS, hw0⟩ : ∃ lam : Fin r → F, (∀ i, lam i ∈ S) ∧
          ∀ x, w i0 x = ∑ i, lam i * w (i0.succAbove i) x := by
        refine ⟨fun i => -μ (i0.succAbove i) / μ i0, fun i => ?_, fun x => ?_⟩
        · refine hfrac (-μ (i0.succAbove i)) (S.neg_mem (hμS _)) (μ i0) (hμS i0) _ ?_ hi0 ?_
          · exact div_mul_cancel₀ _ hi0
          · intro g
            rw [map_div₀, map_neg, hμσ, hμσ]
        · have h := hμw x
          rw [Fin.sum_univ_succAbove _ i0] at h
          have h' : μ i0 * w i0 x = -∑ i, μ (i0.succAbove i) * w (i0.succAbove i) x :=
            eq_neg_of_add_eq_zero_left h
          apply mul_left_cancel₀ hi0
          rw [h', Finset.mul_sum, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          field_simp
      obtain ⟨r', w', hw', hI', hmap⟩ := ih (fun i => w (i0.succAbove i)) (fun i x g => hw _ x g)
      refine ⟨r', w', hw', hI', fun β hβ => ?_⟩
      obtain ⟨β', hβ', heq⟩ := hmap (fun i => β (i0.succAbove i) + β i0 * lam i)
        (fun i => S.add_mem (hβ _) (S.mul_mem (hβ _) (hlamS i)))
      have heq' : ∀ x, ∑ i, (β (i0.succAbove i) + β i0 * lam i) * w (i0.succAbove i) x =
          ∑ i, β' i * w' i x := heq
      refine ⟨β', hβ', fun x => ?_⟩
      rw [← heq' x, Fin.sum_univ_succAbove _ i0, hw0 x, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring

theorem indep_S (hstab : ∀ g, ∀ x ∈ S, σ g x ∈ S)
    (hfrac : ∀ x ∈ S, ∀ y ∈ S, ∀ w : F, w * y = x → y ≠ 0 → (∀ g, σ g w = w) → w ∈ S)
    {r : ℕ} (w : Fin r → X → F) (hw : ∀ i x g, σ g (w i x) = w i x) (hI : Indep σ S w) :
    ∀ s : Fin r → F, (∀ i, s i ∈ S) → (∀ x, ∑ i, s i * w i x = 0) → s = 0 := by
  suffices h : ∀ T : Finset (Fin r), ∀ s : Fin r → F, (∀ i, s i ∈ S) → (∀ i ∉ T, s i = 0) →
      (∀ x, ∑ i, s i * w i x = 0) → s = 0 from
    fun s hs hsw => h Finset.univ s hs (fun i hi => absurd (Finset.mem_univ i) hi) hsw
  intro T
  induction T using Finset.strongInduction with
  | H T ih =>
  intro s hs hT hsw
  by_contra hne
  obtain ⟨i0, hi0⟩ : ∃ i0, s i0 ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have hi0T : i0 ∈ T := by
    by_contra h
    exact hi0 (hT i0 h)
  have key : ∀ g i, σ g (s i0) * s i = s i0 * σ g (s i) := by
    intro g
    have hsupp : ∀ i ∉ T.erase i0, σ g (s i0) * s i - s i0 * σ g (s i) = 0 := by
      intro i hi
      rcases eq_or_ne i i0 with rfl | h
      · ring
      · have h0 : s i = 0 := hT i fun hiT => hi (Finset.mem_erase.2 ⟨h, hiT⟩)
        rw [h0, map_zero]
        ring
    have hrel : ∀ x, ∑ i, (σ g (s i0) * s i - s i0 * σ g (s i)) * w i x = 0 := by
      intro x
      have h1 := hsw x
      have h2 : ∑ i, σ g (s i) * w i x = 0 := by
        have h3 := congrArg (σ g) h1
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, map_zero] at h3
        simpa only [map_mul, hw] using h3
      calc ∑ i, (σ g (s i0) * s i - s i0 * σ g (s i)) * w i x
          = σ g (s i0) * ∑ i, s i * w i x - s i0 * ∑ i, σ g (s i) * w i x := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun i _ => by ring
        _ = 0 := by rw [h1, h2]; ring
    have := ih (T.erase i0) (Finset.erase_ssubset hi0T) (fun i => σ g (s i0) * s i - s i0 * σ g (s i))
      (fun i => S.sub_mem (S.mul_mem (hstab g _ (hs i0)) (hs i)) (S.mul_mem (hs i0) (hstab g _ (hs i))))
      hsupp hrel
    intro i
    exact sub_eq_zero.1 (congr_fun this i)
  have hlam := hI (fun i => s i / s i0) (fun i => ?_) (fun i g => ?_) (fun x => ?_)
  · have h1 := congr_fun hlam i0
    simp only [div_self hi0, Pi.zero_apply] at h1
    exact one_ne_zero h1
  · refine hfrac (s i) (hs i) (s i0) (hs i0) _ (div_mul_cancel₀ _ hi0) hi0 fun g => ?_
    have hne' : σ g (s i0) ≠ 0 := (map_ne_zero (σ g)).2 hi0
    rw [map_div₀, div_eq_div_iff hne' hi0]
    linear_combination (-1 : F) * key g i
  · have hne' : σ g (s i0) ≠ 0 := (map_ne_zero (σ g)).2 hi0
    rw [map_div₀, div_eq_div_iff hne' hi0]
    linear_combination (-1 : F) * key g i
  · have : ∑ i, s i / s i0 * w i x = (∑ i, s i * w i x) / s i0 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hsw x, zero_div]

theorem exists_minor {r a : ℕ} (M : Matrix (Fin r) (Fin a) F) (hM : ∀ z : Fin a → F, M *ᵥ z = 0 → z = 0) :
    ∃ e : Fin a → Fin r, (M.submatrix e id).det ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.Yra1.main M hM

omit [Field F] in
theorem det_mem' [Field F] (S : Subring F) {a : ℕ} (A : Matrix (Fin a) (Fin a) F) (hA : ∀ i j, A i j ∈ S) :
    A.det ∈ S ∧ ∀ i j, A.adjugate i j ∈ S := by
  have h : A = S.subtype.mapMatrix (Matrix.of fun i j => (⟨A i j, hA i j⟩ : S)) := by
    ext i j
    rfl
  refine ⟨?_, fun i j => ?_⟩
  · rw [h, ← RingHom.map_det]
    exact SetLike.coe_mem _
  · rw [h, ← RingHom.map_adjugate]
    exact SetLike.coe_mem _

theorem admissible_of_absolute (hstab : ∀ g, ∀ x ∈ S, σ g x ∈ S)
    (hfrac : ∀ x ∈ S, ∀ y ∈ S, ∀ w : F, w * y = x → y ≠ 0 → (∀ g, σ g w = w) → w ∈ S)
    {a r : ℕ} (ρ : Γ → Matrix (Fin a) (Fin a) F) (hρS : ∀ g i j, ρ g i j ∈ S)
    (heig : ∀ x ∈ S, x ≠ 0 → (∀ g, σ g x = (ρ g).det * x) → ∃ y ∈ S, x * y = 1)
    (c : Fin a → X → F) (hcσ : ∀ g j x, σ g (c j x) = ∑ k, ρ g k j * c k x)
    (hcinj : ∀ z : Fin a → F, (∀ x, ∑ j, z j * c j x = 0) → z = 0)
    (w : Fin r → X → F) (hw : ∀ i x g, σ g (w i x) = w i x)
    (hspan : ∀ j, ∃ β : Fin r → F, (∀ i, β i ∈ S) ∧ ∀ x, c j x = ∑ i, β i * w i x) :
    ∃ P Q : Matrix (Fin a) (Fin a) F, (∀ i j, P i j ∈ S ∧ Q i j ∈ S) ∧ P * Q = 1 ∧
      ∀ g, ρ g * P.map (σ g) = P := by
  obtain ⟨r', w', hw', hI', hmap⟩ := reduce σ S hfrac r w hw
  have hsp' : ∀ j, ∃ β : Fin r' → F, (∀ i, β i ∈ S) ∧ ∀ x, c j x = ∑ i, β i * w' i x := by
    intro j
    obtain ⟨β, hβ, hc⟩ := hspan j
    obtain ⟨β', hβ', he⟩ := hmap β hβ
    exact ⟨β', hβ', fun x => (hc x).trans (he x)⟩
  choose β hβS hβc using hsp'
  have hβσ : ∀ g i j, σ g (β j i) = ∑ k, β k i * ρ g k j := by
    intro g i j
    have h := indep_S σ S hstab hfrac w' hw' hI' (fun i => σ g (β j i) - ∑ k, β k i * ρ g k j)
      (fun i => S.sub_mem (hstab g _ (hβS j i)) (sum_mem fun k _ => S.mul_mem (hβS k i) (hρS g k j)))
      (fun x => by
        have e1 : σ g (c j x) = ∑ i, σ g (β j i) * w' i x := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [hβc j x, map_sum]
          simp only [map_mul, hw']
        have e2 : ∑ k, ρ g k j * c k x = ∑ i, (∑ k, β k i * ρ g k j) * w' i x := by
          simp only [hβc _ x, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
        simp only [sub_mul, Finset.sum_sub_distrib]
        rw [← e1, ← e2, hcσ, sub_self])
    exact sub_eq_zero.1 (congr_fun h i)
  obtain ⟨e, he⟩ := exists_minor (Matrix.of fun i j => β j i) fun z hz => hcinj z fun x => by
    have h0 : ∀ i, ∑ j, β j i * z j = 0 := fun i => by
      have := congr_fun hz i
      simpa [Matrix.mulVec, dotProduct] using this
    calc ∑ j, z j * c j x = ∑ i, (∑ j, β j i * z j) * w' i x := by
          simp only [hβc _ x, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by simp [h0]
  let Q : Matrix (Fin a) (Fin a) F := Matrix.of fun k j => β j (e k)
  have hQS : ∀ i j, Q i j ∈ S := fun i j => hβS _ _
  have hQ : Q.det ≠ 0 := he
  have hQσ : ∀ g, Q.map (σ g) = Q * ρ g := by
    intro g
    ext k j
    simp only [Matrix.map_apply, Matrix.mul_apply, Q, Matrix.of_apply]
    exact hβσ g (e k) j
  obtain ⟨hdS, hadjS⟩ := det_mem' S Q hQS
  obtain ⟨y, hyS, hy⟩ := heig Q.det hdS hQ fun g => by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hQσ g, Matrix.det_mul, mul_comm]
  let P : Matrix (Fin a) (Fin a) F := y • Q.adjugate
  have hPQ : P * Q = 1 := by
    simp only [P, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, mul_comm y, hy, one_smul]
  have hQP : Q * P = 1 := by
    simp only [P, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, mul_comm y, hy, one_smul]
  refine ⟨P, Q, fun i j => ⟨?_, hQS i j⟩, hPQ, fun g => ?_⟩
  · simp only [P, Matrix.smul_apply, smul_eq_mul]
    exact S.mul_mem hyS (hadjS i j)
  · have h1 : Q.map (σ g) * P.map (σ g) = 1 := by
      rw [← Matrix.map_mul, hQP]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    calc ρ g * P.map (σ g) = (P * Q) * (ρ g * P.map (σ g)) := by rw [hPQ, Matrix.one_mul]
      _ = P * ((Q * ρ g) * P.map (σ g)) := by simp only [Matrix.mul_assoc]
      _ = P * (Q.map (σ g) * P.map (σ g)) := by rw [hQσ g]
      _ = P := by rw [h1, Matrix.mul_one]

end CrystallineSemistableComparison.AdmAbs
end
end

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison

theorem adm : ComparisonAdmissible := by
  intro l _ K R G P S hR M hG n hInj hSpan a b
  obtain ⟨r, w, hw, hsp⟩ := hSpan
  have hcσ : ∀ (g : K.fixingSubgroup) (j : Fin a) (φ : Module.Dual K (HdR M.q n)),
      R.σ g (P.c M n (b j) φ) = ∑ k, (M.mat n b g).map R.q k j * P.c M n (b k) φ := by
    intro g j φ
    rw [← P.equi M n hG g (b j) φ]
    have hact : M.act n g (b j) = ∑ k, M.mat n b g k j • b k := by
      conv_lhs => rw [← Matrix.toLin_toMatrix b b (M.act n g)]
      exact Matrix.toLin_self b b _ j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hact, map_sum, AddMonoidHom.finsetSum_apply]
    simp only [P.lin, Matrix.map_apply]
  exact AdmAbs.admissible_of_absolute (fun g => R.σ g) S hR.stab hR.frac (fun g => (M.mat n b g).map R.q)
    (fun g i j => hR.q_mem _)
    (fun x hx hx0 h => hR.eig x hx hx0 fun g =>
      ⟨(M.mat n b g).det, by rw [h g, RingHom.map_det, RingHom.mapMatrix_apply]⟩)
    (fun j φ => P.c M n (b j) φ) hcσ (fun z h => hInj b z h) w (fun i x g => hw i x g)
    (fun j => hsp (b j))

end CrystallineSemistableComparison
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CstSmoothOf
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Development
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open Formalism.Per6 GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst GlobalTheory.LogCris

namespace CrystallineSemistableComparison

def EtaleSideSmoothAndSemistable : Prop := ZIn → ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
  EtSide (Model.Sm (l := l) (K := K)) ∧ EtSide (Model.Good (l := l) (K := K))

def Seam {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {R : Per l K} (G : Model l K → Prop) (D : Dat R) : Prop :=
  D.Laws G ∧ Nonempty (EMap G D) ∧ Nonempty (BMap G D) ∧ Nonempty (PMap G D)

def SeamS : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
  ∃ D : Dat (per l K), Seam Model.Sm D ∧ D.Span Model.Sm (Bcr l)

def Pre.cmp {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {G : Model l K → Prop} (P : Pre G (per l K)) (E : EtSide G)
    (h : ∀ M, G M → ∀ n, P.Inj M n ∧ P.Strict M n) : ComparisonOn G where
  c := P.c
  lin := P.lin
  lin' M n k v φ := by
    have h0 : (per l K).o k = oK k := by
      unfold per
      rfl
    have h1 := P.lin' M n k v φ
    rw [h0] at h1
    exact h1
  fin M n hM := ⟨E.fin M hM n, P.fin M hM n⟩
  equi := P.equi
  inj M n hM := (h M hM n).1
  fil M n hM r v φ hφ := (P.fil M n hM r v φ hφ).imp fun _ e => e.symm
  strict M hM n _ b z hz i := ((h M hM n).2 b z (fun r φ hφ => (hz r φ hφ).imp fun _ e => e.symm) i).imp fun _ e => e.symm
  nat := P.nat

theorem t_inv_mem (l : ℕ) [Fact l.Prime] : (tQ l)⁻¹ ∈ Bcr l := Subring.subset_closure (Or.inr (Or.inr rfl))

end CrystallineSemistableComparison
end
end

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GroundTheory.PAdicHodge Formalism.Per6 DeRhamPotentiallySemistable.DRPst

namespace CrystallineSemistableComparison

theorem zIn (h : FormalIn) (h4 : GlobalTheory.EtC.E4) (h8 : GlobalTheory.EtC.E8) : ZIn :=
  ⟨h.a6nat, h.a6ring, h.a9, h.et.a11, h4, h8, bock h, root h, sum h⟩

theorem etSide : EtaleSideSmoothAndSemistable := fun h l _ K _ =>
  ⟨adic h l K _ (fun _ hM => hM.1) (comp l K).1 fun M hM => geo l K M hM.1,
    adic h l K _ (fun _ hM => hM) (comp l K).2 fun M hM => geo l K M hM⟩

structure Chapters : Prop where
  rin : ∀ (l : ℕ) [Fact l.Prime], E.RIn l
  et : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)), E.EtMap l K
  uniq : E.FirstChernUniqueEtale
  main : ∀ (l : ℕ) [Fact l.Prime], B.Main l
  compat : ∀ (l : ℕ) [Fact l.Prime], B.Compat l
  compatH : ∀ (l : ℕ) [Fact l.Prime], B.CompatH l
  c1 : ∀ (l : ℕ) [Fact l.Prime], B.FirstChernCompatible l
  p : BocksteinBaseChangeP

def CstSmooth : Prop := SmoothModelCrystalline ∧ DeRhamComparisonSmooth ∧ CrysPhi

end CrystallineSemistableComparison
end
end

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GroundTheory.PAdicHodge Formalism.Per6 DeRhamPotentiallySemistable.DRPst

namespace CrystallineSemistableComparison

def EtSideS : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
  EtSide (Model.Sm (l := l) (K := K))

theorem cstSmooth_of_etSide (gL : GlueL) (gE : GlueE) (gB : GlueB) (hC : BcrisPeriodFacts) (hX : ResEx)
    (hI : EtSideS) (h : Chapters) : CstSmooth := by
  have hS : SeamS := by
    intro l _ K _
    obtain ⟨Amp, h1, h2, h3, h4⟩ := h.p l K
    obtain ⟨β, β₁, e⟩ := gB l K Amp (h.main l) (h.compat l) (h.c1 l)
    obtain ⟨r⟩ := hX l K
    obtain ⟨F⟩ := h4 r
    refine ⟨dat Amp, ⟨gL l K Amp (h.compatH l) (h.rin l) h.uniq h1 h2, gE l K Amp (h.et l K), ⟨β⟩, h3⟩, ?_⟩
    rw [← e] at F
    have := fac l K _ _ _ _ _ β β₁ F
    rwa [(hC l K r).2] at this
  refine ⟨?_, ?_, ?_⟩
  · intro l _ K _ M hM hs n a b
    obtain ⟨D, ⟨hL, ⟨e⟩, ⟨β⟩, ⟨κ⟩⟩, hsp⟩ := hS l K
    obtain ⟨P, hP⟩ := pre l K _ _ D (facts l K) (hI l K) hL e β κ
    exact adm l K _ _ P _ (regCr l K) M ⟨hM, hs⟩ n (inj l K _ _ P (facts l K) (hI l K) M ⟨hM, hs⟩ n).1
      (hP _ _ (t_inv_mem l) (regCr l K).q_mem hsp M ⟨hM, hs⟩ ⟨hM, hs⟩ n) a b
  · intro l _ K _
    obtain ⟨D, ⟨hL, ⟨e⟩, ⟨β⟩, ⟨κ⟩⟩, -⟩ := hS l K
    obtain ⟨P, -⟩ := pre l K _ _ D (facts l K) (hI l K) hL e β κ
    exact ⟨P.cmp (hI l K) (inj l K _ _ P (facts l K) (hI l K))⟩
  · intro l _ K _ r
    obtain ⟨Amp, h1, h2, ⟨κ⟩, h4⟩ := h.p l K
    obtain ⟨β, β₁, e⟩ := gB l K Amp (h.main l) (h.compat l) (h.c1 l)
    obtain ⟨F⟩ := h4 r
    obtain ⟨ε⟩ := gE l K Amp (h.et l K)
    rw [← e] at F
    exact phi l K _ _ _ _ _ (facts l K) (hC l K r).1 (hI l K) (gL l K Amp (h.compatH l) (h.rin l) h.uniq h1 h2) ε β β₁ κ F

end CrystallineSemistableComparison
