module

public import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypCard
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ClsChartedLabAt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockRowSubstitutionPreservesComplexSpan

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.ChartRank.HypRankGe
noncomputable section

namespace Formalism.MainNotions.G.CmpJ.PRankGe

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Module Formalism.MainNotions.G.CmpJ.PCard
open scoped TensorProduct

theorem finrank_le_span {O Kf W : Type} [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf]
    [IsFractionRing O Kf] [AddCommGroup W] [Module Kf W] [Module O W] [IsScalarTower O Kf W] (M : Submodule O W)
    [FiniteDimensional Kf (Submodule.span Kf (M : Set W))] :
    finrank O M ≤ finrank Kf (Submodule.span Kf (M : Set W)) := _root_.GlobalTheory.HP.finrank_le_span (O := O) (Kf := Kf) (W := W) M

section Gen

variable {p : ℕ} (H : GAtP p)

def InvK (a : H.comp) (L : H.P.Tup) : Submodule H.Kf H.P.Xsp where
  carrier := {X | X ∈ Submodule.span H.Kf (H.P.HtupW L : Set H.P.Xsp) ∧
    ∀ γ : (H.lev a).Γ, (H.lev a).smul γ L = L → ((H.lev a).χ γ : H.O) • (H.lev a).actX γ X = X}
  zero_mem' := ⟨Submodule.zero_mem _, fun γ _ => by rw [map_zero, smul_zero]⟩
  add_mem' := fun {x y} hx hy => ⟨Submodule.add_mem _ hx.1 hy.1, fun γ hγ => by
    rw [map_add (f := _), smul_add, hx.2 γ hγ, hy.2 γ hγ]⟩
  smul_mem' := fun c x hx => ⟨Submodule.smul_mem _ c hx.1, fun γ hγ => by
    rw [map_smul, ← algebraMap_smul H.Kf, smul_smul, mul_comm, ← smul_smul, algebraMap_smul, hx.2 γ hγ]⟩

def Eqv : Submodule H.Kf H.Fn where
  carrier := {F | ∀ a, (∀ L, H.P.IsLatTup L → F a L ∈ Submodule.span H.Kf (H.P.HtupW L : Set H.P.Xsp)) ∧
    (∀ L, ¬ H.P.IsLatTup L → F a L = 0) ∧
    ∀ (γ : (H.lev a).Γ) L, F a ((H.lev a).smul γ L) = ((H.lev a).χ γ : H.O) • (H.lev a).actX γ (F a L)}
  zero_mem' := fun a => ⟨fun L _ => Submodule.zero_mem _, fun _ _ => rfl, fun γ L => by
    simp only [Pi.zero_apply, map_zero, smul_zero]⟩
  add_mem' := fun {F F'} hF hF' a => ⟨fun L hL => Submodule.add_mem _ ((hF a).1 L hL) ((hF' a).1 L hL),
    fun L hL => by
      show F a L + F' a L = 0
      rw [(hF a).2.1 L hL, (hF' a).2.1 L hL, add_zero],
    fun γ L => by
      show F a _ + F' a _ = _
      rw [(hF a).2.2 γ L, (hF' a).2.2 γ L]
      show _ = ((H.lev a).χ γ : H.O) • (H.lev a).actX γ (F a L + F' a L)
      rw [map_add (f := _), smul_add]⟩
  smul_mem' := fun c F hF a => ⟨fun L hL => Submodule.smul_mem _ c ((hF a).1 L hL),
    fun L hL => by
      show c • F a L = 0
      rw [(hF a).2.1 L hL, smul_zero],
    fun γ L => by
      show c • F a _ = _
      rw [(hF a).2.2 γ L]
      show _ = ((H.lev a).χ γ : H.O) • (H.lev a).actX γ (c • F a L)
      rw [map_smul, ← algebraMap_smul H.Kf ((H.lev a).χ γ : H.O), ← algebraMap_smul H.Kf ((H.lev a).χ γ : H.O), smul_smul, smul_smul,
        mul_comm]⟩

theorem M_le_Eqv : (H.M : Set H.Fn) ⊆ Eqv H := by
  intro F hF a
  have h := (PCard.mem_M H).1 hF a
  simp only [Level.funMod, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mem_ker] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun L hL => Submodule.subset_span (h1 L hL), fun L hL => h2 L hL, fun γ L => ?_⟩
  have := h3 γ L
  rw [LinearMap.sub_apply, sub_eq_zero] at this
  exact this

theorem span_le_Eqv : Submodule.span H.Kf (H.M : Set H.Fn) ≤ Eqv H :=
  Submodule.span_le.2 (M_le_Eqv H)

variable {Cl : Type} [Fintype Cl]

def Cover (rep : Cl → H.comp × H.P.Tup) : Prop :=
  ∀ a L, H.P.IsLatTup L → ∃ (c : Cl) (γ : (H.lev (rep c).1).Γ), (rep c).1 = a ∧ L = (H.lev (rep c).1).smul γ (rep c).2

theorem eqv_eq_zero {rep : Cl → H.comp × H.P.Tup} (hc : Cover H rep) {F : H.Fn} (hF : F ∈ Eqv H)
    (h0 : ∀ c, F (rep c).1 (rep c).2 = 0) : F = 0 := by
  funext a L
  by_cases hL : H.P.IsLatTup L
  · obtain ⟨c, γ, rfl, rfl⟩ := hc a L hL
    rw [(hF _).2.2 γ _, h0 c, map_zero, smul_zero]
    rfl
  · exact (hF a).2.1 L hL

theorem eqv_mem_InvK {F : H.Fn} (hF : F ∈ Eqv H) (a : H.comp) (L : H.P.Tup) : F a L ∈ InvK H a L := by
  by_cases hL : H.P.IsLatTup L
  · refine ⟨(hF a).1 L hL, fun γ hγ => ?_⟩
    have := (hF a).2.2 γ L
    rw [hγ] at this
    exact this.symm
  · rw [(hF a).2.1 L hL]
    exact Submodule.zero_mem _

def evR (rep : Cl → H.comp × H.P.Tup) :
    Submodule.span H.Kf (H.M : Set H.Fn) →ₗ[H.Kf] ((c : Cl) → InvK H (rep c).1 (rep c).2) where
  toFun F c := ⟨F.1 (rep c).1 (rep c).2, eqv_mem_InvK H (span_le_Eqv H F.2) _ _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evR_inj {rep : Cl → H.comp × H.P.Tup} (hc : Cover H rep) : Function.Injective (evR H rep) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro F hF
  apply Subtype.ext
  exact eqv_eq_zero H hc (span_le_Eqv H F.2) fun c => congrArg Subtype.val (congrFun hF c)

theorem finrank_le_of_cover [IsFractionRing H.O H.Kf] {rep : Cl → H.comp × H.P.Tup} (hc : Cover H rep)
    (hfin : ∀ c, FiniteDimensional H.Kf (InvK H (rep c).1 (rep c).2)) :
    finrank H.O H.M ≤ ∑ c, finrank H.Kf (InvK H (rep c).1 (rep c).2) := by
  have : FiniteDimensional H.Kf (Submodule.span H.Kf (H.M : Set H.Fn)) := Module.Finite.of_injective (evR H rep) (evR_inj H hc)
  calc finrank H.O H.M ≤ finrank H.Kf (Submodule.span H.Kf (H.M : Set H.Fn)) := finrank_le_span H.M
    _ ≤ finrank H.Kf ((c : Cl) → InvK H (rep c).1 (rep c).2) := LinearMap.finrank_le_finrank_of_injective (evR_inj H hc)
    _ = ∑ c, finrank H.Kf (InvK H (rep c).1 (rep c).2) := Module.finrank_pi_fintype H.Kf

end Gen

section Forms

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

open Classical

abbrev Hc (S : StepIn M i hi G) (β : S.Ch) : GAtP p := gatCh G fun a : S.cmpt β => S.eC ⟨β, a⟩

def projC {Cl X : Type} [AddCommGroup X] [Module ℂ X] (V : Submodule ℂ (Cl → X)) (c : Cl) : Submodule ℂ X :=
  V.map (LinearMap.proj (R := ℂ) (φ := fun _ : Cl => X) c)

def IsPiSub {Cl X : Type} [AddCommGroup X] [Module ℂ X] (V : Submodule ℂ (Cl → X)) : Prop :=
  ∀ f : Cl → X, (∀ c, f c ∈ projC V c) → f ∈ V

abbrev FiBc (S : StepIn M i hi G) (β : S.Ch) (c : {c // S.chOf c = β}) := projC (FiB S β) c

def FiBPi (S : StepIn M i hi G) (β : S.Ch) : Prop := IsPiSub (FiB S β)

theorem finDim_FiB (S : StepIn M i hi G) (β : S.Ch) (hβ : β ∈ chs S) : FiniteDimensional ℂ (FiB S β) := by
  classical
  have := fin_Fi M i
  have : Module.Finite ℂ ((β : chs S) → FiB S β.1) := Module.Finite.equiv (eF S)
  exact fin_fac (R := ℂ) (φ := fun β : chs S => FiB S β.1) ⟨β, hβ⟩

theorem sum_le_finrank_FiB (S : StepIn M i hi G) (β : S.Ch) (hπ : FiBPi S β) :
    ∑ c, finrank ℂ (FiBc S β c) ≤ finrank ℂ (FiB S β) := by
  rcases isEmpty_or_nonempty {c // S.chOf c = β} with he | hne
  · simp [Finset.univ_eq_empty]
  · obtain ⟨c₀⟩ := hne
    have : FiniteDimensional ℂ (FiB S β) := finDim_FiB S β (c₀.2 ▸ chOf_mem S c₀.1)
    have : ∀ c, FiniteDimensional ℂ (FiBc S β c) := fun c => Module.Finite.map _ _
    let ψ : ((c : {c // S.chOf c = β}) → FiBc S β c) →ₗ[ℂ] FiB S β :=
      { toFun := fun g => ⟨fun c => (g c).1, hπ _ fun c => (g c).2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hψ : Function.Injective ψ := by
      intro g g' h
      funext c
      exact Subtype.ext (congrFun (congrArg Subtype.val h) c)
    rw [← Module.finrank_pi_fintype ℂ]
    exact LinearMap.finrank_le_finrank_of_injective hψ

def RankTie (S : StepIn M i hi G) (β : S.Ch) : Prop :=
  KAat.CompInj (S.K β).lev (S.loc β) ∧ (∀ a, PStabEq.GamOnto (S.K β).lev (S.loc β) a) ∧ PStabEq.LocHypC (S.K β).lev (S.loc β)

def RepOk (S : StepIn M i hi G) (β : S.Ch) (rep : {c // S.chOf c = β} → S.cmpt β × (Hc S β).P.Tup) : Prop :=
  ∀ c, ∃ (g : ∀ v, GL (Fin ((Hc S β).P.m + 1)) ((Hc S β).P.Qq v)) (γ₀ : GL (Fin (D.R.N i)) D.host.E) (κ₀ : (S.K β).lev.U),
    γ₀ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) ∧
    (∀ v, (rep c).2 v = colSpan ((Hc S β).P.W v) (g v : Matrix (Fin ((Hc S β).P.m + 1)) (Fin ((Hc S β).P.m + 1)) ((Hc S β).P.Qq v))) ∧
    (S.loc β).IsPt (rep c).1 g (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ₀ * ((S.K β).y c).1 * κ₀.1)

theorem coverOf {S : StepIn M i hi G} {e : D.what₂.LL →+* G.Kf} (H : ∀ β, S.Core e β) (X : KAat.ChX S) (β : S.Ch) :
    ∃ rep, RepOk S β rep ∧ Cover (Hc S β) rep := by
  have hex : ∀ c : {c // S.chOf c = β}, ∃ (a0 : S.cmpt β) (L : G.P.Tup) (γ₀ : GL (Fin (D.R.N i)) D.host.E),
      G.P.IsLatTup L ∧ KAat.IsCG S (S.eC ⟨β, a0⟩) L c.1 γ₀ := by
    rintro ⟨c0, hc0⟩
    subst hc0
    obtain ⟨a, L, γ₀, hL, hcg⟩ := KAat.exists_of_cls H c0
    obtain ⟨β', a0, hc, g, κ₀, ha, hrest⟩ := id hcg
    subst hc
    exact ⟨a0, L, γ₀, hL, ha ▸ hcg⟩
  choose a0 L γ₀ hL hcg using hex
  refine ⟨fun c => (a0 c, L c), fun c => ?_, fun a L' hL' => ?_⟩
  · obtain ⟨β', a0', hc, g, κ₀, ha, hLg, hγ, hpt⟩ := hcg c
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 (S.eC.injective ha)
    cases eq_of_heq h
    exact ⟨g, γ₀ c, κ₀, hγ, hLg, hpt⟩
  · obtain ⟨c1, γ1, h1⟩ := KAat.exists_isCG H (S.eC ⟨β, a⟩) L' hL'
    have hc1 : S.chOf c1 = β := by rw [KAat.IsCG.chart h1, Equiv.symm_apply_apply]
    obtain ⟨ha, γ, hγ⟩ := KAat.IsCG.orbit H X (hcg ⟨c1, hc1⟩) h1
    obtain ⟨-, h⟩ := Sigma.mk.inj_iff.1 (S.eC.injective ha)
    exact ⟨⟨c1, hc1⟩, γ, eq_of_heq h, hγ⟩

def InvLeOf (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : Prop :=
  BlockRationalityField → (∀ β, S.Core e β) → KAat.ChX S → ∀ β rep, RepOk S β rep → ∀ c,
    FiniteDimensional G.Kf (InvK (Hc S β) (rep c).1 (rep c).2) ∧
      finrank G.Kf (InvK (Hc S β) (rep c).1 (rep c).2) ≤ finrank ℂ (FiBc S β c)

theorem mk_eq_of (S : StepIn M i hi G) (β : S.Ch) {γ : GL (Fin (D.R.N i)) D.host.E}
    (hγ : γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    {x x' : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)} {κ : (S.K β).lev.U}
    (hx : x'.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * x.1 * κ.1) :
    (Quotient.mk'' x' : Cls (S.K β).lev) = Quotient.mk'' x := by
  symm
  refine (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨⟨_, PStabEq.bc_mem hγ⟩, Subgroup.mem_subgroupOf.2 ⟨γ, hγ, rfl⟩, ⟨_, PStabEq.U_le κ.2⟩,
    Subgroup.mem_subgroupOf.2 κ.2, Subtype.ext ?_⟩
  exact hx


set_option maxHeartbeats 1000000 in
theorem fiBPi (S : StepIn M i hi G) (β : S.Ch) : FiBPi S β := by
  intro f hf
  have hφ : ∀ c, ∃ φ ∈ AdForms (S.K β).lev (embT D) (lamTG M i), φ ((S.K β).y c) = f c := by
    intro c
    obtain ⟨φ', hφ', e⟩ := Submodule.mem_map.1 (hf c)
    obtain ⟨φ, hφ, rfl⟩ := Submodule.mem_map.1 hφ'
    exact ⟨φ, hφ, e⟩
  choose φ hφA hφy using hφ
  let g := fun (c : {c // S.chOf c = β}) (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) =>
    if (Quotient.mk'' x : Cls (S.K β).lev) = Quotient.mk'' ((S.K β).y c) then φ c x else 0
  have hg : ∀ c, g c ∈ AdForms (S.K β).lev (embT D) (lamTG M i) := by
    intro c
    have h2 := hφA c
    unfold AdForms at h2 ⊢
    rw [Submodule.mem_inf] at h2 ⊢
    obtain ⟨hA, hV⟩ := h2
    refine ⟨?_, ?_⟩
    · intro γ hγ x x' κ hx y y' hy
      have h1 := hA γ hγ x x' κ hx y y' hy
      have hq := mk_eq_of S β hγ hx
      by_cases hxc : (Quotient.mk'' x : Cls (S.K β).lev) = Quotient.mk'' ((S.K β).y c)
      · have hxc' : (Quotient.mk'' x' : Cls (S.K β).lev) = Quotient.mk'' ((S.K β).y c) := hq.trans hxc
        simp only [g, if_pos hxc, if_pos hxc']
        exact h1
      · have hxc' : ¬ (Quotient.mk'' x' : Cls (S.K β).lev) = Quotient.mk'' ((S.K β).y c) := fun h => hxc (hq.symm.trans h)
        simp only [g, if_neg hxc, if_neg hxc', Pi.zero_apply, mul_zero]
    · refine Submodule.mem_pi.2 fun x _ => ?_
      by_cases hxc : (Quotient.mk'' x : Cls (S.K β).lev) = Quotient.mk'' ((S.K β).y c)
      · simp only [g, if_pos hxc]
        exact Submodule.mem_pi.1 hV x (Set.mem_univ x)
      · simp only [g, if_neg hxc]
        exact Submodule.zero_mem _
  have hsum : f = ∑ c, res (embT D) (S.K β).y (g c) := by
    funext c' z
    rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single c']
    · show f c' z = g c' ((S.K β).y c') z
      simp only [g, if_pos rfl]
      rw [hφy]
    · intro c _ hc
      show g c ((S.K β).y c') z = 0
      have hne : ¬ (Quotient.mk'' ((S.K β).y c') : Cls (S.K β).lev) = Quotient.mk'' ((S.K β).y c) :=
        fun h => hc ((S.K β).y_bij.1 h).symm
      simp only [g, if_neg hne, Pi.zero_apply]
    · intro h
      exact absurd (Finset.mem_univ c') h
  rw [hsum]
  exact Submodule.sum_mem _ fun c _ => Submodule.mem_map_of_mem (hg c)

theorem chartRankGe_of [IsFractionRing G.O G.Kf] (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (H : ∀ β, S.Core e β)
    (hS : BlockRationalityField) (X : KAat.ChX S) (hI : InvLeOf S e) : ChartRankGe S := by
  intro β
  obtain ⟨rep, hok, hcov⟩ := coverOf H X β
  have hI' := hI hS H X β rep hok
  have : ∀ c, FiniteDimensional (Hc S β).Kf (InvK (Hc S β) (rep c).1 (rep c).2) := fun c => (hI' c).1
  calc finrank G.O (Hc S β).M ≤ ∑ c, finrank G.Kf (InvK (Hc S β) (rep c).1 (rep c).2) := finrank_le_of_cover (Hc S β) hcov this
    _ ≤ ∑ c, finrank ℂ (FiBc S β c) := Finset.sum_le_sum fun c _ => (hI' c).2
    _ ≤ finrank ℂ (FiB S β) := sum_le_finrank_FiB S β (fiBPi S β)

end Forms

section LocJ

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w hg)} {Lv : Levels Fl} {i : ℕ}
  (hi : i + 1 ≤ D.R.m) {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}

end LocJ

end Formalism.MainNotions.G.CmpJ.PRankGe
end
end

noncomputable section

namespace Formalism.MainNotions.G.CmpJ.PInvLe

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms NumberField Module Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.PCard
  Formalism.MainNotions.G.CmpJ.PRankGe

section Gen

variable {LL K C Y WK V : Type} [Field LL] [Field K] [Field C] (e : LL →+* K)
  [AddCommGroup Y] [Module LL Y] [AddCommGroup WK] [Module K WK] [AddCommGroup V] [Module C V]

theorem finrank_le_transfer (φK : Y →+ WK) (hK : ∀ (a : LL) y, φK (a • y) = e a • φK y)
    (φC : Y →+ V) [FiniteDimensional C V]
    (hind : ∀ (k : ℕ) (y : Fin k → Y), LinearIndependent LL y → LinearIndependent C (φC ∘ y))
    (N : Submodule K WK) (hN : N ≤ Submodule.span K (Set.range φK)) :
    FiniteDimensional K N ∧ finrank K N ≤ finrank C V := by
  have hr : Module.rank LL Y ≤ (finrank C V : Cardinal) := by
    refine rank_le fun s hs => ?_
    have h := hind s.card (fun j => ((s.equivFin.symm j : s) : Y)) (hs.comp _ s.equivFin.symm.injective)
    simpa using h.fintype_card_le_finrank
  have : FiniteDimensional LL Y := Module.rank_lt_aleph0_iff.1 (lt_of_le_of_lt hr Cardinal.natCast_lt_aleph0)
  let b := Module.finBasis LL Y
  have hsp : Submodule.span K (Set.range φK) ≤ Submodule.span K (Set.range fun j => φK (b j)) := by
    rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr y, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [hK]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hle := hN.trans hsp
  have : FiniteDimensional K (Submodule.span K (Set.range fun j => φK (b j))) :=
    FiniteDimensional.span_of_finite K (Set.finite_range _)
  have : FiniteDimensional K N := Submodule.finiteDimensional_of_le hle
  refine ⟨this, ?_⟩
  calc finrank K N ≤ finrank K (Submodule.span K (Set.range fun j => φK (b j))) := Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin (finrank LL Y)) := finrank_range_le_card _
    _ = finrank LL Y := Fintype.card_fin _
    _ ≤ finrank C V := by
      have h := hind _ (fun j => b j) b.linearIndependent
      simpa using h.fintype_card_le_finrank

end Gen

section RatPts

variable {LL Kf : Type} [Field LL] [Field Kf] (e : LL →+* Kf)

theorem mapE_smul {σ : Type} (r : LL) (Q : MvPolynomial σ LL) :
    MvPolynomial.map e (r • Q) = e r • MvPolynomial.map e Q := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]

theorem ker_desc {σ τ : Type} (Ts : Set (MvPolynomial σ Kf →ₗ[Kf] MvPolynomial τ Kf))
    (hT : ∀ T ∈ Ts, ∀ Q : MvPolynomial σ LL, ∃ Q' : MvPolynomial τ LL, MvPolynomial.map e Q' = T (MvPolynomial.map e Q))
    {ξ : MvPolynomial σ Kf} (hξ : ∀ T ∈ Ts, T ξ = 0) :
    ξ ∈ Submodule.span Kf (MvPolynomial.map e '' {Q | ∀ T ∈ Ts, T (MvPolynomial.map e Q) = 0}) := by
  let φ : MvPolynomial σ LL × MvPolynomial τ LL →+ MvPolynomial σ Kf × MvPolynomial τ Kf :=
    AddMonoidHom.prodMap (MvPolynomial.map e).toAddMonoidHom (MvPolynomial.map e).toAddMonoidHom
  let ev : (σ →₀ ℕ) ⊕ (τ →₀ ℕ) → (MvPolynomial σ Kf × MvPolynomial τ Kf) →ₗ[Kf] Kf :=
    Sum.elim (fun m => (MvPolynomial.lcoeff Kf m).comp (LinearMap.fst Kf _ _))
      (fun m => (MvPolynomial.lcoeff Kf m).comp (LinearMap.snd Kf _ _))
  have hsep : ∀ F, (∀ t, ev t F = 0) → F = 0 := by
    intro F h
    refine Prod.ext (MvPolynomial.ext _ _ fun m => ?_) (MvPolynomial.ext _ _ fun m => ?_)
    · simpa [ev] using h (Sum.inl m)
    · simpa [ev] using h (Sum.inr m)
  have hsm : ∀ (a : LL) x, φ (a • x) = e a • φ x := fun a x =>
    Prod.ext (mapE_smul e a x.1) (mapE_smul e a x.2)
  have hval : ∀ x, IsRat e ev (φ x) := by
    rintro x (m | m)
    · exact ⟨AddMonoidAlgebra.coeff x.1 m, by simp [ev, φ, MvPolynomial.coeff_map]⟩
    · exact ⟨AddMonoidAlgebra.coeff x.2 m, by simp [ev, φ, MvPolynomial.coeff_map]⟩
  let S : Set ((MvPolynomial σ Kf × MvPolynomial τ Kf) →ₗ[Kf] (MvPolynomial σ Kf × MvPolynomial τ Kf)) :=
    {Tm | ∃ T ∈ Ts, Tm = LinearMap.id + (LinearMap.inr Kf _ _).comp (T.comp (LinearMap.fst Kf _ _))}
  have hS : ∀ Tm ∈ S, ∀ x, ∃ y, φ y = Tm (φ x) := by
    rintro Tm ⟨T, hT', rfl⟩ x
    obtain ⟨Q', hQ'⟩ := hT T hT' x.1
    refine ⟨(x.1, x.2 + Q'), Prod.ext ?_ ?_⟩ <;> simp [φ, hQ']
  have key : ∀ p : MvPolynomial σ Kf, (p, (0 : MvPolynomial τ Kf)) ∈ Submodule.span Kf (Set.range φ) := by
    intro p
    refine MvPolynomial.induction_on' p (fun m c => ?_) (fun p q hp hq => ?_)
    · have h1 : (MvPolynomial.monomial m c, (0 : MvPolynomial τ Kf)) = c • φ (MvPolynomial.monomial m 1, 0) := by
        simp [φ, MvPolynomial.smul_monomial]
      rw [h1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · have h2 : (p + q, (0 : MvPolynomial τ Kf)) = (p, 0) + (q, 0) := by simp
      rw [h2]
      exact Submodule.add_mem _ hp hq
  have hinv : ∀ Tm ∈ S, Tm (ξ, 0) = (ξ, 0) := by
    rintro Tm ⟨T, hT', rfl⟩
    simp [hξ T hT']
  have h := span_inv e ev φ hsep hsm hval S hS (key ξ) hinv
  have h' := Submodule.mem_map_of_mem (f := LinearMap.fst Kf (MvPolynomial σ Kf) (MvPolynomial τ Kf)) h
  rw [Submodule.map_span] at h'
  refine Submodule.span_mono ?_ h'
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  refine ⟨x.1, fun T hT' => ?_, rfl⟩
  have := congrArg Prod.snd (hx _ ⟨T, hT', rfl⟩)
  simpa [φ] using this

theorem whc_map {σ M : Type} [AddCommMonoid M] [DecidableEq M] (w : σ → M) (n : M) (Q : MvPolynomial σ LL) :
    MvPolynomial.map e (MvPolynomial.weightedHomogeneousComponent w n Q) =
      MvPolynomial.weightedHomogeneousComponent w n (MvPolynomial.map e Q) := by
  ext d
  simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_weightedHomogeneousComponent]
  split_ifs <;> simp

theorem isWH_iff {σ M R : Type} [CommSemiring R] [AddCommMonoid M] [DecidableEq M] (w : σ → M) (n : M) (f : MvPolynomial σ R) :
    MvPolynomial.IsWeightedHomogeneous w f n ↔ MvPolynomial.weightedHomogeneousComponent w n f = f := by
  constructor
  · intro h
    ext d
    rw [MvPolynomial.coeff_weightedHomogeneousComponent]
    split_ifs with hd
    · rfl
    · by_contra hc
      exact hd (h (Ne.symm hc))
  · intro h d hd
    rw [← h, MvPolynomial.coeff_weightedHomogeneousComponent] at hd
    by_contra hc
    exact hd (if_neg hc)

theorem colAddGen_map {r n : ℕ} (l j : Fin n) (Q : MvPolynomial (Fin r × Fin n) LL) :
    MvPolynomial.map e (Formalism.GradedWeylDivisibility.colAddGen LL l j Q) = Formalism.GradedWeylDivisibility.colAddGen Kf l j (MvPolynomial.map e Q) := by
  induction Q using MvPolynomial.induction_on
  · rename_i a
    simp [Formalism.GradedWeylDivisibility.colAddGen]
  · rename_i p q hp hq
    simp only [map_add (f := _), hp, hq]
  · rename_i p v hp
    simp only [map_mul]
    rw [hp, MvPolynomial.map_X]
    congr 1
    simp only [Formalism.GradedWeylDivisibility.colAddGen, MvPolynomial.aeval_X]
    split_ifs <;> simp

theorem dualWeyl_desc {r n : ℕ} (ν : Fin n → ℕ) :
    Formalism.GradedWeylDivisibility.dualWeyl Kf r n ν ≤
      Submodule.span Kf (MvPolynomial.map e '' {Q | MvPolynomial.map e Q ∈ Formalism.GradedWeylDivisibility.dualWeyl Kf r n ν}) := by
  let Ts : Set (MvPolynomial (Fin r × Fin n) Kf →ₗ[Kf] MvPolynomial (Option (Fin r × Fin n)) Kf) :=
    {T | T = (MvPolynomial.rename some).toLinearMap.comp
        (LinearMap.id - MvPolynomial.weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.colW r n) ν)} ∪
      {T | ∃ l j : Fin n, l < j ∧ T = (Formalism.GradedWeylDivisibility.colAddGen Kf l j).toLinearMap - (MvPolynomial.rename some).toLinearMap}
  have hiff : ∀ f, f ∈ Formalism.GradedWeylDivisibility.dualWeyl Kf r n ν ↔ ∀ T ∈ Ts, T f = 0 := by
    intro f
    rw [Formalism.GradedWeylDivisibility.mem_dualWeyl_iff, isWH_iff]
    constructor
    · rintro ⟨h1, h2⟩ T (hT | ⟨l, j, hlj, hT⟩)
      · rw [hT]
        simp [h1]
      · rw [hT]
        simp [h2 l j hlj]
    · intro h
      refine ⟨?_, fun l j hlj => ?_⟩
      · have := h _ (Or.inl rfl)
        simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, AlgHom.toLinearMap_apply] at this
        have h0 := MvPolynomial.rename_injective some (Option.some_injective _) (this.trans (map_zero _).symm)
        exact (sub_eq_zero.1 h0).symm
      · have := h _ (Or.inr ⟨l, j, hlj, rfl⟩)
        simpa [sub_eq_zero] using this
  have hT : ∀ T ∈ Ts, ∀ Q : MvPolynomial (Fin r × Fin n) LL, ∃ Q' : MvPolynomial (Option (Fin r × Fin n)) LL,
      MvPolynomial.map e Q' = T (MvPolynomial.map e Q) := by
    rintro T (hT | ⟨l, j, hlj, hT⟩) Q <;> rw [hT]
    · exact ⟨MvPolynomial.rename some (Q - MvPolynomial.weightedHomogeneousComponent (Formalism.GradedWeylDivisibility.colW r n) ν Q), by
        simp [MvPolynomial.map_rename, whc_map]⟩
    · exact ⟨Formalism.GradedWeylDivisibility.colAddGen LL l j Q - MvPolynomial.rename some Q, by
        simp [MvPolynomial.map_rename, colAddGen_map]⟩
  intro ξ hξ
  refine Submodule.span_mono ?_ (ker_desc e Ts hT ((hiff ξ).1 hξ))
  rintro _ ⟨Q, hQ, rfl⟩
  exact ⟨Q, (hiff _).2 hQ, rfl⟩

theorem prod_desc {S : Type} [Fintype S] {σ : S → Type} {τ : Type} (f : ∀ s, σ s → τ)
    (Ms : ∀ s, Submodule Kf (MvPolynomial (σ s) Kf))
    (hM : ∀ s, Ms s ≤ Submodule.span Kf (MvPolynomial.map e '' {Q | MvPolynomial.map e Q ∈ Ms s})) :
    Submodule.span Kf {Z | ∃ F : ∀ s, MvPolynomial (σ s) Kf, (∀ s, F s ∈ Ms s) ∧ Z = ∏ s, MvPolynomial.rename (f s) (F s)} ≤
      Submodule.span Kf (MvPolynomial.map e '' {Q | MvPolynomial.map e Q ∈ Submodule.span Kf
        {Z | ∃ F : ∀ s, MvPolynomial (σ s) Kf, (∀ s, F s ∈ Ms s) ∧ Z = ∏ s, MvPolynomial.rename (f s) (F s)}}) := by
  rw [Submodule.span_le]
  rintro _ ⟨F, hF, rfl⟩
  let A : S → Set (MvPolynomial τ Kf) := fun s =>
    {y | ∃ Q : MvPolynomial (σ s) LL, MvPolynomial.map e Q ∈ Ms s ∧ y = MvPolynomial.rename (f s) (MvPolynomial.map e Q)}
  have hx : ∀ s ∈ Finset.univ, MvPolynomial.rename (f s) (F s) ∈ Submodule.span Kf (A s) := by
    intro s _
    have h1 := Submodule.mem_map_of_mem (f := (MvPolynomial.rename (R := Kf) (f s)).toLinearMap) (hM s (hF s))
    rw [Submodule.map_span] at h1
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨_, ⟨Q, hQ, rfl⟩, rfl⟩
    exact ⟨Q, hQ, rfl⟩
  have h := prod_mem_span Finset.univ A _ hx
  refine Submodule.span_mono ?_ h
  rintro _ ⟨a, ha, rfl⟩
  choose Q hQ hQe using fun s => ha s (Finset.mem_univ s)
  refine ⟨∏ s, MvPolynomial.rename (f s) (Q s), ?_, ?_⟩
  · change MvPolynomial.map e (∏ s, MvPolynomial.rename (f s) (Q s)) ∈ Submodule.span Kf
      {Z | ∃ F : ∀ s, MvPolynomial (σ s) Kf, (∀ s, F s ∈ Ms s) ∧ Z = ∏ s, MvPolynomial.rename (f s) (F s)}
    rw [map_prod]
    refine Submodule.subset_span ⟨fun s => MvPolynomial.map e (Q s), hQ, ?_⟩
    simp [MvPolynomial.map_rename]
  · rw [map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [hQe s, MvPolynomial.map_rename]

theorem vsp_desc {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) :
    Vsp Kf lam0 ≤ Submodule.span Kf (MvPolynomial.map e '' {Q | MvPolynomial.map e Q ∈ Vsp Kf lam0}) := by
  have hM : ∀ s : Fin n', (if Antitone (lamAt lam0 s) then Formalism.GradedWeylDivisibility.dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s)) else ⊥) ≤
      Submodule.span Kf (MvPolynomial.map e '' {Q | MvPolynomial.map e Q ∈
        (if Antitone (lamAt lam0 s) then Formalism.GradedWeylDivisibility.dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s)) else ⊥)}) := by
    intro s
    split_ifs
    · exact dualWeyl_desc e _
    · exact bot_le
  exact prod_desc e (σ := fun _ => Fin (m + 1) × Fin (m + 1)) (fun s v => (s, v)) _ hM

end RatPts

section Inv

variable {p : ℕ} (H : GAtP p) {LL : Type} [Field LL] (e : LL →+* H.Kf)

abbrev YR (H : GAtP p) (LL : Type) [Field LL] : Type :=
  MvPolynomial (Σ v : Fin H.P.nV, Fin (H.P.n' v) × (Fin (H.P.m + 1) × Fin (H.P.m + 1))) LL

theorem map_smul_e (r : LL) (Q : YR H LL) : MvPolynomial.map e (r • Q) = e r • MvPolynomial.map e Q := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]

def YInv (a : H.comp) (L : H.P.Tup) : Submodule LL (YR H LL) where
  carrier := {Q | MvPolynomial.map e Q ∈ H.P.Vtup ∧ ∀ γ : (H.lev a).Γ, (H.lev a).smul γ L = L →
    ((H.lev a).χ γ : H.O) • (H.lev a).actX γ (MvPolynomial.map e Q) = MvPolynomial.map e Q}
  add_mem' := fun {Q Q'} h h' => by
    simp only [Set.mem_ofPred_eq, map_add (f := _)] at h h' ⊢
    exact ⟨Submodule.add_mem _ h.1 h'.1, fun γ hγ => by rw [smul_add, h.2 γ hγ, h'.2 γ hγ]⟩
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, map_zero]
    exact ⟨Submodule.zero_mem _, fun γ _ => by rw [smul_zero]⟩
  smul_mem' := fun r Q h => by
    simp only [Set.mem_ofPred_eq] at h ⊢
    rw [map_smul_e]
    refine ⟨Submodule.smul_mem _ _ h.1, fun γ hγ => ?_⟩
    rw [map_smul, ← algebraMap_smul H.Kf, smul_smul, mul_comm, ← smul_smul, algebraMap_smul, h.2 γ hγ]

def SpanRat : Prop :=
  H.P.Vtup ≤ Submodule.span H.Kf (MvPolynomial.map e '' {Q : YR H LL | MvPolynomial.map e Q ∈ H.P.Vtup})

def ActRat (a : H.comp) (L : H.P.Tup) : Prop :=
  ∀ γ : (H.lev a).Γ, (H.lev a).smul γ L = L → ∀ Q : YR H LL, MvPolynomial.map e Q ∈ H.P.Vtup →
    ∃ Q' : YR H LL, MvPolynomial.map e Q' ∈ H.P.Vtup ∧
      MvPolynomial.map e Q' = ((H.lev a).χ γ : H.O) • (H.lev a).actX γ (MvPolynomial.map e Q)

theorem spanRat_holds : SpanRat H e :=
  prod_desc e (σ := fun v => Fin (H.P.n' v) × (Fin (H.P.m + 1) × Fin (H.P.m + 1)))
    (fun v x => (⟨v, x⟩ : Σ v : Fin H.P.nV, Fin (H.P.n' v) × (Fin (H.P.m + 1) × Fin (H.P.m + 1))))
    (fun v => Vsp H.Kf (H.P.lam0 v)) (fun v => vsp_desc e (H.P.lam0 v))

theorem span_HtupW_le {L : H.P.Tup} (hL : H.P.IsLatTup L) :
    Submodule.span H.Kf (H.P.HtupW L : Set H.P.Xsp) ≤ H.P.Vtup :=
  Submodule.span_le.2 fun z hz => Formalism.MainNotions.FormalGroupSystem.Pf.vt_HtupW_le H.P L hL z hz

theorem inv_le_span {a : H.comp} {L : H.P.Tup} (hL : H.P.IsLatTup L) (h1 : SpanRat H e) (h2 : ActRat H e a L) :
    InvK H a L ≤ Submodule.span H.Kf (MvPolynomial.map e '' (YInv H e a L : Set (YR H LL))) := by
  intro ξ hξ
  let Vr : Submodule LL (YR H LL) :=
    { carrier := {Q | MvPolynomial.map e Q ∈ H.P.Vtup}
      add_mem' := fun {Q Q'} h h' => by
        simp only [Set.mem_ofPred_eq, map_add (f := _)] at h h' ⊢
        exact Submodule.add_mem _ h h'
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, map_zero]
        exact Submodule.zero_mem _
      smul_mem' := fun r Q h => by
        simp only [Set.mem_ofPred_eq] at h ⊢
        rw [map_smul_e]
        exact Submodule.smul_mem _ _ h }
  let φ : Vr →+ H.P.Xsp := (MvPolynomial.map e).toAddMonoidHom.comp Vr.subtype.toAddMonoidHom
  let Sx : Set (H.P.Xsp →ₗ[H.Kf] H.P.Xsp) :=
    {Tm | ∃ γ : (H.lev a).Γ, (H.lev a).smul γ L = L ∧ Tm = algebraMap H.O H.Kf ((H.lev a).χ γ : H.O) • (H.lev a).actX γ}
  have hsm : ∀ (r : LL) (x : Vr), φ (r • x) = e r • φ x := fun r x => map_smul_e H e r x.1
  have hval : ∀ x : Vr, IsRat e (evX H) (φ x) := fun x m =>
    ⟨AddMonoidAlgebra.coeff x.1 m, by simp [φ, evX, MvPolynomial.lcoeff_apply, MvPolynomial.coeff_map]⟩
  have hT : ∀ Tm ∈ Sx, ∀ x : Vr, ∃ y : Vr, φ y = Tm (φ x) := by
    rintro Tm ⟨γ, hγ, rfl⟩ x
    obtain ⟨Q', hQ', e'⟩ := h2 γ hγ x.1 x.2
    refine ⟨⟨Q', hQ'⟩, ?_⟩
    simp only [φ, LinearMap.smul_apply, algebraMap_smul]
    exact e'
  have hξs : ξ ∈ Submodule.span H.Kf (Set.range φ) := by
    refine Submodule.span_mono ?_ (h1 (span_HtupW_le H hL hξ.1))
    rintro _ ⟨Q, hQ, rfl⟩
    exact ⟨⟨Q, hQ⟩, rfl⟩
  have hinv : ∀ Tm ∈ Sx, Tm ξ = ξ := by
    rintro Tm ⟨γ, hγ, rfl⟩
    simp only [LinearMap.smul_apply, algebraMap_smul]
    exact hξ.2 γ hγ
  have h := span_inv e (evX H) φ (evX_sep H) hsm hval Sx hT hξs hinv
  refine Submodule.span_mono ?_ h
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨x.1, ⟨x.2, fun γ hγ => ?_⟩, rfl⟩
  have := hx _ ⟨γ, hγ, rfl⟩
  simp only [LinearMap.smul_apply, algebraMap_smul] at this
  exact this

end Inv

section Rec

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

theorem isLatTup_of_repOk {S : StepIn M i hi G} {β : S.Ch} {rep : {c // S.chOf c = β} → S.cmpt β × (Hc S β).P.Tup}
    (hok : RepOk S β rep) (c : {c // S.chOf c = β}) : (Hc S β).P.IsLatTup (rep c).2 := by
  obtain ⟨g, -, -, -, hg, -⟩ := hok c
  intro v
  exact ⟨(g v : Matrix _ _ _), (Matrix.isUnit_iff_isUnit_det _).1 (g v).isUnit, hg v⟩

def ActRatOf (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : Prop :=
  BlockRationalityField → (∀ β, S.Core e β) → KAat.ChX S → ∀ β rep, RepOk S β rep → ∀ c, ActRat (Hc S β) e (rep c).1 (rep c).2

theorem actRat_of_core {S : StepIn M i hi G} {e : D.what₂.LL →+* G.Kf} {β : S.Ch} (H : S.Core e β) (hS : BlockRationalityField)
    (a : S.cmpt β) (L : (Hc S β).P.Tup) : ActRat (Hc S β) e a L := by
  intro γ _ Q hQ
  obtain ⟨κ, hκ⟩ := awayEx_of H.good (S.K β).lev H.gam a γ
  obtain ⟨r, -, hr⟩ := H.chi a γ κ hκ
  have hχ : algebraMap G.O G.Kf (((Hc S β).lev a).χ γ : G.O) = e r⁻¹ := by
    rw [map_inv₀]
    exact eq_inv_of_mul_eq_one_left hr
  refine ⟨r⁻¹ • natActR (Hc S β).P D.what₂.LL (blkLL (S.loc β) (sigD D) (tEL D) S.pos ((S.loc β).gamI a γ)) Q, ?_, ?_⟩
  · rw [mapE_smul, map_natActR]
    exact Submodule.smul_mem _ _ (natActR_VtupR (Hc S β).P G.Kf _ _ hQ)
  · rw [mapE_smul, ← actX_map (S.loc β) (tEL D) S.pos e H.actB H.pos_emb a γ Q, ← hχ, algebraMap_smul]

theorem actRatOf_holds (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : ActRatOf S e :=
  fun hS H _ β rep _ c => actRat_of_core (H β) hS (rep c).1 (rep c).2

def ValLiftOf (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : Prop :=
  BlockRationalityField → (∀ β, S.Core e β) → KAat.ChX S → ∀ β rep, RepOk S β rep → ∀ c,
    ∃ Φ : YInv (Hc S β) e (rep c).1 (rep c).2 →+ FiBc S β c,
      ∀ (k : ℕ) (Q : Fin k → YInv (Hc S β) e (rep c).1 (rep c).2), LinearIndependent D.what₂.LL Q → LinearIndependent ℂ (Φ ∘ Q)

theorem invLeOf_of (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (hR : ActRatOf S e) (hV : ValLiftOf S e) : InvLeOf S e := by
  intro hS H X β rep hok c
  have h2 := hR hS H X β rep hok c
  obtain ⟨Φ, hΦ⟩ := hV hS H X β rep hok c
  have : FiniteDimensional ℂ (FiBc S β c) := by
    have := finDim_FiB S β (c.2 ▸ chOf_mem S c.1)
    exact Module.Finite.map _ _
  let Yc := YInv (Hc S β) e (rep c).1 (rep c).2
  refine finrank_le_transfer e ((MvPolynomial.map e).toAddMonoidHom.comp Yc.subtype.toAddMonoidHom)
    (fun r Q => map_smul_e (Hc S β) e r Q.1) Φ hΦ _ ?_
  refine (inv_le_span (Hc S β) e (isLatTup_of_repOk hok c) (spanRat_holds (Hc S β) e) h2).trans (Submodule.span_mono ?_)
  rintro _ ⟨Q, hQ, rfl⟩
  exact ⟨⟨Q, hQ⟩, rfl⟩

theorem invLeOf_of_lift (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (hV : ValLiftOf S e) : InvLeOf S e :=
  invLeOf_of S e (actRatOf_holds S e) hV

def InvVal (S : StepIn M i hi G) (β : S.Ch) (c : {c // S.chOf c = β}) : Set (Formalism.L2.Forms.Frames (gramC (gramN D i hi) (embT D)) → ℂ) :=
  {v | v ∈ ValC (gramC (gramN D i hi) (embT D)) (lamTG M i) ∧
    ∀ γ : GL (Fin (D.R.N i)) D.host.E, γ ∈ Formalism.UG.UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → ∀ κ : (S.K β).lev.U,
      ((S.K β).y c).1 = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (IsDedekindDomain.FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * ((S.K β).y c).1 * κ.1 →
      ∀ y y' : Formalism.L2.Forms.Frames (gramC (gramN D i hi) (embT D)), IsTr (atInf (embT D) γ) y' y → v y = ((S.K β).lev.chi κ : ℂ) * v y'}

def FormsOnClassOf (S : StepIn M i hi G) : Prop :=
  ∀ β (c : {c // S.chOf c = β}) v, v ∈ InvVal S β c → v ∈ FiBc S β c

def CmpLiftOf (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : Prop :=
  BlockRationalityField → (∀ β, S.Core e β) → KAat.ChX S → ∀ β rep, RepOk S β rep → ∀ c,
    ∃ Φ : YInv (Hc S β) e (rep c).1 (rep c).2 →+ (Formalism.L2.Forms.Frames (gramC (gramN D i hi) (embT D)) → ℂ), (∀ Q, Φ Q ∈ InvVal S β c) ∧
      ∀ (k : ℕ) (Q : Fin k → YInv (Hc S β) e (rep c).1 (rep c).2), LinearIndependent D.what₂.LL Q → LinearIndependent ℂ (Φ ∘ Q)

theorem valLiftOf_of (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (h1 : FormsOnClassOf S) (h2 : CmpLiftOf S e) :
    ValLiftOf S e := by
  intro hS H X β rep hok c
  obtain ⟨Φ, hΦ, hind⟩ := h2 hS H X β rep hok c
  refine ⟨(Φ.codRestrict (FiBc S β c).toAddSubgroup fun Q => h1 β c _ (hΦ Q)), fun k Q hQ => ?_⟩
  exact LinearIndependent.of_comp (FiBc S β c).subtype (hind k Q hQ)

theorem chartRankGe_of_lift [IsFractionRing G.O G.Kf] (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (H : ∀ β, S.Core e β)
    (hS : BlockRationalityField) (X : KAat.ChX S) (hV : ValLiftOf S e) : ChartRankGe S :=
  chartRankGe_of S e H hS X (invLeOf_of_lift S e hV)

end Rec

section Card

variable {D : D7} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

theorem cmpJHyp_of_lift (c : LatCmp D) {I : CmpJIn Tw u μ w h Lv} (Gt : GatTies D) (hS : BlockRationalityField)
    (core : ∀ j hj β, (I.at' j hj).st.Core (c.embW u w h) β) (ok : ∀ j hj, (I.at' j hj).st.okW w)
    (twUnit : ∀ j hj β, (I.at' j hj).st.TwUnit w β) (valIntN : ∀ j hj, (I.at' j hj).st.ValIntN (c.embW u w h) w)
    (iwF : ∀ j hj β, (I.at' j hj).st.IwF β) (hfin : ∀ j, j + 1 ≤ D.R.m → (gatJ Lv (j + 1)).FinClasses)
    (X : ∀ j hj, KAat.ChX (I.at' j hj).st) (hV : ∀ j hj, ValLiftOf (I.at' j hj).st (c.embW u w h)) : CmpJHyp c I :=
  cmpJHyp_of_ge c Gt hS core ok twUnit valIntN iwF hfin fun j hj => by
    have : IsFractionRing (gatJ Lv (j + 1)).O (gatJ Lv (j + 1)).Kf := ((D.gat u w h).P.setting (plc Gt u w h)).frac_O
    exact chartRankGe_of_lift _ _ (core j hj) hS (X j hj) (hV j hj)

theorem cmpJHyp_of_two (c : LatCmp D) {I : CmpJIn Tw u μ w h Lv} (Gt : GatTies D) (hS : BlockRationalityField)
    (core : ∀ j hj β, (I.at' j hj).st.Core (c.embW u w h) β) (ok : ∀ j hj, (I.at' j hj).st.okW w)
    (twUnit : ∀ j hj β, (I.at' j hj).st.TwUnit w β) (valIntN : ∀ j hj, (I.at' j hj).st.ValIntN (c.embW u w h) w)
    (iwF : ∀ j hj β, (I.at' j hj).st.IwF β) (hfin : ∀ j, j + 1 ≤ D.R.m → (gatJ Lv (j + 1)).FinClasses)
    (X : ∀ j hj, KAat.ChX (I.at' j hj).st) (h1 : ∀ j hj, FormsOnClassOf (I.at' j hj).st)
    (h2 : ∀ j hj, CmpLiftOf (I.at' j hj).st (c.embW u w h)) : CmpJHyp c I :=
  cmpJHyp_of_lift c Gt hS core ok twUnit valIntN iwF hfin X fun j hj => valLiftOf_of _ _ (h1 j hj) (h2 j hj)

end Card

end Formalism.MainNotions.G.CmpJ.PInvLe
