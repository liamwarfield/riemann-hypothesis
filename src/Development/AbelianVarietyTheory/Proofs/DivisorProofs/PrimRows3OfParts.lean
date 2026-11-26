module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAdelicThetaSumSqParsevalSecondVariable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelRowsOrthogonalSumOfParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelWOrthogonalSumOfParts

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelRowsEqPrincipalRowsOfType
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelRowsEqPrincipalRowsOfType
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.LevelRowsPrincipal

theorem pLevE_of : GlobalTheory.Published.CuspRapidDecay → HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → R.PGEquiv F → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → R.PLevE F := by
  intro hCusp hHowe D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hLI hOk hC hEx hJunk hGE hPos hScal hB hRT
  have hBlock : (R.toCx3 F).zs.InBlock := GlobalTheory.T.adjointLift_range_le_goodBlock_eigenspaces hCusp R F hLI hOk hC hEx hGE
  have hCarry : ∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c := GlobalTheory.T.thetaLift_carrying_of_base_tuple_rows hCusp hHowe R F hLI hOk hC hEx hJunk hGE hPos
  have hSpan : (⨆ p, R.EEp3 p) = ⊤ :=
    GlobalTheory.T.iSup_eEp3_eq_whole_space_of_weakCharacterisation R F hC hEx (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCusp R.toRealDat) hCarry
  have hTop := GlobalTheory.T.EEg3_eq_univ_of_weakCharacterisation R F hOk hC hSpan hScal hB hRT hBlock
  obtain ⟨h0, h1⟩ := GlobalTheory.LevelRows3.eel_eq_typeSp3 R F hC
  refine ⟨?_, ?_⟩
  · show (R.toCx3 F).EEl false = _ ⊓ _
    rw [hTop, top_inf_eq, h0]
  · show (R.toCx3 F).EEl true = _ ⊓ _
    rw [hTop, top_inf_eq, h1]

end GlobalTheory.LevelRowsPrincipal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelRowsEqPrincipalRowsOfTypeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelRows_eq_principalRows_of_type : GlobalTheory.Published.CuspRapidDecay → HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → R.PGEquiv F → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → R.PLevE F := by
  first | exact @GlobalTheory.LevelRowsPrincipal.pLevE_of | exact GlobalTheory.LevelRowsPrincipal.pLevE_of | (intros; apply GlobalTheory.LevelRowsPrincipal.pLevE_of <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelGoodFormsDimsAgreePartwise
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwSubISupInfLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankISupEqOfISupIndep
namespace GlobalTheory

theorem iSupIndep_of_joint_eigen {E I : Type} [AddCommGroup E] [Module ℂ E]
    (h : I → Module.End ℂ E) (V : (I → ℂ) → Submodule ℂ E)
    (hV : ∀ x, ∀ v ∈ V x, ∀ i, h i v = x i • v) : iSupIndep V := by
  classical
  have stab : ∀ (s : Finset (I → ℂ)) (i : I), ∀ u ∈ ⨆ y ∈ s, V y, h i u ∈ ⨆ y ∈ s, V y := by
    intro s i
    have : (⨆ y ∈ s, V y) ≤ (⨆ y ∈ s, V y).comap (h i) := by
      refine iSup₂_le fun y hy v hv => ?_
      rw [Submodule.mem_comap, hV y v hv i]
      exact Submodule.smul_mem _ _ ((le_iSup₂_of_le (f := fun y (_ : y ∈ s) => V y) y hy le_rfl) hv)
    exact fun u hu => this hu
  have key : ∀ (x : I → ℂ) (s : Finset (I → ℂ)), x ∉ s → ∀ v ∈ V x, v ∈ (⨆ y ∈ s, V y) → v = 0 := by
    intro x s
    induction s using Finset.induction_on with
    | empty => intro _ v _ hv; simpa using hv
    | insert y s hy ih =>
      intro hx v hvx hv
      rw [Finset.mem_insert, not_or] at hx
      rw [Finset.iSup_insert, Submodule.mem_sup] at hv
      obtain ⟨w, hw, u, hu, hsum⟩ := hv
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx.1
      have e : (x i - y i) • v = h i u - y i • u := by
        rw [sub_smul, ← hV x v hvx i, ← hsum, map_add (f := _), hV y w hw i, smul_add]; abel
      have h0 := ih hx.2 ((x i - y i) • v) (Submodule.smul_mem _ _ hvx)
        (e ▸ Submodule.sub_mem _ (stab s i u hu) (Submodule.smul_mem _ _ hu))
      exact (smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hi)
  intro x
  rw [Submodule.disjoint_def]
  intro v hvx hv
  replace hv : v ∈ ⨆ y : {y : I → ℂ // y ≠ x}, V y.1 := by rwa [iSup_subtype]
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hv
  refine key x (s.image Subtype.val) ?_ v hvx ?_
  · intro hx
    obtain ⟨⟨y, hy⟩, -, e⟩ := Finset.mem_image.mp hx
    exact hy e
  · refine (iSup₂_le fun y hy => ?_ : (⨆ y ∈ s, V y.1) ≤ _) hs
    exact le_iSup₂_of_le (f := fun y (_ : y ∈ s.image Subtype.val) => V y) y.1
      (Finset.mem_image_of_mem _ hy) le_rfl

theorem finrank_iSup_eq_of_iSupIndep {E W X : Type} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (V : X → Submodule ℂ E) (V' : X → Submodule ℂ W) (hV : iSupIndep V) (hV' : iSupIndep V')
    (hd : ∀ x, Module.finrank ℂ (V x) = Module.finrank ℂ (V' x)) :
    Module.finrank ℂ (⨆ x, V x : Submodule ℂ E) = Module.finrank ℂ (⨆ x, V' x : Submodule ℂ W) := by
  classical
  rw [Submodule.iSup_eq_range_dfinsupp_lsum, Submodule.iSup_eq_range_dfinsupp_lsum]
  have e : ∀ x, V x ≃ₗ[ℂ] V' x := fun x => LinearEquiv.ofFinrankEq _ _ (hd x)
  exact (((LinearEquiv.ofInjective _ hV.dfinsupp_lsum_injective).symm.trans
    (DFinsupp.mapRange.linearEquiv e)).trans
      (LinearEquiv.ofInjective _ hV'.dfinsupp_lsum_injective)).finrank_eq

theorem finrank_iSup_joint_eigen_eq : ∀ {E W I C : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (h : I → Module.End ℂ E) (h' : I → Module.End ℂ W) (U : C → Submodule ℂ E) (U' : C → Submodule ℂ W) (lab : C → I → ℂ), (∀ c, ∀ x ∈ U c, ∀ i, h i x = lab c i • x) → (∀ c, ∀ x ∈ U' c, ∀ i, h' i x = lab c i • x) → (∀ c c', lab c = lab c' → U c = U c' ∧ U' c = U' c') → (∀ c, Module.finrank ℂ (U c) = Module.finrank ℂ (U' c)) → ∀ S : C → Prop, Module.finrank ℂ (⨆ (c : C) (_ : S c), U c : Submodule ℂ E) = Module.finrank ℂ (⨆ (c : C) (_ : S c), U' c : Submodule ℂ W) := by
  intro E W I C _ _ _ _ _ _ h h' U U' lab hU hU' hlab hd S
  have re : ∀ {F : Type} [AddCommGroup F] [Module ℂ F] (A : C → Submodule ℂ F),
      (⨆ (c : C) (_ : S c), A c) = ⨆ (x : I → ℂ), ⨆ (c : C) (_ : S c ∧ lab c = x), A c := by
    intro F _ _ A
    apply le_antisymm
    · refine iSup₂_le fun c hc => le_iSup_of_le (lab c) ?_
      exact le_iSup₂_of_le (f := fun c' (_ : S c' ∧ lab c' = lab c) => A c') c ⟨hc, rfl⟩ le_rfl
    · exact iSup_le fun x => iSup₂_le fun c hc =>
        le_iSup₂_of_le (f := fun c' (_ : S c') => A c') c hc.1 le_rfl
  have one : ∀ {F : Type} [AddCommGroup F] [Module ℂ F] (A : C → Submodule ℂ F),
      (∀ c c', lab c = lab c' → A c = A c') → ∀ c, S c →
      (⨆ (c' : C) (_ : S c' ∧ lab c' = lab c), A c') = A c := by
    intro F _ _ A hA c hc
    apply le_antisymm
    · exact iSup₂_le fun c' hc' => (hA c' c hc'.2).le
    · exact le_iSup₂_of_le (f := fun c' (_ : S c' ∧ lab c' = lab c) => A c') c ⟨hc, rfl⟩ le_rfl
  have none : ∀ {F : Type} [AddCommGroup F] [Module ℂ F] (A : C → Submodule ℂ F) (x : I → ℂ),
      (¬ ∃ c, S c ∧ lab c = x) → (⨆ (c' : C) (_ : S c' ∧ lab c' = x), A c') = ⊥ := by
    intro F _ _ A x hx
    exact le_bot_iff.mp (iSup₂_le fun c hc => (hx ⟨c, hc⟩).elim)
  have ind : ∀ {F : Type} [AddCommGroup F] [Module ℂ F] (g : I → Module.End ℂ F)
      (A : C → Submodule ℂ F), (∀ c c', lab c = lab c' → A c = A c') →
      (∀ c, ∀ x ∈ A c, ∀ i, g i x = lab c i • x) →
      iSupIndep fun x : I → ℂ => ⨆ (c : C) (_ : S c ∧ lab c = x), A c := by
    intro F _ _ g A hA hg
    refine iSupIndep_of_joint_eigen g _ fun x v hv i => ?_
    by_cases hx : ∃ c, S c ∧ lab c = x
    · obtain ⟨c, hc, rfl⟩ := hx
      rw [one A hA c hc] at hv
      exact hg c v hv i
    · rw [none A x hx, Submodule.mem_bot] at hv
      simp [hv]
  rw [re U, re U']
  refine finrank_iSup_eq_of_iSupIndep _ _ (ind h U (fun c c' e => (hlab c c' e).1) hU)
    (ind h' U' (fun c c' e => (hlab c c' e).2) hU') fun x => ?_
  by_cases hx : ∃ c, S c ∧ lab c = x
  · obtain ⟨c, hc, rfl⟩ := hx
    rw [one U (fun c c' e => (hlab c c' e).1) c hc, one U' (fun c c' e => (hlab c c' e).2) c hc]
    exact hd c
  · rw [none U x hx, none U' x hx]
    simp

end GlobalTheory
end

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.DimPartsFull

theorem dualLab_dualLab' (d : List ℤ) : dualLab (dualLab d) = d := by
  simp [dualLab, List.map_reverse, List.map_map]

section Tw
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (s : Bool)

theorem twSub_map (V : Submodule ℂ E) : V.map (Tw.mkL s E) = Tw.sub s V := by
  ext x
  exact ⟨fun ⟨y, hy, h⟩ => h ▸ hy, fun hx => ⟨Tw.out x, hx, rfl⟩⟩

theorem twSub_iSup {C : Type} (S : C → Prop) (V : C → Submodule ℂ E) :
    Tw.sub s (⨆ (c : C) (_ : S c), V c) = ⨆ (c : C) (_ : S c), Tw.sub s (V c) := by
  rw [← twSub_map, Submodule.map_iSup]
  refine iSup_congr fun c => ?_
  rw [Submodule.map_iSup]
  refine iSup_congr fun _ => ?_
  exact twSub_map s (V c)

theorem twSub_finrank (V : Submodule ℂ E) : Module.finrank ℂ (Tw.sub s V) = Module.finrank ℂ V := by
  unfold Module.finrank
  congr 1
  symm
  exact rank_eq_of_equiv_equiv (cj s)
    (show V ≃+ Tw.sub s V from
      { toFun := fun x => ⟨Tw.mk s x.1, x.2⟩
        invFun := fun x => ⟨Tw.out x.1, x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl })
    (Function.Involutive.bijective (cj_cj s))
    (fun r m => Subtype.ext ((Tw.mkL s E).map_smulₛₗ r m.1))

theorem twSub_le {V V' : Submodule ℂ E} (h : V ≤ V') : Tw.sub s V ≤ Tw.sub s V' := fun _ hx => h hx

theorem twSub_stable {G : Type} [Group G] (ρ : Representation ℂ G E) (V : Submodule ℂ E)
    (h : ∀ g, V.map (ρ g) ≤ V) (g : G) : (Tw.sub s V).map (Tw.rep s ρ g) ≤ Tw.sub s V := by
  rintro _ ⟨x, hx, rfl⟩
  exact h g ⟨Tw.out x, hx, rfl⟩

end Tw

theorem twSub_iSup_inf_level {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (s : Bool) {G : Type} [Group G] [Fintype G]
    (ρ : Representation ℂ G E) (P : Subgroup G) (ψ : P →* ℂˣ) {C : Type} (S : C → Prop) (U : C → Submodule ℂ E)
    (B Lev : Submodule ℂ E) (hUB : ∀ c, U c ≤ B) (hstab : ∀ c g, (U c).map (ρ g) ≤ U c)
    (hLev : Tw.sub s Lev = Tw.sub s B ⊓
      ⨅ h : P, LinearMap.ker (Tw.rep s ρ (h : G) - ((ψ h : ℂˣ) : ℂ) • LinearMap.id)) :
    Tw.sub s (⨆ (c : C) (_ : S c), U c) ⊓ Tw.sub s Lev = Tw.sub s (⨆ (c : C) (_ : S c), U c ⊓ Lev) := by
  rw [twSub_iSup, hLev, ← inf_assoc, inf_eq_left.2 (iSup₂_le fun c _ => twSub_le s (hUB c)),
    GlobalTheory.iSup_stable_inf_typeSpace (Tw.rep s ρ) P ψ _ S (fun c g => twSub_stable s ρ _ (hstab c) g), twSub_iSup]
  refine iSup_congr fun c => iSup_congr fun _ => ?_
  show _ = Tw.sub s (U c) ⊓ Tw.sub s Lev
  rw [hLev, ← inf_assoc, inf_eq_left.2 (twSub_le s (hUB c))]

open Classical in
theorem evC_single {D : D7} (V : HSp D) (P : Pl D.host.E) (a : List ℤ → ℂ) (d : List ℤ) :
    GlobalTheory.Hk3.evC V P a (Finsupp.single d 1) = if IsLab V P d then a d else 0 := by
  unfold GlobalTheory.Hk3.evC
  rw [Finsupp.sum_single_index]
  · split_ifs <;> simp
  · split_ifs <;> simp

theorem dimParts_of_schur {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ} (hOk : A3.fam3.Ok3 s) (hW : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt)
    (hX : GoodStable A3.A.X) (hD : GlobalTheory.CuspMult.CuspDecomp D) (hM : GlobalTheory.CuspMult.MultEq R.toRealDat)
    (hU : R.toRealDat.LUnif) (hS : SchurAll R.toRealDat) : (R.toCx3 F).DimParts false := by
  obtain ⟨hC, hSF, hEE, hWc⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW hEx
  have hIrr : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  obtain ⟨hE, -, -, -, hEev, hEchar⟩ := GlobalTheory.T.exists_sphericalOperators_rows_normal_eigenspaces R.toRealDat F.lv2 hC hS R.SF hSF
  intro j p
  obtain ⟨hWo, -, -, -, hWtop, hWstab, hWev, hWchar⟩ := GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R.toRealDat F.lv2 hC hS hIrr R.SF hSF j
  have hI := (GlobalTheory.Hk3.eH_laws R.toRealDat F.lv2 hC hIrr j).1
  have hlab : ∀ P d, Good R.toRealDat A3.A.μ0 P → (IsLab (Wc D j) P d ↔ IsLab (Yc D 0) P (dualLab d)) :=
    fun P d hP => (GlobalTheory.T.isLabel_thetaLiftSpace_iff_dual (s := 0) R.toRealDat F.lv2 hC j P d hP).1
  let LevW : Submodule ℂ (R.HW j (sg0 D A3.A)).H :=
    (R.toRealDat.Wat j (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A))).comap (R.HW j (sg0 D A3.A)).e
  let LevE : Submodule ℂ R.HE.H := (R.toRealDat.EEat (R.toRealDat.levR F.lv2 false)).comap R.HE.e
  have hWle : ∀ c, Wcc R.toRealDat R.SF j c ≤ LinearMap.range (eH R.toRealDat j) := fun c =>
    hWtop ▸ le_iSup (fun c => Wcc R.toRealDat R.SF j c) c
  have hr1 : LinearMap.range ((R.toCx3 F).w0C false j) = Tw.sub (twAt D.what₂.embLL A3.A.v0) LevW :=
    GlobalTheory.T.range_complex_points_level_forms_eq_good_forms R F hOk hW hU false j
  have hr2 := GlobalTheory.T.range_goodProjector_baseLevel_twistedModel R F hOk hW hEx hU j
  have hWside : (R.toCx3 F).Wp j p ⊓ LinearMap.range ((R.toCx3 F).w0C false j) =
      Tw.sub (twAt D.what₂.embLL A3.A.v0)
        (⨆ (c : Pl D.host.E → List ℤ → ℂ) (_ : R.Carries p c), Wcc R.toRealDat R.SF j c ⊓ LevW) := by
    have e0 : (R.toCx3 F).Wp j p = Tw.sub (twAt D.what₂.embLL A3.A.v0)
        (⨆ (c : Pl D.host.E → List ℤ → ℂ) (_ : R.Carries p c), Wcc R.toRealDat R.SF j c) := by
      show Tw.sub _ (R.Wp3 j p) = _
      unfold RealDat3.Wp3
      simp only [hWc]
    rw [e0, hr1]
    exact twSub_iSup_inf_level _ (R.gW j (sg0 D A3.A)) F.P0 ((Units.map A3.A.fam.v0.embedding.toMonoidHom).comp F.ψ0⁻¹)
      (R.Carries p) _ _ LevW hWle hWstab (hr1.symm.trans hr2)
  have hEside : (R.toCx3 F).EEp p ⊓ (R.toCx3 F).EEl false =
      Tw.sub (twAt D.what₂.embLL A3.A.v0)
        (⨆ (c : Pl D.host.E → List ℤ → ℂ) (_ : R.Carries p c), EEc R.toRealDat R.SF c ⊓ LevE) := by
    have e0 : (R.toCx3 F).EEp p = Tw.sub (twAt D.what₂.embLL A3.A.v0)
        (⨆ (c : Pl D.host.E → List ℤ → ℂ) (_ : R.Carries p c), EEc R.toRealDat R.SF c) := by
      show Tw.sub _ (R.EEp3 p) = _
      unfold RealDat3.EEp3
      simp only [hEE]
    have hl : Tw.sub (twAt D.what₂.embLL A3.A.v0) LevE = Tw.sub (twAt D.what₂.embLL A3.A.v0) ⊤ ⊓
        ⨅ h : F.P0, LinearMap.ker (Tw.rep (twAt D.what₂.embLL A3.A.v0) R.gE (h : G) -
          ((((Units.map A3.A.fam.v0.embedding.toMonoidHom).comp F.ψ0) h : ℂˣ) : ℂ) • LinearMap.id) := by
      have := (GlobalTheory.T.level_rows_eq_type_vectors_of_level R F hW).1
      refine this.trans ?_
      ext x
      exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
    rw [e0]
    exact twSub_iSup_inf_level _ R.gE F.P0 _ (R.Carries p) _ ⊤ LevE (fun _ => le_top)
      (fun c g => GlobalTheory.T.rowParts_full_spherical_algebra_stable_finiteGroup (s := 0) R.toRealDat F.lv2 hC R.SF hSF c g) hl
  rw [hWside, hEside]
  refine (twSub_finrank (E := (R.HW j (sg0 D A3.A)).H) _ _).trans (Eq.trans ?_ (twSub_finrank (E := R.HE.H) _ _).symm)
  have hWfix : ∀ c, ∀ x ∈ Wcc R.toRealDat R.SF j c, eH R.toRealDat j x = x := by
    intro c x hx
    obtain ⟨y, rfl⟩ := hWle c hx
    rw [← Module.End.mul_apply, hI]
  let I := {x : Pl D.host.E × List ℤ // Good R.toRealDat A3.A.μ0 x.1 ∧ IsLab (Wc D j) x.1 x.2}
  let lab : (Pl D.host.E → List ℤ → ℂ) → I → ℂ := fun c i => c i.1.1 i.1.2
  have hEle : ∀ c c', lab c = lab c' → EEc R.toRealDat R.SF c ≤ EEc R.toRealDat R.SF c' := by
    intro c c' hcc x hx
    refine hEchar c' x fun P d hP hd => ?_
    rw [hEev c P hP _ x hx, evC_single, if_pos hd]
    have hl : IsLab (Wc D j) P (dualLab d) := (hlab P (dualLab d) hP).2 (by rwa [dualLab_dualLab'])
    exact congrArg (· • x) (congrFun hcc ⟨(P, dualLab d), hP, hl⟩)
  have hWcle : ∀ c c', lab c = lab c' → Wcc R.toRealDat R.SF j c ≤ Wcc R.toRealDat R.SF j c' := by
    intro c c' hcc x hx
    refine hWchar c' x (hWfix c x hx) fun P d hP hd => ?_
    rw [hWev c P hP _ x hx, evC_single, if_pos hd]
    exact congrArg (· • x) (congrFun hcc ⟨(P, d), hP, hd⟩)
  symm
  refine GlobalTheory.finrank_iSup_joint_eigen_eq (I := I)
    (fun i => hE i.1.1 (Finsupp.single (dualLab i.1.2) 1)) (fun i => hWo i.1.1 (Finsupp.single i.1.2 1))
    (fun c => EEc R.toRealDat R.SF c ⊓ LevE) (fun c => Wcc R.toRealDat R.SF j c ⊓ LevW) lab ?_ ?_ ?_ ?_ (R.Carries p)
  · rintro c x hx ⟨⟨P, d⟩, hP, hd⟩
    rw [hEev c P hP _ x hx.1, evC_single, if_pos ((hlab P d hP).1 hd), dualLab_dualLab']
  · rintro c x hx ⟨⟨P, d⟩, hP, hd⟩
    rw [hWev c P hP _ x hx.1, evC_single, if_pos hd]
  · intro c c' hcc
    rw [le_antisymm (hEle c c' hcc) (hEle c' c hcc.symm), le_antisymm (hWcle c c' hcc) (hWcle c' c hcc.symm)]
    exact ⟨rfl, rfl⟩
  · intro c
    exact (GlobalTheory.T.finrank_W_eigenpart_eq_rows_full_hecke R.toRealDat F.lv2 hOk.ok2 hC hS hX hD hM R.SF hSF F.P0 F.ψ0 j c).symm

end GlobalTheory.DimPartsFull

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelGoodFormsDimsAgreePartwise
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.DimPartsFull

theorem dimParts : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → GoodStable A3.A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R.toRealDat → R.toRealDat.LUnif → (R.toCx3 F).DimParts false :=
  fun hP _ _ _ _ _ _ _ _ _ _ _ _ R F _ hOk hW hEx hX hD hM hU =>
    dimParts_of_schur R F hOk hW hEx hX hD hM hU (GlobalTheory.T.schurConstantsExistOnChain_of_cuspRapidDecay hP R.toRealDat)

end GlobalTheory.DimPartsFull

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelGoodFormsDimsAgreePartwiseStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseLevel_goodForms_dims_agree_partwise : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → GoodStable A3.A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R.toRealDat → R.toRealDat.LUnif → (R.toCx3 F).DimParts false := by
  first | exact @GlobalTheory.DimPartsFull.dimParts | exact GlobalTheory.DimPartsFull.dimParts | (intros; apply GlobalTheory.DimPartsFull.dimParts <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory

theorem primRows3_of_parts : GlobalTheory.Published.CuspRapidDecay → HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → GoodStable A3.A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PHecke F → R.PGUnit F → R.PGEquiv F → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false → (∀ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW → U2.OntoC A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hW) → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → R.PPos → R.PrincipalLevelBijective F → R.PThmB → R.toRealDat.LUnif → (R.toCx3 F).MLat false → R.PThmA → (R.toCx3 F).GalD F.cr false → PrimRows3 R F := by
  intro hCusp hHowe D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hLift hOk hC hEx hInert hGS hCD hME hR hL hHk hGU hGE hRT hLT hLTB hOnto hPos hPP hH2 hB hU hM hA hGal
  have hPP' : 0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0 := ⟨hPP.1, fun i t p => hPP.2 i t p _⟩
  exact
    { heckeR := hR
      heckeL := hL
      hecke := hHk
      gUnit := hGU
      gEquiv := hGE
      block := GlobalTheory.T.adjointLift_range_le_goodBlock_eigenspaces hCusp R F hLift hOk hC hEx hGE
      rowTest := hRT
      liftTest := hLT
      liftTestB := hLTB
      liftOnto := hOnto
      pos := hPos
      posScal := hPP
      levE := GlobalTheory.T.levelRows_eq_principalRows_of_type hCusp hHowe R F hLift hOk hC hEx hInert hGE hPos hPP' hB hRT
      h2P := hH2
      thmB := hB
      sumE := GlobalTheory.T.levelRows_orthogonalSum_of_parts hCusp hHowe R F hLift hOk hC hEx hInert hR hGE hPos hPP' hB
      unif := hU
      mLat := hM
      levW := GlobalTheory.T.baseLevelW_forms_eq_principalForms hCusp hHowe R F hLift hOk hC hEx hInert hGS hCD hME hGE hPos hPP' hA hLT hU
      thmA := hA
      sumW := GlobalTheory.T.baseLevelW_orthogonalSum_of_parts hCusp hHowe R F hLift hOk hC hEx hInert hGS hCD hME hR hGE hPos hPP' hB hU
      scalConj := hGal
      dimParts := GlobalTheory.T.baseLevel_goodForms_dims_agree_partwise hCusp R F hOk hC hEx hGS hCD hME hU }

end GlobalTheory
