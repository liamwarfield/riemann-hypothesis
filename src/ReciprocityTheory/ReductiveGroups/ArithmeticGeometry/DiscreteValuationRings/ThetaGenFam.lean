module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenFibre
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenTerms
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenRank
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

section Rel

variable {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

def SecCorr (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) (x : LB.Sec (LB.LinComb L φ' ε')) : Prop :=
  ∀ (j : K → L.ι) (j' : K' → L.ι), LB.Coh L φ j → LB.Coh L φ' j' → (∀ k k', φ k = φ' k' → j k = j' k') →
    rs (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) (s.f j) =
      rs (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) (x.f j')

private lemma exists_coh_extending_of_mem_wchart (hL : L.IsLB) (φ : K → (Y ⟶ X)) (φ' : K' → (Y ⟶ X)) (j' : K' → L.ι)
    (hj' : LB.Coh L φ' j') (y : Y) (hy : y ∈ LB.wchart L φ' j') :
    ∃ j : K → L.ι, LB.Coh L φ j ∧ (∀ k k', φ k = φ' k' → j k = j' k') ∧ y ∈ LB.wchart L φ j := by
  classical
  have memw : ∀ {T : Type} [Fintype T] (ψ : T → (Y ⟶ X)) (i : T → L.ι),
      y ∈ LB.wchart L ψ i ↔ ∀ t, (ψ t).base y ∈ L.U (i t) := by
    intro T _ ψ i
    first
    | exact Set.mem_iInter
    | simp [LB.wchart]
  have hcov : ∀ x : X, ∃ i, x ∈ L.U i := by
    intro x
    have hx : x ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  let g : (Y ⟶ X) → L.ι := fun ψ =>
    if h : ∃ k', φ' k' = ψ then j' h.choose else (hcov (ψ.base y)).choose
  refine ⟨fun k => g (φ k), ?_, ?_, ?_⟩
  · intro k₁ k₂ h
    show g (φ k₁) = g (φ k₂)
    rw [h]
  · intro k k' h
    have hex : ∃ k'', φ' k'' = φ k := ⟨k', h.symm⟩
    show g (φ k) = j' k'
    simp only [g, dif_pos hex]
    exact hj' _ _ (hex.choose_spec.trans h)
  · rw [memw]
    intro k
    have hy' := (memw φ' j').mp hy
    show (φ k).base y ∈ L.U (g (φ k))
    by_cases hex : ∃ k'', φ' k'' = φ k
    · simp only [g, dif_pos hex]
      have := hy' hex.choose
      rw [hex.choose_spec] at this
      exact this
    · simp only [g, dif_neg hex]
      exact (hcov _).choose_spec

private lemma sections_eq_of_locally_rs_eq {Z : Scheme.{0}} {W : Z.Opens} (a b : Γ(Z, W))
    (h : ∀ z ∈ W, ∃ (V : Z.Opens) (hV : V ≤ W), z ∈ V ∧ rs hV a = rs hV b) : a = b := by
  first
  | (apply TopCat.Presheaf.section_ext Z.sheaf W a b
     intro z hz
     obtain ⟨V, hV, hzV, he⟩ := h z hz
     have ha := congrArg (fun f => f.hom a) (Z.presheaf.germ_res (homOfLE hV) z hzV)
     have hb := congrArg (fun f => f.hom b) (Z.presheaf.germ_res (homOfLE hV) z hzV)
     have hc := congrArg (Z.presheaf.germ V z hzV).hom he
     exact ha.symm.trans (hc.trans hb))
  | (choose V hV hzV he using h
     exact TopCat.Sheaf.eq_of_locally_eq' Z.sheaf (fun z : W => V z.1 z.2) W
       (fun z => homOfLE (hV z.1 z.2))
       (by intro z hz; exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hzV z hz⟩) a b
       (fun z => he z.1 z.2))

lemma rs_resTop {Z : Scheme.{0}} {U V : Z.Opens} (h : V ≤ U) (c : Γ(Z, ⊤)) :
    rs h (resTop U c) = resTop V c := by
  first
  | rfl
  | (simp only [rs, resTop]; rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl)
  | (unfold rs; rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl)
  | (simp [rs, resTop, ← Functor.map_comp])

private lemma map_mul_rs {Z : Scheme.{0}} {U V : Z.Opens} (h : V ≤ U) (a b : Γ(Z, U)) :
    rs h (a * b) = rs h a * rs h b := by
  first
  | exact map_mul _ a b
  | simp [rs]

theorem secCorr_scal (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    {s₁ s₂ : LB.Sec (LB.LinComb L φ ε)} {x₁ x₂ : LB.Sec (LB.LinComb L φ' ε')}
    (h1 : SecCorr φ ε φ' ε' s₁ x₁) (h2 : SecCorr φ ε φ' ε' s₂ x₂) (c d : Γ(Y, ⊤))
    (hx : ∀ j' : K' → L.ι, resTop _ c * x₁.f j' = resTop _ d * x₂.f j') :
    ∀ j : K → L.ι, resTop _ c * s₁.f j = resTop _ d * s₂.f j := by
  have memE : ∀ z : Y, z ∈ LB.wchart L (K := Empty) (fun e => e.elim : Empty → (Y ⟶ X)) (fun e => e.elim) := by
    intro z
    first
    | exact Set.mem_iInter.mpr (fun e => e.elim)
    | simp [LB.wchart]
  have stepA : ∀ j : K → L.ι, LB.Coh L φ j → resTop _ c * s₁.f j = resTop _ d * s₂.f j := by
    intro j hj
    apply sections_eq_of_locally_rs_eq
    intro z hz
    obtain ⟨j', hj', hjj, hzj'⟩ := exists_coh_extending_of_mem_wchart (K := K') (K' := K) hL φ' φ j hj z hz
    have hcomp : ∀ k k', φ k = φ' k' → j k = j' k' := fun k k' h => (hjj k' k h.symm).symm
    refine ⟨LB.wchart L φ j ⊓ LB.wchart L φ' j', inf_le_left, ?_, ?_⟩
    · first
      | exact ⟨hz, hzj'⟩
      | exact TopologicalSpace.Opens.mem_inf.mpr ⟨hz, hzj'⟩
    · have e1 := h1 j j' hj hj' hcomp
      have e2 := h2 j j' hj hj' hcomp
      have e3 := congrArg (rs (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _)) (hx j')
      have m1 := map_mul_rs (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) (resTop _ c) (s₁.f j)
      have m2 := map_mul_rs (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) (resTop _ d) (s₂.f j)
      have m3 := map_mul_rs (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) (resTop _ c) (x₁.f j')
      have m4 := map_mul_rs (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) (resTop _ d) (x₂.f j')
      rw [rs_resTop] at m1 m2 m3 m4
      exact m1.trans ((congrArg (fun t => resTop _ c * t) e1).trans (m3.symm.trans (e3.trans
        (m4.trans ((congrArg (fun t => resTop _ d * t) e2.symm).trans m2.symm)))))
  intro j
  apply sections_eq_of_locally_rs_eq
  intro z hz
  obtain ⟨j'', hj'', -, hz''⟩ := exists_coh_extending_of_mem_wchart (K' := Empty) hL φ
    (fun e => e.elim) (fun e => e.elim) (fun e => e.elim) z (memE z)
  refine ⟨(LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j'', inf_le_left, ?_, ?_⟩
  · first
    | exact ⟨hz, hz''⟩
    | exact TopologicalSpace.Opens.mem_inf.mpr ⟨hz, hz''⟩
  · have e1 := s₁.compat j j''
    have e2 := s₂.compat j j''
    have e3 := congrArg (rs (inf_le_right : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j'' ≤ _))
      (stepA j'' hj'')
    have m1 := map_mul_rs (inf_le_left : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j'' ≤ _)
      (resTop _ c) (s₁.f j)
    have m2 := map_mul_rs (inf_le_left : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j'' ≤ _)
      (resTop _ d) (s₂.f j)
    have m3 := map_mul_rs (inf_le_right : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j'' ≤ _)
      (resTop _ c) (s₁.f j'')
    have m4 := map_mul_rs (inf_le_right : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j'' ≤ _)
      (resTop _ d) (s₂.f j'')
    rw [rs_resTop] at m1 m2 m3 m4
    have key := m3.symm.trans (e3.trans m4)
    rw [m1, m2]
    dsimp only [rs]
    rw [e1, e2, _root_.mul_left_comm, _root_.mul_left_comm (resTop _ d)]
    congr 1

end Rel

section SameSum

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (D : DegData R I)

lemma c_zero : D.toPre.c 0 = 1 := by
  have h := D.toPre.c_add 0 0
  rw [add_zero] at h
  have h' : D.toPre.c 0 * D.toPre.c 0 = D.toPre.c 0 * 1 := by
    rw [_root_.mul_one]
    exact h.symm
  exact _root_.mul_left_cancel h'

lemma famφB0_one : D.toPre.famφB 0 1 = 𝟙 _ := by
  have h1 : (toUnit D.toPre.P.A ≫ D.toPre.c 0) = 1 := by
    rw [c_zero D]
    first
    | simp [Hom.one_def]
    | (rw [Hom.one_def, Hom.one_def, ← Category.assoc]; congr 1)
  show (padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit _ ≫ D.toPre.c 0)).left = 𝟙 _
  rw [h1]
  show ((𝟙 D.toPre.P.A) * 1 : D.toPre.P.A ⟶ D.toPre.P.A).left = _
  rw [_root_.mul_one]
  first
  | rfl
  | simp

lemma famφB0_two : D.toPre.famφB 0 2 = D.toPre.famφB 0 3 := by
  show (toUnit D.toPre.P.A ≫ D.toPre.c 0).left = (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left
  rw [c_zero D, Hom.one_def]
  first
  | simp
  | (congr 1; rw [← Category.assoc]; congr 1)

lemma sameSum_famφB0 : LB.SameSum (D.toPre.famφB 0) (DegPre.famε 1)
    (fun _ : Fin 1 => 𝟙 D.toPre.P.A.left) (fun _ => ((1 : ℕ) : ℤ)) := by
  intro ψ
  have h0 : D.toPre.famφB 0 0 = 𝟙 _ := rfl
  have e1 := famφB0_one D
  have e2 := famφB0_two D
  rw [Fin.sum_univ_four, Fin.sum_univ_one]
  split_ifs
  all_goals first
    | (exfalso; exact ‹¬ 𝟙 D.toPre.P.A.left = ψ› (h0.symm.trans ‹D.toPre.famφB 0 0 = ψ›))
    | (exfalso; exact ‹¬ D.toPre.famφB 0 0 = ψ› (h0.trans ‹𝟙 D.toPre.P.A.left = ψ›))
    | (exfalso; exact ‹¬ 𝟙 D.toPre.P.A.left = ψ› (e1.symm.trans ‹D.toPre.famφB 0 1 = ψ›))
    | (exfalso; exact ‹¬ D.toPre.famφB 0 1 = ψ› (e1.trans ‹𝟙 D.toPre.P.A.left = ψ›))
    | (exfalso; exact ‹¬ D.toPre.famφB 0 3 = ψ› (e2.symm.trans ‹D.toPre.famφB 0 2 = ψ›))
    | (exfalso; exact ‹¬ D.toPre.famφB 0 2 = ψ› (e2.trans ‹D.toPre.famφB 0 3 = ψ›))
    | (simp [DegPre.famε]; done)
    | rfl
    | decide

end SameSum

section Rank

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] {I : Ideal R} (D : DegData R I)


set_option maxHeartbeats 1000000 in
theorem secB_rank_one (hLaws : Laws) (t s' : D.toPre.SecB 1 0) :
    ∃ c₀ c' : R, (∀ j, toW D.toPre.P.A.hom _ c₀ * s'.f j = toW D.toPre.P.A.hom _ c' * t.f j) ∧
      (c₀ = 0 → ∀ j, t.f j = 0) := by
  classical
  let pullSection {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
      (φ : K → (Y ⟶ X)) (ε : K → ℤ) (s : LB.Sec (LB.LinComb L φ ε))
      (f : Z ⟶ Y) (φ' : K → (Z ⟶ X)) (hφ : ∀ k, φ' k = f ≫ φ k) :
      LB.Sec (LB.LinComb L φ' ε) := by
    obtain rfl : φ' = fun k => f ≫ φ k := funext hφ
    exact pullSec L φ ε s f
  have pullSection_f {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
      (φ : K → (Y ⟶ X)) (ε : K → ℤ) (s : LB.Sec (LB.LinComb L φ ε))
      (f : Z ⟶ Y) (φ' : K → (Z ⟶ X)) (hφ : ∀ k, φ' k = f ≫ φ k) (j : K → L.ι) :
      (pullSection L φ ε s f φ' hφ).f j =
        (Z.presheaf.map (homOfLE (wchart_le_preimage L f φ φ' hφ j)).op).hom ((f.app _).hom (s.f j)) := by
    obtain rfl : φ' = fun k => f ≫ φ k := funext hφ
    rfl
  have hL := D.toPre.P.isLB
  obtain ⟨V, hpV, b, hb⟩ := hLaws.secBaseChange (Spec (CommRingCat.of R)) D.toPre.P 1 le_rfl
    (IsLocalRing.closedPoint R)
  have hV : V = ⊤ := eq_top_of_closedPoint_mem V hpV
  let t0 : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Spec (CommRingCat.of R))) V).left :=
    IsOpenImmersion.lift V.ι (𝟙 _) (by
      rintro _ ⟨x, rfl⟩
      refine ⟨⟨x, ?_⟩, rfl⟩
      rw [hV]; trivial)
  have ht0 : t0 ≫ V.ι = 𝟙 _ := IsOpenImmersion.lift_fac _ _ _
  set T := baseAt t0 with hTdef
  have hT : T.hom = 𝟙 _ := by
    show t0 ≫ V.ι ≫ 𝟙 _ = 𝟙 _
    rw [Category.comp_id, ht0]
  let b' : Fin (1 ^ D.toPre.P.g) → LB.Sec (LPow D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) T) := fun i =>
    pullSection D.toPre.P.L _ _ (b i) (homAt t0 ▷ D.toPre.P.A).left (fun _ => (snd T D.toPre.P.A).left)
      (fun _ => by rw [← Over.comp_left, whiskerRight_snd])
  have hpull : ∀ i, IsPullSec D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) (homAt t0 ▷ D.toPre.P.A)
      (whiskerRight_snd (homAt t0) D.toPre.P.A) (b i) (b' i) := fun i j => pullSection_f _ _ _ _ _ _ _ j
  obtain ⟨-, hspan⟩ := hb R t0 b' hpull
  have hsub : Subsingleton (Fin (1 ^ D.toPre.P.g)) := by rw [one_pow]; infer_instance
  have i0 : Fin (1 ^ D.toPre.P.g) := ⟨0, by rw [one_pow]; exact Nat.one_pos⟩
  have mem : ∀ x : LB.Sec (LPow D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) T), ∃ c : Γ(T.left, ⊤),
      (SecM.ofSec D.toPre.P.A x : SecM D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) T) =
        c • SecM.ofSec D.toPre.P.A (b' i0) := by
    intro x
    have hx : (SecM.ofSec D.toPre.P.A x : SecM D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) T) ∈
        Submodule.span Γ(T.left, ⊤) (Set.range fun i => (SecM.ofSec D.toPre.P.A (b' i) :
          SecM D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) T)) := by rw [hspan]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
    refine ⟨c i0, ?_⟩
    rw [← hc, Finset.sum_eq_single i0 (fun i _ hi => absurd (Subsingleton.elim i i0) hi)
      (fun h => absurd (Finset.mem_univ i0) h)]
  obtain ⟨ut, hut⟩ := sec_transport hL (sameSum_famφB0 D) t
  obtain ⟨us, hus⟩ := sec_transport hL (sameSum_famφB0 D) s'
  set π₂ := (snd T D.toPre.P.A).left with hπ₂
  have : IsIso T.hom := by rw [hT]; infer_instance
  have hiso : IsIso π₂ := by
    show IsIso (pullback.snd T.hom D.toPre.P.A.hom)
    infer_instance
  let pl : LB.Sec (LB.LinComb D.toPre.P.L (fun _ : Fin 1 => 𝟙 D.toPre.P.A.left) (fun _ => ((1 : ℕ) : ℤ))) →
      LB.Sec (LPow D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) T) := fun u =>
    pullSection D.toPre.P.L _ _ u π₂ (fun _ => π₂) (fun _ => (Category.comp_id _).symm)
  obtain ⟨c0, hc0⟩ := mem (pl ut)
  obtain ⟨c1, hc1⟩ := mem (pl us)
  have hrel : c0 • (SecM.ofSec D.toPre.P.A (pl us) : SecM D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) T) =
      c1 • SecM.ofSec D.toPre.P.A (pl ut) := by
    simp only [hc0, hc1, smul_smul, mul_comm c0 c1]
  have hfstp : (fst T D.toPre.P.A).left = π₂ ≫ D.toPre.P.A.hom := by
    have h1 : (fst T D.toPre.P.A).left ≫ T.hom = (T ⊗ D.toPre.P.A).hom := Over.w _
    have h2 : π₂ ≫ D.toPre.P.A.hom = (T ⊗ D.toPre.P.A).hom := Over.w _
    rw [hT, Category.comp_id] at h1
    rw [h1, h2]
  have eR' : ∀ c : Γ(T.left, ⊤), (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c) = c :=
    fun c => by rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
  have hlift : ∀ (W : (T ⊗ D.toPre.P.A).left.Opens) (c : Γ(T.left, ⊤)), liftHom D.toPre.P.A W c =
      toW (π₂ ≫ D.toPre.P.A.hom) W ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c) := by
    intro W c
    rw [← toW_congr hfstp W]
    simp only [liftHom, toW, RingHom.comp_apply]
    rw [eR']
    rfl
  have key : ∀ (u₁ u₂ : LB.Sec (LB.LinComb D.toPre.P.L (fun _ : Fin 1 => 𝟙 D.toPre.P.A.left)
      (fun _ => ((1 : ℕ) : ℤ)))) (c c' : Γ(T.left, ⊤)),
      c • (SecM.ofSec D.toPre.P.A (pl u₁) : SecM D.toPre.P.A D.toPre.P.L ((1 : ℕ) : ℤ) T) =
        c' • SecM.ofSec D.toPre.P.A (pl u₂) →
      ∀ j : Fin 1 → D.toPre.P.L.ι, toW D.toPre.P.A.hom _ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c) * u₁.f j =
        toW D.toPre.P.A.hom _ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c') * u₂.f j := by
    intro u₁ u₂ c c' h j
    have hj := congrArg (fun z => z.1 j) h
    change liftHom _ _ c * (pl u₁).f j = liftHom _ _ c' * (pl u₂).f j at hj
    rw [hlift, hlift] at hj
    have h₁ := pullSection_f D.toPre.P.L _ _ u₁ π₂ (fun _ => π₂) (fun _ => (Category.comp_id _).symm) j
    have h₂ := pullSection_f D.toPre.P.L _ _ u₂ π₂ (fun _ => π₂) (fun _ => (Category.comp_id _).symm) j
    simp only [LPow, pl, h₁, h₂] at hj
    apply Scheme.Hom.app_injective π₂
    apply map_inj_of_le_ge (wchart_le_preimage D.toPre.P.L π₂ (fun _ => 𝟙 _) (fun _ => π₂)
      (fun _ => (Category.comp_id _).symm) j) (fun x hx => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k)
    erw [map_mul, map_mul, app_toW, map_mul, map_mul, app_toW, toW_res, toW_res]
    exact hj
  have e1 := key us ut c0 c1 hrel
  have hsc := secCorr_scal hL _ _ _ _ hus hut (scal D.toPre.P.A.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c0))
    (scal D.toPre.P.A.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c1)) (fun j' => by
      rw [resTop_scal, resTop_scal]; exact e1 j')
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c0, (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c1,
    fun j => by rw [← resTop_scal, ← resTop_scal]; exact hsc j, fun h0 => ?_⟩
  have hc00 : c0 = 0 := by rw [← eR' c0, h0, map_zero]
  have hut0 : ∀ j : Fin 1 → D.toPre.P.L.ι, ut.f j = 0 := by
    have h := key ut ut 1 0 (by rw [one_smul, zero_smul, hc0, hc00, zero_smul])
    intro j
    have hj := h j
    rw [map_one, map_zero, map_one, map_zero, _root_.one_mul, zero_mul] at hj
    exact hj
  have ht := secCorr_scal hL _ _ _ _ hut hut 1 0 (fun j' => by rw [hut0 j', mul_zero, mul_zero])
  intro j
  have hj := ht j
  simp only [resTop, map_one, map_zero, _root_.one_mul, zero_mul] at hj
  exact hj

end Rank

end ReciprocityTheory.ChartRestriction.G.DVR.TG
end
end

set_option autoImplicit false
set_option linter.overlappingInstances false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

lemma isUnit_toW_of_K {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of (FractionRing R))) (W : Y.Opens) {r : R}
    (hr : r ≠ 0) : IsUnit (toW (q ≫ jK R) W r) := by
  have e1 : toW (q ≫ jK R) W r = (q.appLE ⊤ W le_top).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) r)) := by
    rw [toW, RingHom.comp_apply]
    rw [← Scheme.Hom.appLE_comp_appLE (f := q) (g := jK R) ⊤ ⊤ W le_top le_top]
    rw [CommRingCat.comp_apply]
    congr 1
    have := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    erw [Scheme.Hom.appLE_eq_app]
    exact this.symm
  rw [e1]
  exact ((isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr)).map _).map _

lemma base_eq_of_isDominant {X Y Z W : Scheme.{0}} {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s]
    (h : f ≫ s = g ≫ s) (i0 : W ⟶ X) [IsDominant i0] (hU : i0 ≫ f = i0 ≫ g) (x : X) : f.base x = g.base x := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let U' : Over Z := Over.mk (i0 ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g
  let i0' : U' ⟶ X' := Over.homMk i0
  have : IsSeparated Y'.hom := ‹_›
  have : IsDominant (equalizer.ι f' g').left := by
    apply +allowSynthFailures IsDominant.of_comp (equalizer.lift i0' ?_).left
    · rwa [← Over.comp_left, equalizer.lift_ι]
    · ext1; exact hU
  have : Surjective (equalizer.ι f' g').left :=
    surjective_of_isDominant_of_isClosed_range _ (Scheme.Hom.isClosedEmbedding _).isClosed_range
  obtain ⟨z, rfl⟩ := (equalizer.ι f' g').left.surjective x
  have e := congr($(equalizer.condition f' g').left)
  rw [Over.comp_left, Over.comp_left] at e
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
  exact congrArg (fun φ => φ.base z) e

section PrB

variable (D) in
lemma prB_std : IsSchemeTheoreticallyDominant (DegPre.prB D.toPre (FractionRing R)).left ∧
    QuasiCompact (DegPre.prB D.toPre (FractionRing R)).left := by
  have := flat_B (D := D)
  have := isDominant_jF R
  have : IsSchemeTheoreticallyDominant (jF R) := IsSchemeTheoreticallyDominant.of_isDominant _
  have : IsIso (jFK (R := R) (FractionRing R)) := by
    have : IsIso (CommRingCat.ofHom (algebraMap (FractionRing R) (FractionRing R))) := by
      rw [Algebra.algebraMap_self]
      exact inferInstanceAs (IsIso (𝟙 (CommRingCat.of (FractionRing R))))
    infer_instance
  have : IsSchemeTheoreticallyDominant (TF (R := R) (FractionRing R)).hom :=
    inferInstanceAs (IsSchemeTheoreticallyDominant (jFK (R := R) (FractionRing R) ≫ jF R))
  have : QuasiCompact (TF (R := R) (FractionRing R)).hom :=
    inferInstanceAs (QuasiCompact (jFK (R := R) (FractionRing R) ≫ jF R))
  exact ⟨inferInstanceAs (IsSchemeTheoreticallyDominant (pullback.snd _ _)),
    inferInstanceAs (QuasiCompact (pullback.snd _ _))⟩

end PrB

lemma toW_of_K {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of (FractionRing R))) (W : Y.Opens) (r : R) :
    toW (q ≫ jK R) W r = (q.appLE ⊤ W le_top).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) r)) := by
  rw [toW, RingHom.comp_apply]
  rw [← Scheme.Hom.appLE_comp_appLE (f := q) (g := jK R) ⊤ ⊤ W le_top le_top]
  rw [CommRingCat.comp_apply]
  congr 1
  have := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  erw [Scheme.Hom.appLE_eq_app]
  exact this.symm

lemma hBF : (DegPre.BF D.toPre (FractionRing R)).hom =
    (pullback.fst _ _ ≫ jFK (R := R) (FractionRing R)) ≫ jK R := by
  simp [DegPre.BF, TF]

lemma constBF_alg (a : R) (W : (DegPre.BF D.toPre (FractionRing R)).left.Opens) :
    DegPre.constBF D.toPre (FractionRing R) (algebraMap R (FractionRing R) a) W =
      toW (DegPre.BF D.toPre (FractionRing R)).hom W a := by
  rw [toW_congr hBF, toW_of_K]
  rw [← Scheme.Hom.appLE_comp_appLE (f := pullback.fst _ _) (g := jFK (R := R) (FractionRing R)) ⊤ ⊤ W le_top le_top]
  rw [CommRingCat.comp_apply]
  have := congrArg (fun φ => φ.hom (algebraMap R (FractionRing R) a))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap (FractionRing R) (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, Algebra.algebraMap_self,
    RingHom.id_apply] at this
  erw [Scheme.Hom.appLE_eq_app, ← this]
  rfl


set_option maxHeartbeats 1000000 in
theorem terms_vanish [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ) (hI : I = maximalIdeal R)
    (F : Fam D.toPre (FractionRing R) 1) (g : ∀ α, D.toPre.SecB 1 α)
    (hgF : ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε 1) (F.s α)
      (D.toPre.famφB α) (DegPre.famε 1) (g α) (DegPre.prB D.toPre (FractionRing R)).left 1) :
    ∀ mu, mu ≠ 0 → ∀ j, (pullback.fst D.toPre.P.A.hom (thick R I 0)).app _ ((g mu).f j) = 0 := by
  subst hI
  classical
  choose Q hQ using QForm.exists_QVal hϖ D
  have hQ' : QForm.IsQ D.toPre ϖ Q := hQ
  let castVal : ℕ∞ →+o WithTop ℚ :=
    { toFun := WithTop.map (Nat.cast : ℕ → ℚ)
      map_zero' := rfl
      map_add' := WithTop.map_add (Nat.castAddMonoidHom ℚ)
      monotone' := ENat.map_natCast_strictMono.monotone }
  let vR := (IsDiscreteValuationRing.addVal R).map castVal rfl
  have hvR : nonZeroDivisors R ≤ vR.toValuation.supp.primeCompl := by
    intro r hr
    change WithTop.map (Nat.cast : ℕ → ℚ) (IsDiscreteValuationRing.addVal R r) ≠ ⊤
    have h := IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr (nonZeroDivisors.ne_zero hr)
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
    rw [← hn]
    exact WithTop.coe_ne_top
  let w := vR.toValuation.extendToLocalization hvR (FractionRing R)
  let v := AddValuation.ofValuation w
  have hv : ValOver ϖ (FractionRing R) v := by
    rintro c n ⟨u, rfl⟩
    rw [Algebra.algebraMap_self, RingHom.id_apply]
    change OrderDual.ofDual (Multiplicative.toAdd (w (_ ^ n * _))) = _
    rw [map_mul, map_zpow₀, Valuation.extendToLocalization_apply_map_apply,
      Valuation.extendToLocalization_apply_map_apply]
    change n • WithTop.map (Nat.cast : ℕ → ℚ) (IsDiscreteValuationRing.addVal R ϖ) +
      WithTop.map (Nat.cast : ℕ → ℚ) (IsDiscreteValuationRing.addVal R (u : R)) = _
    rw [IsDiscreteValuationRing.addVal_uniformizer hϖ, IsDiscreteValuationRing.addVal_eq_zero_of_unit]
    change n • ((1 : ℚ) : WithTop ℚ) + 0 = _
    rw [add_zero, ← zsmul_one (R := ℚ) n]
    cases n with
    | ofNat k =>
      change (k : ℤ) • ((1 : ℚ) : WithTop ℚ) = ↑((k : ℤ) • (1 : ℚ))
      rw [natCast_zsmul, natCast_zsmul, WithTop.coe_nsmul]
    | negSucc k =>
      rw [negSucc_zsmul, negSucc_zsmul, WithTop.LinearOrderedAddCommGroup.coe_neg,
        WithTop.coe_nsmul]
  obtain ⟨hstd, hqc⟩ := prB_std D
  have hs0 : VGe D (FractionRing R) v 1 0 (F.s 0) 0 := by
    refine ⟨1, fun _ => 1, fun _ => g 0, fun _ => F.s 0, fun _ => hgF 0, fun _ => by simp, fun j => ?_⟩
    rw [Fin.sum_univ_one, ← map_one (algebraMap R (FractionRing R)), constBF_alg, map_one, _root_.one_mul]
  intro mu hmu
  have hm := SectionScalarValuation.fe_move hϖ hQ' hv 1 mu 0 F hs0
  have e01 : (0 : D.toPre.X) + 1 • mu = mu := by simp
  rw [e01] at hm
  have hb0 : QForm.bOf D.toPre Q mu 0 = 0 := by
    simp [QForm.bOf, QForm.Q_zero hϖ D hQ']
  have hq1 : 1 ≤ Q mu := QForm.Q_pos hϖ D hQ' hmu
  obtain ⟨N, a, σ, σF, hσF, hva, hsum⟩ := hm
  have hab : ∀ i, ∃ b : R, a i = algebraMap R (FractionRing R) (ϖ * b) := by
    intro i
    by_cases ha : a i = 0
    · exact ⟨0, by rw [ha, mul_zero, map_zero]⟩
    obtain ⟨n, hn⟩ := hasVal_of_ne_zero hϖ ha
    have h1 := hva i
    have hvn := hv _ _ hn
    rw [Algebra.algebraMap_self, RingHom.id_apply] at hvn
    rw [hvn, hb0] at h1
    have hn1 : 1 ≤ n := by
      have : ((0 : ℚ) + ((1 * Q mu + 0 : ℤ) : ℚ)) ≤ (n : ℚ) := by exact_mod_cast h1
      rw [zero_add] at this
      have : (1 : ℚ) ≤ n := le_trans (by exact_mod_cast (by omega : (1 : ℤ) ≤ 1 * Q mu + 0)) this
      exact_mod_cast this
    obtain ⟨u, hu⟩ := hn
    obtain ⟨d, hd⟩ : ∃ d : ℕ, n = d + 1 := ⟨(n - 1).toNat, by omega⟩
    refine ⟨ϖ ^ d * u, ?_⟩
    rw [hu, hd, zpow_add₀ (by exact (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 hϖ.ne_zero),
      zpow_natCast, zpow_one]
    simp only [map_mul, map_pow]
    ring
  choose b hb using hab
  have := flat_B (D := D)
  have hdom : IsDominant (DegPre.prB D.toPre (FractionRing R)).left := inferInstance
  have key : ∀ j₂ : Fin 4 → D.toPre.P.L.ι,
      (∀ k k', (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.famφB mu k =
        (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.famφB mu k' → j₂ k = j₂ k') →
      (g mu).f j₂ = toW D.toPre.P.A.hom _ ϖ *
        ∑ i, toW D.toPre.P.A.hom _ (b i) * (σ i).f j₂ := by
    intro j₂ hcoh
    have hc : LB.Coh D.toPre.P.L (Sum.elim (DegPre.famφ D.toPre (FractionRing R) mu)
        (fun k => (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.famφB mu k)) (Sum.elim j₂ j₂) := by
      intro x y hxy
      rcases x with k | k <;> rcases y with k' | k' <;>
        simp only [Sum.elim_inl, Sum.elim_inr, GC.famφ_eq] at hxy ⊢ <;> exact hcoh k k' hxy
    have E1 := hgF mu j₂ j₂ hc
    have E2 := hsum j₂
    have E3 := fun i => hσF i j₂ j₂ hc
    have hle : (DegPre.prB D.toPre (FractionRing R)).left ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB mu) j₂ ≤
        LB.wchart D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) mu) j₂ ⊓
          LB.wchart D.toPre.P.L (fun k => (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.famφB mu k) j₂ := by
      intro x hx
      refine ⟨Set.mem_iInter.2 fun k => ?_, Set.mem_iInter.2 fun k => ?_⟩
      · rw [GC.famφ_eq]; exact Set.mem_iInter.1 hx k
      · exact Set.mem_iInter.1 hx k
    apply Scheme.Hom.app_injective (DegPre.prB D.toPre (FractionRing R)).left
    apply map_inj_of_le_ge (inf_le_right.trans (wchart_comp_le _ _ j₂)) hle
    refine E1.trans ?_
    have hw : (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.P.A.hom = (DegPre.BF D.toPre (FractionRing R)).hom :=
      Over.w _
    rw [show resTop _ (1 : Γ((DegPre.BF D.toPre (FractionRing R)).left, ⊤)) = 1 from map_one _, _root_.one_mul, E2]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, app_toW, toW_congr hw]
    erw [map_sum, map_mul, map_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have E3i := E3 i
    rw [show resTop _ (1 : Γ((DegPre.BF D.toPre (FractionRing R)).left, ⊤)) = 1 from map_one _, _root_.one_mul] at E3i
    erw [map_mul, map_mul, ← E3i, hb i, constBF_alg, toW_res, toW_res, toW_res, map_mul]
    rw [_root_.mul_assoc]
    rfl
  intro (j : Fin 4 → D.toPre.P.L.ι)
  set π := pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0)
  refine TopCat.Presheaf.section_ext (pullback D.toPre.P.A.hom (thick R (maximalIdeal R) 0)).sheaf _ _ 0
    fun z hz => ?_
  choose ch hch using WeightPf.exists_chart D.toPre.P.L D.toPre.P.isLB
  let j₂ : Fin 4 → D.toPre.P.L.ι := fun k => ch ((D.toPre.famφB mu k).base (π.base z))
  have hcoh : ∀ k k', (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.famφB mu k =
      (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.famφB mu k' → j₂ k = j₂ k' := fun k k' h =>
    congrArg ch (base_eq_of_isDominant D.toPre.P.A.hom
      ((GC.famφB_over mu k).trans (GC.famφB_over mu k').symm) _ h (π.base z))
  have hK := key j₂ hcoh
  have hV : LB.wchart D.toPre.P.L (D.toPre.famφB mu) j ⊓ LB.wchart D.toPre.P.L (D.toPre.famφB mu) j₂ ≤
      LB.wchart D.toPre.P.L (D.toPre.famφB mu) j := inf_le_left
  have hzV : z ∈ π ⁻¹ᵁ (LB.wchart D.toPre.P.L (D.toPre.famφB mu) j ⊓ LB.wchart D.toPre.P.L (D.toPre.famφB mu) j₂) :=
    ⟨hz, Set.mem_iInter.2 fun k => hch _⟩
  have hres : (π.app _) ((D.toPre.P.A.left.presheaf.map (homOfLE hV).op).hom ((g mu).f j)) = 0 := by
    have c := (g mu).compat j j₂
    have hm : ϖ ∈ maximalIdeal R ^ (0 + 1) := by
      rw [zero_add, pow_one]; exact hϖ.not_isUnit
    have h2 : (π.app (LB.wchart D.toPre.P.L (D.toPre.famφB mu) j ⊓ LB.wchart D.toPre.P.L (D.toPre.famφB mu) j₂))
        ((D.toPre.P.A.left.presheaf.map (homOfLE (inf_le_right : LB.wchart D.toPre.P.L (D.toPre.famφB mu) j ⊓
          LB.wchart D.toPre.P.L (D.toPre.famφB mu) j₂ ≤ LB.wchart D.toPre.P.L (D.toPre.famφB mu) j₂)).op).hom
          ((g mu).f j₂)) = 0 := by
      rw [hK]
      erw [map_mul, toW_res, map_mul, app_toW_of_mem D.toPre.P.A.hom _ _ hm, zero_mul]
    erw [c, map_mul, h2]
    rw [mul_zero]
  have hz2 : π ⁻¹ᵁ (LB.wchart D.toPre.P.L (D.toPre.famφB mu) j ⊓ LB.wchart D.toPre.P.L (D.toPre.famφB mu) j₂) ≤
      π ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB mu) j := π.preimage_mono hV
  show (pullback D.toPre.P.A.hom (thick R (maximalIdeal R) 0)).presheaf.germ _ z hz _ =
    (pullback D.toPre.P.A.hom (thick R (maximalIdeal R) 0)).presheaf.germ _ z hz 0
  erw [← TopCat.Presheaf.germ_res_apply _ (homOfLE hz2) z hzV, app_res π hV, hres, map_zero, map_zero]

end ReciprocityTheory.ChartRestriction.G.DVR.TG
end
end

set_option autoImplicit false
set_option linter.overlappingInstances false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]


set_option maxHeartbeats 1000000 in
theorem leading_expansion_term_ne_zero [IsDiscreteValuationRing R] (hI : I = maximalIdeal R) (U : Unif I D A G) (s : H0 U.LG.L 1)
    (hs : NonzeroOnSpecial U s) (g : ∀ α, D.toPre.SecB 1 α) (hexp : U.ExpandsAt 0 1 s g)
    (hv : ∀ mu, mu ≠ 0 → ∀ j, (pullback.fst D.toPre.P.A.hom (thick R I 0)).app _ ((g mu).f j) = 0) :
    ¬ ∀ j, (pullback.fst D.toPre.P.A.hom (thick R I 0)).app _ ((g 0).f j) = 0 := by
  intro h0
  subst hI

  have hloc : ∀ {X : Scheme.{0}} {W : X.Opens} (y : Γ(X, W)),
      (∀ x ∈ W, ∃ V : X.Opens, ∃ hV : V ≤ W, x ∈ V ∧ (X.presheaf.map (homOfLE hV).op).hom y = 0) →
        y = 0 := by
    intro X W y h
    choose V hV hxV hy using h
    refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun p : W => V p.1 p.2) W
      (fun p => homOfLE (hV p.1 p.2)) ?_ y 0 ?_
    · intro x hx
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV x hx⟩
    · intro p
      exact (hy p.1 p.2).trans (map_zero _).symm

  have hvan : ∀ (α : D.toPre.X) (j : Fin 4 → D.toPre.P.L.ι),
      ((U.gt 0).pG.left.app (D.toPre.P.L.wchart (D.toPre.famφB α) j)).hom ((g α).f j) = 0 := by
    intro α j
    have hz : ((pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0)).app
        ((D.toPre.P.L.LinComb (D.toPre.famφB α) (DegPre.famε 1)).U j)).hom ((g α).f j) = 0 := by
      by_cases hα : α = 0
      · subst hα
        exact h0 j
      · exact hv α hα j
    show (((U.gt 0).q.left ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0)).app
        ((D.toPre.P.L.LinComb (D.toPre.famφB α) (DegPre.famε 1)).U j)).hom ((g α).f j) = 0
    try rw [Scheme.comp_app]
    exact (congrArg (fun z => ((U.gt 0).q.left.app _).hom z) hz).trans (map_zero _)
  unfold NonzeroOnSpecial at hs
  obtain ⟨j, hj⟩ := hs
  obtain ⟨S, -, hS⟩ := hexp
  choose ch hch using fun y : D.toPre.P.A.left => WeightPf.exists_chart D.toPre.P.L D.toPre.P.isLB y
  apply hj
  refine hloc _ fun x hx => ?_
  refine ⟨U.expW 0 (fun _ => ch ((U.gt 0).pG.left.base x), fun _ => j 0) j S
      (fun α i => ch (((U.gt 0).pG.left ≫ D.toPre.famφB α i).base x))
      (fun α i => ch ((D.toPre.Oφ (U.gt 0).pG α i).base x)),
    inf_le_left.trans inf_le_right, ?_, ?_⟩
  · refine TopologicalSpace.Opens.mem_inf.mpr ⟨TopologicalSpace.Opens.mem_inf.mpr
      ⟨TopologicalSpace.Opens.mem_inf.mpr ⟨?_, ?_⟩, hx⟩, ?_⟩
    · exact Set.mem_iInter.mpr fun _ => hch _
    · exact Set.mem_iInter.mpr fun _ => Set.mem_iInter.mp hx 0
    · exact WeightPf.mem_finset_inf S _ x fun α _ => TopologicalSpace.Opens.mem_inf.mpr
        ⟨Set.mem_iInter.mpr fun i => hch _, Set.mem_iInter.mpr fun i => hch _⟩
  · have e := hS (fun _ => ch ((U.gt 0).pG.left.base x), fun _ => j 0) j
      (fun α i => ch (((U.gt 0).pG.left ≫ D.toPre.famφB α i).base x))
      (fun α i => ch ((D.toPre.Oφ (U.gt 0).pG α i).base x)) rfl (by
        intro a b hab
        rcases a with _ | a | a <;> rcases b with _ | b | b <;>
          exact congrArg (fun f => ch (f.base x)) hab)
    rw [Finset.sum_eq_zero (fun α _ => by rw [hvan, map_zero, zero_mul]), ← Units.val_pow_eq_pow_val] at e
    exact (Units.mul_right_eq_zero _).mp e

theorem generates_of_ne (hLaws : Laws) [IsDiscreteValuationRing R] (hI : I = maximalIdeal R)
    (t : D.toPre.SecB 1 0) (ht : ¬ ∀ j, (pullback.fst D.toPre.P.A.hom (thick R I 0)).app _ (t.f j) = 0) :
    SecBGenerates 1 0 t := by
  unfold SecBGenerates
  intro s'
  obtain ⟨c₀, c', h, h0⟩ := secB_rank_one (hLaws := hLaws) (t := t) (s' := s')
  haveI : Flat D.toPre.P.A.hom := flat_B

  have hc₀ : c₀ ≠ 0 := by
    intro hz
    apply ht
    intro j
    rw [h0 hz j, map_zero]

  have hdiv : ∃ a : R, c' = c₀ * a := by
    obtain ⟨m, hm | hm⟩ := ValuationRing.cond c₀ c'
    · exact ⟨m, hm.symm⟩
    · by_cases hmu : IsUnit m
      · obtain ⟨u, rfl⟩ := hmu
        refine ⟨↑u⁻¹, ?_⟩
        rw [← hm, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
      · exfalso
        have hmI : m ∈ I ^ (0 + 1) := by
          rw [zero_add, pow_one, hI]
          exact (IsLocalRing.mem_maximalIdeal m).mpr hmu
        have hc' : c' ≠ 0 := by
          rintro rfl
          exact hc₀ (by rw [← hm, zero_mul])
        apply ht
        intro j
        have hj : t.f j = toW D.toPre.P.A.hom _ m * s'.f j := by
          refine (sub_eq_zero.mp (toW_mul_eq_zero D.toPre.P.A.hom _ hc' ?_)).symm
          rw [mul_sub, ← _root_.mul_assoc, ← map_mul, hm, h j, sub_self]
        rw [hj, map_mul, app_toW_of_mem D.toPre.P.A.hom (I ^ (0 + 1)) _ hmI, zero_mul]
  obtain ⟨a, rfl⟩ := hdiv
  have hSa : SecIsMul D.toPre.P.A.hom a s' t := by
    intro j
    rw [resTop_scal]
    refine sub_eq_zero.mp (toW_mul_eq_zero D.toPre.P.A.hom _ hc₀ ?_)
    rw [mul_sub, h j, map_mul, _root_.mul_assoc, sub_self]
  refine ⟨a, hSa, fun b hb => ?_⟩
  by_contra hne
  apply ht
  intro j
  have e1 := hb j
  have e2 := hSa j
  rw [resTop_scal] at e1 e2
  have hz : t.f j = 0 := by
    refine toW_mul_eq_zero D.toPre.P.A.hom _ (sub_ne_zero.mpr hne) ?_
    rw [map_sub, sub_mul, ← e1, ← e2, sub_self]
  rw [hz, map_zero]

end ReciprocityTheory.ChartRestriction.G.DVR.TG
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing QForm SectionScalarValuation

section FEGen

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]

theorem exists_fe_gen (hϖ : Irreducible ϖ) {Q : D.toPre.X → ℤ} (hQ : IsQ D.toPre ϖ Q) (k : ℕ)
    (mu α : D.toPre.X) :
    ∃ u : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.deltaφ D.toPre F k α mu) (DegPre.deltaε k)), u.IsGen ∧
      LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left)
        (DegPre.famMult D.toPre F k mu α) := by
  classical
  have hL := D.toPre.P.isLB
  obtain ⟨Ix, _, φV, εV, e', he', hC, c₀, hc₀, hval⟩ :=
    ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.famMult_data D hϖ hQ k mu α
  obtain ⟨eB, heB, veB⟩ := exists_eB D.toPre k α mu e' he' hC
  have hc0 : c₀ ≠ 0 := ne_zero_of_hasVal hϖ hc₀
  set c : F := algebraMap (FractionRing V) F c₀ with hc
  have hcne : c ≠ 0 := (map_ne_zero _).2 hc0
  let cU : Γ((DegPre.BF D.toPre F).left, ⊤)ˣ :=
    ⟨gF D.toPre F c, gF D.toPre F c⁻¹, by rw [← map_mul, mul_inv_cancel₀ hcne, map_one],
      by rw [← map_mul, inv_mul_cancel₀ hcne, map_one]⟩
  let g0 : LB.Gen (LB.LinComb D.toPre.P.L (Y := (DegPre.BF D.toPre F).left) (K := PEmpty) PEmpty.elim PEmpty.elim) :=
    ⟨fun _ => res le_top cU⟩
  have hg0 : g0.IsGen := fun i j => by
    have hg : (LB.LinComb D.toPre.P.L (Y := (DegPre.BF D.toPre F).left) (K := PEmpty) PEmpty.elim PEmpty.elim).g i j = 1 := by
      simp [LB.LinComb]; rfl
    calc res _ (g0.s i) = res _ (g0.s j) := (res_res' _ _ cU).trans (res_res' _ _ cU).symm
      _ = _ := by rw [hg, _root_.one_mul]
  have hformU : FormEq (Sum.elim (fun i => (DegPre.prB D.toPre F).left ≫ Sum.elim (D.toPre.famφB (α + k • mu))
        (fun i => (𝟙 D.toPre.P.A * cQ D.toPre D.toPre.P.A mu).left ≫ D.toPre.famφB α i) i) PEmpty.elim)
      (Sum.elim (DegPre.deltaε k) PEmpty.elim) (DegPre.deltaφ D.toPre F k α mu) (DegPre.deltaε k) := fun U _ h => by
    have e0 : ∀ f : PEmpty → U, ∏ i, f i = 1 := fun f => Fintype.prod_empty f
    rw [Fintype.prod_sum_type, e0, _root_.mul_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    rcases i with i | i
    · simp only [Sum.elim_inl, DegPre.deltaφ, GC.famφ_eq]
    · simp only [Sum.elim_inr, DegPre.deltaφ, GC.famφ_eq]
      rw [← Category.assoc, trF_prB, Category.assoc]
      rfl
  obtain ⟨u, hu, vu⟩ := exists_gen hL hformU
    (LB.mulGen D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ eB (DegPre.prB D.toPre F).left) g0)
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ heB _) hg0)
  have hval_u : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι),
      Good D.toPre.P.L z J →
      (val u ρ z J).val = (val eB (ρ ≫ (DegPre.prB D.toPre F).left) z J).val * gs ρ z ⊤ (gF D.toPre F c) := by
    intro Z ρ z J hJ
    rw [vu Z ρ z J hJ, val_mul hJ, val_pull hJ, Units.val_mul]
    congr 1
    have hmem : ρ z ∈ LB.wchart D.toPre.P.L (K := PEmpty) PEmpty.elim (fun k => J (ρ ≫ PEmpty.elim k)) :=
      Set.mem_iInter.2 fun k => k.elim
    exact (congrArg Units.val (gm_res ρ z le_top hmem cU)).trans (gs_unit ρ z ⊤ (by trivial) cU).symm
  have z₂ : DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F = 1 := lift_snd _ _
  have hcorr : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left)
      (DegPre.famMult D.toPre F k mu α) := corr_of_val hL fun y J hJ => Units.ext (by
    have face1 (x y' : TF (R := V) F ⟶ D.toPre.P.A) : cubV D.toPre.cub y J 1 x y' = 1 := by
      have H := val_corr hJ (D.toPre.cub.face 0) (lift x y').left
      rw [val_one] at H
      refine Eq.trans ?_ H
      refine Eq.trans ?_ (val_cub D.toPre.cub (lift x y') hJ (pzero D.toPre.P.A _) (x2 D.toPre.P.A 0) (x2 D.toPre.P.A 1)).symm
      congr 1 <;> simp [x2, pzero, Hom.one_def]
    have face2 (x y' : TF (R := V) F ⟶ D.toPre.P.A) : cubV D.toPre.cub y J x 1 y' = 1 := by
      have H := (val_corr hJ D.toPre.cub.cubeSymmetric_swap_first (lift x (lift 1 y')).left).trans
        (val_cub D.toPre.cub (lift x (lift 1 y')) hJ _ _ _)
      have E : cubV D.toPre.cub y J x 1 y' = cubV D.toPre.cub y J 1 x y' := by
        refine Eq.trans H ?_
        congr 1 <;> simp [x3]
      rw [E, face1]
    have N_one (k : ℕ) (a m : TF (R := V) F ⟶ D.toPre.P.A) : cubN (cubV D.toPre.cub y J) k a m 1 = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      have H := (val_corr hJ D.toPre.cub.cubeSymmetric_swap_last (lift (a * m ^ i) (lift m 1)).left).trans
        (val_cub D.toPre.cub (lift (a * m ^ i) (lift m 1)) hJ _ _ _)
      have E : cubV D.toPre.cub y J (a * m ^ i) m 1 = cubV D.toPre.cub y J (a * m ^ i) 1 m := by
        refine Eq.trans H ?_
        congr 1 <;> simp [x3]
      rw [E, face2]
    have E2 : val eB ((DegPre.zF D.toPre F).left ≫ (DegPre.prB D.toPre F).left) y J =
        val e' (DegPre.jFR (R := V) F) y J := by
      have E1 := veB (TF (R := V) F) (DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F) y J hJ
      rw [z₂, N_one, face2, inv_one, _root_.one_mul, _root_.one_mul] at E1
      have e3 : (1 : TF (R := V) F ⟶ D.toPre.P.A).left ≫ D.toPre.P.A.hom = DegPre.jFR (R := V) F := Over.w _
      rw [e3] at E1
      have e4 : (DegPre.zF D.toPre F).left ≫ (DegPre.prB D.toPre F).left = (1 : TF (R := V) F ⟶ D.toPre.P.A).left := by
        rw [← Over.comp_left, z₂]
      rw [e4]; exact E1
    rw [val_pull hJ, Category.id_comp, hval_u _ _ y J hJ, hval F (TF (R := V) F).left (𝟙 (TF (R := V) F).left) y J hJ, E2, gs_gF_zF, gs_scal_jFK,
      Category.id_comp, ← hc]
    exact mul_comm _ _)
  exact ⟨u, hu, hcorr⟩

theorem fam_eq_zero (hϖ : Irreducible ϖ) (G : Fam D.toPre F 1)
    (h0 : ∀ j : Fin 4 → D.toPre.P.L.ι, (G.s 0).f j = 0) :
    ∀ (mu : D.toPre.X) (j : Fin 4 → D.toPre.P.L.ι), (G.s mu).f j = 0 := by
  classical
  choose Q hQ using QForm.exists_QVal hϖ D
  intro mu j
  obtain ⟨u, hu, hc⟩ := exists_fe_gen (F := F) hϖ (Q := Q) hQ 1 mu 0
  have hrel := G.fe mu 0 u hu hc
  have e01 : (0 : D.toPre.X) + 1 • mu = mu := by simp
  rw [e01] at hrel
  have hL := D.toPre.P.isLB
  refine TopCat.Presheaf.section_ext (DegPre.BF D.toPre F).left.sheaf _ _ 0 fun y hy => ?_
  choose ch hch using WeightPf.exists_chart D.toPre.P.L hL
  let j₁ : Fin 4 → D.toPre.P.L.ι := fun k => ch ((DegPre.famφ D.toPre F mu k).base y)
  let j₂ : Fin 4 → D.toPre.P.L.ι := fun k => ch (((DegPre.trF D.toPre F mu).left ≫ DegPre.famφ D.toPre F 0 k).base y)
  let j₃ : Fin 4 ⊕ Fin 4 → D.toPre.P.L.ι := fun k => ch ((DegPre.deltaφ D.toPre F 1 0 mu k).base y)
  have hcoh : LB.Coh D.toPre.P.L (Sum.elim (DegPre.famφ D.toPre F mu)
      (Sum.elim (fun k => (DegPre.trF D.toPre F mu).left ≫ DegPre.famφ D.toPre F 0 k)
        (DegPre.deltaφ D.toPre F 1 0 mu))) (Sum.elim j₁ (Sum.elim j₂ j₃)) := by
    have key : ∀ z, (Sum.elim j₁ (Sum.elim j₂ j₃)) z = ch (((Sum.elim (DegPre.famφ D.toPre F mu)
        (Sum.elim (fun k => (DegPre.trF D.toPre F mu).left ≫ DegPre.famφ D.toPre F 0 k)
          (DegPre.deltaφ D.toPre F 1 0 mu))) z).base y) := by
      rintro (z | z | z) <;> rfl
    intro a b hab
    rw [key a, key b, hab]
  have E := hrel j₁ j₂ j₃ hcoh
  have hy1 : y ∈ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F mu) j₁ := Set.mem_iInter.2 fun k => hch _
  have hy2 : y ∈ LB.wchart D.toPre.P.L (fun k => (DegPre.trF D.toPre F mu).left ≫ DegPre.famφ D.toPre F 0 k) j₂ :=
    Set.mem_iInter.2 fun k => hch _
  have hy3 : y ∈ LB.wchart D.toPre.P.L (DegPre.deltaφ D.toPre F 1 0 mu) j₃ := Set.mem_iInter.2 fun k => hch _

  have hz : ((DegPre.BF D.toPre F).left.presheaf.map (homOfLE (inf_le_left.trans inf_le_left :
      LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F mu) j₁ ⊓
        LB.wchart D.toPre.P.L (fun k => (DegPre.trF D.toPre F mu).left ≫ DegPre.famφ D.toPre F 0 k) j₂ ⊓
        LB.wchart D.toPre.P.L (DegPre.deltaφ D.toPre F 1 0 mu) j₃ ≤ _)).op).hom ((G.s mu).f j₁) = 0 := by
    erw [E, h0 j₂, map_zero, map_zero, zero_mul]

  let W := LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F mu) j ⊓
    (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F mu) j₁ ⊓
      LB.wchart D.toPre.P.L (fun k => (DegPre.trF D.toPre F mu).left ≫ DegPre.famφ D.toPre F 0 k) j₂ ⊓
      LB.wchart D.toPre.P.L (DegPre.deltaφ D.toPre F 1 0 mu) j₃)
  have hyW : y ∈ W := ⟨hy, ⟨⟨hy1, hy2⟩, hy3⟩⟩
  have hW1 : W ≤ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F mu) j ⊓ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F mu) j₁ :=
    le_inf inf_le_left (inf_le_right.trans (inf_le_left.trans inf_le_left))
  have hc1 := congrArg (rs hW1) ((G.s mu).compat j j₁)
  have hWz : rs (inf_le_left : W ≤ _) ((G.s mu).f j) = 0 := by
    erw [rs_rs, rs_mul, rs_rs] at hc1
    erw [hc1]
    have := congrArg (rs (inf_le_right : W ≤ _)) hz
    erw [rs_rs] at this
    erw [this]
    exact (congrArg _ (map_zero _)).trans (mul_zero _)
  show (DegPre.BF D.toPre F).left.presheaf.germ _ y hy ((G.s mu).f j) = (DegPre.BF D.toPre F).left.presheaf.germ _ y hy 0
  erw [← TopCat.Presheaf.germ_res_apply _ (homOfLE (inf_le_left : W ≤ _)) y hyW]
  exact (congrArg _ hWz).trans ((map_zero _).trans (map_zero _).symm)

end FEGen

section Local

end Local

end ReciprocityTheory.ChartRestriction.G.DVR.TG
