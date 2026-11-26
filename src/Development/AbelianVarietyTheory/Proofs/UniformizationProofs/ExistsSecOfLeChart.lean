module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfIsProjBy
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SurjectiveCubeOfGeneric
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijOfOnto
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFinAffineCover
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralFamiliesSpanPullDegeneration
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecScalBoxSecGPre
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionCommutesPullbackCmEndoFourLe
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.UniformisationPowerWithoutExpansion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfLeChart
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistGen

open LBGerm TopologicalSpace

variable {X : Scheme.{0}} {M H : LB X}

theorem gm_tw_g (M H : LB X) (t : ℕ) (y : X) (p q : M.ι × H.ι) (hp : y ∈ M.U p.1 ⊓ H.U p.2)
    (hq : y ∈ M.U q.1 ⊓ H.U q.2) :
    (gm (𝟙 X) y ((tw M H t).U p ⊓ (tw M H t).U q) ((tw M H t).g p q)).val =
      (gm (𝟙 X) y (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1)).val *
        (gm (𝟙 X) y (H.U p.2 ⊓ H.U q.2) (H.g p.2 q.2)).val ^ t := by
  have hy : (𝟙 X : X ⟶ X) y ∈ M.U p.1 ⊓ H.U p.2 ⊓ (M.U q.1 ⊓ H.U q.2) := ⟨hp, hq⟩
  rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, tw_g]
  refine congrArg Units.val ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res (𝟙 X) y _ hy _) ?_))
  rw [zpow_natCast]
  exact (map_pow _ _ _).trans (congrArg (· ^ t) (gm_res (𝟙 X) y _ hy _))

theorem exists_mul_pow (a e : ℕ) (u : LB.Sec (tw M H a)) (s : LB.Sec H) :
    ∃ u' : LB.Sec (tw M H ((a + e : ℕ) : ℤ)), nonzeroLocus u ⊓ nonzeroLocus s ≤ nonzeroLocus u' := by
  let F : ∀ p : M.ι × H.ι, Γ(X, M.U p.1 ⊓ H.U p.2) := fun p =>
    (show Γ(X, M.U p.1 ⊓ H.U p.2) from u.f p) * resG X inf_le_right (s.f p.2) ^ e
  have hF : ∀ (y : X) (p : M.ι × H.ι), y ∈ M.U p.1 ⊓ H.U p.2 → gs (𝟙 X) y _ (F p) =
      gs (𝟙 X) y _ (u.f p) * gs (𝟙 X) y _ (s.f p.2) ^ e := fun y p hy => by
    rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy]
    rfl
  refine ⟨secOfGerm (M := tw M H ((a + e : ℕ) : ℤ)) F fun y p q hp hq => ?_, fun y hy => ?_⟩
  · refine (hF y p hp).trans (Eq.trans ?_ (congrArg₂ (· * ·) (gm_tw_g M H (a + e) y p q hp hq) (hF y q hq)).symm)
    rw [gs_compat u (𝟙 X) y (j := p) (j' := q) hp hq, gm_tw_g M H a y p q hp hq,
      gs_compat s (𝟙 X) y (j := p.2) (j' := q.2) hp.2 hq.2]
    ring
  · obtain ⟨p, hp⟩ := exists_chart_of_mem_nonzeroLocus hy.1
    refine (mem_nonzeroLocus_iff_isUnit (M := tw M H ((a + e : ℕ) : ℤ)) _ (k := p) hp).2 ?_
    refine (congrArg IsUnit (hF y p hp)).mpr ?_
    exact (((mem_nonzeroLocus_iff_isUnit u hp).1 hy.1).mul
      (((mem_nonzeroLocus_iff_isUnit s hp.2).1 hy.2).pow e))

theorem exists_sec_of_le_chart [CompactSpace X] [QuasiSeparatedSpace X] (hM : M.IsLB) (hH : H.IsLB) (n : ℕ)
    (σ : ∀ j, Γ(X, H.U j))
    (hσ : ∀ (y : X) j j', y ∈ H.U j → y ∈ H.U j' → gs (𝟙 X) y _ (σ j) =
      (gm (𝟙 X) y (H.U j ⊓ H.U j') (H.g j j')).val ^ n * gs (𝟙 X) y _ (σ j'))
    (V : X.Opens) (hV : ∀ (y : X) j, y ∈ H.U j → (y ∈ V ↔ IsUnit (gs (𝟙 X) y _ (σ j))))
    (k : M.ι) (hk : V ≤ M.U k) :
    ∃ (N : ℕ) (u : LB.Sec (tw M H ((n * N : ℕ) : ℤ))), V ≤ nonzeroLocus u := by
  obtain ⟨α, _, W, J, hWa, hW, hc⟩ : ∃ (α : Type) (_ : Fintype α) (W : α → X.Opens) (J : α → M.ι × H.ι),
      (∀ a, IsAffineOpen (W a)) ∧ (∀ a, W a ≤ M.U (J a).1 ⊓ H.U (J a).2) ∧ ∀ y : X, ∃ a, y ∈ W a :=
    exists_finite_affine_refinement (isLB_tw hM hH 0)
  have hW₂ : ∀ a, W a ≤ H.U (J a).2 := fun a => (hW a).trans inf_le_right
  have hb : ∀ (U : X.Opens) (j : H.ι) (hU : U ≤ H.U j) (y : X),
      y ∈ X.basicOpen (resG X hU (σ j)) → y ∈ V := fun U j hU y hy => by
    have hy₁ : y ∈ U := X.basicOpen_le _ hy
    have hs := (isUnit_gs_iff (𝟙 X) y _ hy₁ _).2 hy
    rwa [gs_res _ y _ hy₁, ← hV y j (hU hy₁)] at hs
  have step₁ : ∀ a, ∃ (e : ℕ) (v : Γ(X, W a)), ∀ y ∈ W a, y ∈ V →
      gs (𝟙 X) y _ v = gs (𝟙 X) y _ (σ (J a).2) ^ e *
        (gm (𝟙 X) y (M.U (J a).1 ⊓ M.U k) (M.g (J a).1 k)).val := fun a => by
    have le : X.basicOpen (resG X (hW₂ a) (σ (J a).2)) ≤ M.U (J a).1 ⊓ M.U k :=
      fun y hy => ⟨(hW a (X.basicOpen_le _ hy)).1, hk (hb _ _ _ y hy)⟩
    obtain ⟨e, v, hv⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X (W a) (hWa a).isCompact
      (hWa a).isQuasiSeparated (resG X (hW₂ a) (σ (J a).2)) (resG X le (M.g (J a).1 k).val)
    have hv' : resG X (X.basicOpen_le _) v =
        resG X (X.basicOpen_le _) (resG X (hW₂ a) (σ (J a).2)) ^ e * resG X le (M.g (J a).1 k).val := hv
    refine ⟨e, v, fun y hy hs => ?_⟩
    have hy' : y ∈ X.basicOpen (resG X (hW₂ a) (σ (J a).2)) := (isUnit_gs_iff (𝟙 X) y _ hy _).1 (by
      rw [gs_res _ y _ hy]; exact (hV y _ (hW₂ a hy)).1 hs)
    have e₁ := congrArg (gs (𝟙 X) y _) hv'
    rwa [gs_res _ y _ hy', gs_mul _ y _ hy', gs_pow _ y _ hy', gs_res _ y _ hy', gs_res _ y _ hy,
      gs_res _ y _ hy', gs_unit (𝟙 X) y _ (le hy')] at e₁
  choose e v hv using step₁
  obtain ⟨N₁, v', hv'⟩ : ∃ (N₁ : ℕ) (v' : ∀ a, Γ(X, W a)), ∀ a, ∀ y ∈ W a, y ∈ V →
      gs (𝟙 X) y _ (v' a) = gs (𝟙 X) y _ (σ (J a).2) ^ N₁ *
        (gm (𝟙 X) y (M.U (J a).1 ⊓ M.U k) (M.g (J a).1 k)).val :=
    ⟨Finset.univ.sup e, fun a => resG X (hW₂ a) (σ (J a).2) ^ (Finset.univ.sup e - e a) * v a, fun a y hy hs => by
      rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy, hv a y hy hs, ← _root_.mul_assoc, ← pow_add,
        Nat.sub_add_cancel (Finset.le_sup (f := e) (Finset.mem_univ a))]⟩
  have step₂ : ∀ p : α × α, ∃ d : ℕ, ∀ y ∈ W p.1 ⊓ W p.2, gs (𝟙 X) y _ (σ (J p.1).2) ^ d *
      (gs (𝟙 X) y _ (v' p.1) - (gm (𝟙 X) y (M.U (J p.1).1 ⊓ M.U (J p.2).1) (M.g (J p.1).1 (J p.2).1)).val *
        (gm (𝟙 X) y (H.U (J p.1).2 ⊓ H.U (J p.2).2)
        (H.g (J p.1).2 (J p.2).2)).val ^ (n * N₁) * gs (𝟙 X) y _ (v' p.2)) = 0 := by
    rintro ⟨a, b⟩
    have hcpt : IsCompact ((W a ⊓ W b : X.Opens) : Set X) :=
      QuasiSeparatedSpace.inter_isCompact _ _ (W a).isOpen (hWa a).isCompact (W b).isOpen (hWa b).isCompact
    have le₁ : W a ⊓ W b ≤ M.U (J a).1 ⊓ M.U (J b).1 := fun y hy => ⟨(hW a hy.1).1, (hW b hy.2).1⟩
    have le : W a ⊓ W b ≤ H.U (J a).2 ⊓ H.U (J b).2 := fun y hy => ⟨(hW a hy.1).2, (hW b hy.2).2⟩
    have hx : ∀ y ∈ W a ⊓ W b, gs (𝟙 X) y (W a ⊓ W b) (resG X inf_le_left (v' a) -
        resG X le₁ (M.g (J a).1 (J b).1).val * resG X le (H.g (J a).2 (J b).2).val ^ (n * N₁) *
          resG X inf_le_right (v' b)) =
        gs (𝟙 X) y _ (v' a) - (gm (𝟙 X) y (M.U (J a).1 ⊓ M.U (J b).1) (M.g (J a).1 (J b).1)).val *
          (gm (𝟙 X) y (H.U (J a).2 ⊓ H.U (J b).2) (H.g (J a).2 (J b).2)).val ^ (n * N₁) *
            gs (𝟙 X) y _ (v' b) := fun y hy => by
      rw [gs_sub _ y _ hy, gs_mul _ y _ hy, gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy,
        gs_res _ y _ hy, gs_res _ y _ hy, gs_unit (𝟙 X) y _ (le hy), gs_unit (𝟙 X) y _ (le₁ hy)]
    obtain ⟨d, hd⟩ := exists_pow_mul_gs_eq_zero hcpt (resG X (inf_le_left.trans (hW₂ a)) (σ (J a).2)) _
      fun y hy => by
        have hy₁ : y ∈ W a ⊓ W b := X.basicOpen_le _ hy
        have hs := hb _ _ _ y hy
        refine (hx y hy₁).trans ?_
        rw [hv' a y hy₁.1 hs, hv' b y hy₁.2 hs, hσ y (J a).2 (J b).2 (hW₂ a hy₁.1) (hW₂ b hy₁.2),
          ← gm_cocycle hM (𝟙 X) y (hW a hy₁.1).1 (hW b hy₁.2).1 (hk hs), Units.val_mul]
        ring
    refine ⟨d, fun y hy => ?_⟩
    have := hd y hy
    rwa [hx y hy, gs_res _ y _ hy] at this
  choose d hd using step₂
  obtain ⟨c, hc'⟩ : ∃ c, ∀ p, d p ≤ c := ⟨Finset.univ.sup d, fun p => Finset.le_sup (Finset.mem_univ p)⟩
  have hz : ∀ a, ∀ y ∈ W a, gs (𝟙 X) y _ (resG X (hW₂ a) (σ (J a).2) ^ c * v' a) =
      gs (𝟙 X) y _ (σ (J a).2) ^ c * gs (𝟙 X) y _ (v' a) := fun a y hy => by
    rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy]
  obtain ⟨u, hu⟩ := exists_sec_of_refinement (isLB_tw hM hH ((n * (N₁ + c) : ℕ) : ℤ)) W J hW hc
    (fun a => resG X (hW₂ a) (σ (J a).2) ^ c * v' a) fun y a b ha hb => by
      obtain ⟨c', hc''⟩ := Nat.exists_eq_add_of_le (hc' (a, b))
      have e₁ := hd (a, b) y ⟨ha, hb⟩
      have e₂ := hσ y (J a).2 (J b).2 (hW₂ a ha) (hW₂ b hb)
      rw [hz a y ha, hz b y hb, gm_tw_g M H _ y (J a) (J b) (hW a ha) (hW b hb)]
      dsimp only at e₁
      rw [e₂] at e₁ ⊢
      rw [hc'']
      generalize gs (𝟙 X) y _ (σ (J b).2) = τ at e₁ ⊢
      generalize Units.val (gm (𝟙 X) y _ (H.g (J a).2 (J b).2)) = w at e₁ ⊢
      linear_combination (w ^ n * τ) ^ c' * e₁
  refine ⟨N₁ + c, u, fun y hy => ?_⟩
  obtain ⟨a, ha⟩ := hc y
  have hs := (hV y _ (hW₂ a ha)).1 hy
  rw [mem_nonzeroLocus_iff_isUnit u (k := J a) (hW a ha), hu y (J a) a (hW a ha) ha, hz a y ha, hv' a y ha hy]
  exact (Units.isUnit _).mul ((hs.pow c).mul ((hs.pow N₁).mul (Units.isUnit _)))

theorem compact_quasiSeparated (hH : H.IsLB) {I : Type} [Finite I] (s : I → LB.Sec H)
    (hc : ⨆ i, nonzeroLocus (s i) = ⊤) (ha : ∀ i, IsAffineOpen (nonzeroLocus (s i))) :
    CompactSpace X ∧ QuasiSeparatedSpace X := by
  have mem : ∀ y : X, ∃ i, y ∈ nonzeroLocus (s i) := fun y =>
    Opens.mem_iSup.1 (show y ∈ ⨆ i, nonzeroLocus (s i) by rw [hc]; trivial)
  refine ⟨⟨?_⟩, quasiSeparatedSpace_iff_forall_affineOpens.2 fun U V => ?_⟩
  · have : (Set.univ : Set X) = ⋃ i, (nonzeroLocus (s i) : Set X) :=
      (Set.eq_univ_of_forall fun y => Set.mem_iUnion.2 (mem y)).symm
    rw [this]
    exact isCompact_iUnion fun i => (ha i).isCompact
  · have : (U.1 ∩ V.1 : Set X) = ⋃ i, ((nonzeroLocus (s i) ⊓ U.1 : X.Opens) : Set X) ∩
        ((nonzeroLocus (s i) ⊓ V.1 : X.Opens) : Set X) := by
      ext y
      refine ⟨fun hy => ?_, fun hy => ?_⟩
      · obtain ⟨i, hi⟩ := mem y
        exact Set.mem_iUnion.2 ⟨i, ⟨hi, hy.1⟩, ⟨hi, hy.2⟩⟩
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
        exact ⟨hi.1.2, hi.2.2⟩
    rw [this]
    exact isCompact_iUnion fun i => (ha i).isQuasiSeparated _ _ Set.inter_subset_left (Opens.isOpen _)
      (isAffineOpen_nonzeroLocus_inf hH (s i) U.2).isCompact Set.inter_subset_left (Opens.isOpen _)
      (isAffineOpen_nonzeroLocus_inf hH (s i) V.2).isCompact

theorem exists_nhds [CompactSpace X] [QuasiSeparatedSpace X] (hM : M.IsLB) (hH : H.IsLB) (s : LB.Sec H)
    (ha : IsAffineOpen (nonzeroLocus s)) (y : X) (hy : y ∈ nonzeroLocus s) :
    ∃ (V : X.Opens) (N : ℕ), y ∈ V ∧ ∀ e : ℕ, ∃ u : LB.Sec (tw M H ((N + e : ℕ) : ℤ)), V ≤ nonzeroLocus u := by
  obtain ⟨k, hk⟩ := exists_chart hM y
  have hl := nonzeroLocus_secToPow s (le_refl 1)
  rw [← hl] at ha hy
  obtain ⟨a, hle, hya⟩ := ha.exists_basicOpen_le (V := M.U k) ⟨y, hk⟩ hy
  obtain ⟨m, -, σ, hσ⟩ := exists_nonzeroLocus_eq_basicOpen hH (secToPow s 1) a
  obtain ⟨N, u, hu⟩ := exists_sec_of_le_chart hM hH (1 * m) (powSecFn σ) (fun z j j' hj hj' => by
      have hz : z ∈ H.U j ⊓ H.U j' := ⟨hj, hj'⟩
      have e := congrArg (gs (𝟙 X) z _) (powSecFn_compat σ j j')
      rwa [gs_res _ z _ hz, gs_mul _ z _ hz, gs_res _ z _ hz, gs_pow _ z _ hz, gs_unit _ z _ hz] at e)
    (X.basicOpen a) (fun z j hj => by
      rw [isUnit_gs_iff (𝟙 X) z _ hj, ← nonzeroLocus_inf_powSecFn, hσ]
      exact ⟨fun h => ⟨h, hj⟩, fun h => h.1⟩) k hle
  refine ⟨X.basicOpen a, 1 * m * N, hya, fun e => ?_⟩
  obtain ⟨u', hu'⟩ := exists_mul_pow _ e u s
  exact ⟨u', (le_inf hu ((X.basicOpen_le a).trans hl.le)).trans hu'⟩

theorem twist_generated : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ M : LB X, M.IsLB → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → ∃ (n' : ℕ) (u : Fin (n' + 1) → LB.Sec (tw M H t)), ⨆ i, nonzeroLocus (u i) = ⊤ := by
  intro R _ X f H n s hH hs M hM
  obtain ⟨_, _⟩ := compact_quasiSeparated hH s hs.1 fun i => (hs.2 i).1
  have loc : ∀ y : X, ∃ (V : X.Opens) (N : ℕ), y ∈ V ∧
      ∀ e : ℕ, ∃ u : LB.Sec (tw M H ((N + e : ℕ) : ℤ)), V ≤ nonzeroLocus u := fun y => by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show y ∈ ⨆ i, nonzeroLocus (s i) by rw [hs.1]; trivial)
    exact exists_nhds hM hH (s i) (hs.2 i).1 y hi
  choose V N hy hV using loc
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun y => (V y : Set X)) (fun y => (V y).isOpen)
    (fun y _ => Set.mem_iUnion.2 ⟨y, hy y⟩)
  refine ⟨(T.sup N : ℕ), fun t ht => ?_⟩
  have h : ∀ y : T, ∃ u : LB.Sec (tw M H t), V y ≤ nonzeroLocus u := fun y => by
    have h₁ : N y ≤ T.sup N := Finset.le_sup y.2
    obtain ⟨e, rfl⟩ : ∃ e : ℕ, t = ((N y + e : ℕ) : ℤ) := ⟨(t - N y).toNat, by omega⟩
    exact hV y e
  choose u hu using h
  let c : Option T → LB.Sec (tw M H t) := fun o => o.elim DVR.SecOps.secZero u
  let e : Option T ≃ Fin (Fintype.card T + 1) := Fintype.equivFinOfCardEq Fintype.card_option
  refine ⟨_, fun i => c (e.symm i), top_unique fun x _ => ?_⟩
  obtain ⟨y, hyT, hx⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ x))
  refine Opens.mem_iSup.2 ⟨e (some ⟨y, hyT⟩), ?_⟩
  simp only [Equiv.symm_apply_apply]
  exact hu ⟨y, hyT⟩ hx

end GlobalTheory.TwistGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEquivOfIsPushout
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FlatSec

theorem exists_equiv_of_isPushout {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {A A' : CommRingCat.{0}}
    [Algebra R A] (p : A ⟶ A') (s' : R' →+* A')
    (H : IsPushout (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R R')) p
      (CommRingCat.ofHom s')) :
    ∃ e : R' ⊗[R] A ≃+ A', ∀ c v, e (c ⊗ₜ v) = s' c * p.hom v := by
  let _ : Algebra A A' := p.hom.toAlgebra
  let _ : Algebra R' A' := s'.toAlgebra
  let _ : Algebra R A' := (s'.comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' A' := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R A A' := .of_algebraMap_eq fun r => (congrArg (fun q => q.hom r) H.w).symm
  have h : Algebra.IsPushout R R' A A' := (CommRingCat.isPushout_iff_isPushout.mp H).symm
  exact ⟨h.out.equiv.toAddEquiv, fun c v => (h.out.equiv_tmul c v).trans (Algebra.smul_def _ _)⟩

theorem exists_comb_ker {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R']
    {I J : Type} [Fintype I] [Fintype J] {A : I → Type} {B : J → Type} {A' : I → Type} {B' : J → Type}
    [∀ a, AddCommGroup (A a)] [∀ a, Module R (A a)] [∀ b, AddCommGroup (B b)] [∀ b, Module R (B b)]
    [∀ a, AddCommGroup (A' a)] [∀ b, AddCommGroup (B' b)]
    (e : ∀ a, R' ⊗[R] A a ≃+ A' a) (e' : ∀ b, R' ⊗[R] B b ≃+ B' b) (d : (∀ a, A a) →ₗ[R] (∀ b, B b))
    (x : ∀ a, A' a)
    (hx : ∀ (n : ℕ) (c : Fin n → R') (v : Fin n → ∀ a, A a), (∀ a, x a = ∑ i, e a (c i ⊗ₜ v i a)) →
      ∀ b, ∑ i, e' b (c i ⊗ₜ d (v i) b) = 0) :
    ∃ (n : ℕ) (c : Fin n → R') (v : Fin n → ∀ a, A a), (∀ a, x a = ∑ i, e a (c i ⊗ₜ v i a)) ∧ ∀ i, d (v i) = 0 := by
  classical
  obtain ⟨t, ht⟩ := (TensorProduct.piRight R R R' A).surjective (fun a => (e a).symm (x a))
  have key : ∀ (n : ℕ) (c : Fin n → R') (v : Fin n → ∀ a, A a), t = ∑ i, c i ⊗ₜ v i →
      ∀ a, x a = ∑ i, e a (c i ⊗ₜ v i a) := fun n c v h a => by
    have := congrFun ht a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h, map_sum, Finset.sum_apply, AddEquiv.eq_symm_apply, map_sum] at this
    rw [← this]
    rfl
  have h0 : d.lTensor R' t = 0 := by
    obtain ⟨n, c, v, h⟩ := TensorProduct.exists_sum_tmul_eq t
    apply (TensorProduct.piRight R R R' B).injective
    funext b
    apply (e' b).injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, Pi.zero_apply, map_zero, ← hx n c v (key n c v h) b, h, map_sum, map_sum, Finset.sum_apply, map_sum]
    rfl
  obtain ⟨w, hw⟩ := (Module.Flat.lTensor_exact R' (LinearMap.exact_subtype_ker_map d) t).1 h0
  obtain ⟨n, c, v, rfl⟩ := TensorProduct.exists_sum_tmul_eq w
  refine ⟨n, c, fun i => (v i).1, key n c _ ?_, fun i => (v i).2⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hw, map_sum]
  rfl

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' Z : Scheme.{0}}

theorem isPushout_app {g : R →+* R'} (hg : g.Flat) {f : X ⟶ Spec (CommRingCat.of R)} {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of R')} (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    {U : X.Opens} (hU : IsCompact (U : Set X)) (hU' : IsQuasiSeparated (U : Set X)) :
    IsPushout (CommRingCat.ofHom (cst f U)) (CommRingCat.ofHom g) (π.app U)
      (CommRingCat.ofHom (cst f' (π ⁻¹ᵁ U))) := by
  have : Flat (Spec.map (CommRingCat.ofHom g)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact hg
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := π ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU hU')
  refine po.of_iso (Scheme.ΓSpecIso (.of R)) (Iso.refl _) (Scheme.ΓSpecIso (.of R')) (Iso.refl _) ?_ ?_ ?_ ?_
  · ext x; simp [AbLaw.cst, Scheme.Hom.appLE]; rfl
  · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  · simp [Scheme.Hom.app_eq_appLE]
  · ext x; simp [AbLaw.cst, Scheme.Hom.appLE]; rfl

theorem gs_sum (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) {n : ℕ} (a : Fin n → Γ(X, U)) :
    gs r z U (∑ i, a i) = ∑ i, gs r z U (a i) := by simp only [gs_eq r z U h, map_sum]

theorem gs_cst (f : X ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (c : R) :
    gs r z U (cst f U c) = gs r z ⊤ (cst f ⊤ c) := by
  rw [← rs_cst f (le_top : U ≤ ⊤) c]
  exact gs_res r z _ h _

theorem gs_comb (f' : X' ⟶ Spec (CommRingCat.of R')) (π : X' ⟶ X) (U : X.Opens) (z : X') (h : π z ∈ U) {n : ℕ}
    (c : Fin n → R') (v : Fin n → Γ(X, U)) :
    gs (𝟙 X') z (π ⁻¹ᵁ U) (∑ i, cst f' (π ⁻¹ᵁ U) (c i) * (π.app U).hom (v i)) =
      ∑ i, gs (𝟙 X') z ⊤ (cst f' ⊤ (c i)) * gs π z U (v i) := by
  rw [gs_sum (𝟙 X') z (π ⁻¹ᵁ U) h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_mul (𝟙 X') z (π ⁻¹ᵁ U) h, gs_cst f' (𝟙 X') z (π ⁻¹ᵁ U) h, gs_pull (𝟙 X') π z U h, Category.id_comp]

theorem gs_pull_trans {M : LB X} {π : X' ⟶ X} (σ : LB.Sec (M.pull π)) (z : X') {k l : M.ι} (hk : π z ∈ M.U k)
    (hl : π z ∈ M.U l) : gs (𝟙 X') z _ (σ.f (fun _ => k)) =
      (gm π z (M.U k ⊓ M.U l) (M.g k l)).val * gs (𝟙 X') z _ (σ.f (fun _ => l)) := by
  refine (sec_trans σ (𝟙 X') z (j := fun _ => k) (j' := fun _ => l) (Set.mem_iInter.2 fun _ => hk)
    (Set.mem_iInter.2 fun _ => hl)).trans ?_
  rw [trF, Fintype.prod_unique, zpow_one, Category.id_comp]
  rfl

theorem gs_sec_trans {M : LB X} (s : LB.Sec M) (r : Z ⟶ X) (z : Z) {k l : M.ι} (hk : r z ∈ M.U k)
    (hl : r z ∈ M.U l) : gs r z _ (s.f k) = (gm r z (M.U k ⊓ M.U l) (M.g k l)).val * gs r z _ (s.f l) := by
  have hm : r z ∈ M.U k ⊓ M.U l := ⟨hk, hl⟩
  exact (gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (s.compat k l)).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit r z _ hm _) (gs_res r z _ hm _))))

theorem gs_diff {M : LB X} {V W : X.Opens} {k l : M.ι} (hV : V ≤ M.U k) (hW : W ≤ M.U l) (a : Γ(X, V)) (b : Γ(X, W))
    (r : Z ⟶ X) (z : Z) (h : r z ∈ V ⊓ W) :
    gs r z (V ⊓ W) (rs X inf_le_left a - rs X (inf_le_inf hV hW) (M.g k l).val * rs X inf_le_right b) =
      gs r z V a - (gm r z (M.U k ⊓ M.U l) (M.g k l)).val * gs r z W b := by
  rw [LBGerm.gs_sub r z _ h, gs_mul r z _ h, gs_res r z _ h, gs_res r z _ h, gs_res r z _ h,
    gs_unit r z (M.U k ⊓ M.U l) ⟨hV h.1, hW h.2⟩]

theorem exists_comb_of_flat : ∀ (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R'), g.Flat → ∀ (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X] (f : X ⟶ Spec (CommRingCat.of R)) (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → ∀ M : LB X, M.IsLB → ∀ σ : LB.Sec (M.pull π), ∃ (n : ℕ) (c : Fin n → R') (u : Fin n → LB.Sec M), ∀ (z : X') (k : M.ι), π z ∈ M.U k → gs (𝟙 X') z _ (σ.f (fun _ => k)) = ∑ i, gs (𝟙 X') z ⊤ (cst f' ⊤ (c i)) * gs π z _ ((u i).f k) := by
  intro R R' _ _ g hg X _ _ f X' π f' H M hM σ
  obtain ⟨α, _, W, j, hA, hW, hc⟩ := exists_finite_affine_refinement hM
  let _ : Algebra R R' := g.toAlgebra
  have : Module.Flat R R' := hg
  let _ : ∀ U : X.Opens, Algebra R Γ(X, U) := fun U => (cst f U).toAlgebra
  choose e he using fun a => exists_equiv_of_isPushout (R := R) (π.app (W a)) (cst f' (π ⁻¹ᵁ W a))
    (isPushout_app hg H (hA a).isCompact (hA a).isQuasiSeparated)
  choose e' he' using fun p : α × α => exists_equiv_of_isPushout (R := R) (π.app (W p.1 ⊓ W p.2))
    (cst f' (π ⁻¹ᵁ (W p.1 ⊓ W p.2))) (isPushout_app hg H
      (QuasiSeparatedSpace.inter_isCompact _ _ (W p.1).isOpen (hA p.1).isCompact (W p.2).isOpen (hA p.2).isCompact)
      (IsQuasiSeparated.of_quasiSeparatedSpace _))
  let d : (∀ a, Γ(X, W a)) →ₗ[R] (∀ p : α × α, Γ(X, W p.1 ⊓ W p.2)) :=
    { toFun := fun v p => rs X inf_le_left (v p.1) -
        rs X (inf_le_inf (hW p.1) (hW p.2)) (M.g (j p.1) (j p.2)).val * rs X inf_le_right (v p.2)
      map_add' := fun v w => funext fun p => by
        simp only [Pi.add_apply, map_add (f := _)]; ring
      map_smul' := fun r v => funext fun p => by
        simp only [Pi.smul_apply, Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra, rs_cst,
          RingHom.id_apply]; ring }
  have hx : ∀ {n : ℕ} {c : Fin n → R'} {v : Fin n → ∀ a, Γ(X, W a)},
      (∀ a, rs X' (le_pull M π (hW a)) (σ.f fun _ => j a) = ∑ i, e a (c i ⊗ₜ v i a)) →
      ∀ a z, π z ∈ W a → gs (𝟙 X') z _ (σ.f fun _ => j a) =
        ∑ i, gs (𝟙 X') z ⊤ (cst f' ⊤ (c i)) * gs π z _ (v i a) := fun {n c v} h a z hz => by
    have h' := congrArg (gs (𝟙 X') z (π ⁻¹ᵁ W a)) (h a)
    simp only [he] at h'
    rw [gs_comb f' π _ z hz] at h'
    exact (gs_res (𝟙 X') z _ hz _).symm.trans h'
  obtain ⟨n, c, v, hv, hd⟩ := exists_comb_ker e e' d (fun a => rs X' (le_pull M π (hW a)) (σ.f fun _ => j a))
    (fun n c v h p => fn_ext fun z hz => by
      simp only [he']
      rw [gs_comb f' π _ z hz, LBGerm.gs_zero (𝟙 X') z _ hz]
      have h₁ := gs_pull_trans σ z (hW _ hz.1) (hW _ hz.2)
      rw [hx h p.1 z hz.1, hx h p.2 z hz.2, Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h₁
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h₁
      refine (congrArg _ (gs_diff (hW p.1) (hW p.2) (v i p.1) (v i p.2) π z hz)).trans ?_
      ring)
  choose u hu using fun i => exists_sec_of_refinement hM W j hW hc (v i) fun y a b ha hb => by
    have h := congrArg (gs (𝟙 X) y (W a ⊓ W b)) (congrFun (hd i) (a, b))
    exact sub_eq_zero.1 ((gs_diff (hW a) (hW b) (v i a) (v i b) (𝟙 X) y ⟨ha, hb⟩).symm.trans
      (h.trans (LBGerm.gs_zero (𝟙 X) y _ ⟨ha, hb⟩)))
  have hu' : ∀ i a, rs X (hW a) ((u i).f (j a)) = v i a := fun i a => fn_ext fun y hy => by
    rw [gs_res (𝟙 X) y _ hy, hu i y (j a) a (hW a hy) hy, gm_self hM (𝟙 X) y (hW a hy), Units.val_one,
      _root_.one_mul]
  refine ⟨n, c, u, fun z k hk => ?_⟩
  obtain ⟨a, ha⟩ := hc (π z)
  rw [gs_pull_trans σ z hk (hW a ha), hx hv a z ha, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_sec_trans (u i) π z hk (hW a ha), ← hu' i a, gs_res π z _ ha]
  ring

end GlobalTheory.FlatSec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfUniformisationOverDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfUniformisationOverDvr
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem quasiCompact_of_fibres_dvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {X : Scheme.{0}} (f : X ⟶ Sp V)
    (h₁ : QuasiCompact (pullback.snd f (spMap (IsLocalRing.residue V))))
    (h₂ : QuasiCompact (pullback.snd f (jK V))) : QuasiCompact f := by
  have c₁ : CompactSpace ↥(pullback f (spMap (IsLocalRing.residue V))) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f _)
  have c₂ : CompactSpace ↥(pullback f (jK V)) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f _)
  have hu : Set.range (pullback.fst f (spMap (IsLocalRing.residue V))) ∪ Set.range (pullback.fst f (jK V)) =
      Set.univ := by
    rw [Scheme.Pullback.range_fst, Scheme.Pullback.range_fst, Set.eq_univ_iff_forall]
    intro x
    have hx : (Sp V).fromSpecResidueField (f x) (default : PrimeSpectrum _) = f x :=
      Scheme.fromSpecResidueField_apply _ _
    rcases ZJ.field_point_factor_dvr V ((Sp V).residueField (f x)) ((Sp V).fromSpecResidueField (f x)) with
      ⟨r, hr⟩ | ⟨r, hr⟩
    · exact Or.inl ⟨r (default : PrimeSpectrum _), (congrArg (fun g => g (default : PrimeSpectrum _)) hr).symm.trans hx⟩
    · exact Or.inr ⟨r (default : PrimeSpectrum _), (congrArg (fun g => g (default : PrimeSpectrum _)) hr).symm.trans hx⟩
  have : CompactSpace X := ⟨hu ▸ (isCompact_range (pullback.fst f _).continuous).union
    (isCompact_range (pullback.fst f _).continuous)⟩
  exact (quasiCompact_iff_compactSpace f).2 this

theorem isSemiAbelian_of_unifPre_dvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], UnifPre (maximalIdeal V) D A G → IsSemiAbelian G := by
  intro V _ _ _ D A G _ _ U
  obtain ⟨E, -, -, -, -, hE⟩ := gtCoord_isGt V (maximalIdeal V) D.toPre 0 G ⟨U.gt 0⟩
  have h0 := isSemiAbelian_of_isGt _ E _ hE
  have := U.gen_hom
  have hK : IsSemiAbelian ((Over.pullback (jK V)).obj G) :=
    isSemiAbelian_of_grpIso U.gen (isSemiAbelian_of_isAbelianScheme A.A A.isAb)
  let ρ : V ⧸ (maximalIdeal V) ^ (0 + 1) →+* ResidueField V :=
    Ideal.Quotient.factor (Ideal.pow_le_self (by norm_num))
  have hr : spMap (residue V) = spMap ρ ≫ thick V (maximalIdeal V) 0 := by
    rw [← Spec.map_comp]
    congr 1
  have hk : IsSemiAbelian ((Over.pullback (spMap (residue V))).obj G) := by
    rw [hr]
    exact isSemiAbelian_of_grpIso (pullCompIso (spMap ρ) (thick V (maximalIdeal V) 0) G)
      (IsSemiAbelian.pullback (spMap ρ) _ h0)
  exact ZJ.isSemiAbelian_of_fibres_dvr V G U.smooth U.separated
    (quasiCompact_of_fibres_dvr V G.hom hk.quasiCompact hK.quasiCompact) hk hK

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfUniformisationOverDvrStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.isSemiAbelian_of_uniformisation_over_dvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], UnifPre (maximalIdeal V) D A G → IsSemiAbelian G := by
  first | exact @GlobalTheory.isSemiAbelian_of_unifPre_dvr | exact GlobalTheory.isSemiAbelian_of_unifPre_dvr | (intros; apply GlobalTheory.isSemiAbelian_of_unifPre_dvr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecExtendOfNonzeroLocus
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor LBGerm

theorem mem_wchart_oneTerm {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] [Unique K] (k : K) {j : K → L.ι} {x : X} :
    x ∈ LB.wchart L (fun _ : K => 𝟙 X) j ↔ x ∈ L.U (j k) :=
  ⟨fun h => Set.mem_iInter.1 h k, fun h => Set.mem_iInter.2 fun k' => by
    obtain rfl := Subsingleton.elim k k'; exact h⟩

theorem exists_sec_oneTerm {X : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Unique K] [Fintype K'] [Unique K']
    {e e' : ℤ} (he : e = e') (s : (LB.LinComb L (fun _ : K => 𝟙 X) (fun _ => e)).Sec) :
    ∃ s' : (LB.LinComb L (fun _ : K' => 𝟙 X) (fun _ => e')).Sec, nonzeroLocus s' = nonzeroLocus s ∧
      ∀ (x : X) (i : L.ι), x ∈ L.U i → gs (𝟙 X) x _ (s'.f fun _ => i) = gs (𝟙 X) x _ (s.f fun _ => i) := by
  subst he
  have le : ∀ j : K' → L.ι, LB.wchart L (fun _ : K' => 𝟙 X) j ≤
      LB.wchart L (fun _ : K => 𝟙 X) (fun _ => j default) := fun j x hx =>
    (mem_wchart_oneTerm default).2 ((mem_wchart_oneTerm (j := j) default).1 hx)
  let s' : (LB.LinComb L (fun _ : K' => 𝟙 X) (fun _ => e)).Sec :=
    secOfGerm (M := LB.LinComb L (fun _ : K' => 𝟙 X) (fun _ => e)) (fun j => resG X (le j) (s.f fun _ => j default))
      fun y j j' hj hj' => by
        refine (gs_res (𝟙 X) y (le j) hj _).trans ((sec_trans s (𝟙 X) y (le j hj) (le j' hj')).trans
          (congrArg₂ (· * ·) (congrArg Units.val ?_) (gs_res (𝟙 X) y (le j') hj' _).symm))
        refine Eq.trans ?_ (gm_linComb L (fun _ : K' => 𝟙 X) (fun _ => e) (𝟙 X) y j j' hj hj').symm
        rw [trF, Fintype.prod_unique, Fintype.prod_unique]
  have hs : ∀ (x : X) (j : K' → L.ι), x ∈ LB.wchart L (fun _ : K' => 𝟙 X) j →
      gs (𝟙 X) x _ (s'.f j) = gs (𝟙 X) x _ (s.f fun _ => j default) := fun x j hx => gs_res (𝟙 X) x (le j) hx _
  refine ⟨s', nonzeroLocus_eq_of _ _ (fun y hy => ?_) fun y j hj => ?_,
    fun x i hx => hs x _ ((mem_wchart_oneTerm default).2 hx)⟩
  · obtain ⟨j, hj⟩ := exists_chart_of_mem_nonzeroLocus hy
    exact ⟨fun _ => j default, (mem_wchart_oneTerm default).2 ((mem_wchart_oneTerm (j := j) default).1 hj)⟩
  · rw [hs y j hj]
    exact (mem_nonzeroLocus_iff_isUnit s (le j hj)).symm

theorem sec_extend_of_nonzeroLocus : ∀ (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X] (L : LB X), L.IsLB → ∀ (N : ℕ) (s : H0 L N), (∀ a : Γ(X, nonzeroLocus s), ∃ (m : ℕ) (t : H0 L (N * m)), ∀ (x : X) (j : Fin 1 → L.ι), x ∈ nonzeroLocus s → x ∈ L.U (j 0) → Geo.Tor.gs (𝟙 X) x _ (t.f j) = Geo.Tor.gs (𝟙 X) x _ (s.f j) ^ m * Geo.Tor.gs (𝟙 X) x _ a) ∧ ∀ (n : ℕ) (t : H0 L n), (∀ (x : X) (j : Fin 1 → L.ι), x ∈ nonzeroLocus s → x ∈ L.U (j 0) → Geo.Tor.gs (𝟙 X) x _ (t.f j) = 0) → ∃ m : ℕ, ∀ j : Fin 1 → L.ι, (show Γ(X, LB.wchart L (fun _ : Fin 1 => 𝟙 X) j) from s.f j) ^ m * (show Γ(X, LB.wchart L (fun _ : Fin 1 => 𝟙 X) j) from t.f j) = 0 := by
  intro X _ _ L hL N s
  have hj : ∀ j : Fin 1 → L.ι, ∃ i, j = fun _ => i := fun j =>
    ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
  have hJ : ∀ j : PUnit.{1} → L.ι, ∃ i, j = fun _ => i := fun j => ⟨j PUnit.unit, rfl⟩
  obtain ⟨s', hl, hs⟩ : ∃ s' : (lbPow L N).Sec, nonzeroLocus s' = nonzeroLocus s ∧
      ∀ (x : X) (i : L.ι), x ∈ L.U i → gs (𝟙 X) x _ (powFn s' fun _ => i) = gs (𝟙 X) x _ (s.f fun _ => i) :=
    exists_sec_oneTerm L (K' := PUnit) rfl s
  refine ⟨fun a => ?_, fun n t ht => ?_⟩
  · obtain ⟨m, hm⟩ := exists_sec_eq_pow_mul (m := 0) hL s' (fun J => resG X (inf_le_left.trans hl.le) a)
      (mem_secOn_of_germ (M := lbPow L 0) _ fun y J J' h hJ hJ' => by
        rw [gm_lbPow_g 0 (𝟙 X) y J J' hJ hJ', pow_zero, Units.val_one, _root_.one_mul]
        exact (gs_res (𝟙 X) y (inf_le_left.trans hl.le) ⟨h, hJ⟩ a).trans
          (gs_res (𝟙 X) y (inf_le_left.trans hl.le) ⟨h, hJ'⟩ a).symm)
    obtain ⟨u, hu⟩ := hm m le_rfl
    obtain ⟨t, -, ht⟩ := exists_sec_oneTerm L (K' := Fin 1) (e' := ((N * m : ℕ) : ℤ)) (by rw [zero_add]) u
    refine ⟨m, t, fun x j hx hxj => ?_⟩
    obtain ⟨i, rfl⟩ := hj j
    have hy : x ∈ nonzeroLocus s' ⊓ powChart L (fun _ => i) := ⟨hl.ge hx, mem_powChart.2 hxj⟩
    have e := congrArg (gs (𝟙 X) x _) (hu fun _ => i)
    rw [gs_res _ x _ hy, gs_mul _ x _ hy, gs_pow _ x _ hy, gs_res _ x _ hy, gs_res _ x _ hy, hs x i hxj] at e
    exact (ht x i hxj).trans e
  · obtain ⟨t', -, ht'⟩ : ∃ t' : (lbPow L n).Sec, nonzeroLocus t' = nonzeroLocus t ∧
        ∀ (x : X) (i : L.ι), x ∈ L.U i → gs (𝟙 X) x _ (powFn t' fun _ => i) = gs (𝟙 X) x _ (t.f fun _ => i) :=
      exists_sec_oneTerm L (K' := PUnit) rfl t
    obtain ⟨m, hm⟩ := exists_pow_mul_powFn_eq_zero hL s' t' fun J => fn_ext fun y hy => by
      obtain ⟨i, rfl⟩ := hJ J
      rw [gs_res _ y _ hy, gs_zero _ y _ hy, ht' y i (mem_powChart.1 hy.2)]
      exact ht y _ (hl.le hy.1) (mem_powChart.1 hy.2)
    refine ⟨m, fun j => fn_ext fun y hy => ?_⟩
    obtain ⟨i, rfl⟩ := hj j
    have hi : y ∈ L.U i := (mem_wchart_oneTerm (j := fun _ : Fin 1 => i) 0).1 hy
    have hp : y ∈ powChart L (fun _ => i) := mem_powChart.2 hi
    have e := congrArg (gs (𝟙 X) y _) (hm fun _ => i)
    rw [gs_mul _ y _ hp, gs_pow _ y _ hp, gs_zero _ y _ hp, hs y i hi, ht' y i hi] at e
    rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_zero _ y _ hy]
    exact e

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DimEqRankAddDim
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DimEqRankAddDim
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT

theorem dim_eq_rank_add_dim :
    LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => A.g = D.toPre.rank + D.toPre.P.g := by
  rintro ⟨hL, hL₂, -, -, -⟩ R _ _ _ I hadm D A G _ _ hG U
  haveI := hG.geomConnected
  have h₁ := GlobalTheory.finrank_fam_of_expBij hL.secBaseChange R I hadm D A G U.toUnifPre 2 (by norm_num)
    (U.expand 2 (by norm_num))
  have h₂ := (GlobalTheory.FamDimension.main hL.globalFns hL.cube hL.square hL₂.secTwist R I D (FractionRing R) 2
    (by norm_num)).2
  exact Nat.pow_right_injective (le_refl 2) (h₁.symm.trans h₂)

end GlobalTheory.UT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DimEqRankAddDimStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.unif_g_eq_rank_add_g : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => A.g = D.toPre.rank + D.toPre.P.g := by
  first | exact @GlobalTheory.UT.dim_eq_rank_add_dim | exact GlobalTheory.UT.dim_eq_rank_add_dim | (intros; apply GlobalTheory.UT.dim_eq_rank_add_dim <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEvenCubicalTrivialisationSpecialFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEvenCubicalTrivialisationSpecialFibre
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.EvenTriv

theorem exists_even_cubTriv_specialFibre : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (gen : (Over.pullback (jK V)).obj G ≅ A.A), IsMonHom gen.hom → ∀ (P : CP G) (w : G ⟶ G), IsMonHom w → LBIso P.L.L (cubeLB G ![𝟙 G, w] P.L.L) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (Q₀ : TQ (thickObj V (maximalIdeal V) 0 G) X) (P₀ : CP (thickObj V (maximalIdeal V) 0 G)), IsLevelCP (maximalIdeal V) 0 P₀ P → ∃ σ : CubTriv P₀.c Q₀.i, σ.Even := by
  intro _ V _ _ _ _ A G _ _ hG gen _ P w _ hw X _ _ _ Q₀ P₀ ⟨v, hv⟩
  have hp : IsProper (pullback.snd G.hom (jK V)) := by
    have := A.isAb.proper
    have e : pullback.snd G.hom (jK V) = gen.hom.left ≫ A.A.hom := (Over.w gen.hom).symm
    have : IsIso gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map gen.hom))
    exact e ▸ MorphismProperty.comp_mem @IsProper gen.hom.left A.A.hom inferInstance A.isAb.proper
  have hm : (maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  letI : Field (V ⧸ maximalIdeal V ^ (0 + 1)) := Ideal.Quotient.field _
  have hS := IsSemiAbelian.pullback (thick V (maximalIdeal V) 0) G hG
  have := hS.smooth
  have := hS.geomConnected
  have := Q₀.i_hom
  obtain ⟨s⟩ := GlobalTheory.BiextTriv.main (V ⧸ maximalIdeal V ^ (0 + 1)) X (thickObj V (maximalIdeal V) 0 G) P₀.L P₀.c Q₀.i
    Q₀.i_hom
  exact exists_even_of_surjective (surjective_cube_of_generic G hG hp) P w hw P₀
    (IsPullback.of_hasPullback G.hom (thick V (maximalIdeal V) 0)) hv Q₀.i s

end GlobalTheory.EvenTriv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEvenCubicalTrivialisationSpecialFibreStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_even_cubical_trivialisation_specialFibre : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (gen : (Over.pullback (jK V)).obj G ≅ A.A), IsMonHom gen.hom → ∀ (P : CP G) (w : G ⟶ G), IsMonHom w → LBIso P.L.L (cubeLB G ![𝟙 G, w] P.L.L) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (Q₀ : TQ (thickObj V (maximalIdeal V) 0 G) X) (P₀ : CP (thickObj V (maximalIdeal V) 0 G)), IsLevelCP (maximalIdeal V) 0 P₀ P → ∃ σ : CubTriv P₀.c Q₀.i, σ.Even := by
  first | exact @GlobalTheory.EvenTriv.exists_even_cubTriv_specialFibre | exact GlobalTheory.EvenTriv.exists_even_cubTriv_specialFibre | (intros; apply GlobalTheory.EvenTriv.exists_even_cubTriv_specialFibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnifPrePull
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem exists_unifPre_pull : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), I.map φ ≤ I' → IsMonHom bc.hom → ∀ (U : UnifPre I D A G) (eA : (Over.pullback (jK R')).obj G' ≅ A'.A), IsMonHom eA.hom → (∃ wA : LB.Iso (A'.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ))), wA.IsGen) → ∀ (L' : RigLB G') (wL : LB.Iso L'.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf φ)))) (he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = specOf φ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig (rigPullOf (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (specOf φ) he U.LG.L U.LG.rig) → ∃ (U' : UnifPre I' D' A' G') (wL' : LB.Iso U'.LG.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf φ)))), U'.LG = L' ∧ U'.gen = eA ∧ HEq wL' wL ∧ ∀ e : ℕ, ∃ (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I' e G').left ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ∧ ((U'.gt e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ Geo.Tor.PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) h) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R' I' e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → ((bc.hom.left ≫ pullback.fst G.hom (specOf φ))) ((fstG I' e G').left (r z)) ∈ U.LG.L.U jL → (fstG I' e G').left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL' (r ≫ (fstG I' e G').left) z jL jL') := by
  intro hG R R' _ _ _ _ I I' φ D D' hD A A' G _ _ G' _ _ bc hI hbc U eA heA hA L' wL he hwL hrig
  have hgp : IsGrpPullback G' G (specOf φ) (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) :=
    ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G (specOf φ))).congr (Category.id_comp _) rfl
  obtain ⟨c', s', hs', hsr, Hc, Hs⟩ := cubical_symmetry_transport _ _ (specOf φ) G G' _ hgp U.LG L' wL he hwL hrig
    U.cubG U.symG U.symG_gen U.symG_rig
  choose h q' i' hh H using fun e => gtCoord_baseChange_maps R R' φ D.toPre D'.toPre hD I I' hI G G' bc hbc e (U.gt e)
  choose gt' _ Hg using fun e => exists_gtCoord_pull hG R R' φ D.toPre D'.toPre hD I I' hI G G' bc hbc e (U.gt e)
    (h e) (q' e) (i' e) (hh e) (H e)
  have C := fun e => gtCoord_compat_of_pull R R' φ D.toPre D'.toPre hD I I' G G' _ e (U.gt e) (U.gt (e + 1))
    (gt' e) (gt' (e + 1)) (h e) (h (e + 1)) (hh e) (hh (e + 1)) (Hg e) (Hg (e + 1)) (U.gt_q e) (U.gt_t e)
  choose w' hw' sq using fun e => FourthSide.exists_fourth_side _ _ _ _ _ _ D.toPre.P.L D'.toPre.P.L U.LG.L L'.L
    D.toPre.P.isLB D'.toPre.P.isLB U.LG.isLB L'.isLB _ _ (U.gt e).pG.left (gt' e).pG.left (fstG I e G).left
    (fstG I' e G').left (h e) (Hg e).1 (hh e) hD.w wL (U.w e) hD.w_gen hwL (U.w_gen e)
  have RC := unifPull_rig_compat R R' I I' φ D D' hD A A' G G' bc hI hbc U L' wL he hwL hrig gt' w' hw'
    (fun e => (C e).1) (fun e => ⟨h e, hh e, Hg e, sq e⟩)
  have Ev := pulled_comparison_even hG R R' I I' φ D D' hD A A' G G' bc hI hbc U L' wL he hwL hrig gt' w' hw'
    (fun e => (C e).1) (fun e => ⟨h e, hh e, Hg e, sq e⟩) s' hs' Hs
  have Cu := w_cub_pull hG R R' I I' φ D D' hD A A' G G' bc hI hbc U L' wL he hwL hrig gt' w' hw'
    (fun e => (C e).1) (fun e => ⟨h e, hh e, Hg e, sq e⟩) hgp c' Hc
  have ext : LBIso (A'.L.pull eA.hom.left) (L'.L.pull (pullback.fst G'.hom (jK R'))) :=
    LBIso.trans (pull_isLB A'.isLB _) (pull_isLB U.LG.isLB _) (pull_isLB L'.isLB _) hA
      (LBIso.symm (LBIso.chartPull
        (Geo.Tor.chartPullPull L'.L _ _ rfl) (chartPullSame U.LG.L _ _ _ (pullback.fst G'.hom (jK R')) fun _ => rfl) ⟨wL, hwL⟩))
  exact ⟨{ smooth := MorphismProperty.of_isPullback hgp.1 U.smooth
           separated := MorphismProperty.of_isPullback hgp.1 U.separated
           gen := eA, gen_hom := heA, LG := L', cubG := c', symG := s', symG_gen := hs', symG_rig := hsr
           ext := ext, gt := gt', gt_q := fun e => (C e).1, gt_t := fun e => (C e).2
           w := w', w_gen := hw', w_rig := RC.1, w_even := Ev, w_cub := Cu, w_compat := RC.2 },
    wL, rfl, rfl, HEq.rfl, fun e => ⟨h e, hh e, Hg e, sq e⟩⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationBaseChange
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace UnifBaseChange

theorem exists_secScal_one {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (h : Z ⟶ Y) (φ' : K → (Z ⟶ X)) (hφ : φ' = fun k => h ≫ φ k) (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ t : LB.Sec (LB.LinComb L φ' ε), GeneratorPullback.SecScal L φ' ε t φ ε s h 1 := by
  subst hφ
  refine ⟨DVR.pullSec L φ ε s h, fun j₁ j₂ hco => ?_⟩
  obtain rfl : j₁ = j₂ := funext fun k => hco (Sum.inl k) (Sum.inr k) rfl
  rw [resTop, map_one, _root_.one_mul]
  exact (DVR.rs_rs _ _ _).symm

theorem scal_one {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) :
    scal p (1 : R) = 1 := by
  unfold scal
  rw [map_one, map_one]

end UnifBaseChange


open UnifBaseChange ExpandsLinear in
theorem unifBaseChange :
    PolBaseChangeSt → GlobalFnsSt → SecBaseChangeSt → DVR.TwistBaseChangeStatement → UnifBaseChangeSt := by
  intro hP hG hS hT R R' _ _ _ _ I I' hR hR' φ hI D A G _ _ hsa U W hW hη G' _ _ bc hbc A' hg eA heA hwA
    L' wL he hwL hrig
  obtain ⟨D', hD, -, hgD⟩ := exists_degData_isPullDeg hP hG R R' I I' φ hI D W hW hη
  obtain ⟨U', wL', hL, hgen, hw, hlev⟩ := exists_unifPre_pull hG R R' I I' φ D D' hD A A' G G' bc hI hbc
    U.toUnifPre eA heA hwA L' wL he hwL hrig
  subst hL
  obtain rfl := eq_of_heq hw
  haveI := hsa.geomConnected
  haveI := hsa.quasiCompact
  haveI : GeometricallyConnected G'.hom := by
    rw [← Over.w bc.hom]
    have : IsIso bc.hom.left := ((Over.forget _).mapIso bc).isIso_hom
    have : GeometricallyConnected ((Over.pullback (specOf φ)).obj G).hom :=
      inferInstanceAs (GeometricallyConnected (pullback.snd G.hom (specOf φ)))
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_horiz_isIso (fst := bc.hom.left) (f := ((Over.pullback (specOf φ)).obj G).hom) (g := 𝟙 _)
        ⟨(Category.comp_id _).symm⟩) this
  haveI := hR.1
  haveI := hR'.1
  have hexp : ∀ k : ℕ, 1 ≤ k → U'.ExpBij k := by
    intro k hk
    obtain ⟨-, hd⟩ := FamDim.finrank_fam hG hP hT R D.toPre D.tau_bimult (psiOnExists R I hR D) (FractionRing R) k hk
    obtain ⟨hfin, hd'⟩ := FamDim.finrank_fam hG hP hT R' D'.toPre D'.tau_bimult (psiOnExists R' I' hR' D')
      (FractionRing R') k hk
    have hdA := finrank_fam_of_expBij hS R I hR D A G U.toUnifPre k hk (U.expand k hk)
    have hrk : D'.toPre.rank = D.toPre.rank := hD.xe.toIntLinearEquiv.finrank_eq
    refine ExpansionCriterion.expBij_of_onto hS R' I' hR' D' A' G' U' k hk hfin (by rw [hd', hrk, hgD, ← hd, hdA, hg]) fun F₀ => ?_
    obtain ⟨n, F, f, F', f', hF, hspan⟩ := T.exists_integral_families_span_pullDegeneration hP hG hT R R' I hR φ D D'.toPre hD k hk
    have hb : ∀ i, ∃ b : U'.SecK k, U'.Expands k b (F' i) := by
      intro i
      obtain ⟨σ, hσ⟩ := exists_sec_expandsAt_of_integral_family R I hR D A G U.toUnifPre k (fun F => ((U.expand k hk).2 F).exists) (F i) (f i)
        (hF i).1
      obtain ⟨σ', hσ', -⟩ := SecPull.existsUnique_secPull _ _ _ _ U.LG.L U'.LG.L _ U.LG.isLB U'.LG.isLB wL' hwL
        (Fin 1) (fun _ => 𝟙 G'.left) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))
        (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (fun _ => by rw [Category.id_comp, Category.comp_id]) σ
      obtain ⟨b, hb⟩ := exists_secScal_one U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => (k : ℤ))
        (pullback.fst G'.hom (jK R')) (fun _ => pullback.fst G'.hom (jK R'))
        (funext fun _ => (Category.comp_id _).symm) σ'
      refine ⟨b, 1, one_ne_zero, σ', f' i, by rw [scal_one]; exact hb,
        fun α => by rw [scal_one]; exact (hF i).2.1 α, fun e => ?_⟩
      obtain ⟨h, hh⟩ := hlev e
      exact expandsAt_transport R R' I I' D D' A A' G G' U.toUnifPre U' _ hD.w hD.xe _ wL' hD.w_gen hwL
        (ExpGTrans.famφB_pull hD) e e k h ⟨hh.1, hh.2⟩ σ σ' (f i) (f' i) hσ' (hF i).2.2 (hσ e)
    choose b hb using hb
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hspan ▸ Submodule.mem_top : F₀ ∈ _)
    exact ⟨secComb (fun i => scal (pullback.snd G'.hom (jK R')) (c i)) b,
      expands_linear R' I' hR' D' A' G' U' k n b F' c _ hb fun _ => rfl⟩
  exact ⟨D', hD, ⟨U', hexp⟩, rfl, hgen,
    (isPullUnif_iff_stalks R R' I I' φ D D' hD A A' G G' bc U ⟨U', hexp⟩).2 ⟨wL', hwL, he, hrig, hlev⟩⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationBaseChangeStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.uniformisation_baseChange : PolBaseChangeSt → GlobalFnsSt → SecBaseChangeSt → DVR.TwistBaseChangeStatement → UnifBaseChangeSt := by
  first | exact @GlobalTheory.unifBaseChange | exact GlobalTheory.unifBaseChange | (intros; apply GlobalTheory.unifBaseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsFunctional
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnifPowAdm

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Comb

variable {K : Type} [CommRing K] {Y Y' : Scheme.{0}}

def cstHom (π : Y ⟶ Spec (CommRingCat.of K)) (W : Y.Opens) : K →+* Γ(Y, W) :=
  (Y.presheaf.map (homOfLE le_top).op).hom.comp
    (π.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)

theorem res_cstHom (π : Y ⟶ Spec (CommRingCat.of K)) {W W' : Y.Opens} (h : W' ≤ W) (c : K) :
    (Y.presheaf.map (homOfLE h).op).hom (cstHom π W c) = cstHom π W' c :=
  SecOps.resTop_res h _

def IsComb (π : Y ⟶ Spec (CommRingCat.of K)) {M : LB Y} {Λ : Type} [Fintype Λ] (s : LB.Sec M) (c : Λ → K)
    (t : Λ → LB.Sec M) : Prop :=
  ∀ jj, s.f jj = ∑ l, cstHom π (M.U jj) (c l) * (t l).f jj

variable (π : Y ⟶ Spec (CommRingCat.of K)) {M : LB Y} {Λ Λ' : Type} [Fintype Λ] [Fintype Λ']

theorem exists_isComb (c : Λ → K) (t : Λ → LB.Sec M) : ∃ s, IsComb π s c t :=
  ⟨⟨fun jj => ∑ l, cstHom π (M.U jj) (c l) * (t l).f jj, fun i j => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, (t l).compat, res_cstHom, map_mul, res_cstHom, mul_left_comm]⟩, fun _ => rfl⟩

variable {π}

theorem IsComb.trans {s : LB.Sec M} {c : Λ → K} {t : Λ → LB.Sec M} {d : Λ → Λ' → K} {u : Λ' → LB.Sec M}
    (h : IsComb π s c t) (h' : ∀ l, IsComb π (t l) (d l) u) : IsComb π s (fun a => ∑ l, c l * d l a) u := by
  intro jj
  rw [h jj]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [h' _ jj, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]
  exact Finset.sum_comm

theorem IsComb.unique {s s' : LB.Sec M} {c : Λ → K} {t : Λ → LB.Sec M}
    (h : IsComb π s c t) (h' : IsComb π s' c t) : s = s' :=
  SecOps.sec_ext fun jj => (h jj).trans (h' jj).symm

end Comb

section Box

variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {LG : LB G.left} {LG' : LB G'.left}

end Box

section Exp

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ)

theorem expands_comb {Λ : Type} [Fintype Λ] {c : Λ → FractionRing R} {s : Λ → U.SecK k}
    {E : Λ → Fam D.toPre (FractionRing R) k} {s₀ : U.SecK k} (h : ∀ l, U.Expands k (s l) (E l))
    (h₀ : IsComb (pullback.snd G.hom (jK R)) s₀ c s) : U.Expands k s₀ (∑ l, c l • E l) := by
  have e := (Fintype.equivFin Λ).symm
  rw [← e.sum_comp]
  exact ExpandsFracLinear.main R I D A G U k _ (fun l => c (e l)) (fun l => s (e l)) (fun l => E (e l)) s₀
    (fun l => h _) (fun jj => (h₀ jj).trans (e.sum_comp _).symm)

theorem expands_functional (hR : AdmBase R I) {s : U.SecK k} {E E' : Fam D.toPre (FractionRing R) k}
    (h : U.Expands k s E) (h' : U.Expands k s E') : E = E' := by
  have h₀ : U.Expands k SecOps.secZero (∑ l : Fin 2, (![1, -1] : Fin 2 → FractionRing R) l • ![E, E'] l) :=
    expands_comb U k (s := fun _ => s) (fun l => by fin_cases l; exacts [h, h']) (fun jj => by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_neg, map_one, neg_mul, add_neg_cancel]
      rfl)
  have h₁ := GlobalTheory.ExpZero.main R I D A G U k hR _ _ (fun _ => rfl) h₀
  rw [Fin.sum_univ_two] at h₁
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul] at h₁
  exact add_neg_eq_zero.1 h₁

theorem expBij_of_basis (hR : AdmBase R I) {Λ : Type} [Fintype Λ]
    (b : Module.Basis Λ (FractionRing R) (Fam D.toPre (FractionRing R) k)) (σ : Λ → U.SecK k)
    (hσ : ∀ l, U.Expands k (σ l) (b l)) (hspan : ∀ s, ∃ c, IsComb (pullback.snd G.hom (jK R)) s c σ) :
    U.ExpBij k := by
  refine ⟨fun s => ?_, fun E => ?_⟩
  · obtain ⟨c, hc⟩ := hspan s
    exact ⟨_, expands_comb U k hσ hc, fun E hE => expands_functional U k hR hE (expands_comb U k hσ hc)⟩
  · obtain ⟨s, hs⟩ := exists_isComb (pullback.snd G.hom (jK R)) (b.equivFun E) σ
    refine ⟨s, ?_, fun t ht => ?_⟩
    · have := expands_comb U k hσ hs
      rwa [b.sum_equivFun] at this
    · obtain ⟨c, hc⟩ := hspan t
      have e := expands_functional U k hR ht (expands_comb U k hσ hc)
      have e' : b.equivFun E = c := by rw [e, ← b.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
      exact hc.unique (e' ▸ hs)

end Exp

end GlobalTheory.UnifPowAdm
end
end
