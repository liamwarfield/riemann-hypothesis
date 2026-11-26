module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RestrictLineBundleSymmetryUnitsEquivIsoApply
section -- merged from Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.PowerGroupDatum
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum

open ReciprocityTheory.ChartRestriction.G.Semi

variable {S : Scheme.{0}}

structure PowerDatum (j : ℕ) (G' G : Over S) [GrpObj G'] [GrpObj G] where

  pr : Fin j → (G' ⟶ G)

  isMonHom : ∀ i, IsMonHom (pr i)

  bij : ∀ T : Over S, Function.Bijective (fun (x : T ⟶ G') (i : Fin j) => x ≫ pr i)

attribute [instance] PowerDatum.isMonHom

section Power

variable (G : Over S)

variable [GrpObj G]


end Power

section Symm

variable {G : Over S} [GrpObj G]

lemma eSec_inv : eSec G ≫ (GrpObj.inv (X := G)).left = 𝟙 _ ≫ eSec G := by
  rw [Category.id_comp, eSec, ← Over.comp_left]
  congr 1
  simp

variable [IsCommMonObj G]

def IsNormSymm (L : RigLB G) (w : LB.Iso L.L (L.L.pull (GrpObj.inv (X := G)).left)) : Prop :=
  w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit.{1}) (fun _ => eSec G) (fun _ => 1)) L.rig
      (rigPullOf (GrpObj.inv (X := G)).left (𝟙 _) eSec_inv L.L L.rig)

end Symm

namespace PowerDatum

variable {j : ℕ} {G' G : Over S} [GrpObj G'] [GrpObj G] (P : PowerDatum j G' G)

variable [IsCommMonObj G'] [IsCommMonObj G]

end PowerDatum

end GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BoxCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.LB
open GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum (PowerDatum IsNormSymm)

section Units

variable {X Y : Scheme.{0}}

lemma res_self {U : X.Opens} (h : U ≤ U) (x : Γ(X, U)ˣ) : res h x = x := by
  ext
  change (X.presheaf.map (𝟙 (Opposite.op U))).hom (x : Γ(X, U)) = _
  rw [X.presheaf.map_id]
  rfl

lemma res_pullU_id {U W : X.Opens} (h : W ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U) (h' : W ≤ U) (x : Γ(X, U)ˣ) :
    res h (pullU (𝟙 X) U x) = res h' x := by
  ext
  rfl

lemma gen_ext {L : LB X} {s t : LB.Gen L} (h : ∀ i, s.s i = t.s i) : s = t := by
  cases s; cases t
  congr 1
  exact funext h

lemma res_gen_congr {L : LB X} (s : LB.Gen L) {i j : L.ι} (e : i = j) {W : X.Opens}
    (h : W ≤ L.U i) (h' : W ≤ L.U j) : res h (s.s i) = res h' (s.s j) := by
  subst e
  rfl

end Units

section TwoForms

variable {X T : Scheme.{0}} (L : LB X) (f : X ⟶ X)

abbrev SymGen := LB.Gen (LB.LinComb L (K := Fin 2) ![f, 𝟙 X] ![1, -1])

lemma le_two {W : X.Opens} (j : Fin 2 → L.ι) :
    W ≤ wchart L (K := Fin 2) ![f, 𝟙 X] j ↔ W ≤ f ⁻¹ᵁ L.U (j 0) ∧ W ≤ L.U (j 1) := by
  refine ⟨fun h => ⟨h.trans (wchart_le L _ j 0), h.trans (wchart_le L _ j 1)⟩,
    fun h y hy => Set.mem_iInter.2 fun k => ?_⟩
  fin_cases k
  · exact h.1 hy
  · exact h.2 hy

lemma le_one {W : T.Opens} (e : T ⟶ X) (a : PUnit.{1} → L.ι) :
    W ≤ wchart L (fun _ : PUnit.{1} => e) a ↔ W ≤ e ⁻¹ᵁ L.U (a ⟨⟩) :=
  ⟨fun h => h.trans (wchart_le L _ a ⟨⟩), fun h _ hy => Set.mem_iInter.2 fun _ => h hy⟩

lemma toIso_le (p : (PUnit.{1} → L.ι) × L.ι) :
    wchart L (fun _ : PUnit.{1} => f) p.1 ⊓ L.U p.2 ≤
      wchart L (K := Fin 2) ![f, 𝟙 X] ![p.1 ⟨⟩, p.2] :=
  (le_two L f _).2 ⟨(le_one L f _).1 inf_le_left, inf_le_right⟩

lemma ofIso_le (j : Fin 2 → L.ι) :
    wchart L (K := Fin 2) ![f, 𝟙 X] j ≤
      wchart L (fun _ : PUnit.{1} => f) (fun _ => j 0) ⊓ L.U (j 1) :=
  le_inf ((le_one L f _).2 ((le_two L f j).1 le_rfl).1) ((le_two L f j).1 le_rfl).2

def symEquiv : SymGen L f ≃ LB.Iso L (L.pull f) where
  toFun sy := ⟨fun p => res (toIso_le L f p) (ts sy ![p.1 ⟨⟩, p.2])⟩
  invFun w := ⟨fun j => res (ofIso_le L f j) (w.s (fun _ => j 0, j 1))⟩
  left_inv sy := gen_ext fun j => by
    refine (res_res _ _ _).trans ((res_gen_congr sy ?_ _ le_rfl).trans (res_self _ _))
    funext k
    fin_cases k <;> rfl
  right_inv w := gen_ext fun p => (res_res _ _ _).trans (res_self _ _)

lemma restrict_lineBundleSymmetryUnitsEquivIso_apply (sy : SymGen L f) (p : (PUnit.{1} → L.ι) × L.ι) {W : X.Opens}
    (h : W ≤ wchart L (fun _ : PUnit.{1} => f) p.1 ⊓ L.U p.2)
    (h' : W ≤ wchart L (K := Fin 2) ![f, 𝟙 X] ![p.1 ⟨⟩, p.2]) :
    res h ((symEquiv L f sy).s p) = res h' (ts sy ![p.1 ⟨⟩, p.2]) :=
  res_res (toIso_le L f p) h _

lemma res_lcg_two (i j : Fin 2 → L.ι) {W : X.Opens}
    (h : W ≤ wchart L (K := Fin 2) ![f, 𝟙 X] i ⊓ wchart L (K := Fin 2) ![f, 𝟙 X] j)
    (h₁ : W ≤ f ⁻¹ᵁ (L.U (i 0) ⊓ L.U (j 0))) (h₂ : W ≤ L.U (i 1) ⊓ L.U (j 1)) :
    res h (lcg L (K := Fin 2) ![f, 𝟙 X] ![1, -1] i j) =
      res h₁ (pullU f _ (L.g (i 0) (j 0))) * (res h₂ (L.g (i 1) (j 1)))⁻¹ := by
  rw [res_lcg, Fin.prod_univ_two]
  refine congrArg₂ (· * ·) (zpow_one _) ((zpow_neg_one _).trans (congrArg (·⁻¹) ?_))
  exact res_pullU_id _ _ _

lemma res_dg_pull (p q : (PUnit.{1} → L.ι) × L.ι) {W : X.Opens}
    (h : W ≤ wchart L (fun _ : PUnit.{1} => f) p.1 ⊓ L.U p.2 ⊓
      (wchart L (fun _ : PUnit.{1} => f) q.1 ⊓ L.U q.2))
    (h₁ : W ≤ f ⁻¹ᵁ (L.U (p.1 ⟨⟩) ⊓ L.U (q.1 ⟨⟩))) (h₂ : W ≤ L.U p.2 ⊓ L.U q.2) :
    res h (dg (L.pull f) L p q) =
      res h₁ (pullU f _ (L.g (p.1 ⟨⟩) (q.1 ⟨⟩))) * (res h₂ (L.g p.2 q.2))⁻¹ := by
  refine (res_dg (L.pull f) L p q h).trans (congrArg₂ (· * ·) ?_ rfl)
  exact (congrArg (res _) (lcg_pull L f p.1 q.1)).trans (res_res _ _ _)

def SymCompat (sy : SymGen L f) : Prop :=
  ∀ (a b a' b' : L.ι) (W : X.Opens) (h₁ : W ≤ f ⁻¹ᵁ (L.U a ⊓ L.U a')) (h₂ : W ≤ L.U b ⊓ L.U b')
    (h₃ : W ≤ wchart L (K := Fin 2) ![f, 𝟙 X] ![a, b])
    (h₄ : W ≤ wchart L (K := Fin 2) ![f, 𝟙 X] ![a', b']),
    res h₃ (ts sy ![a, b]) =
      res h₁ (pullU f _ (L.g a a')) * (res h₂ (L.g b b'))⁻¹ * res h₄ (ts sy ![a', b'])

lemma isGen_iff_symCompat (sy : SymGen L f) : sy.IsGen ↔ SymCompat L f sy := by
  rw [isGen_iff]
  refine ⟨fun H a b a' b' W h₁ h₂ h₃ h₄ => ?_, fun H i j => ?_⟩
  · have key := congrArg (res (le_inf h₃ h₄)) (H ![a, b] ![a', b'])
    rw [map_mul, res_res, res_res, res_lcg_two L f _ _ _ h₁ h₂] at key
    exact key
  · obtain ⟨a, b, rfl⟩ : ∃ a b, i = ![a, b] := ⟨i 0, i 1, by funext k; fin_cases k <;> rfl⟩
    obtain ⟨a', b', rfl⟩ : ∃ a b, j = ![a, b] := ⟨j 0, j 1, by funext k; fin_cases k <;> rfl⟩
    have h₁ := wchart_inter_le L (K := Fin 2) ![f, 𝟙 X] ![a, b] ![a', b'] 0
    have h₂ := wchart_inter_le L (K := Fin 2) ![f, 𝟙 X] ![a, b] ![a', b'] 1
    rw [← res_self le_rfl (lcg _ _ _ _ _), res_lcg_two L f _ _ _ h₁ h₂]
    exact H a b a' b' _ h₁ h₂ _ _

lemma isGen_symEquiv_iff_symCompat (sy : SymGen L f) :
    (symEquiv L f sy).IsGen ↔ SymCompat L f sy := by
  refine ⟨fun H a b a' b' W h₁ h₂ h₃ h₄ => ?_, fun H p q => ?_⟩
  · have k₃ := h₃.trans (ofIso_le L f _)
    have k₄ := h₄.trans (ofIso_le L f _)
    have key := congrArg (res (le_inf k₃ k₄)) (H (fun _ => a, b) (fun _ => a', b'))
    refine ((restrict_lineBundleSymmetryUnitsEquivIso_apply L f sy (fun _ => a, b) k₃ h₃).symm.trans ?_)
    refine ((res_res _ _ _).symm.trans key).trans ((map_mul _ _ _).trans ?_)
    refine congrArg₂ (· * ·) (res_dg_pull L f (fun _ => a, b) (fun _ => a', b') _ h₁ h₂) ?_
    exact (res_res _ _ _).trans (restrict_lineBundleSymmetryUnitsEquivIso_apply L f sy (fun _ => a', b') k₄ h₄)
  · have h₃ := (inf_le_left (b := wchart L (fun _ : PUnit.{1} => f) q.1 ⊓ L.U q.2)).trans
      (toIso_le L f p)
    have h₄ := (inf_le_right (a := wchart L (fun _ : PUnit.{1} => f) p.1 ⊓ L.U p.2)).trans
      (toIso_le L f q)
    have h₁ := (le_inf h₃ h₄).trans (wchart_inter_le L (K := Fin 2) ![f, 𝟙 X] _ _ 0)
    have h₂ := (le_inf h₃ h₄).trans (wchart_inter_le L (K := Fin 2) ![f, 𝟙 X] _ _ 1)
    refine (restrict_lineBundleSymmetryUnitsEquivIso_apply L f sy p _ h₃).trans ((H _ _ _ _ _ h₁ h₂ h₃ h₄).trans ?_)
    refine congrArg₂ (· * ·) ?_ (restrict_lineBundleSymmetryUnitsEquivIso_apply L f sy q _ h₄).symm
    exact (res_dg_pull L f p q le_rfl h₁ h₂).symm.trans (res_self _ _)

theorem isGen_symEquiv (sy : SymGen L f) : (symEquiv L f sy).IsGen ↔ sy.IsGen :=
  (isGen_symEquiv_iff_symCompat L f sy).trans (isGen_iff_symCompat L f sy).symm

end TwoForms

section Norm

variable {X T : Scheme.{0}} (L : LB X) (f : X ⟶ X) (e : T ⟶ X)

def DiagOne (sy : SymGen L f) : Prop :=
  ∀ (a : L.ι) (W : T.Opens) (h : W ≤ e ⁻¹ᵁ wchart L (K := Fin 2) ![f, 𝟙 X] ![a, a]),
    res h (pullU e _ (ts sy ![a, a])) = 1

def FixesRig (sy : SymGen L f) (r : LB.Gen (L.pull e)) : Prop :=
  ∀ (a b : L.ι) (W : T.Opens) (ha : W ≤ wchart L (fun _ : PUnit.{1} => e) (fun _ => a))
    (hb : W ≤ wchart L (fun _ : PUnit.{1} => e) (fun _ => b))
    (h : W ≤ e ⁻¹ᵁ wchart L (K := Fin 2) ![f, 𝟙 X] ![a, b]),
    res ha (ts r (fun _ => a)) = res h (pullU e _ (ts sy ![a, b])) * res hb (ts r (fun _ => b))

lemma corr_iff_diagOne (he : e ≫ f = e) (sy : SymGen L f) :
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ sy e) (LB.oneGen L) ↔ DiagOne L f e sy := by
  refine ⟨fun H a W h => ?_, fun H j j' hj _ _ => ?_⟩
  · have key := H ![a, a] PEmpty.elim
      (fun k₁ k₂ _ => by fin_cases k₁ <;> fin_cases k₂ <;> rfl) (fun k => k.elim)
      (fun _ k => k.elim)
    have hW : W ≤ wchart L (fun k => e ≫ (![f, 𝟙 X] : Fin 2 → (X ⟶ X)) k) ![a, a] ⊓
        wchart L (Y := T) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim :=
      fun y hy => ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 (h hy) k,
        Set.mem_iInter.2 fun k => k.elim⟩
    have key' := congrArg (res hW) key
    refine ((res_res _ _ _).trans (res_res _ _ _)).symm.trans (key'.trans ?_)
    exact (congrArg (res hW) (map_one _)).trans (map_one _)
  · have h01 : j 0 = j 1 := hj 0 1 (he.trans (Category.comp_id e).symm)
    obtain ⟨a, rfl⟩ : ∃ a, j = ![a, a] := ⟨j 0, by
      funext k
      fin_cases k
      · rfl
      · exact h01.symm⟩
    exact ((res_res _ _ _).trans (H a _ _)).trans (map_one _).symm

lemma diagOne_iff_fixesRig (hL : L.IsLB) (sy : SymGen L f) (hsy : sy.IsGen)
    (r : LB.Gen (L.pull e)) (hr : r.IsGen) : DiagOne L f e sy ↔ FixesRig L f e sy r := by
  refine ⟨fun H a b W ha hb h => ?_, fun H a W h => ?_⟩
  · have hc := (isGen_iff_symCompat L f sy).1 hsy
    set V := wchart L (K := Fin 2) ![f, 𝟙 X] ![a, b] ⊓ L.U a with hV
    have v₁ : V ≤ f ⁻¹ᵁ L.U a := ((le_two L f ![a, b]).1 (inf_le_left : V ≤ _)).1
    have v₂ : V ≤ L.U b := ((le_two L f ![a, b]).1 (inf_le_left : V ≤ _)).2
    have v₃ : V ≤ wchart L (K := Fin 2) ![f, 𝟙 X] ![a, a] :=
      (le_two L f ![a, a]).2 ⟨v₁, inf_le_right⟩
    have hWV : W ≤ e ⁻¹ᵁ V := fun y hy => ⟨h hy, (le_one L e _).1 ha hy⟩
    have k := hc a b a a V (fun y hy => ⟨v₁ hy, v₁ hy⟩) (le_inf v₂ inf_le_right) inf_le_left v₃
    rw [pull_g_self hL f a (fun y hy => ⟨v₁ hy, v₁ hy⟩), _root_.one_mul] at k
    have k' := congrArg (fun x => res hWV (pullU e V x)) k
    simp only [map_mul, map_inv, pullU_res, res_res] at k'
    rw [H a W, _root_.mul_one] at k'
    have k₂ := congrArg (res (le_inf hb ha)) ((isGen_iff L r).1 hr (fun _ => b) (fun _ => a))
    rw [map_mul, res_res, res_res, lcg_pull, res_res] at k₂
    rw [k', k₂, inv_mul_cancel_left]
  · have ha : W ≤ wchart L (fun _ : PUnit.{1} => e) (fun _ => a) :=
      (le_one L e _).2 (h.trans (e.preimage_mono ((le_two L f ![a, a]).1 le_rfl).2))
    exact (mul_right_cancel ((_root_.one_mul _).trans (H a a W ha ha h))).symm

end Norm

section GroupNorm

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

omit [GrpObj G] [IsCommMonObj G] in
lemma prod_punit {M : Type} [CommMonoid M] (g : PUnit.{1} → M) : ∏ k, g k = g ⟨⟩ :=
  Fintype.prod_unique g

lemma maps_iff_fixesRig (L : LB G.left) (r : LB.Gen (L.pull (eSec G)))
    (sy : SymGen L (ι[G]).left) :
    LB.Gen.Maps (LB.linCombIso (symEquiv L _ sy) (K := PUnit.{1}) (fun _ => eSec G) (fun _ => 1))
        r (rigPullOf (ι[G]).left (𝟙 _) GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum.eSec_inv L r) ↔
      FixesRig L (ι[G]).left (eSec G) sy r := by
  have he : eSec G ≫ (ι[G]).left = eSec G := GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum.eSec_inv.trans (Category.id_comp _)

  have main : ∀ (a b : L.ι) (W : (𝟙_ (Over S)).left.Opens)
      (hW : W ≤ wchart (L.pull (ι[G]).left) (fun _ : PUnit.{1} => eSec G) (fun _ _ => a) ⊓
        wchart L (fun _ : PUnit.{1} => eSec G) (fun _ => b))
      (h : W ≤ eSec G ⁻¹ᵁ wchart L (K := Fin 2) ![(ι[G]).left, 𝟙 _] ![a, b]),
      res hW ((LB.linCombIso (symEquiv L _ sy) (K := PUnit.{1}) (fun _ => eSec G)
        (fun _ => 1)).s (fun _ _ => a, fun _ => b)) =
        res h (pullU (eSec G) _ (ts sy ![a, b])) := by
    intro a b W hW h
    refine (congrArg (res hW) ((prod_punit _).trans
      (zpow_one _))).trans ?_
    refine (res_res _ _ _).trans ?_
    exact (res_pullU_eq (eSec G) (toIso_le L _ (fun _ => a, b)) h _ _).symm
  have main₂ : ∀ (a : L.ι) (W : (𝟙_ (Over S)).left.Opens)
      (hW : W ≤ wchart (L.pull (ι[G]).left) (fun _ : PUnit.{1} => eSec G) (fun _ _ => a))
      (ha : W ≤ wchart L (fun _ : PUnit.{1} => eSec G) (fun _ => a)),
      res hW ((rigPullOf (ι[G]).left (𝟙 _) GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum.eSec_inv L r).s (fun _ _ => a)) =
        res ha (ts r (fun _ => a)) := fun a W hW ha =>
    (res_res _ _ _).trans (res_pullU_id _ _ _)
  refine ⟨fun H a b W ha hb h => ?_, fun H p => ?_⟩
  · have hW₁ : W ≤ wchart (L.pull (ι[G]).left) (fun _ : PUnit.{1} => eSec G) (fun _ _ => a) :=
      fun y hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 (h hy) 0
    have key := congrArg (res (le_inf hW₁ hb)) (H (fun _ _ => a, fun _ => b))
    refine (main₂ a W hW₁ ha).symm.trans ((res_res _ _ _).symm.trans (key.trans ?_))
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (main a b W _ h) (res_res _ _ _))
  · obtain ⟨a, b⟩ := p
    have ha : wchart (L.pull (ι[G]).left) (fun _ : PUnit.{1} => eSec G) a ⊓
        wchart L (fun _ : PUnit.{1} => eSec G) b ≤
        wchart L (fun _ : PUnit.{1} => eSec G) (fun _ => a ⟨⟩ ⟨⟩) :=
      inf_le_left.trans (rigPull_le (ι[G]).left (𝟙 _) GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum.eSec_inv L a)
    have h : wchart (L.pull (ι[G]).left) (fun _ : PUnit.{1} => eSec G) a ⊓
        wchart L (fun _ : PUnit.{1} => eSec G) b ≤
        eSec G ⁻¹ᵁ wchart L (K := Fin 2) ![(ι[G]).left, 𝟙 _] ![a ⟨⟩ ⟨⟩, b ⟨⟩] :=
      fun y hy => toIso_le L _ (a ⟨⟩, b ⟨⟩)
        ⟨Set.mem_iInter.1 hy.1 ⟨⟩, Set.mem_iInter.1 hy.2 ⟨⟩⟩
    refine (main₂ (a ⟨⟩ ⟨⟩) _ inf_le_left ha).trans
      ((H (a ⟨⟩ ⟨⟩) (b ⟨⟩) _ ha inf_le_right h).trans ?_)
    exact congrArg₂ (· * ·) ((main (a ⟨⟩ ⟨⟩) (b ⟨⟩) _ le_rfl h).symm.trans (res_self _ _)) rfl

def IsCanonSym (L : LB G.left) (sy : SymGen L (ι[G]).left) : Prop :=
  sy.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ sy (eSec G)) (LB.oneGen L)

theorem isNormSymm_iff (L : RigLB G) (sy : SymGen L.L (ι[G]).left) :
    IsNormSymm L (symEquiv L.L _ sy) ↔ IsCanonSym L.L sy := by
  have he : eSec G ≫ (ι[G]).left = eSec G := GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum.eSec_inv.trans (Category.id_comp _)
  refine (and_congr (isGen_symEquiv L.L _ sy) (maps_iff_fixesRig L.L L.rig sy)).trans ?_
  exact and_congr_right fun hsy => ((corr_iff_diagOne L.L _ _ he sy).trans
    (diagOne_iff_fixesRig L.L _ _ L.isLB sy hsy L.rig L.rigGen)).symm

end GroupNorm

section Pow

variable {S : Scheme.{0}}

variable {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ}

variable [IsCommMonObj G'] [IsCommMonObj G]

end Pow

section Clauses

variable {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
  [IsCommMonObj G] {j : ℕ}

end Clauses

end GlobalTheory.BoxCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PullRigIsSymmetric
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.HomComb

section Generators

variable {X X' Y Z : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K]

def combGen (F : J → (X' ⟶ X)) (δ : J → ℤ) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) : LB.Gen (LB.LinComb (LB.LinComb L F δ) φ ε) where
  s := fun jj => ∏ i, res (GeneratorPullback.box_le L F φ jj i) ((t i).s (fun k _ => jj k i)) ^ δ i

theorem gm_combGen (F : J → (X' ⟶ X)) (δ : J → ℤ) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) (r : Z ⟶ Y) (z : Z)
    (jj : K → (LB.LinComb L F δ).ι) (h : r z ∈ LB.wchart (LB.LinComb L F δ) φ jj) :
    gm r z (LB.wchart (LB.LinComb L F δ) φ jj) ((combGen L F δ φ ε t).s jj) =
      ∏ i, gm r z (LB.wchart (L.pull (F i)) φ (fun k _ => jj k i)) ((t i).s (fun k _ => jj k i)) ^ δ i :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ =>
    (map_zpow _ _ _).trans (congrArg (· ^ δ i) (gm_res r z _ h _)))

theorem trF_comb (F : J → (X' ⟶ X)) (δ : J → ℤ) (φ : K → (Y ⟶ X')) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z)
    (jj jj' : K → (LB.LinComb L F δ).ι) (h : r z ∈ LB.wchart (LB.LinComb L F δ) φ jj)
    (h' : r z ∈ LB.wchart (LB.LinComb L F δ) φ jj') :
    trF (L := LB.LinComb L F δ) φ ε r z jj jj' =
      ∏ i, trF (L := L.pull (F i)) φ ε r z (fun k _ => jj k i) (fun k _ => jj' k i) ^ δ i := by
  unfold trF
  simp only [← Finset.prod_zpow]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  refine (congrArg (· ^ ε k) (gm_linComb L F δ (r ≫ φ k) z (jj k) (jj' k) (Set.mem_iInter.1 h k)
    (Set.mem_iInter.1 h' k))).trans ?_
  refine (Finset.prod_zpow _ _ _).symm.trans (Finset.prod_congr rfl fun i _ => ?_)
  rw [← zpow_mul, mul_comm, zpow_mul]
  refine congrArg (fun q => (q ^ ε k) ^ δ i) ?_
  exact (gm_pull_g L (F i) (r ≫ φ k) z (fun _ => jj k i) (fun _ => jj' k i)
    (Set.mem_iInter.1 (GeneratorPullback.box_le L F φ jj i h) k) (Set.mem_iInter.1 (GeneratorPullback.box_le L F φ jj' i h') k)).symm

theorem isGen_combGen (F : J → (X' ⟶ X)) (δ : J → ℤ) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) (ht : ∀ i, (t i).IsGen) :
    (combGen L F δ φ ε t).IsGen := by
  refine isGen_of_gm _ fun y jj jj' h h' => ?_
  rw [gm_combGen L F δ φ ε t (𝟙 Y) y jj h, gm_combGen L F δ φ ε t (𝟙 Y) y jj' h', trF_comb L F δ φ ε (𝟙 Y) y jj jj' h h',
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← mul_zpow]
  exact congrArg (· ^ δ i) (gen_trans (ht i) (𝟙 Y) y (GeneratorPullback.box_le L F φ jj i h) (GeneratorPullback.box_le L F φ jj' i h'))

variable {L}

theorem good_factor {F : J → (X' ⟶ X)} {δ : J → ℤ} {z : Z} {I : (Z ⟶ X') → (LB.LinComb L F δ).ι}
    (hI : Good (LB.LinComb L F δ) z I) (i : J) : Good (L.pull (F i)) z (fun χ _ => I χ i) :=
  fun χ => mem_pull.2 (Set.mem_iInter.1 (hI χ) i)

theorem val_combGen {F : J → (X' ⟶ X)} {δ : J → ℤ} {φ : K → (Y ⟶ X')} {ε : K → ℤ}
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) (r : Z ⟶ Y) {z : Z} {I : (Z ⟶ X') → (LB.LinComb L F δ).ι}
    (hI : Good (LB.LinComb L F δ) z I) :
    val (combGen L F δ φ ε t) r z I = ∏ i, val (t i) r z (fun χ _ => I χ i) ^ δ i :=
  gm_combGen L F δ φ ε t r z _ (hI.mem φ r)

end Generators

theorem isCub_prod {B U J : Type} [CommGroup B] [CommGroup U] [Fintype J] (θ : J → B → B → B → U)
    (h : ∀ i, IsCub (θ i)) (δ : J → ℤ) : IsCub (fun x y z => ∏ i, θ i x y z ^ δ i) := by
  constructor
  · intro x y
    exact Finset.prod_eq_one fun i _ => by rw [(h i).face, one_zpow]
  · intro x y z
    exact Finset.prod_congr rfl fun i _ => by rw [(h i).s01]
  · intro x y z
    exact Finset.prod_congr rfl fun i _ => by rw [(h i).s12]
  · intro x x' x'' y
    simp only [← Finset.prod_mul_distrib, ← mul_zpow]
    exact Finset.prod_congr rfl fun i _ => by rw [(h i).coc]

variable {S : Scheme.{0}} {G A : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A]
  {J : Type} [Fintype J]

def pullRig (L : RigLB G) (f : A ⟶ G) [IsMonHom f] : RigLB A :=
  (CubeMap.ofHom f).rigLB L (LB.isLB_linComb L.isLB _ _)
    (LBxP.isGen_pullAlong L.L f.left (𝟙 _) (fun _ : PUnit => eSec G) (fun _ => 1) (fun _ => eSec A)
      (fun _ => (CubeMap.ofHom f).e_comm) L.rig L.rigGen)

def pullCub {L : RigLB G} (c : CubicalStr G L) (f : A ⟶ G) [IsMonHom f] : CubicalStr A (pullRig L f) :=
  CubePf.cubical (CubeMap.ofHom f) L c _ _

theorem pullRig_isSymmetric {L : RigLB G} (c : CubicalStr G L) (hs : L.IsSymmetric) (f : A ⟶ G) [IsMonHom f] :
    (pullRig L f).IsSymmetric := by
  obtain ⟨_, _, -, h⟩ := proved_CubePullSt S S G A (CubeMap.ofHom f) L c
  exact h hs

variable (u : J → (A ⟶ G)) [∀ i, IsMonHom (u i)] (δ : J → ℤ)

def combRig (L : RigLB G) : RigLB A where
  L := LB.LinComb L.L (fun i => (u i).left) δ
  rig := combGen L.L (fun i => (u i).left) δ (fun _ : PUnit => eSec A) (fun _ => 1) fun i => (pullRig L (u i)).rig
  isLB := LB.isLB_linComb L.isLB _ _
  rigGen := isGen_combGen _ _ _ _ _ _ fun i => (pullRig L (u i)).rigGen

def combCub {L : RigLB G} (c : CubicalStr G L) : CubicalStr A (combRig u δ L) :=
  CubTransport.cubicalOfVal (L := combRig u δ L)
    (combGen L.L (fun i => (u i).left) δ (thφ A (x3 A)) thε fun i => (pullCub c (u i)).t)
    (isGen_combGen _ _ _ _ _ _ fun i => (pullCub c (u i)).isGen) fun T z I hI => by
      have hCub (i : J) : IsCub (cubV (pullCub c (u i)) (T := T) z (fun χ _ => I χ i)) := by
        let ci := pullCub c (u i)
        have hi := good_factor hI i
        constructor
        · intro x y
          have hface := val_corr hi (ci.face 0) (lift x y).left
          refine Eq.trans ?_ (hface.trans (val_one _))
          refine Eq.trans ?_ (val_cub ci (lift x y) hi (pzero A _) (x2 A 0) (x2 A 1)).symm
          congr 1 <;> simp [x2, pzero, Hom.one_def]
        · intro x y w
          refine ((val_corr hi ci.cubeSymmetric_swap_first (lift x (lift y w)).left).trans
            (val_cub ci (lift x (lift y w)) hi _ _ _)).trans ?_
          congr 1 <;> simp [x3]
        · intro x y w
          refine ((val_corr hi ci.cubeSymmetric_swap_last (lift x (lift y w)).left).trans
            (val_cub ci (lift x (lift y w)) hi _ _ _)).trans ?_
          congr 1 <;> simp [x3]
        · intro x x' x'' y
          let r := lift x (lift x' (lift x'' y))
          have e := ((val_mul hi _ _ r.left).trans
            (congrArg₂ (· * ·) (val_cub ci r hi _ _ _) (val_cub ci r hi _ _ _))).symm.trans
            ((val_corr hi ci.cocycle r.left).trans ((val_mul hi _ _ r.left).trans
              (congrArg₂ (· * ·) (val_cub ci r hi _ _ _) (val_cub ci r hi _ _ _))))
          have a₀ : r ≫ x4 A 0 = x := by simp [r, x4]
          have a₁ : r ≫ x4 A 1 = x' := by simp [r, x4]
          have a₂ : r ≫ x4 A 2 = x'' := by simp [r, x4]
          have a₃ : r ≫ x4 A 3 = y := by simp [r, x4]
          have b₀ : r ≫ padd A (x4 A 0) (x4 A 1) = x * x' :=
            (MonObj.comp_mul _ _ _).trans (by rw [a₀, a₁])
          have b₁ : r ≫ padd A (x4 A 1) (x4 A 2) = x' * x'' :=
            (MonObj.comp_mul _ _ _).trans (by rw [a₁, a₂])
          rwa [b₀, b₁, a₀, a₁, a₂, a₃] at e
      have h := isCub_prod _ hCub δ
      convert h using 4 with x y w
      exact val_combGen (fun i => (pullCub c (u i)).t) _ hI

theorem isSymmetric_iff (L : RigLB G) : L.IsSymmetric ↔ ∃ sy, BoxCompare.IsCanonSym L.L sy := by
  refine ⟨fun ⟨_, w, h⟩ => ?_, fun ⟨sy, h⟩ => ⟨GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum.eSec_inv, _, (BoxCompare.isNormSymm_iff L sy).2 h⟩⟩
  obtain ⟨sy, rfl⟩ := (BoxCompare.symEquiv L.L _).surjective w
  exact ⟨sy, (BoxCompare.isNormSymm_iff L sy).1 h⟩

theorem combRig_isSymmetric {L : RigLB G} (c : CubicalStr G L) (hs : L.IsSymmetric) :
    (combRig u δ L).IsSymmetric := by
  choose sy hsy using fun i => (isSymmetric_iff _).1 (pullRig_isSymmetric c hs (u i))
  refine (isSymmetric_iff _).2 ⟨combGen L.L (fun i => (u i).left) δ _ _ sy,
    isGen_combGen _ _ _ _ _ _ fun i => (hsy i).1, corr_of_val (combRig u δ L).isLB fun y I hI => ?_⟩
  refine (val_pull hI _ _ _).trans (Eq.trans ?_ (val_one _).symm)
  refine (val_combGen sy _ hI).trans (Finset.prod_eq_one fun i _ => ?_)
  have e := (val_pull (good_factor hI i) (sy i) (eSec A) (𝟙 _)).symm.trans
    ((val_corr (good_factor hI i) (hsy i).2 (𝟙 _)).trans (val_one _))
  exact (congrArg (· ^ δ i) e).trans (one_zpow _)

end GlobalTheory.HomComb
end
end

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Serre GlobalTheory.CechPic GlobalTheory.HermTensorLB GlobalTheory.HomComb
open scoped CategoryTheory.Obj

namespace GlobalTheory.HomComb

open ReciprocityTheory.ChartRestriction.G.Out

section Transport

variable {X X' W W' Y Y' Y₀ Y₀' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {Φ : W' ⟶ W}
  {J K : Type} [Fintype J] [Fintype K] {u : J → (W ⟶ X)} {u' : J → (W' ⟶ X')}

theorem mem_of_comm {f : Z ⟶ W'} {g : W' ⟶ X} {f' : Z ⟶ W} {g' : W ⟶ X} (e : f ≫ g = f' ≫ g') (z : Z) {U : X.Opens}
    (h : g (f z) ∈ U) : g' (f' z) ∈ U := by
  have : (f ≫ g) z ∈ U := h
  rw [e] at this
  exact this

def combIso (hu : ∀ i, u' i ≫ F = Φ ≫ u i) (δ : J → ℤ) (w : LB.Iso L' (L.pull F)) :
    LB.Iso (LB.LinComb L' u' δ) ((LB.LinComb L u δ).pull Φ) where
  s p := ∏ i, res (U := u' i ⁻¹ᵁ ((L.pull F).U (fun _ => p.1 ⟨⟩ i) ⊓ L'.U (p.2 i)))
    (V := ((LB.LinComb L u δ).pull Φ).U p.1 ⊓ (LB.LinComb L' u' δ).U p.2)
    (fun y hy => ⟨mem_pull.2 (mem_of_comm (hu i).symm y (Set.mem_iInter.1 (mem_pull.1 hy.1) i)),
      Set.mem_iInter.1 hy.2 i⟩) (pullU (u' i) _ (w.s (fun _ => p.1 ⟨⟩ i, p.2 i))) ^ δ i

theorem gw_combIso (hu : ∀ i, u' i ≫ F = Φ ≫ u i) (δ : J → ℤ) (w : LB.Iso L' (L.pull F)) (f : Z ⟶ W') (z : Z)
    (j : J → L.ι) (k : J → L'.ι) (hj : Φ (f z) ∈ LB.wchart L u j) (hk : f z ∈ LB.wchart L' u' k) :
    gw (L := LB.LinComb L u δ) (L' := LB.LinComb L' u' δ) (combIso hu δ w) f z j k =
      ∏ i, gw w (f ≫ u' i) z (j i) (k i) ^ δ i := by
  have hm : f z ∈ ((LB.LinComb L u δ).pull Φ).U (fun _ => j) ⊓ (LB.LinComb L' u' δ).U k := ⟨mem_pull.2 hj, hk⟩
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ => (map_zpow _ _ _).trans (congrArg (· ^ δ i) ?_))
  exact (gm_res f z _ hm _).trans (gm_pull f (u' i) z ((L.pull F).U (fun _ => j i) ⊓ L'.U (k i))
    ⟨mem_pull.2 (mem_of_comm (hu i).symm (f z) (Set.mem_iInter.1 hj i)), Set.mem_iInter.1 hk i⟩ _)

theorem pGen_combIso (hu : ∀ i, u' i ≫ F = Φ ≫ u i) (δ : J → ℤ) {w : LB.Iso L' (L.pull F)} (hw : PGen w) :
    PGen (L := LB.LinComb L u δ) (L' := LB.LinComb L' u' δ) (combIso hu δ w) := by
  intro Z f z j j' k k' hj hj' hk hk'
  rw [gw_combIso hu δ w f z j k hj hk, gw_combIso hu δ w f z j' k' hj' hk']
  refine Eq.trans ?_ (congrArg (· * _) (congrArg₂ (fun a b => a * b⁻¹) (gm_linComb L u δ (f ≫ Φ) z j j' hj hj')
    (gm_linComb L' u' δ f z k k' hk hk'))).symm
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hw Z (f ≫ u' i) z (j i) (j' i) (k i) (k' i) (mem_of_comm (hu i).symm (f z) (Set.mem_iInter.1 hj i))
    (mem_of_comm (hu i).symm (f z) (Set.mem_iInter.1 hj' i)) (Set.mem_iInter.1 hk i) (Set.mem_iInter.1 hk' i),
    mul_zpow, mul_zpow, inv_zpow, Category.assoc, Category.assoc, hu]

theorem gm_pullAlong (L : LB X) (F : X' ⟶ X) (h : Y' ⟶ Y) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (ψ : K → (Y' ⟶ X'))
    (hψ : ∀ k, ψ k ≫ F = h ≫ φ k) (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y') (z : Z) (jj : K → PUnit → L.ι)
    (hz : r z ∈ LB.wchart (L.pull F) ψ jj) :
    gm r z (LB.wchart (L.pull F) ψ jj) ((GeneratorPullback.pullAlong L F h φ ε ψ hψ t).s jj) =
      gm (r ≫ h) z (LB.wchart L φ fun k => jj k ⟨⟩) (t.s fun k => jj k ⟨⟩) :=
  (gm_res r z _ hz _).trans (gm_pull r h z _ (GeneratorPullback.pullAlong_le L F h φ ψ hψ jj hz) _)

theorem pMaps_combIso (hu : ∀ i, u' i ≫ F = Φ ≫ u i) (δ : J → ℤ) {w : LB.Iso L' (L.pull F)} {ε : K → ℤ}
    {ψ' : K → (Y₀' ⟶ X')} {ψ : K → (Y₀ ⟶ X)} {a₀ : LB.Gen (LB.LinComb L' ψ' ε)} {t₀ : LB.Gen (LB.LinComb L ψ ε)}
    {h₀ : Y₀' ⟶ Y₀} (H : PMaps w ψ' ψ ε a₀ t₀ h₀) {φ' : K → (Y' ⟶ W')} {φ : K → (Y ⟶ W)} {h : Y' ⟶ Y}
    (hφ : ∀ k, φ' k ≫ Φ = h ≫ φ k) {ρ' : J → (Y' ⟶ Y₀')} {ρ : J → (Y ⟶ Y₀)}
    (hρ' : ∀ i k, φ' k ≫ u' i = ρ' i ≫ ψ' k) (hρ : ∀ i k, φ k ≫ u i = ρ i ≫ ψ k) (hh : ∀ i, h ≫ ρ i = ρ' i ≫ h₀) :
    PMaps (L := LB.LinComb L u δ) (L' := LB.LinComb L' u' δ) (combIso hu δ w) φ' φ ε
      (combGen L' u' δ φ' ε fun i => GeneratorPullback.pullAlong L' (u' i) (ρ' i) ψ' ε φ' (hρ' i) a₀)
      (combGen L u δ φ ε fun i => GeneratorPullback.pullAlong L (u i) (ρ i) ψ ε φ (hρ i) t₀) h := by
  intro Z r z p q hp hq
  have mp : (r ≫ h) z ∈ LB.wchart (LB.LinComb L u δ) φ p :=
    Set.mem_iInter.2 fun k => mem_of_comm (hφ k) (r z) (hp k)
  have mq : r z ∈ LB.wchart (LB.LinComb L' u' δ) φ' q := Set.mem_iInter.2 hq
  rw [gm_combGen L u δ φ ε _ (r ≫ h) z p mp, gm_combGen L' u' δ φ' ε _ r z q mq,
    Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) (gw_combIso hu δ w (r ≫ φ' k) z (p k) (q k) (hp k) (hq k))]
  simp only [← Finset.prod_zpow]
  rw [Finset.prod_comm, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gm_pullAlong _ _ _ _ _ _ _ _ _ _ _ (GeneratorPullback.box_le L u φ p i mp),
    gm_pullAlong _ _ _ _ _ _ _ _ _ _ _ (GeneratorPullback.box_le L' u' φ' q i mq), Category.assoc, hh, ← Category.assoc,
    H Z (r ≫ ρ' i) z (fun k => p k i) (fun k => q k i)
      (fun k => by
        have e := mem_of_comm (hu i).symm (φ' k (r z)) (Set.mem_iInter.1 (hp k) i)
        exact mem_of_comm (hρ' i k) (r z) (U := F ⁻¹ᵁ L.U (p k i)) e)
      (fun k => mem_of_comm (hρ' i k) (r z) (Set.mem_iInter.1 (hq k) i)),
    mul_zpow, ← Finset.prod_zpow]
  refine congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_)
  rw [← zpow_mul, ← zpow_mul, mul_comm, Category.assoc, Category.assoc, hρ']

end Transport

variable {S S' : Scheme.{0}} {G A : Over S} {G' A' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A]
  [GrpObj G'] [IsCommMonObj G'] [GrpObj A'] [IsCommMonObj A'] {J : Type} [Fintype J]

theorem isPullCubical_comb (m : CubeMap G' G) (n : CubeMap A' A) (he : n.e = m.e) (u : J → (A ⟶ G))
    [∀ i, IsMonHom (u i)] (u' : J → (A' ⟶ G')) [∀ i, IsMonHom (u' i)] (δ : J → ℤ)
    (hu : ∀ i, (u' i).left ≫ m.F = n.F ≫ (u i).left) {L : RigLB G} {L' : RigLB G'} {c : CubicalStr G L}
    {c' : CubicalStr G' L'} (H : m.IsPullCubical c' c) : n.IsPullCubical (combCub u' δ c') (combCub u δ c) := by
  obtain ⟨w, hw, hr, ht⟩ := H
  refine ⟨combIso hu δ w, (isGen_iff _).2 (pGen_combIso hu δ ((isGen_iff _).1 hw)), ?_, ?_⟩
  · refine (maps_iff _ _ (fun _ => eSec A) _ _ (combRig u δ L).rig n.e _ (rigPull_le _ _ n.e_comm _) (fun _ => rfl)).2 ?_
    exact pMaps_combIso hu δ
      ((maps_iff _ _ (fun _ => eSec G) _ _ L.rig m.e _ (rigPull_le _ _ m.e_comm _) (fun _ => rfl)).1 hr)
      (fun _ => n.e_comm) (fun i _ => (CubeMap.ofHom (u' i)).e_comm) (fun i _ => (CubeMap.ofHom (u i)).e_comm)
      (fun i => (Category.comp_id _).trans (he.trans (Category.id_comp _).symm))
  · refine (maps_iff _ _ (thφ A (x3 A)) _ _ (combCub u δ c).t n.F3 _ (n.theta_le _) (fun _ => rfl)).2 ?_
    refine pMaps_combIso hu δ
      ((maps_iff _ _ (thφ G (x3 G)) _ _ c.t m.F3 _ (m.theta_le _) (fun _ => rfl)).1 ht)
      (fun I => n.psum_comm I.down) (fun i I => (CubeMap.ofHom (u' i)).psum_comm I.down)
      (fun i I => (CubeMap.ofHom (u i)).psum_comm I.down) (fun i => hom_ext_triple _ fun l => ?_)
    rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, cubeMap_comp_proj_three, Category.assoc, Category.assoc, cubeMap_comp_proj_three,
      ← Category.assoc (CubeMap.ofHom (u' i)).F3, cubeMap_comp_proj_three, Category.assoc]
    exact congrArg _ (hu i).symm

end GlobalTheory.HomComb

namespace GlobalTheory.HermTensor

variable {S : Scheme.{0}} {G A T T' : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A]

theorem isMonHom_psum [GrpObj T] {n : ℕ} (x : Fin n → (T ⟶ G)) (hx : ∀ i, IsMonHom (x i)) (I : Finset (Fin n)) :
    IsMonHom (psum G x I) := by
  unfold psum
  induction (List.finRange n).filter (· ∈ I) with
  | nil => exact isMonHom_one
  | cons k l ih =>
    have := hx k
    exact isMonHom_mul (x k) _

variable {O : Type} [CommRing O] [StarRing O] {M : Type} [AddCommGroup M] [Module O M]
  {a : OAct O G} {b : OAct O A} (t : IsTensor A b G a M) (P : Summand O M) (h : HermForm O M)

def gen (i : Fin P.n) : M := P.proj (Pi.single i 1)

def gram (i j : Fin P.n) : O := h (gen P j) (gen P i)

def crd (i : Fin P.n) : A ⟶ G := t.mapLeft (IsTensor.self a) (LinearMap.proj i ∘ₗ P.incl)


omit [StarRing O] in
theorem isLinearHom_crd (i : Fin P.n) : IsLinearHom b a (crd t P i) := t.isLinearHom_mapLeft _ _

instance isMonHom_crd (i : Fin P.n) : IsMonHom (crd t P i) := IsTensor.isMonHom_mapLeft _ _ _


abbrev BIx (n : ℕ) : Type := (Fin n × Fin n) × ULift.{0} (Finset (Fin 2))

def biExp (n : ℕ) (q : BIx n) : ℤ := (-1) ^ (2 - q.2.down.card)

def biMap (x z : T ⟶ A) (q : BIx P.n) : T ⟶ G :=
  psum G ![x ≫ crd t P q.1.1, z ≫ crd t P q.1.2 ≫ a.act (gram P h q.1.1 q.1.2)] q.2.down

instance isMonHom_biMap [GrpObj T] (x z : T ⟶ A) [IsMonHom x] [IsMonHom z] (q : BIx P.n) :
    IsMonHom (biMap t P h x z q) :=
  isMonHom_psum _ (fun i => by
    have := a.hom
    fin_cases i
    · exact inferInstanceAs (IsMonHom (x ≫ crd t P q.1.1))
    · exact inferInstanceAs (IsMonHom (z ≫ crd t P q.1.2 ≫ a.act (gram P h q.1.1 q.1.2)))) _

def biLB (L : LB G.left) (x z : T ⟶ A) : LB T.left :=
  LB.LinComb L (fun q => (biMap t P h x z q).left) (biExp P.n)

theorem isLB_biLB {L : LB G.left} (hL : L.IsLB) (x z : T ⟶ A) : (biLB t P h L x z).IsLB := LB.isLB_linComb hL _ _

def bi (c : Pic G.left) (x z : T ⟶ A) : Pic T.left :=
  ∑ i, ∑ j, lam c (x ≫ crd t P i) (z ≫ crd t P j ≫ a.act (gram P h i j))

theorem cls_biLB {L : LB G.left} (hL : L.IsLB) (x z : T ⟶ A) (hb : (biLB t P h L x z).IsLB) :
    cls _ hb = bi t P h (cls L hL) x z := by
  refine (cls_linComb hL _ _ hb).trans ?_
  refine (Fintype.sum_prod_type _).trans ((Fintype.sum_prod_type _).trans ?_)
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hc : (cubeLB G ![x ≫ crd t P i, z ≫ crd t P j ≫ a.act (gram P h i j)] L).IsLB := LB.isLB_linComb hL _ _
  refine Eq.trans ?_ (cls_cube_two hL _ _ hc)
  refine Eq.trans ?_ (cls_linComb hL _ _ hc).symm
  refine Finset.sum_congr rfl fun I _ => ?_
  simp only [biMap, biExp]

theorem pull_bi (c : Pic G.left) (g : T' ⟶ T) (x z : T ⟶ A) :
    pull g.left (bi t P h c x z) = bi t P h c (g ≫ x) (g ≫ z) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [bi, map_sum, pull_lam, Category.assoc]

theorem bi_one_left (c : Pic G.left) (z : T ⟶ A) : bi t P h c 1 z = 0 := by
  simp only [bi, MonObj.one_comp, lam_one_left, Finset.sum_const_zero]

def IsAdj (a : OAct O G) (L : LB G.left) : Prop :=
  ∀ c, LBIso (cubeLB G ![fst G G ≫ a.act c, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ a.act (star c)] L)

section Laws

variable {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ s : LB.Gen (Theta G L), s.IsGen) (hadj : IsAdj a L)


omit [IsCommMonObj G] in
include hadj in
theorem lam_act [IsCommMonObj G] (x y : T ⟶ G) (c : O) :
    lam (cls L hL) (x ≫ a.act c) y = lam (cls L hL) x (y ≫ a.act (star c)) := by
  have h₀ := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).2 (hadj c)
  have h' := congrArg (pull (lift x y).left)
    ((cls_cube_two hL _ _ _).symm.trans (h₀.trans (cls_cube_two hL _ _ _)))
  simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h'


include hΘ in
theorem bi_mul_left (x y z : T ⟶ A) :
    bi t P h (cls L hL) (x * y) z = bi t P h (cls L hL) x z + bi t P h (cls L hL) y z := by
  simp only [bi, MonObj.mul_comp, lam_mul_left hL hΘ, Finset.sum_add_distrib]


include hΘ in
theorem bi_mul_right (x y z : T ⟶ A) :
    bi t P h (cls L hL) x (y * z) = bi t P h (cls L hL) x y + bi t P h (cls L hL) x z := by
  have := a.hom
  simp only [bi, MonObj.mul_comp, lam_mul_right hL hΘ, Finset.sum_add_distrib]


include hadj in
theorem bi_comm (x z : T ⟶ A) : bi t P h (cls L hL) x z = bi t P h (cls L hL) z x := by
  rw [bi, bi, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [lam_comm, ← Category.assoc z, lam_act hL hadj, Category.assoc, gram, gram, h.star_apply]


include hadj in
theorem bi_act (x z : T ⟶ A) (c : O) :
    bi t P h (cls L hL) (x ≫ b.act c) z = bi t P h (cls L hL) x (z ≫ b.act (star c)) := by
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Category.assoc, (isLinearHom_crd t P i).comm, ← Category.assoc x, lam_act hL hadj, Category.assoc,
    Category.assoc, Category.assoc, act_comm a, ← Category.assoc (b.act _), (isLinearHom_crd t P j).comm,
    Category.assoc]



include hΘ hadj in
theorem lam_bi {w : O} (hw : w + star w = 1) (x z : T ⟶ A) :
    lam (bi t P h (cls L hL) (𝟙 A) (b.act w)) x z = bi t P h (cls L hL) x z := by
  have := b.hom w
  have e : bi t P h (cls L hL) x z = bi t P h (cls L hL) x (z ≫ b.act w) + bi t P h (cls L hL) z (x ≫ b.act w) := by
    rw [bi_comm t P h hL hadj z, bi_act t P h hL hadj, ← bi_mul_right t P h hL hΘ, ← MonObj.comp_mul, ← b.add, hw,
      b.one, Category.comp_id]
  rw [lam, e]
  simp only [pull_bi, Category.comp_id, MonObj.mul_comp, bi_one_left, bi_mul_left t P h hL hΘ,
    bi_mul_right t P h hL hΘ]
  abel




end Laws

section Rigid

variable [GrpObj T] [IsCommMonObj T] (x z : T ⟶ A) [IsMonHom x] [IsMonHom z]

def biRig (L : RigLB G) : RigLB T := combRig (biMap t P h x z) (biExp P.n) L

def biCub {L : RigLB G} (c : CubicalStr G L) : CubicalStr T (biRig t P h x z L) := combCub _ _ c

theorem biRig_isSymmetric {L : RigLB G} (c : CubicalStr G L) (hs : L.IsSymmetric) : (biRig t P h x z L).IsSymmetric :=
  combRig_isSymmetric _ _ c hs

end Rigid

def poi (L : RigLB G) : RigLB (A ⊗ A) := biRig t P h (fst A A) (snd A A) L

def theta (w : O) (L : RigLB G) : RigLB A := haveI := b.hom w; biRig t P h (𝟙 A) (b.act w) L

def thetaCub (w : O) {L : RigLB G} (c : CubicalStr G L) : CubicalStr A (theta t P h w L) :=
  haveI := b.hom w; biCub t P h (𝟙 A) (b.act w) c

theorem theta_isSymmetric (w : O) {L : RigLB G} (c : CubicalStr G L) (hs : L.IsSymmetric) :
    (theta t P h w L).IsSymmetric :=
  haveI := b.hom w; biRig_isSymmetric t P h (𝟙 A) (b.act w) c hs

theorem cls_poi (L : RigLB G) : cls _ (poi t P h L).isLB = bi t P h (cls L.L L.isLB) (fst A A) (snd A A) :=
  cls_biLB t P h L.isLB _ _ _

theorem cls_theta (w : O) (L : RigLB G) :
    cls _ (theta t P h w L).isLB = bi t P h (cls L.L L.isLB) (𝟙 A) (b.act w) :=
  cls_biLB t P h L.isLB _ _ _

theorem biLB_iso_pull (L : RigLB G) (x z : T ⟶ A) :
    LBIso (biLB t P h L.L x z) ((poi t P h L).L.pull (lift x z).left) := by
  refine (cls_eq_iff (isLB_biLB t P h L.isLB x z) (LB.isLB_linComb (poi t P h L).isLB _ _)).1 ?_
  rw [cls_biLB t P h L.isLB, cls_pull (poi t P h L).isLB, cls_poi, pull_bi, lift_fst, lift_snd]

theorem theta_iso_pull (w : O) (L : RigLB G) :
    LBIso (theta t P h w L).L ((poi t P h L).L.pull (lift (𝟙 A) (b.act w)).left) :=
  biLB_iso_pull t P h L _ _

section ThetaLaws

variable {L : RigLB G} (c : CubicalStr G L) (hadj : IsAdj a L.L) {w : O} (hw : w + star w = 1)


include c hadj hw

theorem lam_theta (x z : T ⟶ A) : lam (cls _ (theta t P h w L).isLB) x z = bi t P h (cls L.L L.isLB) x z := by
  rw [cls_theta, lam_bi t P h L.isLB ⟨c.t, c.isGen⟩ hadj hw]

theorem theta_isAdj : IsAdj b (theta t P h w L).L := fun d => by
  have hN := (theta t P h w L).isLB
  refine (cls_eq_iff (LB.isLB_linComb hN _ _) (LB.isLB_linComb hN _ _)).1 ?_
  refine (cls_cube_two hN _ _ _).trans (Eq.trans ?_ (cls_cube_two hN _ _ _).symm)
  rw [lam_theta t P h c hadj hw, lam_theta t P h c hadj hw, bi_act t P h L.isLB hadj]

theorem theta_prim : LBIso (theta t P h w L).L (cubeLB A ![𝟙 A, b.act w] (theta t P h w L).L) := by
  have hN := (theta t P h w L).isLB
  refine (cls_eq_iff hN (LB.isLB_linComb hN _ _)).1 (Eq.trans ?_ (cls_cube_two hN _ _ _).symm)
  rw [lam_theta t P h c hadj hw, cls_theta]



end ThetaLaws

section BaseChange

variable {S' : Scheme.{0}} {G₁ A₁ : Over S'} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj A₁] [IsCommMonObj A₁]
  {a₁ : OAct O G₁} {b₁ : OAct O A₁} (t₁ : IsTensor A₁ b₁ G₁ a₁ M) {f : S' ⟶ S} {φ : G₁.left ⟶ G.left}
  {ψ : A₁.left ⟶ A.left} (hφ : IsLinearPullback a₁ a f φ) (hψ : IsLinearPullback b₁ b f ψ)
  (hm : ∀ m, (t₁.tmul m).left ≫ ψ = φ ≫ (t.tmul m).left)
include hφ hψ hm


omit [StarRing O] in
theorem mapLeft_self_comm (l : M →ₗ[O] O) :
    (t₁.mapLeft (IsTensor.self a₁) l).left ≫ φ = ψ ≫ (t.mapLeft (IsTensor.self a) l).left := by
  have key : ∀ y : A₁ ⟶ A₁, pushHom hφ.1 A₁ (y ≫ t₁.mapLeft (IsTensor.self a₁) l) =
      pushHom hψ.1 A₁ y ≫ t.mapLeft (IsTensor.self a) l := fun y => by
    refine t₁.induction_on (P := fun y => pushHom hφ.1 A₁ (y ≫ t₁.mapLeft (IsTensor.self a₁) l) =
      pushHom hψ.1 A₁ y ≫ t.mapLeft (IsTensor.self a) l) y (by simp) (fun m x => Over.OverMorphism.ext ?_)
      (fun y z hy hz => by rw [MonObj.mul_comp, map_mul, map_mul, MonObj.mul_comp, hy, hz])
    rw [Category.assoc, IsTensor.tmul_mapLeft, IsTensor.self_tmul]
    change (x.left ≫ _) ≫ φ = ((x.left ≫ _) ≫ ψ) ≫ _
    rw [Category.assoc, Category.assoc, Category.assoc, hφ.comm, reassoc_of% hm, ← Over.comp_left,
      IsTensor.tmul_mapLeft, IsTensor.self_tmul]
  have e := congrArg (fun q => q.left) (key (𝟙 A₁))
  rw [Category.id_comp] at e
  exact e.trans (congrArg (· ≫ _) (Category.id_comp ψ))

theorem biMap_comm {T₁ : Over S'} (x₁ z₁ : T₁ ⟶ A₁) (x z : T ⟶ A) (U : Over.mk (T₁.hom ≫ f) ⟶ T)
    (hx : x₁.left ≫ ψ = U.left ≫ x.left) (hz : z₁.left ≫ ψ = U.left ≫ z.left) (q : BIx P.n) :
    (biMap t₁ P h x₁ z₁ q).left ≫ φ = U.left ≫ (biMap t P h x z q).left := by
  have hc : ∀ i, (crd t₁ P i).left ≫ φ = ψ ≫ (crd t P i).left := fun i => mapLeft_self_comm t t₁ hφ hψ hm _
  refine psum_push hφ.1 _ _ U (fun i => Over.OverMorphism.ext ?_) _
  fin_cases i
  · change (x₁.left ≫ _) ≫ φ = U.left ≫ x.left ≫ _
    rw [Category.assoc, hc, reassoc_of% hx]
  · change (z₁.left ≫ _ ≫ _) ≫ φ = U.left ≫ z.left ≫ _ ≫ _
    rw [Category.assoc, Category.assoc, hφ.comm, reassoc_of% hc, reassoc_of% hz]

theorem thetaCub_isPullCubical (w : O) (m : CubeMap G₁ G) (hF : m.F = φ) (he : m.e = f) {L : RigLB G} {L₁ : RigLB G₁}
    {c : CubicalStr G L} {c₁ : CubicalStr G₁ L₁} (H : m.IsPullCubical c₁ c) :
    (cubeMapOf hψ.1).IsPullCubical (thetaCub t₁ P h w c₁) (thetaCub t P h w c) := by
  have := b.hom w
  have := b₁.hom w
  subst hF
  refine isPullCubical_comb m (cubeMapOf hψ.1) he.symm _ _ _ (fun q => ?_) H
  exact (biMap_comm t P h t₁ hφ hψ hm (𝟙 A₁) (b₁.act w) (𝟙 A) (b.act w) (pushPt hψ.1.1.w (𝟙 A₁))
    (Category.comp_id _).symm ((hψ.comm w).trans (congrArg (· ≫ _) (Category.id_comp ψ).symm)) q).trans
    (congrArg (· ≫ _) (Category.id_comp ψ))

end BaseChange

theorem isSemiAbelian_tensor {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M]
    [Module.Projective O M] {a : OAct O G} {b : OAct O A} (t : IsTensor A b G a M) (hG : IsSemiAbelian G) :
    IsSemiAbelian A := by
  obtain ⟨n, ρ, -, hr⟩ := t.exists_retract
  exact GlobalTheory.SS.isSemiAbelian_of_retract S _ A (GlobalTheory.PowGrp.isSemiAbelian_pow S _ G n (Out.powIsPowGrp G n) hG)
    ⟨inferInstance, t.of_isSemiAbelian hG⟩ ρ.i ρ.r hr ρ.retract

end GlobalTheory.HermTensor
