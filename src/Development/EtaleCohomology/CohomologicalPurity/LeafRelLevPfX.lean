module

public import Development.EtaleCohomology.CohomologicalPurity.LeafExcDegPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafExcIdentPf

@[expose] public section

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafRelLevPfX
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

instance discPC : PreservesColimitsOfSize.{0, 0} disc :=
  inferInstanceAs (PreservesColimitsOfSize.{0, 0} (Functor.const SimplexCategoryᵒᵖ : PSh ⥤ _))

def pbMapIso {C D : Type*} [Category C] [Category D] (Fn : C ⥤ D) {B G A' A : C} (g : G ⟶ B) (a : A' ⟶ A)
    (π' : A' ⟶ B) (π : A ⟶ B) (h : a ≫ π = π') [HasPullback π' g] [HasPullback π g]
    [HasPullback (Fn.map π') (Fn.map g)] [HasPullback (Fn.map π) (Fn.map g)]
    [PreservesLimit (cospan π' g) Fn] [PreservesLimit (cospan π g) Fn] :
    Arrow.mk (Fn.map (pullback.map π' g π g a (𝟙 _) (𝟙 _) (by simp [h]) (by simp))) ≅
    Arrow.mk (pullback.map (Fn.map π') (Fn.map g) (Fn.map π) (Fn.map g) (Fn.map a) (𝟙 _) (𝟙 _)
      (by simp [← Fn.map_comp, h]) (by simp)) :=
  Arrow.isoMk (PreservesPullback.iso Fn π' g) (PreservesPullback.iso Fn π g) (by
    apply pullback.hom_ext
    · simp only [Arrow.mk_hom, Category.assoc, pullback.lift_fst, PreservesPullback.iso_hom_fst,
        PreservesPullback.iso_hom_fst_assoc, ← Fn.map_comp]
    · simp only [Arrow.mk_hom, Category.assoc, pullback.lift_snd, PreservesPullback.iso_hom_snd, ← Fn.map_comp, Category.comp_id])

theorem types_pb {A : Type} {E : A → Type} {P Y G : Type} (ι : ∀ a, E a ⟶ P) (hP : Nonempty (IsColimit (Cofan.mk P ι)))
    (p : P ⟶ Y) (g : G ⟶ Y) (e : ∀ a, E a ⟶ Y) (he : ∀ a, ι a ≫ p = e a)
    {Q : Type} (fst : Q ⟶ P) (snd : Q ⟶ G) (w : fst ≫ p = snd ≫ g) (hQ : IsLimit (PullbackCone.mk fst snd w))
    {Q' : A → Type} (fst' : ∀ a, Q' a ⟶ E a) (snd' : ∀ a, Q' a ⟶ G) (w' : ∀ a, fst' a ≫ e a = snd' a ≫ g)
    (hQ' : ∀ a, IsLimit (PullbackCone.mk (fst' a) (snd' a) (w' a)))
    (j : ∀ a, Q' a ⟶ Q) (hj1 : ∀ a, j a ≫ fst = fst' a ≫ ι a) (hj2 : ∀ a, j a ≫ snd = snd' a) :
    Nonempty (IsColimit (Cofan.mk Q j)) := by
  rw [Cofan.nonempty_isColimit_iff_bijective_fromSigma] at hP ⊢
  have J1 : ∀ a y, fst (j a y) = ι a (fst' a y) := fun a y => ConcreteCategory.congr_hom (hj1 a) y
  have J2 : ∀ a y, snd (j a y) = snd' a y := fun a y => ConcreteCategory.congr_hom (hj2 a) y
  constructor
  · rintro ⟨a, y⟩ ⟨b, z⟩ hyz
    have hyz' : j a y = j b z := hyz
    have h1 : ι a (fst' a y) = ι b (fst' b z) := by rw [← J1, ← J1, hyz']
    have h2 : snd' a y = snd' b z := by rw [← J2, ← J2, hyz']
    have h3 := hP.1 (a₁ := ⟨a, fst' a y⟩) (a₂ := ⟨b, fst' b z⟩) h1
    obtain ⟨rfl, h4⟩ := Sigma.mk.inj_iff.mp h3
    have h4' : fst' a y = fst' a z := eq_of_heq h4
    have : y = z := PullbackCone.IsLimit.type_ext (hQ' a) h4' h2
    subst this; rfl
  · intro q
    obtain ⟨⟨a, u⟩, hu⟩ := hP.2 (fst q)
    have hu' : ι a u = fst q := hu
    have hc : e a u = g (snd q) := by
      rw [← ConcreteCategory.congr_hom (he a) u]
      change p (ι a u) = g (snd q)
      rw [hu']
      exact ConcreteCategory.congr_hom w q
    let y : Q' a := (PullbackCone.IsLimit.equivPullbackObj (hQ' a)).symm ⟨(u, snd q), hc⟩
    have y1 : fst' a y = u := PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst (hQ' a) _
    have y2 : snd' a y = snd q := PullbackCone.IsLimit.equivPullbackObj_symm_apply_snd (hQ' a) _
    refine ⟨⟨a, y⟩, ?_⟩
    change j a y = q
    refine PullbackCone.IsLimit.type_ext hQ ?_ ?_
    · change fst (j a y) = fst q
      rw [J1, y1, hu']
    · change snd (j a y) = snd q
      rw [J2, y2]

theorem psh_pb {A : Type} {E : A → PSh} {P Y G : PSh} (ι : ∀ a, E a ⟶ P) (hP : Nonempty (IsColimit (Cofan.mk P ι)))
    (p : P ⟶ Y) (g : G ⟶ Y) (e : ∀ a, E a ⟶ Y) (he : ∀ a, ι a ≫ p = e a) :
    Nonempty (IsColimit (Cofan.mk (pullback p g) fun a =>
      pullback.map (e a) g p g (ι a) (𝟙 _) (𝟙 _) (by simp [he]) (by simp))) := by
  obtain ⟨hP⟩ := hP
  refine ⟨evaluationJointlyReflectsColimits _ fun U => (isColimitMapCoconeCofanMkEquiv _ _ _).symm ?_⟩
  have hPU := isColimitCofanMkObjOfIsColimit ((evaluation _ _).obj U) _ _ hP
  have hQ := isLimitPullbackConeMapOfIsLimit ((evaluation _ _).obj U) pullback.condition (pullbackIsPullback p g)
  have hQ' := fun a => isLimitPullbackConeMapOfIsLimit ((evaluation _ _).obj U) pullback.condition
    (pullbackIsPullback (e a) g)
  exact (types_pb _ ⟨hPU⟩ _ _ _ (fun a => congrArg (fun t => NatTrans.app t U) (he a)) _ _ _ hQ _ _ _ hQ' _
    (fun a => by rw [← Functor.map_comp, ← Functor.map_comp, pullback.lift_fst])
    (fun a => by rw [← Functor.map_comp, pullback.lift_snd, Category.comp_id])).some

theorem inj_aug_RRelL {J : Type} [SmallCategory J] {Y : PSh} (Dx : J ⥤ PSh) (cx : ∀ j, Dx.obj j ⟶ Y) (hcx : Coc Dx cx)
    (n : SimplexCategoryᵒᵖ) (σ : Fin (n.unop.len + 1) ⥤ J) : inj Dx n σ ≫ (aug cx hcx).app n = cx (σ.obj 0) := by
  ext U x
  have e : (homOfLE (Fin.zero_le (0 : Fin (n.unop.len + 1))) : (0 : Fin _) ⟶ 0) = 𝟙 _ := Subsingleton.elim _ _
  change (cx (σ.obj 0)).app U ((Dx.map (σ.map (homOfLE (Fin.zero_le 0)))).app U x) = (cx (σ.obj 0)).app U x
  rw [e, σ.map_id, Dx.map_id]; rfl

theorem inj_nat {J : Type} [SmallCategory J] {D' D : J ⥤ PSh} (α : D' ⟶ D) (n : SimplexCategoryᵒᵖ)
    (σ : Fin (n.unop.len + 1) ⥤ J) : inj D' n σ ≫ ((hocF J).map α).app n = α.app (σ.obj 0) ≫ inj D n σ := by
  ext U x
  exact mkChn_congr (F := D.flip.obj U) σ
    (funext fun i => ConcreteCategory.congr_hom (NatTrans.congr_app (α.naturality (σ.map (homOfLE (Fin.zero_le i)))) U) x) _ _

theorem LeafRelLev_of : LeafRelLev := by
  intro hL J _ D' D α Y G g c' c hc' hc h h' n
  have hj : ∀ j, α.app j ≫ c j = c' j := fun j => congrArg (fun t => NatTrans.app t (op (SimplexCategory.mk 0))) (h j)
  have hn : ((hocF J).map α).app n ≫ (aug c hc).app n = (aug c' hc').app n := congrArg (fun t => NatTrans.app t n) h'
  refine ⟨Fin (n.unop.len + 1) ⥤ J, fun σ => σ.obj 0, fun σ => disc.obj (pullback (c' (σ.obj 0)) g),
    fun σ => disc.obj (pullback (c (σ.obj 0)) g),
    Cofan.mk (disc.obj (pullback ((aug c' hc').app n) g)) (fun σ => disc.map (pullback.map _ _ _ _ (inj D' n σ)
      (𝟙 _) (𝟙 _) (by simp [inj_aug_RRelL]) (by simp))),
    Cofan.mk (disc.obj (pullback ((aug c hc).app n) g)) (fun σ => disc.map (pullback.map _ _ _ _ (inj D n σ)
      (𝟙 _) (𝟙 _) (by simp [inj_aug_RRelL]) (by simp))),
    fun σ => disc.map (pullback.map _ _ _ _ (α.app (σ.obj 0)) (𝟙 _) (𝟙 _) (by simp [hj]) (by simp)),
    disc.map (pullback.map _ _ _ _ (((hocF J).map α).app n) (𝟙 _) (𝟙 _) (by simp [hn]) (by simp)),
    ⟨isColimitCofanMkObjOfIsColimit disc _ _ (psh_pb _ (hL J D' n) _ g _ (inj_aug_RRelL D' c' hc' n)).some⟩,
    ⟨isColimitCofanMkObjOfIsColimit disc _ _ (psh_pb _ (hL J D n) _ g _ (inj_aug_RRelL D c hc n)).some⟩, ?_, ?_, ?_⟩
  · intro σ
    change disc.map _ ≫ disc.map _ = disc.map _ ≫ disc.map _
    rw [← disc.map_comp, ← disc.map_comp]
    congr 1
    apply pullback.hom_ext <;>
      simp only [pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
        pullback.lift_snd_assoc, Category.comp_id]
    rw [inj_nat]
  · intro σ
    exact ⟨(pbMapIso disc g (α.app (σ.obj 0)) (c' (σ.obj 0)) (c (σ.obj 0)) (hj _)).symm⟩
  · have e := (pbMapIso ((evaluation _ _).obj n) (disc.map g) ((hocF J).map α) (aug c' hc') (aug c hc) h').symm
    exact ⟨disc.mapArrow.mapIso e⟩

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafDescOGluePfP
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl

def LeafResK : Prop := ∀ (q : ℕ) (i : ℤ),
  (∀ s, Injective ((res _ (tw q i)).X s)) ∧ ∀ s < 0, IsZero ((res _ (tw q i)).X s)

def LeafZcPull : Prop := ∀ {R : Type} [CommRing R] (K : Cx R) {X' X : Scheme.{0}} (f : X' ⟶ X) (U' : X'.Opens)
  (U : X.Opens), U' ≤ f ⁻¹ᵁ U → ∀ (n : ℤ) (a : Sec (K.X n) X), a ∈ Zc K U n → Sec.res f a ∈ Zc K U' n

def LeafZcIn : Prop := ∀ {R : Type} [CommRing R] (K : Cx R) {X : Scheme.{0}} (U W V : X.Opens) (h : V ≤ W), V ≤ U →
  ∀ (n : ℤ) (a : Sec (K.X n) W.toScheme), a ∈ Zc K (W.ι ⁻¹ᵁ U) n → rs h a = 0

private theorem sres_zero {R : Type} [CommRing R] {G : Shv R} {X Y : Scheme.{0}} (f : Y ⟶ X) :
    Sec.res f (0 : Sec G X) = 0 := by
  show (G.obj.map f.op).hom 0 = 0
  exact map_zero _

private theorem smap_zero {R : Type} [CommRing R] {G H : Shv R} (φ : G ⟶ H) {X : Scheme.{0}} :
    Sec.map φ (0 : Sec G X) = 0 := by
  show (φ.hom.app (op X)).hom 0 = 0
  exact map_zero _

private theorem Bd_zero {R : Type} [CommRing R] (K : Cx R) {X : Scheme.{0}} (U : X.Opens) (n : ℤ) : Bd K U n 0 :=
  ⟨0, sres_zero _, smap_zero _⟩

private theorem leι {X : Scheme.{0}} {V W : X.Opens} (h : V ≤ W) (U : X.Opens) :
    V.ι ⁻¹ᵁ U ≤ X.homOfLE h ⁻¹ᵁ (W.ι ⁻¹ᵁ U) :=
  le_of_comp _ _ U rfl _ (Scheme.homOfLE_ι _ _) le_rfl

private theorem descent_glue_of_residue_pullback_inclusion (hK : LeafResK) (hP : LeafZcPull) (hI : LeafZcIn) : LeafDescOGlue := by
  intro hD hF q X U m i hL A V s hcov H
  obtain ⟨cls, hon, hker, hnat⟩ := hD q m i
  have H1 : ∀ n < m, ∀ (W : X.Opens), ∀ a ∈ Zc (res _ (tw q i)) (W.ι ⁻¹ᵁ U) n, ∀ x ∈ W,
      ∃ (V : X.Opens) (h : V ≤ W), x ∈ V ∧ Bd (res _ (tw q i)) (V.ι ⁻¹ᵁ U) n (rs h a) := by
    intro n hn W a ha x hx
    by_cases hxU : x ∈ U
    · refine ⟨W ⊓ U, inf_le_left, ⟨hx, hxU⟩, ?_⟩
      rw [hI _ U W (W ⊓ U) _ inf_le_right n a ha]
      exact Bd_zero _ _ _
    · obtain ⟨V', hV'W, hxV', hsub⟩ := hL x W hx
      refine ⟨V', hV'W, hxV', ?_⟩
      obtain ⟨cn, -, hkern, -⟩ := hD q n i
      have hz := hP _ (X.homOfLE hV'W) (V'.ι ⁻¹ᵁ U) (W.ι ⁻¹ᵁ U) (leι hV'W U) n a ha
      have := hsub n hn
      exact (hkern (V'.ι ⁻¹ᵁ U) ⟨_, hz⟩).1 (Subsingleton.elim _ _)
  obtain ⟨-, hglue⟩ := hF _ (res _ (tw q i)) (hK q i).1 (hK q i).2 X U m H1
  choose l hl using fun a => hon ((V a).ι ⁻¹ᵁ U) (s a)
  let V' : Option A → X.Opens := fun o => Option.elim o U V
  let a' : ∀ k, Sec ((res _ (tw q i)).X m) (V' k).toScheme := fun
    | none => 0
    | some a => (l a).1
  have hmem : ∀ k, a' k ∈ Zc (res _ (tw q i)) ((V' k).ι ⁻¹ᵁ U) m := by
    rintro (_ | a)
    · exact zero_mem _
    · exact (l a).2
  have hcv : ∀ x : X, ∃ k, x ∈ V' k := by
    intro x
    by_cases hx : x ∈ U
    · exact ⟨none, hx⟩
    · obtain ⟨a, ha⟩ := hcov x hx
      exact ⟨some a, ha⟩
  have hcmp : ∀ k l', ∀ x ∈ V' k, x ∈ V' l' → ∃ (T : X.Opens) (hk : T ≤ V' k) (hl : T ≤ V' l'), x ∈ T ∧
      Bd (res _ (tw q i)) (T.ι ⁻¹ᵁ U) m (rs hk (a' k) - rs hl (a' l')) := by
    intro k l' x hk hl'
    by_cases hxU : x ∈ U
    · refine ⟨V' k ⊓ V' l' ⊓ U, inf_le_left.trans inf_le_left, inf_le_left.trans inf_le_right, ⟨⟨hk, hl'⟩, hxU⟩, ?_⟩
      rw [hI _ U (V' k) _ _ inf_le_right m (a' k) (hmem k), hI _ U (V' l') _ _ inf_le_right m (a' l') (hmem l'),
        sub_zero]
      exact Bd_zero _ _ _
    · rcases k with _ | a
      · exact absurd hk hxU
      rcases l' with _ | b
      · exact absurd hl' hxU
      obtain ⟨T, ha, hb, ha', hb', hxT, heq⟩ := H a b x hk hl' hxU
      refine ⟨T, ha, hb, hxT, ?_⟩
      have za := hP _ (X.homOfLE ha) (T.ι ⁻¹ᵁ U) ((V a).ι ⁻¹ᵁ U) ha' m (l a).1 (l a).2
      have zb := hP _ (X.homOfLE hb) (T.ι ⁻¹ᵁ U) ((V b).ι ⁻¹ᵁ U) hb' m (l b).1 (l b).2
      have e1 := hnat (X.homOfLE ha) (T.ι ⁻¹ᵁ U) ((V a).ι ⁻¹ᵁ U) ha' (l a) ⟨_, za⟩ rfl
      have e2 := hnat (X.homOfLE hb) (T.ι ⁻¹ᵁ U) ((V b).ι ⁻¹ᵁ U) hb' (l b) ⟨_, zb⟩ rfl
      rw [hl a] at e1
      rw [hl b] at e2
      have h0 : cls (T.ι ⁻¹ᵁ U) (⟨_, za⟩ - ⟨_, zb⟩) = 0 := by
        rw [map_sub, ← e1, ← e2, heq, sub_self]
      exact (hker _ _).1 h0
  obtain ⟨c, hc, hcb⟩ := hglue (Option A) V' a' hmem hcv hcmp
  refine ⟨cls U ⟨c, hc⟩, fun a => ?_⟩
  have zc := hP _ (V a).ι ((V a).ι ⁻¹ᵁ U) U le_rfl m c hc
  show Hs.pull q (opnMap (V a).ι ((V a).ι ⁻¹ᵁ U) U le_rfl) m i (cls U ⟨c, hc⟩) = s a
  rw [hnat (V a).ι ((V a).ι ⁻¹ᵁ U) U le_rfl ⟨c, hc⟩ ⟨_, zc⟩ rfl, ← hl a, ← sub_eq_zero, ← map_sub]
  exact (hker _ _).2 (hcb (some a))

private theorem sres_comp {R : Type} [CommRing R] {G : Shv R} {X Y Z : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) (a : Sec G X) :
    Sec.res g (Sec.res f a) = Sec.res (g ≫ f) a := by
  show (G.obj.map g.op).hom ((G.obj.map f.op).hom a) = (G.obj.map (g ≫ f).op).hom a
  rw [op_comp, Functor.map_comp]; rfl

private theorem sres_id {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} (a : Sec G X) : Sec.res (𝟙 X) a = a := by
  show (G.obj.map (𝟙 X).op).hom a = a
  rw [op_id, CategoryTheory.Functor.map_id]; rfl

private theorem smap_res {R : Type} [CommRing R] {G H : Shv R} (φ : G ⟶ H) {X Y : Scheme.{0}} (f : Y ⟶ X) (a : Sec G X) :
    Sec.map φ (Sec.res f a) = Sec.res f (Sec.map φ a) := by
  show (φ.hom.app (op Y)).hom ((G.obj.map f.op).hom a) = (H.obj.map f.op).hom ((φ.hom.app (op X)).hom a)
  have h := φ.hom.naturality f.op
  exact congrArg (fun t => t.hom a) h

private theorem LeafZcPull_pf : LeafZcPull := by
  intro R _ K X' X f U' U h n a ha
  obtain ⟨h1, h2⟩ := (mem_Zc a).1 ha
  refine (mem_Zc _).2 ⟨?_, ?_⟩
  · rw [sres_comp, ← Scheme.Hom.resLE_comp_ι f h, ← sres_comp, h1, sres_zero]
  · rw [smap_res, h2, sres_zero]

private theorem LeafZcIn_pf : LeafZcIn := by
  intro R _ K X U W V h hU n a ha
  obtain ⟨h1, -⟩ := (mem_Zc a).1 ha
  have e : (⊤ : V.toScheme.Opens) ≤ X.homOfLE h ⁻¹ᵁ (W.ι ⁻¹ᵁ U) :=
    le_of_comp _ _ U rfl _ (Scheme.homOfLE_ι _ _) ((Scheme.Opens.ι_preimage_self V).symm.le.trans (fun y hy => hU hy))
  have h0 : Sec.res (⊤ : V.toScheme.Opens).ι (rs h a) = 0 := by
    rw [sres_comp, ← Scheme.Hom.resLE_comp_ι (X.homOfLE h) e, ← sres_comp, h1, sres_zero]
  rw [← sres_id (rs h a), ← Scheme.toIso_inv_ι, ← sres_comp, h0, sres_zero]

private theorem resK_inj (q : ℕ) (i : ℤ) (s : ℤ) : Injective ((res _ (tw q i)).X s) := by unfold GlobalTheory.EtC.res; infer_instance
private theorem LeafResK_pf : LeafResK := fun q i => ⟨resK_inj q i, fun s hs => by
  have : (res _ (tw q i)).IsStrictlyGE 0 := by unfold GlobalTheory.EtC.res; infer_instance
  exact CochainComplex.isZero_of_isStrictlyGE (res _ (tw q i)) 0 s hs⟩

theorem LeafDescOGlue_of : LeafDescOGlue := descent_glue_of_residue_pullback_inclusion LeafResK_pf LeafZcPull_pf LeafZcIn_pf

end LateralTheory.CohomologicalPurity.Cl
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafAugSurjPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem altSum (m : ℕ) : ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) = if Even m then 0 else 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (-1 : ℤ) ^ i) (m + 2)]
  induction m with
  | zero => simp [Finset.sum_range_succ]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd m with h | h
    · have h' : ¬ Even (m + 1) := by simpa [Nat.even_add_one] using h
      simp [h, h', pow_succ, h.neg_one_pow]
    · have h' : Even (m + 1) := by simpa [Nat.even_add_one, Nat.not_even_iff_odd] using h
      have hn : ¬ Even m := Nat.not_even_iff_odd.2 h
      simp [hn, h', pow_succ, h.neg_one_pow]

theorem dL {R : Type} [CommRing R] (Y : PSh) (m : ℕ) (T : Scheme.{0}ᵒᵖ) (z : ((((chainsP R).obj (disc.obj Y)).X (m + 1)).obj T)) :
    ((((chainsP R).obj (disc.obj Y)).d (m + 1) m).app T).hom z = (∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ)) • z := by
  change (((freeP R).obj Y).obj T) at z
  have e : ∀ i : Fin (m + 2), SimplicialObject.δ (disc.obj Y) i = 𝟙 _ := fun _ => rfl
  simp [chainsP, e]
  erw [LinearMap.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp
  simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one] using
    (Module.End.intCast_apply (R := ULift.{1} R) ((-1 : ℤ) ^ (i : ℕ)) z)

section
variable {R : Type} [CommRing R]

theorem bdyL (Y : PSh) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (x : ((((chainsP R).obj (disc.obj Y)).X (n + 1)).obj T))
    (hx : Cyc ((chainsP R).obj (disc.obj Y)) (n + 1) T x) : Bdy ((chainsP R).obj (disc.obj Y)) (n + 1) T x := by
  by_cases h : Even (n + 1)
  · have h0 := hx n
    rw [dL, altSum, if_neg (by simpa [Nat.even_add_one] using h)] at h0
    simp only [one_smul] at h0
    exact ⟨0, by rw [map_zero]; exact h0.symm⟩
  · refine ⟨x, ?_⟩
    have e := dL (R := R) Y (n + 1) T x
    rw [altSum, if_neg h] at e
    exact e.trans (one_smul ℤ _)

def imSv {K L : PCx R} (φ : K ⟶ L) (n : ℕ) {T : Scheme.{0}} (y : (L.X n).obj (op T)) : Sieve T where
  arrows U f := ∃ x', ((φ.f n).app (op U)).hom x' = ((L.X n).map f.op).hom y
  downward_closed := by
    rintro U V f ⟨x', hx⟩ g
    refine ⟨((K.X n).map g.op).hom x', ?_⟩
    have h1 := congrArg (fun h => h.hom x') ((φ.f n).naturality g.op)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
    rw [h1, hx, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem imSv_add {K L : PCx R} (φ : K ⟶ L) (n : ℕ) {T : Scheme.{0}} (y z : (L.X n).obj (op T)) :
    imSv φ n y ⊓ imSv φ n z ≤ imSv φ n (y + z) := by
  rintro U f ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]⟩

theorem imSv_smul {K L : PCx R} (φ : K ⟶ L) (n : ℕ) {T : Scheme.{0}} (y : (L.X n).obj (op T)) (r : ULift.{1} R) :
    imSv φ n y ≤ imSv φ n (r • y) := by
  rintro U f ⟨a, ha⟩
  exact ⟨r • a, by rw [map_smul, map_smul, ha]⟩

theorem imSv_zero {K L : PCx R} (φ : K ⟶ L) (n : ℕ) {T : Scheme.{0}} :
    imSv φ n (0 : (L.X n).obj (op T)) = ⊤ := by
  ext U f
  simp only [Sieve.top_apply, iff_true]
  exact ⟨0, by rw [map_zero, map_zero]⟩

end

section
variable {J : Type} [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X)
  (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) (R : Type) [CommRing R]

theorem gen_mem (hcov : ∀ x : X, ∃ j, x ∈ Set.range (c j)) [∀ j, IsOpenImmersion (c j)]
    {T : Scheme.{0}} (g : T ⟶ X) :
    imSv ((chainsP R).map (aug _ hc)) 0
      (ModuleCat.freeMk (ULift.up g) : (((chainsP R).obj (disc.obj (yoneda.obj X))).X 0).obj (op T)) ∈
      Scheme.etaleTopology T := by
  let j : T → J := fun t => (hcov (g t)).choose
  let V : T → T.Opens := fun t => g ⁻¹ᵁ (c (j t)).opensRange
  have hV : ∀ t, t ∈ V t := fun t => (hcov (g t)).choose_spec
  let 𝒰 : T.Cover (Scheme.precoverage @Etale) := Scheme.Cover.mkOfCovers T (fun t => (V t).toScheme)
    (fun t => (V t).ι) (fun t => ⟨t, ⟨t, hV t⟩, by simp⟩)
  refine GrothendieckTopology.superset_covering _ ?_ 𝒰.mem_grothendieckTopology
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro _ _ ⟨t⟩
  have hr : Set.range ((V t).ι ≫ g) ⊆ Set.range (c (j t)) := by
    rintro _ ⟨y, rfl⟩
    have := (V t).range_ι ▸ Set.mem_range_self (f := (V t).ι) y
    simpa [V] using this
  let a := IsOpenImmersion.lift (c (j t)) ((V t).ι ≫ g) hr
  let σ : Fin (0 + 1) ⥤ J := (Functor.const _).obj (j t)
  refine ⟨ModuleCat.freeMk (ULift.up ((inj (D ⋙ yoneda) (op (SimplexCategory.mk 0)) σ).app (op (V t).toScheme) a)), ?_⟩
  erw [ModuleCat.free_map_apply, ModuleCat.free_map_apply]
  refine congrArg ModuleCat.freeMk (ULift.ext ?_)
  show (a ≫ D.map (𝟙 (j t))) ≫ c (j t) = (V t).ι ≫ g
  rw [D.map_id, Category.comp_id]
  exact IsOpenImmersion.lift_fac _ _ _
end

theorem all_mem {J : Type} [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X)
    (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) (R : Type) [CommRing R]
    (hcov : ∀ x : X, ∃ j, x ∈ Set.range (c j)) [∀ j, IsOpenImmersion (c j)] {T : Scheme.{0}}
    (x : (((chainsP R).obj (disc.obj (yoneda.obj X))).X 0).obj (op T)) :
    imSv ((chainsP R).map (aug _ hc)) 0 x ∈ Scheme.etaleTopology T := by
  let M := (((chainsP R).obj (disc.obj (yoneda.obj X))).X 0).obj (op T)
  let b : Module.Basis (ULift.{1} (T ⟶ X)) (ULift.{1} R) M := Finsupp.basisSingleOne
  have hx : x ∈ Submodule.span (ULift.{1} R) (Set.range b) := b.mem_span x
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨g⟩, rfl⟩ := hy
    exact gen_mem D X c hc R hcov g
  | zero => rw [imSv_zero]; exact GrothendieckTopology.top_mem _ _
  | add y z _ _ hy hz =>
    exact GrothendieckTopology.superset_covering _ (imSv_add _ _ y z)
      (GrothendieckTopology.intersection_covering _ hy hz)
  | smul r y _ hy => exact GrothendieckTopology.superset_covering _ (imSv_smul _ _ y r) hy

theorem LeafAugSurj_of : LeafAugSurj := by
  intro J _ D X c ho hcov hc R _ n T x hx
  rcases n with _ | n
  · refine ⟨imSv ((chainsP R).map (aug _ hc)) 0 x, ?_, ?_⟩
    · have := ho
      exact all_mem D X c hc R hcov x
    · rintro U f ⟨x', hx'⟩
      refine ⟨x', fun m => ?_, 0, ?_⟩
      · rw [HomologicalComplex.shape _ 0 m (by simp)]
        rfl
      · rw [map_zero, hx', sub_self]
  · refine ⟨⊤, GrothendieckTopology.top_mem _ _, fun U f _ => ⟨0, fun m => by simp, ?_⟩⟩
    obtain ⟨y, hy⟩ := bdyL _ n T x hx
    refine ⟨-((((chainsP R).obj (disc.obj (yoneda.obj X))).X (n + 1 + 1)).map f.op).hom y, ?_⟩
    have h := congrArg (fun h => h.hom y) ((((chainsP R).obj (disc.obj (yoneda.obj X))).d (n + 1 + 1) (n + 1)).naturality f.op)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [map_neg, map_zero, zero_sub, h, hy]

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafEqvOfExcPf
noncomputable section
open CategoryTheory Limits GlobalTheory.EtC AlgebraicGeometry CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.EquivalenceOfExcision
variable (R : Type) [CommRing R]
instance i1 : PreservesColimitsOfShape WalkingSpan (ModuleCat.free (ULift.{1, 0} R)) :=
  haveI := (ModuleCat.adj (ULift.{1, 0} R)).leftAdjoint_preservesColimits; inferInstance
instance i2 : PreservesColimitsOfShape WalkingSpan (free R) := by
  unfold free freeP; infer_instance
instance i3 : PreservesColimitsOfShape WalkingSpan (chainsN R) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  have e : chainsN R ⋙ HomologicalComplex.eval _ _ n ≅
      (evaluation SimplexCategoryᵒᵖ PSh).obj (Opposite.op (SimplexCategory.mk n)) ⋙ free R :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)
  exact preservesColimitsOfShape_of_natIso e.symm
instance i4 : PreservesColimitsOfShape WalkingSpan (ComplexShape.embeddingDownNat.extendFunctor (Shv R)) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro m
  by_cases hm : ∃ k, ComplexShape.embeddingDownNat.f k = m
  · obtain ⟨k, hk⟩ := hm
    have e : ComplexShape.embeddingDownNat.extendFunctor (Shv R) ⋙ HomologicalComplex.eval _ _ m ≅
        HomologicalComplex.eval _ _ k :=
      NatIso.ofComponents (fun K => K.extendXIso _ hk) (by
        intro K L φ
        change (HomologicalComplex.extendMap φ _).f m ≫ (L.extendXIso _ hk).hom = (K.extendXIso _ hk).hom ≫ φ.f k
        rw [HomologicalComplex.extendMap_f φ _ hk]; simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
    exact preservesColimitsOfShape_of_natIso e.symm
  · push Not at hm
    have hz : ∀ K : ChainComplex (Shv R) ℕ,
        IsZero ((ComplexShape.embeddingDownNat.extendFunctor (Shv R) ⋙ HomologicalComplex.eval _ _ m).obj K) :=
      fun K => K.isZero_extend_X _ m hm
    exact ⟨fun {K} => ⟨fun {c} _ => ⟨{
      desc := fun s => (hz _).to_ s.pt
      fac := fun s j => (hz _).eq_of_src _ _
      uniq := fun s _ _ => (hz _).eq_of_src _ _ }⟩⟩⟩
instance i5 : PreservesColimitsOfShape WalkingSpan (chains R) := by
  unfold chains; infer_instance

theorem hkc (R : Type) [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ) (x : HK R M F n) :
    HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  unfold HK.pull HK.pre
  simp only [cpre]
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]
theorem hki (R : Type) [CommRing R] {K : Cx R} (F : Shv R) (n : ℤ) (x : HK R K F n) :
    HK.pull R (𝟙 K) F n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  unfold HK.pull HK.pre
  simp only [cpre]
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

theorem hkc' (R : Type) [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ) (x : HK R M F n) :
    HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := hkc R f g F n x

section
variable {P' P : Arrow Spc} (φ : P' ⟶ P)
open LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut

abbrev jj : P.right ⟶ MM φ := pushout.inr P'.hom (P'.hom ≫ φ.right)
abbrev ii : P'.right ⟶ MM φ := pushout.inl P'.hom (P'.hom ≫ φ.right)
def rr : MM φ ⟶ P.right :=
  pushout.desc (f := P'.hom) (g := P'.hom ≫ φ.right) φ.right (𝟙 _) (by simp)
def hh : dbl P' ⟶ MM φ :=
  pushout.desc (f := P'.hom) (g := P'.hom) (ii φ) (φ.right ≫ jj φ) (by
    exact (pushout.condition (f := P'.hom) (g := P'.hom ≫ φ.right)).trans
      (Category.assoc _ _ _))
abbrev Jr : Arrow Spc := Arrow.mk (jj φ)

theorem jr : jj φ ≫ rr φ = 𝟙 _ :=
  pushout.inr_desc (f := P'.hom) (g := P'.hom ≫ φ.right) _ _ _

def ss : dbl (Jr φ) ⟶ MM φ :=
  pushout.desc (f := jj φ) (g := jj φ) (𝟙 _) (rr φ ≫ jj φ) (by
    rw [← Category.assoc, jr, Category.id_comp, Category.comp_id])

theorem j_gM : jj φ ≫ gM φ = dbl.inr P :=
  pushout.inr_desc (f := P'.hom) (g := P'.hom ≫ φ.right) _ _ _
theorem gM_fold : gM φ ≫ dbl.fold P = rr φ := by
  refine pushout.hom_ext (C := Spc) (f := P'.hom) (g := P'.hom ≫ φ.right) ?_ ?_
  · change (ii φ ≫ gM φ) ≫ dbl.fold P = ii φ ≫ rr φ
    have hM : ii φ ≫ gM φ = φ.right ≫ dbl.inl P :=
      pushout.inl_desc (f := P'.hom) (g := P'.hom ≫ φ.right) _ _ _
    have hfold : dbl.inl P ≫ dbl.fold P = 𝟙 P.right :=
      pushout.inl_desc (f := P.hom) (g := P.hom) _ _ _
    have hrr : ii φ ≫ rr φ = φ.right :=
      pushout.inl_desc (f := P'.hom) (g := P'.hom ≫ φ.right) _ _ _
    rw [hM, Category.assoc, hfold, Category.comp_id, hrr]
  · change (jj φ ≫ gM φ) ≫ dbl.fold P = jj φ ≫ rr φ
    rw [j_gM, dbl.inr_fold, jr]
theorem inl_h : dbl.inl P' ≫ hh φ = ii φ :=
  pushout.inl_desc (f := P'.hom) (g := P'.hom) _ _ _
theorem inr_h : dbl.inr P' ≫ hh φ = φ.right ≫ jj φ :=
  pushout.inr_desc (f := P'.hom) (g := P'.hom) _ _ _
theorem h_gM : hh φ ≫ gM φ = dbl.map φ := by
  refine pushout.hom_ext (C := Spc) (f := P'.hom) (g := P'.hom) ?_ ?_
  · change (dbl.inl P' ≫ hh φ) ≫ gM φ = dbl.inl P' ≫ dbl.map φ
    have hM : ii φ ≫ gM φ = φ.right ≫ dbl.inl P :=
      pushout.inl_desc (f := P'.hom) (g := P'.hom ≫ φ.right) _ _ _
    have hmap : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P :=
      pushout.inl_desc (f := P'.hom) (g := P'.hom) _ _ _
    rw [inl_h, hM, hmap]
  · change (dbl.inr P' ≫ hh φ) ≫ gM φ = dbl.inr P' ≫ dbl.map φ
    rw [inr_h, Category.assoc, j_gM, dbl.inr_map]
theorem etale_mapping_cylinder_double_section_inl_comp : dbl.inl (Jr φ) ≫ ss φ = 𝟙 _ :=
  pushout.inl_desc (f := jj φ) (g := jj φ) _ _ _
theorem etale_mapping_cylinder_double_section_inr_comp : dbl.inr (Jr φ) ≫ ss φ = rr φ ≫ jj φ :=
  pushout.inr_desc (f := jj φ) (g := jj φ) _ _ _

theorem key (hR : LeafRel) (q : ℕ) (i n : ℤ) (y : Ht q (MM φ) n i)
    (h1 : pull _ (jj φ) (tw q i) n y = 0) (h2 : pull _ (hh φ) (tw q i) n y = 0) : y = 0 := by
  obtain ⟨e, he⟩ := hR q i
  have PO : IsPushout ((chains (ZMod q)).map P'.hom) ((chains (ZMod q)).map (P'.hom ≫ φ.right)) ((chains (ZMod q)).map (ii φ)) ((chains (ZMod q)).map (jj φ)) :=
    (IsPushout.of_hasPushout P'.hom (P'.hom ≫ φ.right)).map _
  let pM : (chains (ZMod q)).obj (MM φ) ⟶ cokernel ((chains (ZMod q)).map P'.hom) := PO.desc (cokernel.π ((chains (ZMod q)).map P'.hom)) 0 (by simp)
  have pM1 : (chains (ZMod q)).map (ii φ) ≫ pM = cokernel.π _ := PO.inl_desc _ _ _
  have pM2 : (chains (ZMod q)).map (jj φ) ≫ pM = 0 := PO.inr_desc _ _ _
  have wκ : (chains (ZMod q)).map P'.hom ≫ (chains (ZMod q)).map (ii φ) ≫ cokernel.π ((chains (ZMod q)).map (jj φ)) = 0 := by
    have hc : P'.hom ≫ ii φ = (P'.hom ≫ φ.right) ≫ jj φ := pushout.condition
    rw [← Category.assoc, ← (chains (ZMod q)).map_comp, hc, (chains (ZMod q)).map_comp, Category.assoc, cokernel.condition, comp_zero]
  let κ : cokernel ((chains (ZMod q)).map P'.hom) ⟶ cokernel ((chains (ZMod q)).map (Jr φ).hom) := cokernel.desc _ _ wκ
  let κ' : cokernel ((chains (ZMod q)).map (Jr φ).hom) ⟶ cokernel ((chains (ZMod q)).map P'.hom) := cokernel.desc ((chains (ZMod q)).map (jj φ)) pM pM2
  have hπ : pM ≫ κ = cokernel.π ((chains (ZMod q)).map (Jr φ).hom) := by
    apply PO.hom_ext
    · rw [← Category.assoc, pM1]; exact cokernel.π_desc _ _ _
    · rw [← Category.assoc, pM2, zero_comp]; exact (cokernel.condition _).symm
  have hκ : κ' ≫ κ = 𝟙 _ := by
    apply coequalizer.hom_ext
    rw [Category.comp_id]; exact (cokernel.π_desc_assoc _ _ _ _).trans hπ
  let s : Hs q (Jr φ) n i := ⟨pull _ (ss φ) _ n y, by
    change pull _ (dbl.inr (Jr φ)) _ n (pull _ (ss φ) _ n y) = 0
    rw [← pull_comp, etale_mapping_cylinder_double_section_inr_comp, pull_comp, h1, map_zero]⟩
  let x := (e (Jr φ) n).symm s
  have hx : (e (Jr φ) n x).1 = HK.pull _ ((chains (ZMod q)).map (ss φ) ≫ cokernel.π _) (tw q i) n x := by
    apply he
    · rw [← Category.assoc, ← (chains (ZMod q)).map_comp, etale_mapping_cylinder_double_section_inl_comp, (chains (ZMod q)).map_id, Category.id_comp]
    · rw [← Category.assoc, ← (chains (ZMod q)).map_comp, etale_mapping_cylinder_double_section_inr_comp, (chains (ZMod q)).map_comp, Category.assoc]
      erw [cokernel.condition, comp_zero]
  have hs : (e (Jr φ) n x).1 = pull _ (ss φ) _ n y := by simp [x, s]
  have hy : y = pull _ (dbl.inl (Jr φ)) _ n (pull _ (ss φ) _ n y) := by
    rw [← pull_comp, etale_mapping_cylinder_double_section_inl_comp, pull_id]
  have hp : (e P' n (HK.pull _ κ (tw q i) n x)).1 = HK.pull _ ((chains (ZMod q)).map (hh φ) ≫ pM) (tw q i) n (HK.pull _ κ (tw q i) n x) := by
    apply he
    · rw [← Category.assoc, ← (chains (ZMod q)).map_comp, inl_h, pM1]
    · rw [← Category.assoc, ← (chains (ZMod q)).map_comp, inr_h, (chains (ZMod q)).map_comp, Category.assoc, pM2, comp_zero]
  have hh0 : pull _ (hh φ) _ n y = HK.pull _ ((chains (ZMod q)).map (hh φ) ≫ pM) (tw q i) n (HK.pull _ κ (tw q i) n x) := by
    rw [← hkc', Category.assoc, hπ, hy, ← pull_comp, ← hs, hx]
    change HK.pull _ ((chains (ZMod q)).map _) _ n _ = _
    have hhs : hh φ ≫ dbl.inl (Jr φ) ≫ ss φ = hh φ := by rw [etale_mapping_cylinder_double_section_inl_comp]; exact Category.comp_id _
    rw [← hkc', ← Category.assoc, ← (chains (ZMod q)).map_comp, Category.assoc, hhs]
  have hz : HK.pull _ κ (tw q i) n x = 0 := by
    apply (e P' n).injective
    rw [map_zero]; apply Subtype.ext; rw [hp, ← hh0, h2]; rfl
  have hx0 : x = 0 := by
    rw [← hki _ (tw q i) n x, ← hκ, hkc', hz, map_zero]
  rw [hy, ← hs, hx0, map_zero]; rfl

end

end LateralTheory.CohomologicalPurity.EquivalenceOfExcision

namespace LateralTheory.CohomologicalPurity.TubeCut
open LateralTheory.CohomologicalPurity.EquivalenceOfExcision

theorem LeafEqvOfExc_of (hR : LeafRel) : LeafEqvOfExc := by
  intro q P' P φ hE i n
  open LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut in
  constructor
  · intro a b hab
    rw [← sub_eq_zero] at hab ⊢
    rw [← map_sub] at hab
    set x := a - b
    have h1 : pull _ (dbl.inr P) (tw q i) n x = 0 := by
      rw [← j_gM φ, pull_comp, hab, map_zero]
    have h2 : Hs.pull q φ n i ⟨x, h1⟩ = 0 := by
      apply Subtype.ext
      change pull _ (dbl.map φ) _ n x = 0
      rw [← h_gM φ, pull_comp, hab, map_zero]
    have := (hE n i).1 (h2.trans (map_zero _).symm)
    exact congrArg Subtype.val this
  · intro y
    set y0 := y - pull _ (rr φ) (tw q i) n (pull _ (jj φ) (tw q i) n y)
    have hy0 : pull _ (jj φ) (tw q i) n y0 = 0 := by
      simp only [y0, map_sub]; rw [← pull_comp, jr, pull_id, sub_self]
    let z : Hs q P' n i := ⟨pull _ (hh φ) _ n y0, by
      change pull _ (dbl.inr P') _ n (pull _ (hh φ) _ n y0) = 0
      rw [← pull_comp, inr_h, pull_comp, hy0, map_zero]⟩
    obtain ⟨x, hx⟩ := (hE n i).2 z
    have hd : pull _ (gM φ) (tw q i) n x.1 - y0 = 0 := by
      apply key φ hR q i n
      · rw [map_sub, ← pull_comp, j_gM, hy0, sub_zero]; exact x.2
      · rw [map_sub, ← pull_comp, h_gM, sub_eq_zero]; exact congrArg Subtype.val hx
    refine ⟨x.1 + pull _ (dbl.fold P) (tw q i) n (pull _ (jj φ) (tw q i) n y), ?_⟩
    rw [map_add (f := _), ← pull_comp, gM_fold, sub_eq_zero.mp hd]
    simp [y0]

end LateralTheory.CohomologicalPurity.TubeCut
end
end
