module

public import Development.EtaleCohomology.EtaleSheaves.TorEtPf
public import Development.EtaleCohomology.EtaleSheaves.HensCut
public import Development.EtaleCohomology.EtaleSheaves.StalkGermPf
public import Development.EtaleCohomology.EtaleSheaves.HalfDegreeVanishing.SecondBlockUnimodularLocusInclusionMono

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.TwistTensorRestriction
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ZModFlatnessFromBaerCriterion

def TensTwRes : Prop := ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {I J T : Cx (ZMod q)}
  (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (I.X 0) U) (e' : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (J.X 0) U),
  IsTwRes q i I e → IsTwRes q j J e' → (∀ t, FlatS (J.X t)) → ∀ τ : Pair I J T, τ.IsTensor →
  IsTwRes q k T fun U ζ => τ.mul U 0 0 0 (add_zero 0) (e U ζ) (e' U ζ)

def LeafInjSecInj : Prop := ∀ (q : ℕ) [NeZero q] (M : Shv (ZMod q)) [Injective M] (U : Scheme.{0}),
  Module.Injective (ULift.{1} (ZMod q)) (Sec M U)

def LeafInjFlatZMod : Prop := ∀ (q : ℕ) [NeZero q] (M : Type 1) [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M],
  Module.Injective (ULift.{1} (ZMod q)) M → Module.Flat (ULift.{1} (ZMod q)) M

theorem flatS_of_sec {R : Type} [CommRing R] (M : Shv R)
    (h : ∀ U : Scheme.{0}, Module.Flat (ULift.{1} R) (Sec M U)) : FlatS M := by
  refine ⟨M.obj, 𝟙 M.obj, fun U y => ⟨⊤, (Scheme.etaleTopology).top_mem U, fun V g _ => ⟨Sec.res g y, rfl⟩⟩,
    fun U x hx => ⟨⊤, (Scheme.etaleTopology).top_mem U, fun V g _ => ?_⟩, fun U _ => h U⟩
  have hx' : x = 0 := hx
  subst hx'
  exact map_zero _

instance resGE (q : ℕ) (i : ℤ) : (res (ZMod q) (tw q i)).IsStrictlyGE 0 := by
  unfold res InjectiveResolution.cochainComplex
  infer_instance

theorem res_isTwRes (q : ℕ) [NeZero q] (i : ℤ) :
    IsTwRes q i (res (ZMod q) (tw q i)) (fun _ ζ => resGen i ζ) := by
  refine ⟨resGE q i, resAug (tw q i), ?_, fun U ζ => ?_⟩
  · unfold resAug
    exact (inferInstance : QuasiIso (injectiveResolution (tw q i)).ι')
  · simp only [resGen, resι, sglι, Sec.map]
    rfl

theorem res_flat (hA : LeafInjSecInj) (hB : LeafInjFlatZMod) (q : ℕ) [NeZero q] (j t : ℤ) :
    FlatS ((res (ZMod q) (tw q j)).X t) := by
  refine flatS_of_sec _ fun U => hB q _ ?_
  have : Injective ((res (ZMod q) (tw q j)).X t) := by
    unfold res; infer_instance
  exact hA q _ U

end LateralTheory.E.ZModFlatnessFromBaerCriterion

open LateralTheory.E.ZModFlatnessFromBaerCriterion in
theorem LateralTheory.E.LeafTwPairHtpyPf.LeafTwTensRes_of (h97 : TensTwRes) (hA : LeafInjSecInj) (hB : LeafInjFlatZMod) :
    LateralTheory.E.LeafTwPairHtpyPf.LeafTwTensRes := by
  intro q _ i j T τ hτ
  exact h97 q i j (i + j) rfl (fun _ ζ => resGen i ζ) (fun _ ζ => resGen j ζ) (res_isTwRes q i) (res_isTwRes q j)
    (res_flat hA hB q j) τ hτ
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.InjStepPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ZLGPf LateralTheory.E.ZarIndPf

namespace LateralTheory.E.InjStepPf

def TwoStep : Prop := MV → Hyp → ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [CompactSpace S]
  [QuasiSeparatedSpace S] [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f],
  IsUnit (q : Γ(S, ⊤)) → ∀ i n : ℤ,
  (∀ U : S.Opens, IsCompact (U : Set S) → Bij q i (n - 1) f p U) →
  ∀ (U V W : S.Opens) (hV : V ≤ U) (hW : W ≤ U), IsCompact (V : Set S) → IsCompact (W : Set S) →
  ∀ x : Ht q (sch.obj (overO p U)) n i, pull _ (sch.map (fO f p U)) _ _ x = 0 →
  pull _ (sch.map (resO p hV)) _ _ x = 0 → pull _ (sch.map (resO p hW)) _ _ x = 0 →
  pull _ (sch.map (resO p (sup_le hV hW))) _ _ x = 0

def EmptyH : Prop := Hyp → ∀ (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) (U : S.Opens), (U : Set S) = ∅ →
  ∀ (i n : ℤ) (x : Ht q (sch.obj (overO p U)) n i), x = 0

variable {X S : Scheme.{0}}

theorem resO_comp (p : X ⟶ S) {V W U : S.Opens} (h1 : V ≤ W) (h2 : W ≤ U) :
    resO p h1 ≫ resO p h2 = resO p (h1.trans h2) := by
  apply pullback.hom_ext <;> simp only [resO, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Scheme.homOfLE_homOfLE, Category.comp_id]

theorem resO_refl (p : X ⟶ S) (U : S.Opens) : resO p (le_refl U) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [resO]

theorem dies_mono {q : ℕ} {i n : ℤ} (p : X ⟶ S) {V W U : S.Opens} (h1 : V ≤ W) (h2 : W ≤ U)
    (x : Ht q (sch.obj (overO p U)) n i) (hx : pull _ (sch.map (resO p h2)) _ _ x = 0) :
    pull _ (sch.map (resO p (h1.trans h2))) _ _ x = 0 := by
  rw [← resO_comp p h1 h2, Functor.map_comp, pull_comp, hx, map_zero]

def OverMV : Prop := MV → Hyp → ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (i m : ℤ) (V W : S.Opens),
  ∃ (δX : Ht q (sch.obj (overO p (V ⊓ W))) m i →+ Ht q (sch.obj (overO p (V ⊔ W))) (m + 1) i)
    (δY : Ht q (sch.obj (overO (f ≫ p) (V ⊓ W))) m i →+ Ht q (sch.obj (overO (f ≫ p) (V ⊔ W))) (m + 1) i),
  (∀ x, pull _ (sch.map (resO p (le_sup_left : V ≤ V ⊔ W))) _ _ x = 0 →
      pull _ (sch.map (resO p (le_sup_right : W ≤ V ⊔ W))) _ _ x = 0 → ∃ w, δX w = x) ∧
  (∀ a b, δX (pull _ (sch.map (resO p (inf_le_left : V ⊓ W ≤ V))) _ _ a -
      pull _ (sch.map (resO p (inf_le_right : V ⊓ W ≤ W))) _ _ b) = 0) ∧
  (∀ w, δY w = 0 → ∃ a b, w = pull _ (sch.map (resO (f ≫ p) (inf_le_left : V ⊓ W ≤ V))) _ _ a -
      pull _ (sch.map (resO (f ≫ p) (inf_le_right : V ⊓ W ≤ W))) _ _ b) ∧
  ∀ w, δY (pull _ (sch.map (fO f p (V ⊓ W))) _ _ w) = pull _ (sch.map (fO f p (V ⊔ W))) _ _ (δX w)

theorem fO_res {Y : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) :
    resO (f ≫ p) h ≫ fO f p U = fO f p V ≫ resO p h := by
  apply pullback.hom_ext <;> simp only [resO, fO, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
    pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]

theorem pull_fO_res {q : ℕ} {i n : ℤ} {Y : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U)
    (x : Ht q (sch.obj (overO p U)) n i) :
    pull _ (sch.map (fO f p V)) _ _ (pull _ (sch.map (resO p h)) _ _ x) =
      pull _ (sch.map (resO (f ≫ p) h)) _ _ (pull _ (sch.map (fO f p U)) _ _ x) := by
  rw [← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, fO_res]

theorem pull_res_res {q : ℕ} {i n : ℤ} (p : X ⟶ S) {V W U : S.Opens} (h1 : V ≤ W) (h2 : W ≤ U)
    (x : Ht q (sch.obj (overO p U)) n i) :
    pull _ (sch.map (resO p h1)) _ _ (pull _ (sch.map (resO p h2)) _ _ x) = pull _ (sch.map (resO p (h1.trans h2))) _ _ x := by
  rw [← pull_comp, ← Functor.map_comp, resO_comp]

theorem TwoStep_of (hO : OverMV) : TwoStep := by
  intro hM hH q Y X S f p _ _ _ _ _ _ hq i n hb U V W hV hW hVc hWc x hx hdV hdW
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  have hb' : ∀ U : S.Opens, IsCompact (U : Set S) → Bij q i m f p U := by simpa using hb
  obtain ⟨δX, δY, e1, e2, e3, e4⟩ := hO hM hH q f p i m V W
  set x' := pull _ (sch.map (resO p (sup_le hV hW))) _ _ x with hx'
  have d1 : pull _ (sch.map (resO p (le_sup_left : V ≤ V ⊔ W))) _ _ x' = 0 := by
    rw [hx', pull_res_res]; exact hdV
  have d2 : pull _ (sch.map (resO p (le_sup_right : W ≤ V ⊔ W))) _ _ x' = 0 := by
    rw [hx', pull_res_res]; exact hdW
  obtain ⟨w, hw⟩ := e1 x' d1 d2
  have fx' : pull _ (sch.map (fO f p (V ⊔ W))) _ _ x' = 0 := by
    rw [hx', pull_fO_res, hx, map_zero]
  have hδ : δY (pull _ (sch.map (fO f p (V ⊓ W))) _ _ w) = 0 := by rw [e4, hw, fx']
  obtain ⟨a', b', hab⟩ := e3 _ hδ
  obtain ⟨a, rfl⟩ := (hb' V hVc).2 a'
  obtain ⟨b, rfl⟩ := (hb' W hWc).2 b'
  have hI : IsCompact ((V ⊓ W : S.Opens) : Set S) := by
    rw [TopologicalSpace.Opens.coe_inf]
    exact QuasiSeparatedSpace.inter_isCompact _ _ V.isOpen hVc W.isOpen hWc
  have hw2 : w = pull _ (sch.map (resO p (inf_le_left : V ⊓ W ≤ V))) _ _ a -
      pull _ (sch.map (resO p (inf_le_right : V ⊓ W ≤ W))) _ _ b := by
    apply (hb' _ hI).1
    rw [hab, map_sub, pull_fO_res, pull_fO_res]
  rw [← hw, hw2, e2]

theorem InjStep_of (hT : TwoStep) (hE : EmptyH) : InjStep := by
  intro hM hH q Y X S f p _ _ _ _ _ _ hq i n hg hb U hU
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_cases hne : (U : Set S) = ∅
  · exact hE hH q p U hne i n x
  obtain ⟨s0, hs0⟩ := Set.nonempty_iff_ne_empty.2 hne

  have loc : ∀ s ∈ (U : Set S), ∃ (V : S.Opens) (h : V ≤ U), s ∈ V ∧ IsCompact (V : Set S) ∧
      pull _ (sch.map (resO p h)) _ _ x = 0 := by
    intro s hs
    obtain ⟨V, hVU, hsV, hd⟩ := (hg s).1 U hs x hx
    obtain ⟨V', hV'B, hsV', hV'V⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens) hsV
    exact ⟨V', hV'V.trans hVU, hsV', IsAffineOpen.isCompact hV'B, dies_mono p hV'V hVU x hd⟩
  let P : Set S → Prop := fun T => ∃ (V : S.Opens) (h : V ≤ U), T ⊆ V ∧ IsCompact (V : Set S) ∧
      pull _ (sch.map (resO p h)) _ _ x = 0
  have hP : P (U : Set S) := by
    refine hU.induction_on (p := P) ?_ ?_ ?_ ?_
    · obtain ⟨V, h, _, hc, hd⟩ := loc s0 hs0
      exact ⟨V, h, Set.empty_subset _, hc, hd⟩
    · intro s t hst ⟨V, h, htV, hc, hd⟩
      exact ⟨V, h, hst.trans htV, hc, hd⟩
    · intro s t ⟨V, h, hsV, hc, hd⟩ ⟨W, h', htW, hc', hd'⟩
      refine ⟨V ⊔ W, sup_le h h', ?_, ?_, hT hM hH q f p hq i n hb U V W h h' hc hc' x hx hd hd'⟩
      · exact Set.union_subset_union hsV htW
      · simpa using hc.union hc'
    · intro s hs
      obtain ⟨V, h, hsV, hc, hd⟩ := loc s hs
      exact ⟨V, mem_nhdsWithin_of_mem_nhds (V.isOpen.mem_nhds hsV), V, h, subset_rfl, hc, hd⟩
  obtain ⟨V, h, hUV, _, hd⟩ := hP
  have hVU : V = U := le_antisymm h hUV
  subst hVU
  simpa [resO_refl, pull_id] using hd

end LateralTheory.E.InjStepPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.FibStalkPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.FibPf LateralTheory.E.FibClosedPf

namespace LateralTheory.E.FibStalkPf

theorem eqv_iso {X Y : Scheme.{0}} (e : X ≅ Y) (q : ℕ) (i : ℤ) : Eqv _ (sch.map e.hom) (tw q i) := by
  intro n
  refine Function.bijective_iff_has_inverse.2 ⟨pull _ (sch.map e.inv) (tw q i) n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, ← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id, pull_id]
  · rw [← pull_comp, ← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]

theorem eqv_comp {q : ℕ} {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} {F : Shv (ZMod q)} (hf : Eqv _ f F) (hg : Eqv _ g F) :
    Eqv _ (f ≫ g) F := by
  intro n
  have : (pull _ (f ≫ g) F n : _ → _) = (pull _ f F n) ∘ (pull _ g F n) := funext fun x => pull_comp _ f g F n x
  rw [this]; exact (hf n).comp (hg n)

theorem eqv_left {q : ℕ} {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} {F : Shv (ZMod q)} (h : Eqv _ (f ≫ g) F) (hg : Eqv _ g F) :
    Eqv _ f F := by
  intro n
  have h1 := h n
  have : (pull _ (f ≫ g) F n : _ → _) = (pull _ f F n) ∘ (pull _ g F n) := funext fun x => pull_comp _ f g F n x
  rw [this] at h1
  exact (Function.Bijective.of_comp_iff _ (hg n)).1 h1

theorem eqv_right {q : ℕ} {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} {F : Shv (ZMod q)} (h : Eqv _ (f ≫ g) F) (hf : Eqv _ f F) :
    Eqv _ g F := by
  intro n
  have h1 := h n
  have : (pull _ (f ≫ g) F n : _ → _) = (pull _ f F n) ∘ (pull _ g F n) := funext fun x => pull_comp _ f g F n x
  rw [this] at h1
  exact (Function.Bijective.of_comp_iff' (hf n) _).1 h1

end LateralTheory.E.FibStalkPf

namespace LateralTheory.E.FibStalkPf

def StalkSH : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {S : Scheme.{0}} (p : S ⟶ Spec (CommRingCat.of A)),
  AICSch S → ∀ s : (pullback p (cpt A) : Scheme.{0}), SH ((pullback p (cpt A)).presheaf.stalk s)

def FibreEqv : Prop := Hyp → HZero → AICAcyc → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) →
  ∀ {Z S : Scheme.{0}} (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A)) [QuasiCompact p] [QuasiSeparated p] [QuasiCompact c]
  [QuasiSeparated c] [IsDominant c], AICSch Z → AICSch S →
  (∀ (B : Type) [CommRing B] [IsLocalRing B], SH B → IsUnit (q : B) → ∀ t : Spec (CommRingCat.of B) ⟶ S, PB q i (pullback.snd c t)) →
  ∀ s : (pullback p (cpt A) : Scheme.{0}),
    Eqv _ (sch.map (pullback.snd (pullback.snd c ((pullback p (cpt A)).fromSpecStalk s ≫ pullback.fst p (cpt A)))
      (cpt ((pullback p (cpt A)).presheaf.stalk s)))) (tw q i)

theorem FibStalk_of (hS : StalkSH) (hF : FibreEqv) : FibStalk := by
  intro H h0 hA q i A _ _ hq Z S c p _ _ _ _ _ hZs hSs hB s
  have hsh : SH ((pullback p (cpt A)).presheaf.stalk s) := hS A p hSs s
  obtain ⟨_, _⟩ := id hsh
  have hu0 : IsUnit (q : Γ((pullback p (cpt A) : Scheme.{0}), ⊤)) := unit_of hq (pullback.fst p (cpt A) ≫ p)
  have hu : IsUnit (q : (pullback p (cpt A)).presheaf.stalk s) := by
    simpa using hu0.map ((pullback p (cpt A)).presheaf.germ ⊤ s trivial).hom
  have hfst := hB _ hsh hu ((pullback p (cpt A)).fromSpecStalk s ≫ pullback.fst p (cpt A))
  have hfib := hF H h0 hA q i A hq c p hZs hSs hB s
  have hE1 : Eqv _ (sch.map (cpt ((pullback p (cpt A)).presheaf.stalk s))) (tw q i) :=
    H.e1 q _ (IsLocalRing.maximalIdeal _) hu i
  have core : Eqv _ (sch.map (pullback.snd c ((pullback p (cpt A)).fromSpecStalk s ≫ pullback.fst p (cpt A)))) (tw q i) := by
    refine eqv_right ?_ hfst
    rw [← Functor.map_comp, pullback.condition, Functor.map_comp]
    exact eqv_comp hfib hE1
  have sq2 : IsPullback (pullback.fst (c ≫ p) (cpt A)) (fm c p ≫ 𝟙 _) c (pullback.fst p (cpt A)) := by
    rw [Category.comp_id]; exact (fm_isPullback c p).flip
  have big := (IsPullback.of_hasPullback (fm c p ≫ 𝟙 _) ((pullback p (cpt A)).fromSpecStalk s)).paste_horiz sq2
  have hsnd : Eqv _ (sch.map (pullback.snd (fm c p ≫ 𝟙 _) ((pullback p (cpt A)).fromSpecStalk s))) (tw q i) := by
    rw [← big.isoPullback_hom_snd, Functor.map_comp]; exact eqv_comp (eqv_iso _ q i) core
  refine eqv_left (g := sch.map (pullback.snd (𝟙 _) ((pullback p (cpt A)).fromSpecStalk s))) ?_
    (eqv_iso (asIso (pullback.snd (𝟙 _) ((pullback p (cpt A)).fromSpecStalk s))) q i)
  rw [← Functor.map_comp]
  convert hsnd using 2
  rw [pullback.map]; erw [pullback.lift_snd]; exact Category.comp_id _

end LateralTheory.E.FibStalkPf

namespace LateralTheory.E.FibStalkPf

def StalkSHS : Prop := ∀ (S : Scheme.{0}), AICSch S → ∀ x : S, SH (S.presheaf.stalk x)

def QuotSH : Prop := ∀ (R R' : Type) [CommRing R] [CommRing R'] [IsLocalRing R'] (f : R →+* R'), Function.Surjective f → SH R → SH R'

theorem StalkSH_of (hS : StalkSHS) (hQ : QuotSH) : StalkSH := by
  intro A _ _ S p hSs s
  have h1 : SurjectiveOnStalks (cpt A) :=
    SurjectiveOnStalks.Spec_iff.2 (RingHom.surjectiveOnStalks_of_surjective IsLocalRing.residue_surjective)
  have h2 : SurjectiveOnStalks (pullback.fst p (cpt A)) := MorphismProperty.of_isPullback (P := @SurjectiveOnStalks) (IsPullback.of_hasPullback p (cpt A)).flip h1
  exact hQ _ _ ((pullback.fst p (cpt A)).stalkMap s).hom ((pullback.fst p (cpt A)).stalkMap_surjective s) (hS S hSs _)

end LateralTheory.E.FibStalkPf

namespace LateralTheory.E.FibStalkPf
open Polynomial IsLocalRing

theorem quotSH : QuotSH := by
  intro R R' _ _ _ f hf ⟨hH, hK⟩
  have hl : IsLocalHom f := IsLocalHom.of_surjective f hf
  have hmem : ∀ x, f x ∈ maximalIdeal R' ↔ x ∈ maximalIdeal R := fun x => by
    simp only [mem_maximalIdeal, mem_nonunits_iff]
    exact ⟨fun h hx => h (hx.map f), fun h hx => h (isUnit_of_map_unit f x hx)⟩
  refine ⟨⟨fun g hg a₀' h0 h1 => ?_⟩, ?_⟩
  · obtain ⟨G, hGm, -, hGmon⟩ := lifts_and_natDegree_eq_and_monic
      ((lifts_iff_coeff_lifts g).2 fun n => hf _) hg
    obtain ⟨a₀, rfl⟩ := hf a₀'
    have e0 : f (G.eval a₀) = g.eval (f a₀) := by rw [← hGm, Polynomial.eval_map, eval₂_at_apply]
    have e1 : f (G.derivative.eval a₀) = g.derivative.eval (f a₀) := by
      rw [← hGm, derivative_map, Polynomial.eval_map, eval₂_at_apply]
    obtain ⟨a, ha, ha'⟩ := HenselianLocalRing.is_henselian G hGmon a₀ ((hmem _).1 (e0 ▸ h0))
      (isUnit_of_map_unit f _ (e1 ▸ h1))
    refine ⟨f a, ?_, ?_⟩
    · rw [IsRoot, ← hGm, Polynomial.eval_map, eval₂_at_apply, ha.eq_zero, map_zero]
    · rw [← map_sub]; exact (hmem _).2 ha'
  · have hs : Function.Surjective (ResidueField.map f) := by
      intro y
      obtain ⟨y, rfl⟩ := residue_surjective y
      obtain ⟨x, rfl⟩ := hf y
      exact ⟨residue R x, ResidueField.map_residue f x⟩
    refine IsSepClosed.of_exists_root _ fun p hpm hpi hps => ?_
    obtain ⟨P, hP, hdeg, -⟩ := lifts_and_natDegree_eq_and_monic
      ((lifts_iff_coeff_lifts p).2 fun n => hs _) hpm
    have hPs : P.Separable := (separable_map (ResidueField.map f)).1 (hP ▸ hps)
    have hPd : P.degree ≠ 0 := by
      have := hpi.natDegree_pos
      intro h; rw [natDegree_eq_zero_iff_degree_le_zero.2 h.le] at hdeg; omega
    obtain ⟨x, hx⟩ := IsSepClosed.exists_root P hPd hPs
    exact ⟨ResidueField.map f x, by rw [← hP, Polynomial.eval_map, eval₂_at_apply, hx.eq_zero]; simp⟩

end LateralTheory.E.FibStalkPf

namespace LateralTheory.E.FibStalkPf
open Polynomial IsLocalRing

def StalkAIC : Prop := ∀ (S : Scheme.{0}), AICSch S → ∀ x : S, AIC (S.presheaf.stalk x)

theorem aic_root {R : Type} [CommRing R] [IsLocalRing R] (h : AIC R) : ∀ (n : ℕ) (f : R[X]), f.Monic → f.natDegree = n →
    ∀ a₀, f.eval a₀ ∈ maximalIdeal R → ∃ a, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal R := by
  intro n
  induction n with
  | zero =>
    intro f hm hd a₀ h0
    rw [Polynomial.eq_one_of_monic_natDegree_zero hm hd, eval_one] at h0
    exact absurd ((Ideal.eq_top_iff_one _).2 h0) (maximalIdeal.isMaximal R).ne_top
  | succ n ih =>
    intro f hm hd a₀ h0
    obtain ⟨b, hb⟩ := h f hm (by omega)
    have hf : (X - C b) * (f /ₘ (X - C b)) = f := by rw [mul_divByMonic_eq_iff_isRoot]; exact hb
    have hgm : (f /ₘ (X - C b)).Monic := (monic_X_sub_C b).of_mul_monic_left (by rw [hf]; exact hm)
    have hgd : (f /ₘ (X - C b)).natDegree = n := by rw [natDegree_divByMonic f (monic_X_sub_C b), natDegree_X_sub_C]; omega
    rw [← hf, eval_mul, eval_sub, eval_X, eval_C] at h0
    rcases (maximalIdeal.isMaximal R).isPrime.mem_or_mem h0 with h1 | h2
    · exact ⟨b, hb, by rw [← neg_sub]; exact neg_mem h1⟩
    · obtain ⟨a, ha, ha'⟩ := ih _ hgm hgd a₀ h2
      exact ⟨a, by rw [IsRoot, ← hf, eval_mul, ha.eq_zero, mul_zero], ha'⟩

theorem sh_of_aic {R : Type} [CommRing R] [IsLocalRing R] (h : AIC R) : SH R := by
  refine ⟨{ is_henselian := fun f hf a₀ h0 _ => aic_root h _ f hf rfl a₀ h0 }, ?_⟩
  refine IsSepClosed.of_exists_root _ fun p hpm hpi _ => ?_
  obtain ⟨P, hP, hdeg, hPm⟩ := lifts_and_natDegree_eq_and_monic
    ((lifts_iff_coeff_lifts p).2 fun n => residue_surjective _) hpm
  obtain ⟨x, hx⟩ := h P hPm (by have := hpi.natDegree_pos; omega)
  exact ⟨residue R x, by rw [← hP, Polynomial.eval_map, eval₂_at_apply, hx]; simp⟩

theorem stalkSHS_of (hA : StalkAIC) : StalkSHS := fun S hS x => sh_of_aic (hA S hS x)

end LateralTheory.E.FibStalkPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.CechYoneda
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.CechSigma_xy1Pf_Yo
open LateralTheory.E.CechSigmaProof LateralTheory.E.CechSigma_xy1Pf_Lev

def eW {A B : Scheme.{0}} (p : A ⟶ B) (n : ℕ) :
    yoneda.obj (widePullback B (fun _ : Fin (n + 1) => A) (fun _ => p)) ≅
      widePullback (yoneda.obj B) (fun _ : Fin (n + 1) => yoneda.obj A) (fun _ => yoneda.map p) :=
  preservesLimitIso yoneda (WidePullbackShape.wideCospan B (fun _ : Fin (n + 1) => A) (fun _ => p)) ≪≫
    HasLimit.isoOfNatIso (WidePullbackShape.diagramIsoWideCospan _)

theorem eW_π {A B : Scheme.{0}} (p : A ⟶ B) (n : ℕ) (i : Fin (n + 1)) :
    (eW p n).hom ≫ WidePullback.π _ i = yoneda.map (WidePullback.π _ i) := by
  simp only [eW, Iso.trans_hom, WidePullback.π]
  erw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc, preservesLimitIso_hom_π]
  simp only [WidePullbackShape.diagramIsoWideCospan, NatIso.ofComponents_hom_app]
  exact Category.comp_id _

theorem eW_base {A B : Scheme.{0}} (p : A ⟶ B) (n : ℕ) :
    (eW p n).hom ≫ WidePullback.base _ = yoneda.map (WidePullback.base _) := by
  simp only [eW, Iso.trans_hom, WidePullback.base]
  erw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc, preservesLimitIso_hom_π]
  simp only [WidePullbackShape.diagramIsoWideCospan, NatIso.ofComponents_hom_app]
  exact Category.comp_id _

theorem cechYoneda : CechYoneda := by
  intro A B C D p q s n
  refine ⟨(Arrow.isoMk (eW p n) (eW q n) ?_).symm⟩
  apply WidePullback.hom_ext
  · intro i
    simp only [Arrow.mk_hom, Category.assoc]
    erw [Arrow.mapCechNerve_app, WidePullback.lift_π]
    erw [← Category.assoc, eW_π, Category.assoc, eW_π]
    change yoneda.map _ ≫ yoneda.map s.left = yoneda.map _ ≫ yoneda.map _
    simp only [wpMap]
    erw [← Functor.map_comp, ← Functor.map_comp, WidePullback.lift_π]
  · simp only [Arrow.mk_hom, Category.assoc]
    erw [Arrow.mapCechNerve_app, WidePullback.lift_base]
    erw [← Category.assoc, eW_base, Category.assoc, eW_base]
    change yoneda.map _ ≫ yoneda.map s.right = yoneda.map _ ≫ yoneda.map _
    simp only [wpMap]
    erw [← Functor.map_comp, ← Functor.map_comp, WidePullback.lift_base]

end LateralTheory.E.CechSigma_xy1Pf_Yo
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.GlueRelPfCone
noncomputable section
open CategoryTheory Limits GlobalTheory.EtC CochainComplex.HomComplex CochainComplex

namespace LateralTheory.E.GlueRelPfCone

theorem pre_pull_zero (R : Type) [CommRing R] {K L : Cx R} (φ : K ⟶ L) (F : Shv R) (m : ℤ) (b : HK R L F m) :
    HK.pre R (mappingCone.fst φ) F m (m + 1) (add_comm 1 m) (HK.pull R φ F m b) = 0 := by
  obtain ⟨b, rfl⟩ := b.mk_surjective
  change CohomologyClass.mk (zcomp (mappingCone.fst φ) (zcomp (Cocycle.ofHom φ) b (zero_add m)) (add_comm 1 m)) = 0
  rw [CohomologyClass.mk_eq_zero_iff]
  refine ⟨m, rfl, -(m.negOnePow • (mappingCone.snd φ).comp b.1 (zero_add m)), ?_⟩
  ext1
  simp only [zcomp, Cocycle.ofHom_coe]
  rw [δ_neg, δ_units_smul, δ_comp _ _ (zero_add m) 1 (m + 1) (m + 1) rfl (zero_add 1) rfl, mappingCone.δ_snd]
  simp [Cocycle.δ_eq_zero, Cochain.comp_assoc_of_second_is_zero_cochain, smul_smul, Int.units_mul_self]

theorem range_of_pre_zero (R : Type) [CommRing R] {K L : Cx R} (φ : K ⟶ L) (F : Shv R) (m : ℤ) (x : HK R K F m)
    (hx : HK.pre R (mappingCone.fst φ) F m (m + 1) (add_comm 1 m) x = 0) : x ∈ Set.range (HK.pull R φ F m) := by
  obtain ⟨a, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk (zcomp (mappingCone.fst φ) a (add_comm 1 m)) = 0 at hx
  rw [CohomologyClass.mk_eq_zero_iff] at hx
  obtain ⟨m', hm', γ, hγ⟩ := hx
  obtain rfl : m' = m := by omega
  have hγ' : δ m' (m' + 1) γ = (mappingCone.fst φ).1.comp a.1 (add_comm 1 m') := by
    rw [hγ]; rfl
  have hb : δ m' (m' + 1) ((Cochain.ofHom (mappingCone.inr φ)).comp γ (zero_add m')) = 0 := by
    rw [δ_comp _ _ (zero_add m') 1 (m' + 1) (m' + 1) rfl (zero_add 1) rfl, hγ', δ_ofHom]
    rw [← Cochain.comp_assoc_of_first_is_zero_cochain, mappingCone.inr_fst]
    simp
  let b : Cocycle L (res R F) m' := Cocycle.mk (-(m'.negOnePow • (Cochain.ofHom (mappingCone.inr φ)).comp γ (zero_add m')))
    (m' + 1) rfl (by rw [δ_neg, δ_units_smul, hb]; simp)
  refine ⟨CohomologyClass.mk b, ?_⟩
  change CohomologyClass.mk (zcomp (Cocycle.ofHom φ) b (zero_add m')) = CohomologyClass.mk a
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  refine ⟨m' - 1, by omega, -((mappingCone.inl φ).comp γ (by omega)), ?_⟩
  ext1
  rw [δ_neg, δ_comp _ _ (show -1 + m' = m' - 1 by omega) 0 (m' + 1) m' (by omega) (by omega) rfl, hγ',
    mappingCone.δ_inl]
  rw [← Cochain.comp_assoc _ _ _ (neg_add_cancel 1) (add_comm 1 m') (by omega), mappingCone.inl_fst]
  simp [zcomp, b, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain, sub_eq_add_neg]

theorem coneExact : LateralTheory.E.GlueRelPf.ConeExact := by
  intro R _ K L φ F m x
  exact ⟨range_of_pre_zero R φ F m x, by rintro ⟨b, rfl⟩; exact pre_pull_zero R φ F m b⟩

end LateralTheory.E.GlueRelPfCone
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.DiagramChase
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ContPf

namespace LateralTheory.E.StepSPf

def PO (q : ℕ) {J : Type} [SmallCategory J] (D : J ⥤ Scheme.{0}) (c : Cone D) (j0 : J) (W : (D.obj j0).Opens) : Prop :=
  ∀ n i : ℤ,
  (∀ x : Ht q (sch.obj (c.π.app j0 ⁻¹ᵁ W).toScheme) n i, ∃ (k : J) (f : k ⟶ j0)
      (y : Ht q (sch.obj (D.map f ⁻¹ᵁ W).toScheme) n i),
      pull _ (sch.map ((c.π.app k).resLE (D.map f ⁻¹ᵁ W) (c.π.app j0 ⁻¹ᵁ W)
        (by rw [← Scheme.Hom.comp_preimage, c.w]))) _ _ y = x) ∧
  ∀ (k : J) (f : k ⟶ j0) (y : Ht q (sch.obj (D.map f ⁻¹ᵁ W).toScheme) n i),
    pull _ (sch.map ((c.π.app k).resLE (D.map f ⁻¹ᵁ W) (c.π.app j0 ⁻¹ᵁ W)
        (by rw [← Scheme.Hom.comp_preimage, c.w]))) _ _ y = 0 →
    ∃ (l : J) (g : l ⟶ k), pull _ (sch.map ((D.map g).resLE (D.map f ⁻¹ᵁ W) (D.map (g ≫ f) ⁻¹ᵁ W)
        (by rw [← Scheme.Hom.comp_preimage, ← D.map_comp]))) _ _ y = 0

def Restr : Prop := ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D),
  IsLimit c → (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) → (∀ j, CompactSpace (D.obj j)) →
  (∀ j, QuasiSeparatedSpace (D.obj j)) → (∀ j, IsUnit (q : Γ(D.obj j, ⊤))) → ∀ (j0 : J) (X : Scheme.{0}) (e : D.obj j0 ≅ X)
  (W : X.Opens), IsCompact (W : Set X) → PC W.toScheme → PO q D c j0 (e.hom ⁻¹ᵁ W)

def DiagramChase₂ : Prop := Hyp → MV → ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D),
  IsLimit c → (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) → (∀ j, CompactSpace (D.obj j)) →
  (∀ j, QuasiSeparatedSpace (D.obj j)) → (∀ j, IsUnit (q : Γ(D.obj j, ⊤))) → ∀ (j0 : J) (X : Scheme.{0}) (e : D.obj j0 ≅ X)
  (U V : X.Opens), U ⊔ V = ⊤ → PO q D c j0 (e.hom ⁻¹ᵁ U) → PO q D c j0 (e.hom ⁻¹ᵁ V) → PO q D c j0 (e.hom ⁻¹ᵁ (U ⊓ V)) →
  ∀ n i : ℤ, ∀ x : Ht q (sch.obj c.pt) n i, ∃ j y, pull _ (sch.map (c.π.app j)) _ _ y = x

theorem S_of_restr_chase (hR : Restr) (hC : DiagramChase₂) : LateralTheory.E.ContStepPf.StepS := by
  intro h hmv X U V hU hV hUV pU pV pW q J _ _ D c hc ha hcs hqs hu j0 ⟨e⟩ n i
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated e.inv
  have hW : IsCompact ((U ⊓ V : X.Opens) : Set X) := by
    rw [TopologicalSpace.Opens.coe_inf]
    exact QuasiSeparatedSpace.inter_isCompact _ _ U.2 hU V.2 hV
  exact hC h hmv q D c hc ha hcs hqs hu j0 X e U V hUV (hR q D c hc ha hcs hqs hu j0 X e U hU pU)
    (hR q D c hc ha hcs hqs hu j0 X e V hV pV) (hR q D c hc ha hcs hqs hu j0 X e (U ⊓ V) hW pW) n i

theorem po_res_zero {q : ℕ} {Y Z : Scheme.{0}} (φ : Y ⟶ Z) (A : Z.Opens) (B B' : Y.Opens) (hB : B = B')
    (h : B ≤ φ ⁻¹ᵁ A) (h' : B' ≤ φ ⁻¹ᵁ A) (n i : ℤ) (y : Ht q (sch.obj A.toScheme) n i) :
    pull _ (sch.map (φ.resLE A B h)) _ _ y = 0 → pull _ (sch.map (φ.resLE A B' h')) (tw q i) n y = 0 := by
  subst hB; exact id

theorem restr : Restr := by
  intro q J _ _ D c hc ha hcs hqs hu j0 X e W hWc pW
  have : ∀ {i j : J} (f : i ⟶ j), IsAffineHom (D.map f) := ha
  set W' : (D.obj j0).Opens := e.hom ⁻¹ᵁ W with hW'def
  have hW' : IsCompact (W' : Set (D.obj j0)) := QuasiCompact.isCompact_preimage (f := e.hom) _ W.2 hWc
  have key := pW q (opensDiagram D j0 W') (opensCone D c j0 W') (isLimitOpensCone D c hc j0 W')
    (fun f => inferInstance)
    (fun j => isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage (f := D.map j.hom) _ W'.2 hW'))
    (fun j => by have := hqs j.left; exact (D.map j.hom ⁻¹ᵁ W').ι.isOpenEmbedding.quasiSeparatedSpace)
    (fun j => by
      have h := (hu j.left).map ((D.map j.hom ⁻¹ᵁ W').ι.appTop.hom)
      simp only [map_natCast] at h
      exact h)
    (Over.mk (𝟙 j0)) ⟨(Scheme.isoOfEq _ (by simp [hW'def])) ≪≫ e.hom.preimageIso W⟩
  intro n i
  refine ⟨fun x => ?_, fun k f y hy => ?_⟩
  · obtain ⟨j, y, hy⟩ := (key n i).1 x
    exact ⟨j.left, j.hom, y, hy⟩
  · obtain ⟨k', g, hg⟩ := (key n i).2 (Over.mk f) y hy
    have hw : g.left ≫ f = k'.hom := Over.w g
    refine ⟨k'.left, g.left, ?_⟩
    exact po_res_zero (D.map g.left) _ _ _ (by rw [hw]) _ _ n i y hg

end LateralTheory.E.StepSPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.KummerInduction
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ContPf LateralTheory.E.ContStepPf

namespace LateralTheory.E.StepKPf

variable {J : Type} [SmallCategory J]

def lv (D : J ⥤ Scheme.{0}) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) {k : J} (f : k ⟶ j0) :
    (D.obj k).Opens := (D.map f ≫ e.hom) ⁻¹ᵁ U

def lm {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) : c.pt.Opens :=
  (c.π.app j0 ≫ e.hom) ⁻¹ᵁ U

theorem lm_le {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) {k : J}
    (f : k ⟶ j0) : lm c e U ≤ (c.π.app k) ⁻¹ᵁ lv D e U f := by
  rw [lm, lv, ← Scheme.Hom.comp_preimage, ← Category.assoc, c.w f]

theorem lv_le (D : J ⥤ Scheme.{0}) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) {k l : J}
    (f : k ⟶ j0) (g : l ⟶ k) : lv D e U (g ≫ f) ≤ (D.map g) ⁻¹ᵁ lv D e U f := by
  rw [lv, lv, ← Scheme.Hom.comp_preimage, ← Category.assoc, ← D.map_comp]

def rL {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) {k : J}
    (f : k ⟶ j0) : (lm c e U).toScheme ⟶ (lv D e U f).toScheme :=
  (c.π.app k).resLE _ _ (lm_le c e U f)

def rD (D : J ⥤ Scheme.{0}) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) {k l : J}
    (f : k ⟶ j0) (g : l ⟶ k) : (lv D e U (g ≫ f)).toScheme ⟶ (lv D e U f).toScheme :=
  (D.map g).resLE _ _ (lv_le D e U f g)

def RC (q : ℕ) {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) : Prop :=
  ∀ n i : ℤ,
  (∀ x : Ht q (sch.obj (lm c e U).toScheme) n i, ∃ (k : J) (f : k ⟶ j0) (y : Ht q (sch.obj (lv D e U f).toScheme) n i), pull _ (sch.map (rL c e U f)) _ _ y = x) ∧
  ∀ (k : J) (f : k ⟶ j0) (y : Ht q (sch.obj (lv D e U f).toScheme) n i), pull _ (sch.map (rL c e U f)) _ _ y = 0 →
    ∃ (l : J) (g : l ⟶ k), pull _ (sch.map (rD D e U f g)) _ _ y = 0

def Restr : Prop := Hyp → ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D),
  IsLimit c → (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) → (∀ j, CompactSpace (D.obj j)) →
  (∀ j, QuasiSeparatedSpace (D.obj j)) → (∀ j, IsUnit (q : Γ(D.obj j, ⊤))) → ∀ (j0 : J) (X : Scheme.{0})
  (e : D.obj j0 ≅ X) (U : X.Opens), IsCompact ((e.hom ⁻¹ᵁ U : (D.obj j0).Opens) : Set (D.obj j0)) →
  PC U.toScheme → RC q c e U

def DiagramChase₂ : Prop := Hyp → MV → ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D),
  IsLimit c → ∀ (j0 : J) (X : Scheme.{0}) (e : D.obj j0 ≅ X) (U V : X.Opens), U ⊔ V = ⊤ →
  RC q c e U → RC q c e V → RC q c e (U ⊓ V) →
  ∀ (n i : ℤ) (k : J) (f : k ⟶ j0) (y : Ht q (sch.obj (D.obj k)) n i), pull _ (sch.map (c.π.app k)) _ _ y = 0 →
    ∃ (l : J) (g : l ⟶ k), pull _ (sch.map (D.map g)) _ _ y = 0

theorem cpt_pre {Y X : Scheme.{0}} (e : Y ≅ X) (U : X.Opens) (hU : IsCompact (U : Set X)) :
    IsCompact ((e.hom ⁻¹ᵁ U : Y.Opens) : Set Y) :=
  (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)).isCompact_preimage.mpr hU

theorem StepK_of (hR : Restr) (hC : DiagramChase₂) : StepK := by
  intro h hmv X U V hU hV hUV pU pV pW q J _ _ D c hc ha hcs hqs hu j0 ⟨e⟩ n i j y hy
  have := hqs j0
  have hU' := cpt_pre e U hU
  have hV' := cpt_pre e V hV
  have hW' : IsCompact ((e.hom ⁻¹ᵁ (U ⊓ V) : (D.obj j0).Opens) : Set (D.obj j0)) := by
    rw [Scheme.Hom.preimage_inf]
    exact QuasiSeparatedSpace.inter_isCompact _ _ (e.hom ⁻¹ᵁ U).isOpen hU' (e.hom ⁻¹ᵁ V).isOpen hV'
  have rU := hR h q D c hc ha hcs hqs hu j0 X e U hU' pU
  have rV := hR h q D c hc ha hcs hqs hu j0 X e V hV' pV
  have rW := hR h q D c hc ha hcs hqs hu j0 X e (U ⊓ V) hW' pW
  let k := IsCofiltered.min j j0
  have hy' : pull _ (sch.map (c.π.app k)) _ _ (pull _ (sch.map (D.map (IsCofiltered.minToLeft j j0))) _ _ y) = 0 := by
    rw [← pull_comp, ← Functor.map_comp, c.w]; exact hy
  obtain ⟨l, g, hg⟩ := hC h hmv q D c hc j0 X e U V hUV rU rV rW n i k (IsCofiltered.minToRight j j0) _ hy'
  refine ⟨l, g ≫ IsCofiltered.minToLeft j j0, ?_⟩
  rw [D.map_comp, Functor.map_comp, pull_comp]; exact hg

end LateralTheory.E.StepKPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ClsBiprodEqZero
noncomputable section
open CategoryTheory Limits AlgebraicGeometry CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.BinPf

universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

theorem cls_biprod_eq_zero {K₁ K₂ L : CochainComplex C ℤ} {n : ℤ} (x : CohomologyClass (K₁ ⊞ K₂) L n)
    (h₁ : cpre (Cocycle.ofHom (biprod.inl : K₁ ⟶ K₁ ⊞ K₂)) L n n (zero_add n) x = 0)
    (h₂ : cpre (Cocycle.ofHom (biprod.inr : K₂ ⟶ K₁ ⊞ K₂)) L n n (zero_add n) x = 0) : x = 0 := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  rw [cpre_mk, CohomologyClass.mk_eq_zero_iff] at h₁ h₂
  obtain ⟨m, hm, β₁, hβ₁⟩ := h₁
  obtain ⟨m', hm', β₂, hβ₂⟩ := h₂
  have hmm : m' = m := by omega
  subst hmm
  rw [CohomologyClass.mk_eq_zero_iff]
  refine ⟨m', hm', (Cochain.ofHom (biprod.fst : K₁ ⊞ K₂ ⟶ K₁)).comp β₁ (zero_add m') +
    (Cochain.ofHom (biprod.snd : K₁ ⊞ K₂ ⟶ K₂)).comp β₂ (zero_add m'), ?_⟩
  rw [δ_add, δ_ofHom_comp, δ_ofHom_comp, hβ₁, hβ₂]
  change (Cochain.ofHom (biprod.fst : K₁ ⊞ K₂ ⟶ K₁)).comp ((Cochain.ofHom biprod.inl).comp α.1 (zero_add n)) (zero_add n) +
    (Cochain.ofHom (biprod.snd : K₁ ⊞ K₂ ⟶ K₂)).comp ((Cochain.ofHom biprod.inr).comp α.1 (zero_add n)) (zero_add n) = α.1
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.add_comp, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp, ← Cochain.ofHom_add, biprod.total,
    Cochain.id_comp]

theorem hkpull_comp {R : Type} [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ)
    (x : HK R M F n) : HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [HK.pull, HK.pre, cpre_mk, zcomp, Cochain.ofHom_comp]

theorem hkpull_id {R : Type} [CommRing R] {K : Cx R} (F : Shv R) (n : ℤ)
    (x : HK R K F n) : HK.pull R (𝟙 K) F n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [HK.pull, HK.pre, cpre_mk, zcomp]

def ChainsCoprod : Prop := ∀ (R : Type) [CommRing R] (U V : Spc),
  IsIso (biprod.desc ((chains R).map (coprod.inl : U ⟶ U ⨿ V)) ((chains R).map (coprod.inr : V ⟶ U ⨿ V)))

def CoprodAcyc : Prop := ∀ (q : ℕ) (U V : Spc), Acyc q U → Acyc q V → Acyc q (U ⨿ V)

theorem coprodAcyc_of (hC : ChainsCoprod) : CoprodAcyc := by
  intro q U V hU hV n i hn
  have hI := hC (ZMod q) U V
  set φ := biprod.desc ((chains (ZMod q)).map (coprod.inl : U ⟶ U ⨿ V)) ((chains (ZMod q)).map (coprod.inr : V ⟶ U ⨿ V))
  have h0 : ∀ x : Ht q (U ⨿ V) n i, x = 0 := by
    intro x
    have hy : HK.pull _ φ _ n x = 0 := by
      apply cls_biprod_eq_zero
      · have e := hkpull_comp (biprod.inl) φ (tw q i) n x
        rw [biprod.inl_desc] at e
        have : HK.pull _ ((chains (ZMod q)).map (coprod.inl : U ⟶ U ⨿ V)) (tw q i) n x = 0 :=
          (hU n i hn).elim _ _
        rw [this] at e
        exact e.symm
      · have e := hkpull_comp (biprod.inr) φ (tw q i) n x
        rw [biprod.inr_desc] at e
        have : HK.pull _ ((chains (ZMod q)).map (coprod.inr : V ⟶ U ⨿ V)) (tw q i) n x = 0 :=
          (hV n i hn).elim _ _
        rw [this] at e
        exact e.symm
    have e := hkpull_comp (inv φ) φ (tw q i) n x
    rw [IsIso.inv_hom_id, hkpull_id, hy, map_zero] at e
    exact e
  exact ⟨fun x y => by rw [h0 x, h0 y]⟩

def DescEqv : Prop := LateralTheory.E.t_E2Cut.Hyp → ∀ (q : ℕ) (A R0 R1 : Type) [CommRing A] [CommRing R0] [CommRing R1]
  (e : A ≃+* R0 × R1) (i : ℤ),
  Eqv _ (coprod.desc (spMap ((RingHom.fst R0 R1).comp e.toRingHom)) (spMap ((RingHom.snd R0 R1).comp e.toRingHom))) (tw q i)

end LateralTheory.E.BinPf

theorem LateralTheory.E.ProdAcycPf.Bin_of (hD : LateralTheory.E.BinPf.DescEqv) (hC : LateralTheory.E.BinPf.ChainsCoprod) :
    LateralTheory.E.ProdAcycPf.Bin := by
  intro H q A R0 R1 _ _ _ ⟨e⟩ h0 h1 n i hn
  have hb := (hD H q A R0 R1 e i n).1
  have hs := LateralTheory.E.BinPf.coprodAcyc_of hC q _ _ h0 h1 n i hn
  exact ⟨fun x y => hb (Subsingleton.elim _ _)⟩
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafMapWPf
section -- merged from Development.EtaleCohomology.EtaleSheaves.HalfDegreeVanishing
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.D2 LateralTheory.E.LeafGeomPf

namespace LateralTheory.E.HalfDegreeVanishing

theorem um_hom_val {N : ℕ} {A : Type} [CommRing A] {v w v' w' : Um N A} (hv : v = v') (hw : w = w') (p : v' ⟶ w') :
    (eqToHom hv ≫ p ≫ eqToHom hw.symm).1 = p.1 := by
  subst hv hw; simp

theorem um_functor_ext {N n : ℕ} {A : Type} [CommRing A] (F G : Fin (n + 1) ⥤ Um N A)
    (ho : ∀ i, (F.obj i).1 = (G.obj i).1) (hm : ∀ {i j : Fin (n + 1)} (f : i ⟶ j), (F.map f).1 = (G.map f).1) : F = G := by
  refine CategoryTheory.Functor.ext (fun i => Subtype.ext (ho i)) (fun i j f => ?_)
  apply Subtype.ext
  exact (hm f).trans (um_hom_val (Subtype.ext (ho i)) (Subtype.ext (ho j)) (G.map f)).symm

variable {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b))

theorem arrow_eq {n : ℕ} {X : Scheme.{0}} (x : Sx (PB (bsumOf V W)) n X) {i j : Fin (n + 1)} (f : i ⟶ j) :
    (show GL (Fin b) (Scheme.Γ.obj (op X)) from (pw W (pe V W x)).map f).val.mulVec (wb (a := a) ((pv V W x).obj i).1) =
      (((pv V W x).map f).1.2 : Scheme.Γ.obj (op X)) • wb (a := a) ((pv V W x).obj j).1 := by
  have e := ((pv V W x).map f).2
  rw [cond] at e
  have e2 := congrArg (wb (a := a)) e
  rw [wb_mulVec] at e2
  exact e2

def gfun {n : ℕ} {X : Scheme.{0}} (x : Sx (PB (bsumOf V W)) n X) (hx : AllSec V W x) :
    Fin (n + 1) ⥤ Um b (Scheme.Γ.obj (op X)) where
  obj i := ⟨wb (a := a) ((pv V W x).obj i).1, hx i⟩
  map {i j} f := ⟨((pw W (pe V W x)).map f, ((pv V W x).map f).1.2), arrow_eq V W x f⟩
  map_id i := Subtype.ext (Prod.ext ((pw W (pe V W x)).map_id i) (congrArg (fun p => p.1.2) ((pv V W x).map_id i)))
  map_comp f g := Subtype.ext (Prod.ext ((pw W (pe V W x)).map_comp f g) (congrArg (fun p => p.1.2) ((pv V W x).map_comp f g)))

theorem pe_res {n : ℕ} {X Y : Scheme.{0}} (k : Y ⟶ X) (x : Sx (PB (bsumOf V W)) n X) :
    pe V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n))).map k.op x) = (E.obj (op (SimplexCategory.mk n))).map k.op (pe V W x) :=
  NatTrans.naturality_apply
    ((pullback.fst (bsumOf V W) (PGL.pr (a + b))).app (op (SimplexCategory.mk n))) k.op x

theorem pw_res {n : ℕ} {X Y : Scheme.{0}} (k : Y ⟶ X) (e : Sx E n X) {i j : Fin (n + 1)} (f : i ⟶ j) :
    (show GL (Fin b) (Scheme.Γ.obj (op Y)) from (pw W ((E.obj (op (SimplexCategory.mk n))).map k.op e)).map f) =
      Matrix.GeneralLinearGroup.map (Scheme.Γ.map k.op).hom (show GL (Fin b) (Scheme.Γ.obj (op X)) from (pw W e).map f) :=
  eq_of_heq (Functor.hcongr_hom (NatTrans.naturality_apply (W.app (op (SimplexCategory.mk n))) k.op e) f)

end LateralTheory.E.HalfDegreeVanishing
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.D2 LateralTheory.E.LeafGeomPf LateralTheory.E.HalfDegreeVanishing

namespace LateralTheory.E.LeafMapWPf

variable {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b))

theorem pvm_res {n : ℕ} {X Y : Scheme.{0}} (k : Y ⟶ X) (x : Sx (PB (bsumOf V W)) n X) {i j : Fin (n + 1)} (f : i ⟶ j) :
    (((pv V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n))).map k.op x)).map f).1.2 : Scheme.Γ.obj (op Y)) =
      Scheme.Γ.map k.op (((pv V W x).map f).1.2 : Scheme.Γ.obj (op X)) := by
  let N := op (SimplexCategory.mk n)
  let projection : (PB (bsumOf V W)).obj N ⟶ (PGL (a + b)).obj N :=
    (pullback.snd (bsumOf V W) (PGL.pr (a + b))).app N
  have h := types_congr_hom (projection.naturality k.op) x
  have h2 := congrArg (fun p => (p.1.2 : Scheme.Γ.obj (op Y))) (Functor.congr_hom h f)
  refine h2.trans ?_
  have h3 := congrArg (fun p => (p.2 : Scheme.Γ.obj (op Y)))
    (um_hom_val (Functor.congr_obj h i) (Functor.congr_obj h j)
      ((((PGL (a + b)).obj N).map k.op (pv V W x)).map f))
  exact h3.trans rfl

theorem pvm_simp {n m : ℕ} {X : Scheme.{0}} (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (x : Sx (PB (bsumOf V W)) n X)
    {i j : Fin (m + 1)} (f : i ⟶ j) :
    (((pv V W ((((PB (bsumOf V W)).map θ.op).app (op X)) x)).map f).1.2 : Scheme.Γ.obj (op X)) =
      (((((PGL (a + b)).map θ.op).app (op X)) (pv V W x) : Fin (m + 1) ⥤ Um (a + b) (Scheme.Γ.obj (op X))).map f).1.2 := by
  have h := types_congr_hom
    (NatTrans.congr_app ((pullback.snd (bsumOf V W) (PGL.pr (a + b))).naturality θ.op) (op X)) x
  have h2 := congrArg (fun p => (p.1.2 : Scheme.Γ.obj (op X))) (Functor.congr_hom h f)
  refine h2.trans ?_
  have h3 := congrArg (fun p => (p.2 : Scheme.Γ.obj (op X))) (um_hom_val (Functor.congr_obj h i) (Functor.congr_obj h j) (((ConcreteCategory.hom
      (((pullback.snd (bsumOf V W) (PGL.pr (a + b))).app (op (SimplexCategory.mk n))).app (op X) ≫
        (((PGL (a + b)).map θ.op).app (op X)))) x).map f))
  exact h3.trans rfl

theorem pe_simp {n m : ℕ} {X : Scheme.{0}} (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (x : Sx (PB (bsumOf V W)) n X) :
    pe V W ((((PB (bsumOf V W)).map θ.op).app (op X)) x) = ((E.map θ.op).app (op X)) (pe V W x) :=
  types_congr_hom
    (NatTrans.congr_app ((pullback.fst (bsumOf V W) (PGL.pr (a + b))).naturality θ.op) (op X)) x

theorem pw_simp {n m : ℕ} {X : Scheme.{0}} (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (e : Sx E n X)
    {i j : Fin (m + 1)} (f : i ⟶ j) :
    (show GL (Fin b) (Scheme.Γ.obj (op X)) from (pw W (((E.map θ.op).app (op X)) e)).map f) =
      (show GL (Fin b) (Scheme.Γ.obj (op X)) from
        ((((ofCat (glCat b)).map θ.op).app (op X)) (pw W e) : Fin (m + 1) ⥤ SingleObj (GL (Fin b) (Scheme.Γ.obj (op X)))).map f) :=
  eq_of_heq (Functor.hcongr_hom (types_congr_hom (NatTrans.congr_app (W.naturality θ.op) (op X)) e) f)

def gX (n : SimplexCategoryᵒᵖ) (X : Scheme.{0}ᵒᵖ) (x : ((U2 V W).obj n).obj X) : ((PGL b).obj n).obj X :=
  show Fin (n.unop.len + 1) ⥤ Um b (Scheme.Γ.obj (op X.unop)) from gfun V W x.1 x.2

theorem gX_nat_X (n : SimplexCategoryᵒᵖ) {X Y : Scheme.{0}ᵒᵖ} (k : X ⟶ Y) (x : ((U2 V W).obj n).obj X) :
    gX V W n Y (((U2 V W).obj n).map k x) = ((PGL b).obj n).map k (gX V W n X x) := by
  apply um_functor_ext
  · intro i
    show wb (a := a) ((pv V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n.unop.len))).map k.unop.op x.1)).obj i).1 = _
    rw [pv_res]; rfl
  · intro i j f
    apply Prod.ext
    · show (show GL (Fin b) _ from (pw W (pe V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n.unop.len))).map k.unop.op x.1))).map f) = _
      rw [pe_res, pw_res]; rfl
    · apply Units.ext
      exact pvm_res V W k.unop x.1 f

theorem gX_nat_n {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (X : Scheme.{0}ᵒᵖ) (x : ((U2 V W).obj n).obj X) :
    gX V W m X ((((U2 V W).map θ).app X) x) = (((PGL b).map θ).app X) (gX V W n X x) := by
  apply um_functor_ext
  · intro i
    show wb (a := a) ((pv V W ((((PB (bsumOf V W)).map θ.unop.op).app (op X.unop)) x.1)).obj i).1 = _
    rw [pv_simp]; rfl
  · intro i j f
    apply Prod.ext
    · show (show GL (Fin b) _ from (pw W (pe V W ((((PB (bsumOf V W)).map θ.unop.op).app (op X.unop)) x.1))).map f) = _
      rw [pe_simp, pw_simp]; rfl
    · apply Units.ext
      exact (pvm_simp V W θ.unop x.1 f).trans rfl

def gmap : U2 V W ⟶ PGL b where
  app n :=
    { app := fun X => TypeCat.ofHom (gX V W n X)
      naturality := fun X Y k => by
        ext x
        exact gX_nat_X V W n k x }
  naturality n m θ := by
    ext X x
    exact gX_nat_n V W θ X x

theorem gmap_pr : gmap V W ≫ PGL.pr b = f2 V W ≫ PB.pr _ ≫ W := by
  ext n X x
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun i j f => ?_)
  erw [Category.id_comp, Category.comp_id]
  rfl

theorem gmap_line : gmap V W ≫ PGL.line b = f2 V W ≫ pullback.snd (bsumOf V W) (PGL.pr (a + b)) ≫ PGL.line (a + b) := by
  ext n X x
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun i j f => ?_)
  erw [Category.id_comp, Category.comp_id]
  rfl

theorem LeafMapW_of : LateralTheory.E.HalfDegreeVanishing.LeafMapW := fun V W => ⟨gmap V W, gmap_pr V W, gmap_line V W⟩

end LateralTheory.E.LeafMapWPf
end
end
