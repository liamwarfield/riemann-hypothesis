module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcDatumMatchLengthSymmPreimages
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CmFieldHostElementAddConjEqOne
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdaptedBasisFourierTermSizesTorusPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormsOfAdapted
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.NormsPf
open GlobalTheory.ZH

section
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

theorem sum_smul_f {I : Type} (A : Finset I) (a : I → F) (s : I → Fam D F k) (α : D.X) (j) :
    ((∑ i ∈ A, a i • s i).s α).f j = ∑ i ∈ A, resTop _ (gF D F (a i)) * ((s i).s α).f j := by
  classical
  induction A using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
  | insert i A hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, DVR.add_f, DVR.smul_f, ih]

theorem sum_smul_subtype {I : Type} [Fintype I] (p : I → Prop) [Fintype {i // p i}] (a : I → F) (s : I → Fam D F k)
    (α : D.X) (h : ∀ i, ¬ p i → ∀ j, ((s i).s α).f j = 0) :
    (∑ i, a i • s i).s α = (∑ i : {i // p i}, a i • s i).s α := by
  classical
  refine SecOps.sec_ext fun j => ?_
  rw [sum_smul_f, sum_smul_f, ← Finset.sum_subtype (Finset.univ.filter p) (by simp)
    (fun i => resTop _ (gF D F (a i)) * ((s i).s α).f j), Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · rfl
  · rw [h i hi j, mul_zero]

theorem zero_of_famOf {s : Fam D F k} {f : ∀ α, D.SecB k α} (hs : FamOf D F f s) {α : D.X}
    (h : ∀ j, (f α).f j = 0) (j) : (s.s α).f j = 0 := by
  refine sec_ext_val (s' := SecOps.secZero) D.P.isLB (fun y J hJ => ?_) j
  rw [← SectionScalarValuation.secScal_sval (hs α) _ y hJ, UUA.sval_zero_of h _ y J (hJ.mem _ _),
    UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _)]

theorem basis_of_eq (hT : TwistBaseChangeStatement) [IsLocalRing R] [IsNoetherianRing R] (hk : 1 ≤ k) {α : D.X}
    {R' : Type} [CommRing R'] (φ : R →+* R') {B : Scheme.{0}} {pB : B ⟶ Sp R'} {π : B ⟶ D.P.A.left}
    (H : IsPullback π pB D.P.A.hom (spMap φ)) {I : Type} [Fintype I] {β : I → D.SecB k α} (hβ : IsBasisB D β)
    (ψ : Fin 4 → (B ⟶ D.P.A.left)) (hψ : ψ = fun i => π ≫ D.famφB α i)
    (t : I → LB.Sec (LB.LinComb D.P.L ψ (DegPre.famε k)))
    (ht : ∀ i, GeneratorPullback.SecScal D.P.L ψ (DegPre.famε k) (t i) (D.famφB α) (DegPre.famε k) (β i) π 1)
    (b : LB.Sec (LB.LinComb D.P.L ψ (DegPre.famε k))) : ∃! a : I → R', IsLin pB t a b := by
  subst hψ
  have e : t = fun i => DVR.pullSec D.P.L (D.famφB α) (DegPre.famε k) (β i) π := funext fun i =>
    SecOps.sec_ext fun j => sec_ext_val D.P.isLB (fun y J hJ =>
      (SectionScalarValuation.secScal_sval (ht i) _ y hJ).symm.trans (SectionScalarValuation.sval_pullSec _ _ _ _ _ y hJ).symm) j
  rw [e]
  exact BasisBaseChange.basis_pullback hT R D k hk α R' φ B pB π H I β hβ b

theorem component_basis (hT : TwistBaseChangeStatement) [IsLocalRing R] [IsNoetherianRing R] (hk : 1 ≤ k) {α : D.X}
    {I : Type} [Fintype I] {β : I → D.SecB k α} (hβ : IsBasisB D β) (s : I → Fam D F k)
    (hs : ∀ i, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) ((s i).s α)
      (D.famφB α) (DegPre.famε k) (β i) (DegPre.prB D F).left 1)
    (b : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))) :
    ∃! a : I → F, b = (∑ i, a i • s i).s α := by
  let f : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))
  have hTF : jFK (R := R) F ≫ jK R = spMap f := by
    show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have H : IsPullback (DegPre.prB D F).left (fst (TF (R := R) F) D.P.A).left D.P.A.hom (spMap f) := by
    rw [← hTF]
    exact (IsPullback.of_hasPullback (jFK (R := R) F ≫ jK R) D.P.A.hom).flip
  have h := basis_of_eq hT hk f H hβ (DegPre.famφ D F α) (funext fun i => GC.famφ_eq D F α i)
    (fun i => (s i).s α) hs b
  refine (existsUnique_congr fun a => ?_).1 h
  exact ⟨fun h => SecOps.sec_ext fun j => (h j).trans (sum_smul_f _ a s α j).symm,
    fun h j => (congrArg (fun x => x.f j) h).trans (sum_smul_f _ a s α j)⟩

end

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}
  {k : ℕ}

theorem vge_comb_iff (hT : TwistBaseChangeStatement) (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) (hk : 1 ≤ k)
    {α : D.toPre.X} {I : Type} [Fintype I] {β : I → D.toPre.SecB k α} (hβ : IsBasisB D.toPre β)
    (s : I → Fam D.toPre F k)
    (hs : ∀ i, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) ((s i).s α)
      (D.toPre.famφB α) (DegPre.famε k) (β i) (DegPre.prB D.toPre F).left 1) (a : I → F) (q : ℚ) :
    VGe D F v k α ((∑ i, a i • s i).s α) q ↔ ∀ i, (q : WithTop ℚ) ≤ v (a i) := by
  constructor
  · intro h
    obtain ⟨b, hb, e⟩ := GlobalTheory.TermSize.exists_comb hϖ hv hβ s hs h
    rw [(component_basis hT hk hβ s hs _).unique rfl e]
    exact hb
  · intro h
    let e := (Fintype.equivFin I).symm
    refine ⟨_, fun i => a (e i), fun i => β (e i), fun i => (s (e i)).s α, fun i => hs _, fun i => h _, fun j => ?_⟩
    rw [sum_smul_f]
    exact (Equiv.sum_comp e _).symm

end

theorem norms_of_adapted : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ k : ℕ, 1 ≤ k → ∀ (r : ℕ) (cls : Fin r → D.toPre.X) (mu : ℕ) (f : Fin r → ∀ α, D.toPre.SecB k α) (s : Fin r → Fam D.toPre F k), AdFam D Q k cls mu f → (∀ i, GlobalTheory.ZH.FamOf D.toPre F (f i) (s i)) → Norms D Q v k cls s := by
  intro hLL _ _ _ _ V _ _ _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv k hk r cls mu f s hA hs
  classical
  obtain ⟨⟨hshort, hcls, hcov, -⟩, -, hzero, hbas⟩ := hA
  have hG := hLL.1.globalFns
  have hT : TwistBaseChangeStatement := GlobalTheory.twistBaseChange_of_finrank_sections_one fun K _ _ P =>
    (hLL.1.globalSectionsRank K P 1 le_rfl).trans (one_pow _)
  have hsub : ∀ (a : Fin r → F) i₀, (∑ i, a i • s i).s (cls i₀) =
      (∑ i : {i // cls i = cls i₀}, a i • s i).s (cls i₀) := fun a i₀ =>
    sum_smul_subtype (fun i => cls i = cls i₀) a s _ fun i hi =>
      zero_of_famOf (hs i) (hzero i _ fun z hz => hi (hcls i₀ i ⟨z, hz⟩).symm)
  have hB := fun i₀ => component_basis (F := F) hT hk (hbas i₀) (fun i => s i) (fun i => hs i _)
  have hV : ∀ (a : Fin r → F) (q : ℚ) i₀, VGe D F v k (cls i₀) ((∑ i, a i • s i).s (cls i₀)) q ↔
      ∀ i : {i // cls i = cls i₀}, (q : WithTop ℚ) ≤ v (a i) := fun a q i₀ => by
    rw [hsub]
    exact vge_comb_iff hT hϖ hv hk (hbas i₀) (fun i => s i) (fun i => hs i _) (fun i => a i) q
  refine ⟨fun s' => ?_, fun a q => ⟨?_, ⟨fun h i => (hV a q i).1 (h _) ⟨i, rfl⟩, fun h α => ?_⟩,
    fun i h => (hV a q i).1 h ⟨i, rfl⟩⟩⟩
  · have ex : ∀ α, ∃ c : {i // cls i = α} → F, (∃ i₀, cls i₀ = α) →
        s'.s α = (∑ i : {i // cls i = α}, c i • s i).s α := fun α => by
      by_cases h : ∃ i₀, cls i₀ = α
      · obtain ⟨i₀, rfl⟩ := h
        obtain ⟨c, hc⟩ := (hB i₀ (s'.s (cls i₀))).exists
        exact ⟨c, fun _ => by convert hc⟩
      · exact ⟨0, fun h' => absurd h' h⟩
    choose c hc using ex
    refine existsUnique_of_exists_of_unique ⟨fun i => c (cls i) ⟨i, rfl⟩, fam_ext fun α j => ?_⟩ fun a a' ha ha' => ?_
    · obtain ⟨i₀, z, rfl⟩ := hcov α
      refine congrArg (fun x => x.f j) (GlobalTheory.FamFree.eq_of_eq_add_nsmul hG _ _ ⟨z, rfl⟩ ?_)
      rw [hsub, hc _ ⟨i₀, rfl⟩]
      have e : ∀ α (i : {i // cls i = α}), c α i = c (cls i) ⟨i, rfl⟩ := by rintro _ ⟨i, rfl⟩; rfl
      simp only [← e]
    · funext i
      have h := (hB i (s'.s (cls i))).unique (y₁ := fun i' => a i') (y₂ := fun i' => a' i')
        (by rw [ha, hsub]) (by rw [ha', hsub])
      exact congrFun h ⟨i, rfl⟩
  · rw [n1a V ϖ hϖ D Q hQ F v hv k hk (Finset.univ.image cls) (fun χ => by
      obtain ⟨i, hi⟩ := hcov χ
      exact ⟨cls i, Finset.mem_image_of_mem _ (Finset.mem_univ i), hi⟩) _ q]
    simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index, forall_apply_eq_imp_iff, hV]
    exact ⟨fun h i => h i ⟨i, rfl⟩, fun h i₀ i => by have := h i; rwa [i.2] at this⟩
  · obtain ⟨i₀, z, rfl⟩ := hcov α
    refine (SectionScalarValuation.fe_move hϖ hQ hv k z (cls i₀) _ ((hV a q i₀).2 fun i => h i)).mono ?_
    have h1 := hshort i₀ z
    rw [q_shift hϖ hQ] at h1
    have h2 : (0 : ℤ) ≤ k * Q z + QForm.bOf D.toPre Q z (cls i₀) :=
      nonneg_of_mul_nonneg_right (a := (k : ℤ)) (by linarith) (by omega)
    have h3 : (0 : ℚ) ≤ ((k * Q z + QForm.bOf D.toPre Q z (cls i₀) : ℤ) : ℚ) := by exact_mod_cast h2
    linarith

end GlobalTheory.OneBasis.NormsPf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoSection
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.Bridge
open GlobalTheory.ConstFam GlobalTheory.FieldBaseChange

section General
variable {X X' X₁ X₂ Y Y' : Scheme.{0}}

theorem exists_iso_section {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (w₀ : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (hw : w₀.IsGen) (g : X₁ ⟶ Y) (hg : g ≫ f₁ = 𝟙 _) :
    ∃ w₁ : LB.Iso L₁ (L₂.pull (g ≫ f₂)), PGen w₁ ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ X₁) (z : Z) (j : L₂.ι) (i : L₁.ι),
      (g ≫ f₂) (r z) ∈ L₂.U j → r z ∈ L₁.U i → gw w₁ r z j i = GlobalTheory.BoxExpansion.pw w₀ (r ≫ g) z i j := by
  have hpt : ∀ x : X₁, f₁ (g x) = x := fun x => congrArg (fun q => q x) hg
  have le : ∀ (J : PUnit → L₂.ι) (i : L₁.ι), (L₂.pull (g ≫ f₂)).U J ⊓ L₁.U i ≤
      g ⁻¹ᵁ ((L₂.pull f₂).U J ⊓ (L₁.pull f₁).U (fun _ => i)) := fun J i x hx =>
    ⟨mem_pull.2 (mem_pull₂.1 hx.1), mem_pull.2 (by rw [hpt]; exact hx.2)⟩
  let w₁ : LB.Iso L₁ (L₂.pull (g ≫ f₂)) := ⟨fun p => res (le p.1 p.2) (pullU g _ (w₀.s (p.1, fun _ => p.2)))⟩
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ X₁) (z : Z) (j : L₂.ι) (i : L₁.ι),
      (g ≫ f₂) (r z) ∈ L₂.U j → r z ∈ L₁.U i → gw w₁ r z j i = GlobalTheory.BoxExpansion.pw w₀ (r ≫ g) z i j :=
    fun Z r z j i hj hi => by
      have hm : r z ∈ (L₂.pull (g ≫ f₂)).U (fun _ => j) ⊓ L₁.U i := ⟨mem_pull.2 hj, hi⟩
      exact (gm_res r z (le _ _) hm _).trans (gm_pull r g z _ (le _ _ hm) _)
  refine ⟨w₁, fun Z r z j j' i i' hj hj' hi hi' => ?_, key⟩
  have := GlobalTheory.BoxExpansion.pw_trans hw (r ≫ g) z (j₁ := i) (j₁' := i') (j₂ := j) (j₂' := j')
    (by show f₁ (g (r z)) ∈ _; rw [hpt]; exact hi) (by show f₁ (g (r z)) ∈ _; rw [hpt]; exact hi') hj hj'
  rw [Category.assoc, Category.assoc, hg, Category.comp_id] at this
  rw [key Z r z j i hj hi, key Z r z j' i' hj' hi', this]

variable {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}

theorem pmaps_of_val (hL : L.IsLB) (hL' : L'.IsLB) {φ' : PUnit → (Y' ⟶ X')} {φ : PUnit → (Y ⟶ X)} {ε : PUnit → ℤ}
    {h : Y' ⟶ Y} (hψ : ∀ k, φ' k ≫ F = h ≫ φ k) {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)}
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) J J', Good L z J → Good L' z J' →
      val t (r ≫ h) z J = (∏ k, wVal w z J J' (r ≫ φ' k) ^ ε k) * val a r z J') : PMaps w φ' φ ε a t h := by
  intro Z r z p q hp hq
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (fun k => (r ≫ φ' k) ≫ F) p (fun _ _ _ => rfl) hp
  obtain ⟨J', hJ', e'⟩ := exists_good L' hL' z (fun k => r ≫ φ' k) q (fun _ _ _ => rfl) hq
  have := H Z r z J J' hJ hJ'
  rw [val_of t _ z J p (fun k => by rw [← e k, Category.assoc, Category.assoc, hψ]), val_of a _ z J' q e'] at this
  refine this.trans (congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_))
  rw [wVal, e k, e' k]

theorem exists_equiv (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) (e : Y ≅ X') {R : Type} [CommRing R]
    (π' : X' ⟶ Spec (CommRingCat.of R)) (π : Y ⟶ Spec (CommRingCat.of R)) (hπ : e.inv ≫ π = π') (p : Y ⟶ X)
    (hp : p = e.hom ≫ F) (k : ℤ) :
    ∃ θ : SecOver π (LB.LinComb L (fun _ : Fin 1 => p) (fun _ => k)) ≃ₗ[R]
        SecOver π' (LB.LinComb L' (fun _ : Fin 1 => 𝟙 X') (fun _ => k)),
      ∀ t (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) J J', Good L z J → Good L' z J' →
        sval t (r ≫ e.inv) z J = (wVal w z J J' r ^ k).val * sval (θ t) r z J' := by
  subst hp
  have hψ : ∀ _ : Fin 1, 𝟙 X' ≫ F = e.inv ≫ e.hom ≫ F := fun _ => by rw [e.inv_hom_id_assoc, Category.id_comp]
  have hid : e.inv ≫ π = π' ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)) := by
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id, hπ]
  let θ := pullThrough (φ := fun _ : Fin 1 => e.hom ≫ F) (φ' := fun _ : Fin 1 => 𝟙 X') hw hL hL' hψ (fun _ => k) hid
  have hθ : ∀ t (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) J J', Good L z J → Good L' z J' →
      sval t (r ≫ e.inv) z J = (wVal w z J J' r ^ k).val * sval (θ t) r z J' := fun t Z r z J J' hJ hJ' => by
    have := sval_pullThrough (φ := fun _ : Fin 1 => e.hom ≫ F) (φ' := fun _ : Fin 1 => 𝟙 X') hw hL hL' hψ hid t r hJ hJ'
    rwa [Fin.prod_univ_one, Category.comp_id] at this
  refine ⟨LinearEquiv.ofBijective θ ⟨?_, fun a => ?_⟩, hθ⟩
  · refine (injective_iff_map_eq_zero θ).2 fun t ht => sec_ext' hL fun y J hJ => ?_
    obtain ⟨J', hJ'⟩ := exists_good' hL' y
    have := hθ t _ e.hom y J J' hJ hJ'
    rw [e.hom_inv_id, ht, sval_zero' hJ', mul_zero] at this
    rw [this, sval_zero' hJ]
  · have hq : e.hom ≫ π' = (e.hom ≫ π') ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)) := by
      rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]
    have hφ : ∀ _ : Fin 1, e.hom = e.hom ≫ 𝟙 X' := fun _ => (Category.comp_id _).symm
    obtain ⟨t, ht⟩ := exists_sec_up (φ' := fun _ : Fin 1 => e.hom) ((isGen_iff w).1 hw) hL hL'
      (pullOver L' (fun _ => k) hq hφ a)
    have H : SecThrough w (fun _ : Fin 1 => e.hom) (fun _ => e.hom ≫ F) (fun _ => k)
        (pullOver L' (fun _ => k) hq hφ a) t (𝟙 _) := fun Z r z p q hp hq => by
      rw [Category.comp_id]
      exact ht Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq)
    refine ⟨t, sec_ext' hL' fun y J' hJ' => ?_⟩
    obtain ⟨J, hJ⟩ := exists_good' hL y
    have a₁ := H.sval (fun _ => (Category.id_comp _).symm) e.inv hJ hJ'
    have a₂ := hθ t _ (𝟙 _) y J J' hJ hJ'
    rw [Fin.prod_univ_one, sval_pullOver hq hφ a _ hJ', e.inv_hom_id, Category.comp_id] at a₁
    rw [Category.id_comp] at a₂
    exact (Units.mul_right_inj _).1 (a₂.symm.trans a₁)

end General

section Basis
variable {Z : Scheme.{0}} {G₀ : Over Z} {L₀ : LB G₀.left} {R : Type} [CommRing R]
  {G : Over (Spec (CommRingCat.of R))} {L : LB G.left} {χ : Sp R ⟶ Z} {Φ : G.left ⟶ G₀.left}

theorem exists_basis (hL₀ : L₀.IsLB) (hL : L.IsLB) (H : IsPullback Φ G.hom G₀.hom χ) {ω : LB.Iso L (L₀.pull Φ)}
    (hω : ω.IsGen) {k n : ℕ} (σ : Fin n → H0 L k) (hσ : IsBasisH σ) :
    ∃ (g : G.left ⟶ (Over.mk χ ⊗ G₀).left) (b : Fin n → LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk χ))),
      g ≫ (fst (Over.mk χ) G₀).left = G.hom ∧ g ≫ (snd (Over.mk χ) G₀).left = Φ ∧ BasisAlong G₀ L₀ k (𝟙 _) b ∧
      ∀ i (Y : Scheme.{0}) (r : Y ⟶ G.left) (z : Y) J J', Good L₀ z J → Good L z J' →
        sval (L := L₀) (φ := fun _ : Fin 1 => (snd (Over.mk χ) G₀).left) (ε := fun _ => (k : ℤ)) (b i) (r ≫ g) z J =
          (wVal ω z J J' r).val ^ k * sval (σ i) r z J' := by
  let e : G.left ≅ (Over.mk χ ⊗ G₀).left := H.flip.isoPullback
  have e₁ : e.hom ≫ (fst (Over.mk χ) G₀).left = G.hom := H.flip.isoPullback_hom_fst
  have e₂ : e.hom ≫ (snd (Over.mk χ) G₀).left = Φ := H.flip.isoPullback_hom_snd
  obtain ⟨θ, hθ⟩ := exists_equiv hω hL₀ hL e.symm G.hom (fst (Over.mk χ) G₀).left e₁ (snd (Over.mk χ) G₀).left
    (by rw [← e₂]; exact (e.inv_hom_id_assoc _).symm) (k : ℤ)
  refine ⟨e.hom, fun i => θ.symm (σ i), e₁, e₂, fun s => ?_, fun i Y r z J J' hJ hJ' => ?_⟩
  · have k₁ : ∀ (s' : SecOver G.hom (LB.LinComb L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)))) (c : Fin n → R),
        (∀ j, s'.f j = ∑ i, resTop _ (scal G.hom (c i)) * (σ i).f j) ↔
          s' = ∑ i, c i • (show SecOver G.hom _ from σ i) := fun s' c => by
      have : ∀ j, LB.Sec.f (∑ i, c i • (show SecOver G.hom _ from σ i) : SecOver G.hom _) j =
          ∑ i, resTop _ (scal G.hom (c i)) * (σ i).f j := fun j =>
        map_sum (chartLin G.hom _ j) _ _
      exact ⟨fun h => SecOver.ext _ _ fun j => (h j).trans (this j).symm, fun h j => h ▸ this j⟩
    have k₂ : ∀ c : Fin n → R, Lin G₀ L₀ k (𝟙 (Over.mk χ)) (fun i => θ.symm (σ i)) (fun i => fnR (c i)) s ↔
        θ s = ∑ i, c i • (show SecOver G.hom _ from σ i) := fun c => by
      have v : ∀ z J, Good L₀ z J → sval (L := L₀) (φ := fun _ : Fin 1 => (snd (Over.mk χ) G₀).left)
          (ε := fun _ => (k : ℤ)) (∑ i, c i • θ.symm (σ i) : SecOver (fst (Over.mk χ) G₀).left _) (𝟙 _) z J =
          ∑ i, gs (fst (Over.mk χ) G₀).left z ⊤ (fnR (c i)) * sval (L := L₀)
            (φ := fun _ : Fin 1 => (snd (Over.mk χ) G₀).left) (ε := fun _ => (k : ℤ)) (θ.symm (σ i))
            ((𝟙 (Over.mk χ)) ▷ G₀).left z J := fun z J hJ => by
        rw [sval_sum' hJ]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [sval_smul' hJ, Category.id_comp, id_whiskerRight, Over.id_left]
        rfl
      have u : θ.symm (∑ i, c i • (show SecOver G.hom _ from σ i)) = ∑ i, c i • θ.symm (σ i) :=
        (map_sum _ _ _).trans (Finset.sum_congr rfl fun i _ => map_smul _ _ _)
      refine Iff.trans ?_ (θ.eq_symm_apply (y := s))
      rw [u]
      exact ⟨fun h => sec_ext' hL₀ fun z J hJ => (h z J hJ).trans (v z J hJ).symm,
        fun h z J hJ => (congrArg (fun q => sval (L := L₀) (φ := fun _ : Fin 1 => (snd (Over.mk χ) G₀).left)
          (ε := fun _ => (k : ℤ)) q (𝟙 _) z J) h).trans (v z J hJ)⟩
    obtain ⟨c, hc, hu⟩ := hσ (θ s)
    refine ⟨fun i => fnR (c i), (k₂ c).2 ((k₁ _ c).1 hc), fun c' hc' => ?_⟩
    obtain ⟨c'', rfl⟩ : ∃ c'' : Fin n → R, c' = fun i => fnR (c'' i) :=
      ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (c' i), funext fun i =>
        (congrArg (fun q => q.hom (c' i)) (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id).symm⟩
    rw [hu c'' ((k₁ _ c'').2 ((k₂ c'').1 hc'))]
  · have := hθ (θ.symm (σ i)) Y r z J J' hJ hJ'
    rw [zpow_natCast, Units.val_pow_eq_pow_val] at this
    exact this.trans (congrArg (fun q => _ * sval q r z J') (θ.apply_symm_apply (σ i)))

end Basis

section Expand
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)

theorem exists_expandsG (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (hE : ∀ e, U.ExpandsAt e k σ f)
    (s : Fam D.toPre F k) (hs : GlobalTheory.ZH.FamOf D.toPre F f s) : ∃ σ' : U.SecGF F k, U.ExpandsG F k σ' s ∧
      ∀ y J, Good U.LG.L y J → sval σ' (𝟙 _) y J = sval σ (UnifPre.gFK (G := G) F) y J := by
  have one : ∀ {Y : Scheme.{0}} (π : Y ⟶ Spec (CommRingCat.of F)) (y : Y), gs (𝟙 Y) y ⊤ (scal π (1 : F)) = 1 :=
    fun π y => by simp only [gs_eq _ y ⊤ trivial, scal, map_one]
  obtain ⟨σ', h⟩ := GlobalTheory.BoxExpansion.exists_secLin U.LG.isLB
    (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (UnifPre.gFK (G := G) F)
    (fun _ : Fin 1 => UnifPre.gFK (G := G) F) (φ := fun _ => 𝟙 G.left) (fun _ => (Category.comp_id _).symm)
    (fun _ : Fin 1 => σ) (fun _ => (1 : F))
  refine ⟨σ', ⟨1, fun _ => 1, fun _ => σ, fun _ => f, fun _ => hE, h,
    fun α => (secLin_iff_val D.toPre.P.isLB _ _ _ _).2 fun y J hJ => ?_⟩, fun y J hJ => ?_⟩
  · rw [Fin.sum_univ_one, one, _root_.one_mul]
    exact (SectionScalarValuation.secScal_sval (hs α) _ y hJ).symm
  · have := (secLin_iff_val U.LG.isLB _ _ _ _).1 h y J hJ
    rwa [Fin.sum_univ_one, one, _root_.one_mul, Category.id_comp] at this

end Expand

theorem exists_bridge : ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] (L₀ : LB G₀.left), L₀.IsLB → ∀ (ρ₀ : LB.Gen (L₀.pull (eSec G₀))), ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (χ : Sp R ⟶ Z) (Φ : G.left ⟶ G₀.left) (ω : LB.Iso U.LG.L (L₀.pull Φ)), RigPull G G₀ χ Φ ω U.LG.rig ρ₀ → ∃ (φ : A.A.left ⟶ G₀.left) (w : LB.Iso A.L (L₀.pull φ)) (ρ : LB.Gen (A.L.pull (eSec A.A))) (w₀ : W0 U), RigPull A.A G₀ (jK R ≫ χ) φ w ρ ρ₀ ∧ NormW U w₀ ρ ∧ ∀ (k r : ℕ) (σ : Fin r → H0 U.LG.L k), IsBasisH σ → ∃ b : Fin r → LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk χ)), BasisAlong G₀ L₀ k (𝟙 _) b ∧ ∀ (i : Fin r) (F : Type) [Field F] [Algebra (FractionRing R) F] (f : ∀ α, D.toPre.SecB k α) (s : Fam D.toPre F k) (t : SecA A F k), (∀ e, U.ExpandsAt e k (σ i) f) → GlobalTheory.ZH.FamOf D.toPre F f s → Thru w k (T' := TFK (R := R) F) (T := Over.mk χ) (jFK (R := R) F ≫ jK R) (b i) t → U.ExpandsF F k w₀ t s := by
  intro Z G₀ _ L₀ hL₀ ρ₀ R _ _ I D A G _ _ U χ Φ ω ⟨gp, hω, _, hρ⟩
  obtain ⟨w₀, hw₀⟩ := U.ext
  have := U.gen_hom
  have hg : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]
  have hg' : U.gen.hom.left ≫ U.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.hom_inv_id, Over.id_left]
  have : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have gi : IsGrpPullback A.A ((Over.pullback (jK R)).obj G) (𝟙 _) U.gen.inv.left := isGrpPullback_of_iso U.gen.symm
  have gψ : IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) :=
    (gi.comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl
  have ei : eSec A.A ≫ U.gen.inv.left = eSec ((Over.pullback (jK R)).obj G) :=
    (GlobalTheory.PolBaseChange.eSec_comm gi).trans (Category.id_comp _)
  have eψ := GlobalTheory.PolBaseChange.eSec_comm gψ
  obtain ⟨w₁, hw₁, Hw₁⟩ := exists_iso_section w₀ hw₀ U.gen.inv.left hg
  obtain ⟨ρ, hρ₁, Hρ⟩ := exists_gen_through (K := PUnit) (φ' := fun _ => eSec A.A) (φ := fun _ => eSec G)
    (ε := fun _ => 1) (h := jK R) ((isGen_iff w₁).2 hw₁) U.LG.isLB A.isLB (fun _ => eψ) U.LG.rig U.LG.rigGen
  obtain ⟨w, T⟩ := exists_comp U.LG.isLB ω w₁ ((isGen_iff ω).1 hω) hw₁ hL₀ A.isLB
  refine ⟨_, w, ρ, w₀, ⟨gψ.comp gp, (isGen_iff w).2 (T.pgen_comp U.LG.isLB ((isGen_iff ω).1 hω) hw₁), hρ₁,
    T.pmaps_comp U.LG.isLB (fun _ => eψ) hρ (pmaps_of_val U.LG.isLB A.isLB (fun _ => eψ) Hρ)⟩,
    ⟨hw₀, hρ₁, fun z JA JG hA hG => ?_⟩, fun k r σ hσ => ?_⟩
  · have a := Hρ _ (𝟙 _) z JG JA hG hA
    rw [Fintype.prod_unique, zpow_one, Category.id_comp, Category.id_comp] at a
    have c := Hw₁ _ (eSec A.A) z _ _ (hG (eSec A.A ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R))) (hA (eSec A.A))
    refine Eq.trans (congrArg (· * _) ?_) a.symm
    refine Eq.trans ?_ c.symm
    rw [eψ, ei]
    rfl
  · obtain ⟨g, b, g₁, g₂, hb, Hb⟩ := exists_basis hL₀ U.LG.isLB gp.1 hω σ hσ
    refine ⟨b, hb, fun i F _ _ f s t hE hs ht => ?_⟩
    obtain ⟨σ', h₁, h₂⟩ := exists_expandsG U F k (σ i) f hE s hs
    have m₁ : (U.genF F).left ≫ (fst (TFK (R := R) F) A.A).left =
        (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
      rw [← Over.comp_left, lift_fst]
    have m₂ : (U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left =
        (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left := by
      rw [← Over.comp_left, lift_snd, Over.comp_left]
    have m₃ : ((snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left) ≫ U.gen.inv.left =
        (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by rw [Category.assoc, hg', Category.comp_id]
    have m₄ : ((snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left) ≫ U.gen.inv.left ≫
        pullback.fst G.hom (jK R) = UnifPre.gFK (G := G) F := by rw [← Category.assoc, m₃]
    refine ⟨σ', GlobalTheory.BoxExpansion.isoRel_of_val A.isLB U.LG.isLB m₂ (Category.id_comp _) fun y JA JG hA hG => ?_, h₁⟩
    obtain ⟨J, hJ⟩ := exists_good' hL₀ y
    have a := ht _ (U.genF F).left (UnifPre.gFK (G := G) F ≫ g) (by
      rw [Category.assoc, g₁, ← Category.assoc (U.genF F).left, m₁, Category.assoc, pullback.condition,
        ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ jK R) ((Over.w (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G))).trans
        (Over.w (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G))).symm)) (by
      rw [Category.assoc, g₂, ← Category.assoc (U.genF F).left, m₂, ← m₄]
      simp only [Category.assoc]) y J JA hJ hA
    rw [Hb i _ _ y J JG hJ hG, m₂] at a
    generalize hm : (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left = m at a m₃ m₄ ⊢
    have p₁ : (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) (m y) ∈ U.LG.L.U (JG (UnifPre.gFK (G := G) F)) := by
      have := hG (UnifPre.gFK (G := G) F)
      rw [← m₄] at this ⊢
      exact this
    have c := T _ m y _ _ _ (hJ (m ≫ (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) ≫ Φ)) p₁ (hA m)
    rw [Hw₁ _ m y _ _ p₁ (hA m), m₃, m₄] at c
    have d : wVal w y J JA m = wVal ω y J JG (UnifPre.gFK (G := G) F) * _ :=
      c.trans (congrArg (· * _) (by rw [wVal, ← Category.assoc m, m₄]))
    rw [d, Units.val_mul, mul_pow, _root_.mul_assoc, ← Units.val_pow_eq_pow_val, Units.mul_right_inj,
      ← Units.val_pow_eq_pow_val] at a
    exact (h₂ y JG hG).trans a

end GlobalTheory.OneBasis.Bridge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMinOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
attribute [local instance] SplitExt.free SplitExt.finite

namespace GlobalTheory.OneBasis.AdaptedFamily

theorem exists_min_on {X : Type} {Q : X → ℤ} (h : ∀ x, 0 ≤ Q x) {s : Set X} (hs : s.Nonempty) :
    ∃ x ∈ s, ∀ y ∈ s, Q x ≤ Q y := by
  obtain ⟨x, hx, hm⟩ := (wellFounded_lt (α := ℕ)).has_min ((fun x => (Q x).toNat) '' s) (hs.image _)
  obtain ⟨x, hx, rfl⟩ := hx
  refine ⟨x, hx, fun y hy => ?_⟩
  have h₁ : ¬ (Q y).toNat < (Q x).toNat := hm _ ⟨y, hy, rfl⟩
  have h₂ := h x
  have h₃ := h y
  omega

theorem main : LL → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ k : ℕ, 1 ≤ k → ∃ (r : ℕ) (cls : Fin r → D.toPre.X) (mu : ℕ) (f : Fin r → ∀ α, D.toPre.SecB k α), AdFam D Q k cls mu f ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (i : Fin r), ∃ s : Fam D.toPre F k, GlobalTheory.ZH.FamOf D.toPre F (f i) s := by
  classical
  intro hL V _ _ _ ϖ hϖ D Q hQ k hk
  have hQ0 : ∀ χ, 0 ≤ Q χ := fun χ => by
    by_cases h : χ = 0
    · rw [h, QForm.Q_zero hϖ D hQ]
    · have := QForm.Q_pos hϖ D hQ h; omega
  let C := D.toPre.X ⧸ FamFree.multiples D.toPre k
  have hc : Nat.card C = k ^ Module.finrank ℤ D.toPre.X := AddSubgroup.index_range_nsmul D.toPre.X k
  have : Finite C := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  have := Fintype.ofFinite C
  let e : Fin (Fintype.card (C × Fin (k ^ D.toPre.P.g))) ≃ C × Fin (k ^ D.toPre.P.g) := (Fintype.equivFin _).symm
  choose rep hrep hmin using fun c : C => exists_min_on hQ0
    (s := {α | (QuotientAddGroup.mk α : C) = c}) ⟨c.out, c.out_eq⟩
  have hQmin : ∀ c z, Q (rep c) ≤ Q (rep c + k • z) := fun c m =>
    hmin c _ (((FamFree.mk_eq_mk_iff _ _).2 ⟨m, rfl⟩).symm.trans (hrep c))
  choose b hb using fun c => AdaptedBasis.exists_isBasisB hL.2.1.secTwist D.toPre hk (rep c)
  choose Φ f hΦ hf hz using fun c m =>
    AdaptedBasis.integralFamily_of_min hL.1.globalFns hϖ hQ hk (rep c) (b c m) (hQmin c)
  have inj : ∀ c c', rep c = rep c' → c = c' := fun c c' h => (hrep c).symm.trans (by rw [h]; exact hrep c')
  let ε : ∀ i₀, {i // rep (e i).1 = rep (e i₀).1} ≃ Fin (k ^ D.toPre.P.g) := fun i₀ =>
    { toFun := fun i => (e i.1).2
      invFun := fun m => ⟨e.symm ((e i₀).1, m), by rw [Equiv.apply_symm_apply]⟩
      left_inv := fun i => Subtype.ext (e.symm_apply_eq.2 (Prod.ext (inj _ _ i.2).symm rfl))
      right_inv := fun m => by simp }
  refine ⟨_, fun i => rep (e i).1, k ^ D.toPre.P.g, fun i => f (e i).1 (e i).2,
    ⟨⟨fun i => hQmin _, fun i i' ⟨m, hm⟩ => ?_, fun α => ?_, fun i₀ => ?_⟩, fun i => ⟨_, hΦ _ _⟩, fun i => hz _ _,
      fun i₀ => ?_⟩, fun F _ _ i => FamBaseChange.main hL.1.globalFns V _ D k _ _ (hΦ _ _) F⟩
  · exact congrArg rep ((hrep _).symm.trans (((FamFree.mk_eq_mk_iff _ _).2 ⟨m, hm.symm⟩).symm.trans (hrep _)))
  · obtain ⟨m, hm⟩ := (FamFree.mk_eq_mk_iff _ _).1 (hrep (QuotientAddGroup.mk α))
    refine ⟨e.symm (QuotientAddGroup.mk α, ⟨0, by positivity⟩), m, ?_⟩
    simp only [Equiv.apply_symm_apply]
    exact hm.symm
  · exact (Nat.card_congr (ε i₀)).trans (Nat.card_fin _)
  · refine AdaptedBasis.isBasisB_reindex (ε i₀) (hb (e i₀).1) fun i => ?_
    have key : ∀ c c' m, c = c' → f c m (rep c') = b c' m := by
      rintro c _ m rfl; exact hf c m
    exact key _ _ _ (inj _ _ i.2)

end GlobalTheory.OneBasis.AdaptedFamily
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemMaximalIdeal
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.ModelBasis
open GlobalTheory.FieldBaseChange GlobalTheory.IntegralCombination GlobalTheory.ZH GlobalTheory.ZH.AdaptedSpan

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (maximalIdeal V)}
  {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))} [GrpObj G]
  [IsCommMonObj G]

theorem toGen_injective (U : UnifPre (maximalIdeal V) D A G) (k : ℕ) : Function.Injective (toGen U k) := by
  have := U.smooth
  have : Flat G.hom := inferInstance
  have h := GlobalTheory.ExtUnique.spec_fractionRing V (FractionRing V)
  have h₁ : IsSchemeTheoreticallyDominant (jK V) := h.2
  have h₂ : QuasiCompact (jK V) := h.1
  have : IsSchemeTheoreticallyDominant (pullback.fst G.hom (jK V)) := inferInstance
  exact GlobalTheory.ConstFam.pullOver_injective_of_dominant _ _ _ _

theorem chart_sum {Y : Scheme.{0}} {p : Y ⟶ Spec (CommRingCat.of V)} {M : LB Y} {J : Type} [Fintype J]
    (c : J → V) (x : J → SecOver p M) (j : M.ι) :
    LB.Sec.f (∑ i, c i • x i : SecOver p M) j = ∑ i, resTop _ (scal p (c i)) * LB.Sec.f (x i) j :=
  map_sum (chartLin p M j) (fun i => c i • x i) _


open Classical in
theorem mem_maximalIdeal (hW : WeightIndepSt) (U : UnifPre (maximalIdeal V) D A G) {k : ℕ} {J : Type} [Fintype J]
    (σ : J → SecG U k) (cls : J → D.toPre.X) (f : J → ∀ α, SecAb D.toPre k α)
    (hE : ∀ i, U.ExpandsAt 0 k (σ i) (f i)) (hz : ∀ i i₀, cls i ≠ cls i₀ → f i (cls i₀) = 0)
    (hB : ∀ i₀, IsBasisB D.toPre (fun i : {i // cls i = cls i₀} => f i (cls i₀))) (c : J → V)
    (h : ∀ j, ((fstG (maximalIdeal V) 0 G).left.app _).hom (LB.Sec.f (∑ i, c i • σ i : SecG U k) j) = 0) (i₀ : J) :
    c i₀ ∈ maximalIdeal V := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨g, hg⟩ := (GlobalTheory.ExtDiv.main V ϖ hϖ D A G U 0 k (cls i₀) _).1
    (hW V _ D A G U 0 k _ _ h (expandsAt_sum U 0 k σ f hE c) (cls i₀))
  obtain ⟨a, ha, -⟩ := hB i₀ g
  let β : {i // cls i = cls i₀} → SecAb D.toPre k (cls i₀) := fun i => f i (cls i₀)
  have e₁ : (show SecAb D.toPre k (cls i₀) from g) = ∑ i, a i • β i :=
    SecOver.ext _ _ fun j => (ha j).trans (chart_sum a β j).symm
  have e₂ : (∑ i, c i • f i (cls i₀) : SecAb D.toPre k (cls i₀)) =
      ϖ ^ (0 + 1) • (show SecAb D.toPre k (cls i₀) from g) := SecOver.ext _ _ hg
  have e₃ : (∑ i, c i • f i (cls i₀) : SecAb D.toPre k (cls i₀)) = ∑ i : {i // cls i = cls i₀}, c i • β i := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun i => cls i = cls i₀),
      Finset.sum_eq_zero (s := (Finset.univ : Finset {i // ¬ cls i = cls i₀}))
        (fun i _ => by rw [hz i i₀ i.2, smul_zero]), add_zero]
  have e₄ : (∑ i : {i // cls i = cls i₀}, c i • β i) = ∑ i, (ϖ ^ (0 + 1) * a i) • β i := by
    rw [← e₃, e₂, e₁, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_smul _ _ _
  have e₅ := (hB i₀ (∑ i : {i // cls i = cls i₀}, c i • β i : SecAb D.toPre k (cls i₀))).unique
    (y₁ := fun i => c i) (y₂ := fun i => ϖ ^ (0 + 1) * a i) (fun j => chart_sum _ β j)
    (fun j => by rw [e₄]; exact chart_sum _ β j)
  have e₆ : c i₀ = ϖ ^ (0 + 1) * a ⟨i₀, rfl⟩ := congrFun e₅ ⟨i₀, rfl⟩
  rw [e₆, zero_add, pow_one]
  exact Ideal.mul_mem_right _ _ hϖ.not_isUnit

theorem main : LL → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (k : ℕ), 1 ≤ k → ∀ (r : ℕ) (cls : Fin r → D.toPre.X) (mu : ℕ) (f : Fin r → ∀ α, D.toPre.SecB k α), AdFam D Q k cls mu f → ∃ σ : Fin r → H0 U.LG.L k, (∀ i e, U.ExpandsAt e k (σ i) (f i)) ∧ IsBasisH σ := by
  intro hL V _ _ _ D Q A G _ _ U k hk r cls mu f ⟨⟨_, h₂, h₃, _⟩, h₅, h₆, h₇⟩
  have ex : ∀ i, ∃ σ : SecG U.toUnifPre k, ∀ e, U.ExpandsAt e k σ (f i) := fun i => by
    obtain ⟨s, hs⟩ := h₅ i
    exact GlobalTheory.IntegralExpansion.main hL.1 V D A G U k hk s (f i) hs
  choose σ hσ using ex
  refine ⟨σ, hσ, fun s => ?_⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have := U.smooth
  have : Flat G.hom := inferInstance
  obtain ⟨a, ha⟩ := AdaptedSpan.exists_comb hL.1.globalFns U hk σ cls f h₂ h₃ hσ h₅ h₆ h₇ (toGen U.toUnifPre k s)
  obtain ⟨d, b, hd, hb⟩ := exists_denom a
  have e : (d • (show SecG U.toUnifPre k from s)) = ∑ i, b i • σ i := toGen_injective U.toUnifPre k (by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smulₛₗ, map_sum, ha, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smulₛₗ, smul_smul, hb])
  refine GlobalTheory.SaturatedSections.existsUnique_comb
    (A := fun j => Γ(G.left, (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))).U j))
    (fun j => GlobalTheory.SaturatedSections.cst G.hom _) hϖ
    (fun j x hx => GlobalTheory.SaturatedSections.eq_zero_of_cst_mul G.hom _ hϖ.ne_zero x hx) (fun i j => LB.Sec.f (σ i) j)
    (fun c y hy => mem_maximalIdeal hL.2.2.2.1.weightIndep U.toUnifPre σ cls f (fun i => hσ i 0)
      (fun i i₀ h => SecOver.ext _ _ fun j => h₆ i (cls i₀) (fun m hm => h (h₂ i₀ i ⟨m, hm⟩).symm) j) h₇ c
      fun j => ?_) s.f d b hd fun j => ?_
  · refine (GlobalTheory.ThickDiv.app_eq_zero_iff hϖ G 0 _ _).2 ⟨y j, ?_⟩
    rw [zero_add, pow_one]
    exact (chart_sum c σ j).trans (hy j).symm
  · exact (congrArg (fun t : SecG U.toUnifPre k => LB.Sec.f t j) e).trans (chart_sum b σ j)

end GlobalTheory.OneBasis.ModelBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdaptedBasisAtTraitVsGenericBasis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.GBasis

theorem exists_pull {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (h : Y' ⟶ Y) (φ₁ : K → (Y' ⟶ X)) (hφ : ∀ a, φ₁ a = h ≫ φ a) (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ s₁ : LB.Sec (LB.LinComb L φ₁ ε), ∀ (z : Y') J, Good L z J → sval s₁ (𝟙 _) z J = sval s h z J := by
  obtain rfl : φ₁ = fun a => h ≫ φ a := funext hφ
  exact ⟨_, fun z J hJ => (SectionScalarValuation.sval_pullSec φ ε s h (𝟙 _) z hJ).trans (by rw [Category.id_comp])⟩

theorem exists_lin_one {S : Scheme.{0}} (G : Over S) (L : LB G.left) (N : ℕ) {T T' : Over S} (h : T' ⟶ T)
    (b : LB.Sec (LPow G L (N : ℤ) T)) : ∃ s, Lin G L N h (fun _ : Fin 1 => b) (fun _ => 1) s := by
  obtain ⟨s, hs⟩ := exists_pull (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ))
    (h ▷ G).left (fun _ : Fin 1 => (snd T' G).left)
    (fun _ => by rw [← Over.comp_left, whiskerRight_snd]) b
  refine ⟨s, fun z J hJ => (hs z J hJ).trans ?_⟩
  rw [Fin.sum_univ_one, gs_eq _ z ⊤ trivial, map_one, map_one, _root_.one_mul]

theorem fnR_surj {R : Type} [CommRing R] {n : ℕ} (c : Fin n → Γ(Sp R, ⊤)) : ∃ a : Fin n → R, c = fun i => fnR (a i) :=
  ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (c i), funext fun i => by
    simp [fnR]⟩

section Av
variable {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

theorem liftFun_one (W) : liftFun A.A (T := TFK (R := R) F) W ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom 1) = 1 := by
  simp only [liftFun, map_one]

theorem eq_of_cmb_one {b t : SecA A F k} (h : Cmb (fun _ : Fin 1 => b) (fun _ => 1) t) : t = b :=
  SecOps.sec_ext fun j => by rw [h j, Fin.sum_univ_one, liftFun_one, _root_.one_mul]

theorem exists_cmb : ∀ {n : ℕ} (b : Fin n → SecA A F k) (a : Fin n → F), ∃ t, Cmb b a t := by
  intro n
  induction n with
  | zero =>
    intro b a
    exact ⟨SecOps.secZero, fun j => by rw [Fin.sum_univ_zero]; rfl⟩
  | succ n ih =>
    intro b a
    obtain ⟨t, ht⟩ := ih (fun i => b i.succ) (fun i => a i.succ)
    refine ⟨SecOps.secAdd (SecOps.secScale ((fst (TFK (R := R) F) A.A).left.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (a 0))) (b 0)) t, fun j => ?_⟩
    rw [Fin.sum_univ_succ, ← ht j]; rfl

variable {M : Type} [AddCommGroup M] [Module F M] {E : SecA A F k → M → Prop}

theorem cmb_rel (hex : ∀ t, ∃ s, E t s)
    (hl : ∀ (t t' t'' : SecA A F k) (s s' : M) (c : F), E t s → E t' s' →
      (∀ j, t''.f j = liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * t.f j + t'.f j) →
      E t'' (c • s + s')) :
    ∀ {n : ℕ} (b : Fin n → SecA A F k) (s : Fin n → M) (a : Fin n → F) (t : SecA A F k), (∀ i, E (b i) (s i)) →
      Cmb b a t → E t (∑ i, a i • s i) := by
  intro n
  induction n with
  | zero =>
    intro b s a t hb h
    obtain ⟨u, hu⟩ := hex t
    have := hl t t t u u (-1) hu hu (fun j => by rw [h j, Fin.sum_univ_zero, mul_zero, add_zero])
    rw [neg_one_smul, neg_add_cancel] at this
    rwa [Fin.sum_univ_zero]
  | succ n ih =>
    intro b s a t hb h
    obtain ⟨t', ht'⟩ := exists_cmb (fun i => b i.succ) (fun i => a i.succ)
    rw [Fin.sum_univ_succ]
    exact hl (b 0) t' t _ _ (a 0) (hb 0)
      (ih _ (fun i => s i.succ) _ t' (fun i => hb i.succ) ht') fun j => by
      rw [h j, Fin.sum_univ_succ, ht' j]

end Av

theorem card_eq_of_bases {F M : Type} [Field F] [AddCommGroup M] [Module F M] {n m : ℕ} {s : Fin n → M}
    {s' : Fin m → M} (h : ∀ x, ∃! a : Fin n → F, x = ∑ i, a i • s i) (h' : ∀ x, ∃! a : Fin m → F, x = ∑ i, a i • s' i) :
    n = m := by
  have key : ∀ {n : ℕ} {s : Fin n → M}, (∀ x, ∃! a : Fin n → F, x = ∑ i, a i • s i) →
      Nonempty ((Fin n → F) ≃ₗ[F] M) := fun {n s} h =>
    ⟨LinearEquiv.ofBijective (Fintype.linearCombination F s) ⟨fun a b e => (h _).unique
      (Fintype.linearCombination_apply F s a) (e.trans (Fintype.linearCombination_apply F s b)), fun x => by
        obtain ⟨a, ha, -⟩ := h x
        exact ⟨a, (Fintype.linearCombination_apply F s a).trans ha.symm⟩⟩⟩
  obtain ⟨e⟩ := key h
  obtain ⟨e'⟩ := key h'
  simpa using (e.trans e'.symm).finrank_eq

theorem val_nonneg {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}
    (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) (c : V) :
    (0 : WithTop ℚ) ≤ v (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) c)) := by
  by_cases hc : c = 0
  · simp [hc]
  · obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
    have h : HasVal ϖ (algebraMap V (FractionRing V) c) (n : ℤ) :=
      ⟨u, by rw [hu, map_mul, map_pow, zpow_natCast, _root_.mul_comm]⟩
    rw [hv _ _ h]
    exact_mod_cast (Nat.cast_nonneg n : (0 : ℚ) ≤ n)

theorem prim_of {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
    {D : DegData V (maximalIdeal V)} {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q)
    {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} {r mu : ℕ}
    {cls : Fin r → D.toPre.X} {s : Fin r → Fam D.toPre F 1} (hA : Adapted 1 Q cls mu) (hN : Norms D Q v 1 cls s)
    {c d : Fin r → F} (hc : ∀ i, 0 ≤ v (c i)) (hd : ∀ i, 0 ≤ v (d i)) (hs : ∀ i, s i = d i • ∑ j, c j • s j) :
    Prim D Q v (∑ j, c j • s j) := by
  classical
  have h0 : ∀ i, Q (cls i) = 0 := fun i => by
    have a := hA.1 i (-cls i)
    rw [one_smul, add_neg_cancel, QForm.Q_zero hϖ D hQ] at a
    by_cases e : cls i = 0
    · rw [e, QForm.Q_zero hϖ D hQ]
    · have := QForm.Q_pos hϖ D hQ e
      omega
  have hn : ∀ q : ℚ, NuGe D Q F v 1 (∑ j, c j • s j) q ↔ ∀ i, (q : WithTop ℚ) ≤ v (c i) := fun q => by
    rw [(hN.2 c q).1]
    simp only [h0, Int.cast_zero, zero_div, add_zero]
  refine ⟨(hn 0).2 hc, fun q hq H => ?_⟩
  obtain ⟨i, -⟩ := hA.2.2.1 0
  have e : (Pi.single i 1 : Fin r → F) = fun j => d i * c j := (hN.1 (s i)).unique
    (by simp [Pi.single_apply]) (by rw [hs i, Finset.smul_sum]; simp only [mul_smul])
  have e₁ : (1 : F) = d i * c i := by simpa using congrFun e i
  have e₂ : v (d i) + v (c i) = 0 := by rw [← v.map_mul, ← e₁, v.map_one]
  have e₃ : (q : WithTop ℚ) ≤ 0 := by
    calc (q : WithTop ℚ) = 0 + q := (zero_add _).symm
      _ ≤ v (d i) + v (c i) := add_le_add (hd i) ((hn q).1 H i)
      _ = 0 := e₂
  have : q ≤ 0 := by exact_mod_cast e₃
  linarith

theorem main : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] (L₀ : LB G₀.left), L₀.IsLB → ∀ (ρ₀ : LB.Gen (L₀.pull (eSec G₀))), ∀ (χ : Sp V ⟶ Z) (Φ : G.left ⟶ G₀.left) (ω : LB.Iso U.LG.L (L₀.pull Φ)), RigPull G G₀ χ Φ ω U.LG.rig ρ₀ → ∀ (K : Type) [Field K] (x : Sp K ⟶ Z) (gam : K →+* FractionRing V) (h : spMap gam ≫ x = jK V ≫ χ) (θ : LB.Sec (LPow G₀ L₀ ((1 : ℕ) : ℤ) (Over.mk x))), FrameAt G₀ L₀ 1 x gam χ h (fun _ : Fin 1 => θ) → ∀ (k r : ℕ) (τ : Fin r → LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk x))), 1 ≤ k → AllBasis G₀ L₀ k x τ → ∃ (φ : A.A.left ⟶ G₀.left) (w : LB.Iso A.L (L₀.pull φ)) (ρ : LB.Gen (A.L.pull (eSec A.A))) (w₀ : W0 U.toUnifPre) (th : SecA A F 1) (ϑ : Fam D.toPre F 1) (cls : Fin r → D.toPre.X) (mu : ℕ) (b τF : Fin r → SecA A F k) (s : Fin r → Fam D.toPre F k) (B : Matrix (Fin r) (Fin r) (FractionRing V)), RigPull A.A G₀ (jK V ≫ χ) φ w ρ ρ₀ ∧ NormW U.toUnifPre w₀ ρ ∧ U.ExpandsF F 1 w₀ th ϑ ∧ Prim D Q v ϑ ∧ Thru w 1 (T' := TFK (R := V) F) (T := Over.mk x) (jFK (R := V) F ≫ spMap gam) θ th ∧ (∀ i, Thru w k (T' := TFK (R := V) F) (T := Over.mk x) (jFK (R := V) F ≫ spMap gam) (τ i) (τF i)) ∧ Adapted k Q cls mu ∧ Norms D Q v k cls s ∧ (∀ i, U.ExpandsF F k w₀ (b i) (s i)) ∧ (∀ t, ∃! a, Cmb τF a t) ∧ (∀ i, Cmb τF (B.map (algebraMap (FractionRing V) F) i) (b i)) ∧ BasisBy G₀ L₀ k x gam χ h τ B := by
  intro hLL h1 h2 h3 h4 V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U Z G₀ _ L₀ hL₀ ρ₀ χ Φ ω hRP K _ x gam h θ
    hFr k r τ hk hτ
  have hB : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  obtain ⟨hbij, hlin⟩ := expBijF_and_expandsF_lin hLL V _ hB D A G hG U
  obtain ⟨φ, w, ρ, w₀, hR, hW, hbr⟩ := GlobalTheory.OneBasis.Bridge.exists_bridge Z G₀ L₀ hL₀ ρ₀ V _ D A G U.toUnifPre χ Φ ω hRP
  have cal := GlobalTheory.OneBasis.Calc.main Z G₀ L₀ hL₀ V (jK V ≫ χ) A φ w hR.1 hR.2.1 F
  have lev : ∀ k : ℕ, 1 ≤ k → ∃ (r : ℕ) (cls : Fin r → D.toPre.X) (mu : ℕ)
      (b : Fin r → LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk χ))) (bF : Fin r → SecA A F k) (s : Fin r → Fam D.toPre F k),
      BasisAlong G₀ L₀ k (𝟙 _) b ∧
      (∀ i, Thru w k (T' := TFK (R := V) F) (T := Over.mk χ) (jFK (R := V) F ≫ jK V) (b i) (bF i)) ∧
      Adapted k Q cls mu ∧ Norms D Q v k cls s ∧ ∀ i, U.ExpandsF F k w₀ (bF i) (s i) := fun k hk => by
    obtain ⟨r, cls, mu, f, hf, hs⟩ := GlobalTheory.OneBasis.AdaptedFamily.main hLL V ϖ hϖ D Q hQ k hk
    choose s hs using hs F
    obtain ⟨σ, hσ, hσb⟩ := GlobalTheory.OneBasis.ModelBasis.main hLL V D Q A G U k hk r cls mu f hf
    obtain ⟨b, hb, hb'⟩ := hbr k r σ hσb
    choose bF hbF using fun i => ((cal k).1 (Over.mk χ) (jFK (R := V) F ≫ jK V) (Category.assoc _ _ _) (b i)).exists
    exact ⟨r, cls, mu, b, bF, s, hb, hbF, hf.1,
      GlobalTheory.OneBasis.NormsPf.norms_of_adapted hLL h1 h2 h3 h4 V hc ϖ hϖ D Q hQ F v hv k hk r cls mu f s hf hs,
      fun i => hb' i F (f i) (s i) (bF i) (hσ i) (hs i) (hbF i)⟩
  have down : ∀ (k : ℕ) (s : LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk (jK V ≫ χ)))), ∃ t : SecA A F k,
      Thru w k (T' := TFK (R := V) F) (T := Over.mk (jK V ≫ χ)) (spMap (algebraMap (FractionRing V) F)) s t :=
    fun k s => ((cal k).1 (Over.mk (jK V ≫ χ)) (jFK (R := V) F) rfl s).exists
  have one : ∀ (k : ℕ) (T : Over Z) (g : Over.mk (jK V ≫ χ) ⟶ T) b s (bF t : SecA A F k),
      Lin G₀ L₀ k g (fun _ : Fin 1 => b) (fun _ => 1) s →
      Thru w k (T' := TFK (R := V) F) (spMap (algebraMap (FractionRing V) F) ≫ g.left) b bF →
      Thru w k (T' := TFK (R := V) F) (T := Over.mk (jK V ≫ χ)) (spMap (algebraMap (FractionRing V) F)) s t →
      t = bF := fun k T g b s bF t a₁ a₂ a₃ => by
    have := (cal k).2.1 (FractionRing V) (jK V ≫ χ) T g (algebraMap (FractionRing V) F) rfl 1 (fun _ => b)
      (fun _ => 1) s (fun _ => bF) t (by simpa only [fnR, map_one] using a₁) (fun _ => a₂) a₃
    simp only [map_one] at this
    exact eq_of_cmb_one this
  have rel : ∀ (k : ℕ), 1 ≤ k → ∀ {n : ℕ} (b : Fin n → SecA A F k) (s : Fin n → Fam D.toPre F k) (a : Fin n → F)
      (t : SecA A F k), (∀ i, U.ExpandsF F k w₀ (b i) (s i)) → Cmb b a t → U.ExpandsF F k w₀ t (∑ i, a i • s i) :=
    fun k hk => cmb_rel (fun t => ((hbij F k hk w₀ hW.1).1 t).exists) (hlin F k w₀)
  have hx : (jFK (R := V) F ≫ spMap gam) ≫ x = jFK (R := V) F ≫ jK V ≫ χ := by rw [Category.assoc, h]

  obtain ⟨th, hth⟩ := ((cal 1).1 (Over.mk x) (jFK (R := V) F ≫ spMap gam) hx θ).exists
  obtain ⟨ϑ, hϑ, hP⟩ : ∃ ϑ, U.ExpandsF F 1 w₀ th ϑ ∧ Prim D Q v ϑ := by
    obtain ⟨r₁, cls₁, mu₁, b₁, bF₁, s₁, hb₁, ht₁, hA₁, hN₁, hE₁⟩ := lev 1 le_rfl
    obtain ⟨b', hb', H⟩ := hFr
    obtain ⟨s₀, l₁, l₂⟩ := H 0
    obtain ⟨t₀, ht₀⟩ := down 1 s₀
    obtain ⟨bF', hbF'⟩ :=
      ((cal 1).1 (Over.mk χ) (jFK (R := V) F ≫ jK V) (Category.assoc _ _ _) (b' 0)).exists
    have e₁ := one 1 _ _ _ _ th t₀ l₁ hth ht₀
    have e₂ := one 1 _ _ _ _ bF' t₀ l₂ hbF' ht₀
    obtain rfl : bF' = th := e₂.symm.trans e₁
    let ga : V →+* F := (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))
    have hga : spMap ga = jFK (R := V) F ≫ jK V := Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)
    have cm : ∀ (n : ℕ) (b : Fin n → LB.Sec (LPow G₀ L₀ ((1 : ℕ) : ℤ) (Over.mk χ))) (bF : Fin n → SecA A F 1) s t,
        BasisAlong G₀ L₀ 1 (𝟙 _) b →
        (∀ i, Thru w 1 (T' := TFK (R := V) F) (T := Over.mk χ) (jFK (R := V) F ≫ jK V) (b i) (bF i)) →
        Thru w 1 (T' := TFK (R := V) F) (T := Over.mk χ) (jFK (R := V) F ≫ jK V) s t →
        ∃ c : Fin n → F, (∀ i, 0 ≤ v (c i)) ∧ Cmb bF c t := fun n b bF s t a₁ a₂ a₃ => by
      obtain ⟨c, hc⟩ := (a₁ s).exists
      obtain ⟨c, rfl⟩ := fnR_surj c
      rw [← hga] at a₂ a₃
      refine ⟨fun i => ga (c i), fun i => val_nonneg hϖ hv (c i), (cal 1).2.1 V χ (Over.mk χ) (𝟙 _) ga
        (by rw [hga, Category.assoc]) n b c s bF t hc (fun i => ?_) a₃⟩
      have e : spMap ga ≫ (𝟙 (Over.mk χ) : _ ⟶ _).left = spMap ga := Category.comp_id _
      rw [e]
      exact a₂ i
    obtain ⟨c, hc₀, hc₁⟩ := cm _ b₁ bF₁ _ _ hb₁ ht₁ hbF'
    have hE := rel 1 le_rfl bF₁ s₁ c _ hE₁ hc₁
    choose d hd₀ hd₁ using fun i => cm 1 b' (fun _ => bF') _ _ hb'
      (fun j => by rw [Subsingleton.elim j 0]; exact hbF') (ht₁ i)
    refine ⟨_, hE, prim_of hϖ hQ hA₁ hN₁ (d := fun i => d i 0) hc₀ (fun i => hd₀ i 0) fun i => ?_⟩
    have := rel 1 le_rfl (fun _ : Fin 1 => bF') (fun _ => _) (d i) _ (fun _ => hE) (hd₁ i)
    rw [Fin.sum_univ_one] at this
    exact ((hbij F 1 le_rfl w₀ hW.1).1 _).unique (hE₁ i) this

  obtain ⟨r', cls, mu, b, bF, s, hb, ht, hA, hN, hE⟩ := lev k hk
  choose τF hτF using fun i => ((cal k).1 (Over.mk x) (jFK (R := V) F ≫ spMap gam) hx (τ i)).exists
  have hg : spMap ((algebraMap (FractionRing V) F).comp gam) = jFK (R := V) F ≫ spMap gam :=
    Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)
  have hbas : ∀ t : SecA A F k, ∃! a, Cmb τF a t :=
    (cal k).2.2 K x ((algebraMap (FractionRing V) F).comp gam) (by rw [hg, hx]) r τ τF hτ (by rw [hg]; exact hτF)
  obtain rfl : r' = r := by
    choose s' hs' using fun i => ((hbij F k hk w₀ hW.1).1 (τF i)).exists
    refine card_eq_of_bases hN.1 (s' := s') fun y => ?_
    obtain ⟨t, ht, hu⟩ := (hbij F k hk w₀ hW.1).2 y
    obtain ⟨a, ha, hau⟩ := hbas t
    refine ⟨a, ((hbij F k hk w₀ hW.1).1 t).unique ht (rel k hk τF s' a t hs' ha), fun a' ha' => hau a' ?_⟩
    obtain ⟨t', ht'⟩ := exists_cmb τF a'
    have := rel k hk τF s' a' t' hs' ht'
    rw [← ha'] at this
    rw [← hu t' this]
    exact ht'
  choose g hg using fun i => exists_lin_one G₀ L₀ k
    (Over.homMk (jK V) rfl : Over.mk (jK V ≫ χ) ⟶ Over.mk χ) (b i)
  have hBi : ∀ i, ∃ c : Fin r' → FractionRing V,
      Lin G₀ L₀ k (Over.homMk (spMap gam) h : Over.mk (jK V ≫ χ) ⟶ Over.mk x) τ (fun j => fnR (c j)) (g i) := fun i => by
    obtain ⟨c, hc⟩ := (hτ (FractionRing V) gam (jK V ≫ χ) h (g i)).exists
    obtain ⟨c, rfl⟩ := fnR_surj c
    exact ⟨c, hc⟩
  choose B hBB using hBi
  refine ⟨φ, w, ρ, w₀, th, ϑ, cls, mu, bF, τF, s, Matrix.of B, hR, hW, hϑ, hP, hth, hτF, hA, hN, hE, hbas, fun i => ?_,
    b, hb, fun i => ⟨g i, hBB i, hg i⟩⟩
  obtain ⟨t, ht'⟩ := down k (g i)
  rw [← one k _ _ _ _ (bF i) t (hg i) (ht i) ht']
  exact (cal k).2.1 (FractionRing V) (jK V ≫ χ) (Over.mk x) _ (algebraMap (FractionRing V) F) rfl r' τ (B i) (g i) τF t
    (hBB i) hτF ht'

end GlobalTheory.GBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdaptedBasisAtTraitVsGenericBasisStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adaptedBasis_at_trait_vs_generic_basis : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] (L₀ : LB G₀.left), L₀.IsLB → ∀ (ρ₀ : LB.Gen (L₀.pull (eSec G₀))), ∀ (χ : Sp V ⟶ Z) (Φ : G.left ⟶ G₀.left) (ω : LB.Iso U.LG.L (L₀.pull Φ)), RigPull G G₀ χ Φ ω U.LG.rig ρ₀ → ∀ (K : Type) [Field K] (x : Sp K ⟶ Z) (gam : K →+* FractionRing V) (h : spMap gam ≫ x = jK V ≫ χ) (θ : LB.Sec (LPow G₀ L₀ ((1 : ℕ) : ℤ) (Over.mk x))), FrameAt G₀ L₀ 1 x gam χ h (fun _ : Fin 1 => θ) → ∀ (k r : ℕ) (τ : Fin r → LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk x))), 1 ≤ k → AllBasis G₀ L₀ k x τ → ∃ (φ : A.A.left ⟶ G₀.left) (w : LB.Iso A.L (L₀.pull φ)) (ρ : LB.Gen (A.L.pull (eSec A.A))) (w₀ : W0 U.toUnifPre) (th : SecA A F 1) (ϑ : Fam D.toPre F 1) (cls : Fin r → D.toPre.X) (mu : ℕ) (b τF : Fin r → SecA A F k) (s : Fin r → Fam D.toPre F k) (B : Matrix (Fin r) (Fin r) (FractionRing V)), RigPull A.A G₀ (jK V ≫ χ) φ w ρ ρ₀ ∧ NormW U.toUnifPre w₀ ρ ∧ U.ExpandsF F 1 w₀ th ϑ ∧ Prim D Q v ϑ ∧ Thru w 1 (T' := TFK (R := V) F) (T := Over.mk x) (jFK (R := V) F ≫ spMap gam) θ th ∧ (∀ i, Thru w k (T' := TFK (R := V) F) (T := Over.mk x) (jFK (R := V) F ≫ spMap gam) (τ i) (τF i)) ∧ Adapted k Q cls mu ∧ Norms D Q v k cls s ∧ (∀ i, U.ExpandsF F k w₀ (b i) (s i)) ∧ (∀ t, ∃! a, Cmb τF a t) ∧ (∀ i, Cmb τF (B.map (algebraMap (FractionRing V) F) i) (b i)) ∧ BasisBy G₀ L₀ k x gam χ h τ B := by
  first | exact @GlobalTheory.GBasis.main | exact GlobalTheory.GBasis.main | (intros; apply GlobalTheory.GBasis.main <;> assumption)
end
