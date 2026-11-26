module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpCoordinatesTangentFieldHolomorphicPeriodMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingHeckeTranslateEqZeta

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechPicardGlueFiniteDisjointCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechPicardGlueFiniteDisjointCover
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic

namespace GlobalTheory.CechPic.Glue

def extUnit {X W : Scheme.{0}} (g : W ⟶ X) [IsOpenImmersion g] (V : W.Opens) : Γ(W, V)ˣ →* Γ(X, g ''ᵁ V)ˣ :=
  Units.map (g.appIso V).inv.hom.toMonoidHom

theorem gm_extUnit {X W T : Scheme.{0}} (g : W ⟶ X) [IsOpenImmersion g] (V : W.Opens) (a : Γ(W, V)ˣ)
    (r : T ⟶ W) (t : T) (ht : r t ∈ V) : gm (r ≫ g) t (g ''ᵁ V) (extUnit g V a) = gm r t V a := by
  have hm : r t ∈ g ⁻¹ᵁ (g ''ᵁ V) := ⟨r t, ht, rfl⟩
  have e : pullU g (g ''ᵁ V) (extUnit g V a) = res (g.preimage_image_eq V).le a :=
    Units.ext (congrArg (fun q => q.hom a.val) (g.appIso_inv_app V))
  rw [← gm_pull r g t _ hm, e, gm_res r t _ hm]

theorem image_inf_le {X W : Scheme.{0}} (g : W ⟶ X) [IsOpenImmersion g] (A B : W.Opens) :
    g ''ᵁ A ⊓ g ''ᵁ B ≤ g ''ᵁ (A ⊓ B) := by
  rintro _ ⟨⟨a, ha, rfl⟩, hb⟩
  exact ⟨a, ⟨ha, (g.apply_mem_image_iff).1 hb⟩, rfl⟩

variable {Y : Scheme.{0}} {κ : Type} {Z : κ → Scheme.{0}} (f : ∀ i, Z i ⟶ Y) [∀ i, IsOpenImmersion (f i)]
  (L : ∀ i, LB (Z i))

def gT (i : κ) (k k' : (L i).ι) : Γ(Y, (f i) ''ᵁ (L i).U k ⊓ (f i) ''ᵁ (L i).U k')ˣ :=
  res (image_inf_le (f i) _ _) (extUnit (f i) _ ((L i).g k k'))


open Classical in
def gS : ∀ p q : (Σ i, (L i).ι),
    Γ(Y, (f p.1) ''ᵁ (L p.1).U p.2 ⊓ (f q.1) ''ᵁ (L q.1).U q.2)ˣ
  | ⟨i, k⟩, ⟨i', k'⟩ => if h : i = i' then by subst h; exact gT f L i k k' else 1

def glueLB : LB Y where
  ι := Σ i, (L i).ι
  U p := (f p.1) ''ᵁ (L p.1).U p.2
  g := gS f L

theorem glueLB_g (i : κ) (k k' : (L i).ι) : (glueLB f L).g ⟨i, k⟩ ⟨i, k'⟩ = gT f L i k k' := by
  show gS f L ⟨i, k⟩ ⟨i, k'⟩ = _
  simp [gS]

theorem gm_glueLB {T : Scheme.{0}} (i : κ) (r : T ⟶ Z i) (t : T) (k k' : (L i).ι) (hk : r t ∈ (L i).U k)
    (hk' : r t ∈ (L i).U k') :
    gm (r ≫ f i) t ((glueLB f L).U ⟨i, k⟩ ⊓ (glueLB f L).U ⟨i, k'⟩) ((glueLB f L).g ⟨i, k⟩ ⟨i, k'⟩) =
      gm r t ((L i).U k ⊓ (L i).U k') ((L i).g k k') := by
  rw [glueLB_g]
  have hm : (r ≫ f i) t ∈ (f i) ''ᵁ (L i).U k ⊓ (f i) ''ᵁ (L i).U k' :=
    ⟨(f i).apply_mem_image_iff.2 hk, (f i).apply_mem_image_iff.2 hk'⟩
  exact (gm_res _ t _ hm _).trans (gm_extUnit (f i) _ _ r t ⟨hk, hk'⟩)

theorem mem_image {X W : Scheme.{0}} (g : W ⟶ X) [IsOpenImmersion g] {A : W.Opens} {y : X} (h : y ∈ g ''ᵁ A) :
    ∃ z ∈ A, g z = y := h

theorem same_of_mem {i i' : κ} (hd : Pairwise fun i i' => Disjoint (f i).opensRange (f i').opensRange) {y : Y}
    (h : y ∈ (f i).opensRange) (h' : y ∈ (f i').opensRange) : i = i' := by
  by_contra hne
  exact (hd hne).le_bot ⟨h, h'⟩

variable {L} in
theorem isLB_glueLB (hL : ∀ i, (L i).IsLB) (hcov : ⨆ i, (f i).opensRange = ⊤)
    (hd : Pairwise fun i i' => Disjoint (f i).opensRange (f i').opensRange) : (glueLB f L).IsLB := {
  cover := by
    refine top_le_iff.1 fun y _ => ?_
    have hy : y ∈ ⨆ i, (f i).opensRange := by rw [hcov]; trivial
    obtain ⟨i, z, rfl⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    obtain ⟨k, hk⟩ := exists_chart (hL i) z
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, k⟩, (f i).apply_mem_image_iff.2 hk⟩
  g_self := by
    rintro ⟨i, k⟩
    refine unit_ext fun y hy => ?_
    obtain ⟨z, hz, rfl⟩ := mem_image (f i) hy
    refine gm_inj (f i) z hy hy ?_
    have e := gm_glueLB f L i (𝟙 _) z k k hz hz
    rw [Category.id_comp] at e
    rw [map_one, gm_res _ z _ hy, e, gm_self (hL i) _ z hz]
  cocycle := by
    rintro ⟨i, k⟩ ⟨i', k'⟩ ⟨i'', k''⟩
    refine unit_ext fun y hy => ?_
    have h1 : y ∈ (f i).opensRange := (f i).image_le_opensRange _ hy.1.1
    have h2 : y ∈ (f i').opensRange := (f i').image_le_opensRange _ hy.1.2
    have h3 : y ∈ (f i'').opensRange := (f i'').image_le_opensRange _ hy.2
    obtain rfl := same_of_mem f hd h1 h2
    obtain rfl := same_of_mem f hd h1 h3
    obtain ⟨z, hz, rfl⟩ := mem_image (f i) hy.1.1
    have hz' : z ∈ (L i).U k' := (f i).apply_mem_image_iff.1 hy.1.2
    have hz'' : z ∈ (L i).U k'' := (f i).apply_mem_image_iff.1 hy.2
    refine gm_inj (f i) z hy hy ?_
    have e1 := gm_glueLB f L i (𝟙 _) z k k' hz hz'
    have e2 := gm_glueLB f L i (𝟙 _) z k' k'' hz' hz''
    have e3 := gm_glueLB f L i (𝟙 _) z k k'' hz hz''
    rw [Category.id_comp] at e1 e2 e3
    rw [map_mul, gm_res _ z _ hy, gm_res _ z _ hy, gm_res _ z _ hy, e1, e2, e3,
      gm_cocycle (hL i) _ z hz hz' hz''] }

theorem exists_pic_glue : ∀ {Y : Scheme.{0}} {κ : Type} [Finite κ] {Z : κ → Scheme.{0}} (f : ∀ i, Z i ⟶ Y)
    [∀ i, IsOpenImmersion (f i)], (⨆ i, (f i).opensRange = ⊤) →
    (Pairwise fun i i' => Disjoint (f i).opensRange (f i').opensRange) →
    ∀ c : ∀ i, Pic (Z i), ∃ d : Pic Y, ∀ i, GlobalTheory.CechPic.pull (f i) d = c i := by
  intro Y κ _ Z f _ hcov hd c
  choose L hL hc using fun i => cls_surj (c i)
  have hG := isLB_glueLB f hL hcov hd
  refine ⟨cls (glueLB f L) hG, fun i => ?_⟩
  rw [← cls_pull hG (f i) (pull_isLB hG (f i)), ← hc i]
  refine Eq.symm ((cls_eq_iff (hL i) (pull_isLB hG (f i))).2 (iso_of_chart (pull_isLB hG (f i)) ?_))
  exact
    { idx := fun k _ => ⟨i, k⟩
      le := fun k z hz => mem_pull.2 ((f i).apply_mem_image_iff.2 hz)
      g := fun z k k' hk hk' => Eq.symm ((gm_pull_g (glueLB f L) (f i) (𝟙 _) z (fun _ => ⟨i, k⟩) (fun _ => ⟨i, k'⟩)
        (mem_pull.2 ((f i).apply_mem_image_iff.2 hk)) (mem_pull.2 ((f i).apply_mem_image_iff.2 hk'))).trans
        (gm_glueLB f L i (𝟙 _) z k k' hk hk')) }

end GlobalTheory.CechPic.Glue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechPicardGlueFiniteDisjointCoverStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cechPicard_glue_finite_disjoint_cover : ∀ {Y : Scheme.{0}} {κ : Type} [Finite κ] {Z : κ → Scheme.{0}} (f : ∀ i, Z i ⟶ Y) [∀ i, IsOpenImmersion (f i)], (⨆ i, (f i).opensRange = ⊤) → (Pairwise fun i i' => Disjoint (f i).opensRange (f i').opensRange) → ∀ c : ∀ i, Pic (Z i), ∃ d : Pic Y, ∀ i, GlobalTheory.CechPic.pull (f i) d = c i := by
  first | exact @GlobalTheory.CechPic.Glue.exists_pic_glue | exact GlobalTheory.CechPic.Glue.exists_pic_glue | (intros; apply GlobalTheory.CechPic.Glue.exists_pic_glue <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeSpanSupPow
noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Poinc

namespace GlobalTheory.Izumi

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)

theorem norm_val_add_le {U : Set M.Z} {x : M.Z} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} (hy : M.Cen U x y)
    (F G : M.O x) :
    ‖M.val (gPt p ≫ y) ((F + G : M.O x) : Ω)‖ ≤ max ‖M.val (gPt p ≫ y) (F : Ω)‖ ‖M.val (gPt p ≫ y) (G : Ω)‖ := by
  rw [Subalgebra.coe_add, RatModel.val_add (RatModel.gPt_specializes hy.1) F.2 G.2]
  exact IsUltrametricDist.norm_add_le_max _ _

theorem norm_val_mul_le {U : Set M.Z} {x : M.Z} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} (hy : M.Cen U x y)
    (c F : M.O x) : ‖M.val (gPt p ≫ y) ((c * F : M.O x) : Ω)‖ ≤ ‖M.val (gPt p ≫ y) (F : Ω)‖ := by
  rw [Subalgebra.coe_mul, RatModel.val_mul (RatModel.gPt_specializes hy.1) c.2 F.2, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hy.norm_val_le_one c.2)

def smallIdeal (U : M.Z.Opens) (x : M.Z) (f : Ω) (N : ℕ) : Ideal (M.O x) where
  carrier := {F | ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U x y →
      ‖M.val (gPt p ≫ y) F‖ ≤ ‖M.val (gPt p ≫ y) f‖ ∨
        ∃ h, NonUnitAt M x h ∧ ‖M.val (gPt p ≫ y) F‖ ≤ ‖M.val (gPt p ≫ y) h‖ ^ N}
  zero_mem' := by
    intro p _ y _
    left
    have h0 : ((0 : M.O x) : Ω) = 0 := rfl
    rw [h0, RatModel.val_zero, norm_zero]
    exact norm_nonneg _
  add_mem' := by
    intro F G hF hG p _ y hy
    have h := norm_val_add_le M hy F G
    rcases le_total ‖M.val (gPt p ≫ y) (F : Ω)‖ ‖M.val (gPt p ≫ y) (G : Ω)‖ with hle | hle
    · rw [max_eq_right hle] at h
      rcases hG p y hy with h' | ⟨k, hk, h'⟩
      · exact Or.inl (h.trans h')
      · exact Or.inr ⟨k, hk, h.trans h'⟩
    · rw [max_eq_left hle] at h
      rcases hF p y hy with h' | ⟨k, hk, h'⟩
      · exact Or.inl (h.trans h')
      · exact Or.inr ⟨k, hk, h.trans h'⟩
  smul_mem' := by
    intro c F hF p _ y hy
    have h := norm_val_mul_le M hy c F
    rcases hF p y hy with h' | ⟨k, hk, h'⟩
    · exact Or.inl (h.trans h')
    · exact Or.inr ⟨k, hk, h.trans h'⟩

variable {M}

theorem mem_smallIdeal {U : M.Z.Opens} {x : M.Z} {f : Ω} {N : ℕ} {F : M.O x} :
    F ∈ smallIdeal M U x f N ↔ ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U x y →
      ‖M.val (gPt p ≫ y) F‖ ≤ ‖M.val (gPt p ≫ y) f‖ ∨
        ∃ h, NonUnitAt M x h ∧ ‖M.val (gPt p ≫ y) F‖ ≤ ‖M.val (gPt p ≫ y) h‖ ^ N := Iff.rfl

theorem smallIdeal_antitone (U : M.Z.Opens) (x : M.Z) (f : Ω) : Antitone (smallIdeal M U x f) := by
  intro N N' hN F hF p _ y hy
  rcases hF p y hy with h' | ⟨k, hk, h'⟩
  · exact Or.inl h'
  · refine Or.inr ⟨k, hk, h'.trans (pow_le_pow_of_le_one (norm_nonneg _) (hy.norm_val_le_one hk.1) hN)⟩

theorem self_mem_smallIdeal (U : M.Z.Opens) {x : M.Z} {f : Ω} (hf : f ∈ M.O x) (N : ℕ) :
    (⟨f, hf⟩ : M.O x) ∈ smallIdeal M U x f N :=
  fun _ _ _ _ => Or.inl le_rfl

end GlobalTheory.Izumi

namespace GlobalTheory.Izumi

open IsLocalRing

theorem exists_le_span_sup_pow (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (K : ℕ → Ideal A)
    (f : A) (hK : Antitone K) (hf : ∀ N, f ∈ K N)
    (h : ⨅ N, (K N).map (algebraMap A (AdicCompletion (maximalIdeal A) A)) ≤
      Ideal.span {algebraMap A (AdicCompletion (maximalIdeal A) A) f}) (e : ℕ) :
    ∃ N, K N ≤ Ideal.span {f} ⊔ maximalIdeal A ^ e := by
  set B := AdicCompletion (maximalIdeal A) A
  set φ := algebraMap A B
  have : IsNoetherianRing B := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion A _
  set I : Ideal B := Ideal.span {φ f}
  let L : ℕ → Submodule B (B ⧸ I) := fun N => Submodule.map I.mkQ ((K N).map φ)
  have hL : Directed (· ≥ ·) L := by
    refine Antitone.directed_ge fun N N' hN => ?_
    exact Submodule.map_mono (Ideal.map_mono (hK hN))
  have hIK : ∀ N, I ≤ (K N).map φ := fun N =>
    (Ideal.span_le).2 (Set.singleton_subset_iff.2 (Ideal.mem_map_of_mem φ (hf N)))
  have h0 : (⨅ N, L N) = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨b, rfl⟩ := I.mkQ_surjective x
    have hb : b ∈ ⨅ N, (K N).map φ := by
      refine Submodule.mem_iInf _ |>.2 fun N => ?_
      obtain ⟨b', hb', hbb'⟩ := (Submodule.mem_iInf _).1 hx N
      have hd : b' - b ∈ I := by
        rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
        simp only [Submodule.mkQ_apply] at hbb'
        rw [hbb', sub_self]
      have := Submodule.sub_mem _ hb' (hIK N hd)
      simpa using this
    have := h hb
    simp only [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact this
  obtain ⟨N, hN⟩ := GlobalTheory.Chevalley.exists_le_maximalIdeal_pow_smul_of_directed B (B ⧸ I) ℕ L
    inferInstance hL h0 e
  refine ⟨N, fun a ha => ?_⟩
  have h1 : I.mkQ (φ a) ∈ maximalIdeal B ^ e • (⊤ : Submodule B (B ⧸ I)) :=
    hN (Submodule.mem_map_of_mem (Ideal.mem_map_of_mem φ ha))
  have h2 : maximalIdeal B ^ e • (⊤ : Submodule B (B ⧸ I)) = Submodule.map I.mkQ (maximalIdeal B ^ e) := by
    have h4 : maximalIdeal B ^ e • (⊤ : Submodule B B) = maximalIdeal B ^ e := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top]
    rw [← Submodule.range_mkQ I, ← Submodule.map_top, ← Submodule.map_smul'', h4]
  rw [h2, ← Submodule.mem_comap, Submodule.comap_map_mkQ] at h1
  obtain ⟨u, hu, t, ht, hut⟩ := Submodule.mem_sup.1 h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hu
  set ψ := AdicCompletion.evalₐ (maximalIdeal A) (R := A) e
  have hψ : ∀ r : A, ψ (φ r) = Ideal.Quotient.mk _ r := fun r => ψ.commutes r
  have ht0 : ψ t = 0 := by
    have hle : maximalIdeal B ^ e ≤ RingHom.ker ψ.toRingHom := by
      rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, Ideal.map_le_iff_le_comap]
      intro r hr
      simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
      rw [hψ, Ideal.Quotient.eq_zero_iff_mem]
      exact hr
    exact hle ht
  obtain ⟨c', hc'⟩ := Ideal.Quotient.mk_surjective (ψ c)
  have h3 := congrArg ψ hut
  rw [map_add (f := _), map_mul, ht0, add_zero, hψ, hψ, ← hc', ← map_mul, Ideal.Quotient.eq] at h3
  have : a = c' * f + (a - c' * f) := by ring
  rw [this]
  exact Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f)) (by rw [← neg_sub]; exact neg_mem h3)

end GlobalTheory.Izumi
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartFiniteEtaleCoverGenericPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartFiniteEtaleCoverGenericPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

noncomputable section
namespace GlobalTheory.Poinc.Chart

theorem stalkMap_finite_of_chart (K A : Type) [Field K] [CommRing A] {X Y : Scheme.{0}} (q : Y ⟶ X) (j : Sp A ⟶ Y)
    (φ : A →+* K) [IsFinite q] [IsOpenImmersion j] (hφ : ∀ z : K, ∃ a c : A, z = φ a / φ c) (g : Sp K ⟶ X)
    (hg : g = spMap φ ≫ j ≫ q) : (g.stalkMap (genericPoint (Sp K))).hom.Finite := by
  rw [← Category.assoc] at hg
  subst hg
  have hpt : genericPoint (Sp K) = closedPoint (CommRingCat.of K) := Subsingleton.elim _ _
  rw [hpt]
  have h1 : ((spMap φ ≫ j) ≫ q).stalkMap (closedPoint (CommRingCat.of K)) =
      Scheme.stalkClosedPointTo ((spMap φ ≫ j) ≫ q) ≫ (stalkClosedPointIso (CommRingCat.of K)).inv :=
    (Iso.eq_comp_inv _).2 rfl
  rw [h1]
  refine RingHom.Finite.comp (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (CommRingCat.of K)).inv).2) ?_
  rw [Scheme.stalkClosedPointTo_comp]
  set τ := Scheme.stalkClosedPointTo (spMap φ ≫ j) with hτdef
  have h2 : q.stalkMap _ ≫ τ = (X.residue _ ≫ q.residueFieldMap _) ≫ Y.descResidueField τ := by
    rw [Scheme.residue_residueFieldMap, Category.assoc, Scheme.residue_descResidueField]
  have hτ : ∀ a : A, ∃ s, τ.hom s = φ a := by
    intro a
    have h3 : τ = j.stalkMap _ ≫ Scheme.stalkClosedPointTo (spMap φ) := Scheme.stalkClosedPointTo_comp _ _
    have h5 : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (Spec (CommRingCat.of A)).presheaf.germ ⊤ ((spMap φ) (closedPoint (CommRingCat.of K))) trivial ≫
        inv (j.stalkMap ((spMap φ) (closedPoint (CommRingCat.of K)))) ≫
        j.stalkMap ((spMap φ) (closedPoint (CommRingCat.of K))) ≫ Scheme.stalkClosedPointTo (spMap φ) =
        CommRingCat.ofHom φ := by
      rw [IsIso.inv_hom_id_assoc, Scheme.germ_stalkClosedPointTo_Spec, Iso.inv_hom_id_assoc]
    refine ⟨((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (Spec (CommRingCat.of A)).presheaf.germ ⊤ ((spMap φ) (closedPoint (CommRingCat.of K))) trivial ≫
        inv (j.stalkMap ((spMap φ) (closedPoint (CommRingCat.of K))))).hom a, ?_⟩
    rw [h3]
    exact congrArg (fun m => m.hom a) h5
  have hsurj : Function.Surjective (Y.descResidueField τ).hom := by
    intro z
    obtain ⟨a, c, rfl⟩ := hφ z
    obtain ⟨s, hs⟩ := hτ a
    obtain ⟨t, ht⟩ := hτ c
    refine ⟨Y.residue _ s / Y.residue _ t, ?_⟩
    rw [map_div₀, ← hs, ← ht]
    rfl
  rw [h2]
  exact (RingHom.Finite.of_surjective _ hsurj).comp ((GlobalTheory.residueFieldMap_finite_of_locallyQuasiFinite q _).comp
    (RingHom.Finite.of_surjective _ (Scheme.residue_surjective X _)))

theorem exists_chart : ∀ (n N : ℕ) (X Y : Scheme.{0}) (sX : X ⟶ Sp (cycAway n)) (sY : Y ⟶ Sp (cycAway N)) (q : Y ⟶ X), 0 < n → 0 < N → Smooth sX → Smooth sY → IsFinite q → Etale q → Surjective q → ∀ η ∈ genericPoints X, ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra (cycAway N) Ω) (_ : ArithBase (cycAway N) Ω) (R : Subalgebra (cycAway N) Ω) (y : Sp R ⟶ Y), R.FG ∧ (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) ∧ y ≫ sY = spMap (algebraMap (cycAway N) R) ∧ (∀ w, (spMap R.val.toRingHom ≫ y ≫ q) w = η) ∧ ((spMap R.val.toRingHom ≫ y ≫ q).stalkMap (genericPoint (Sp Ω))).hom.Finite := by
  intro n N X Y sX sY q hn hN hsX hsY hq he hs η hη
  obtain ⟨η', hη', rfl⟩ := GlobalTheory.QuotTriple.genericPoints_subset_image (π := q) hη
  have hgen : (sY η').asIdeal = ⊥ := by
    let b : Sp (cycAway N) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (cycAway N))
    have hb : b ⤳ sY η' := (PrimeSpectrum.le_iff_specializes _ _).1 (show (⊥ : Ideal _) ≤ _ from bot_le)
    obtain ⟨z', hz', e⟩ := Flat.generalizingMap sY hb
    have h1 : closure {η'} ⊆ closure ({z'} : Set Y) := hz'.closure_subset
    have h2 : closure ({z'} : Set Y) ⊆ closure {η'} := hη'.2 isIrreducible_singleton.closure h1
    have h3 : η' ⤳ z' := specializes_iff_closure_subset.2 h2
    have : z' = η' := (hz'.antisymm h3).eq
    rw [← this, e]
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ η') isOpen_univ
  replace hU : IsAffineOpen U := hU
  haveI : LocallyOfFiniteType sY := inferInstance
  let P : PrimeSpectrum Γ(Y, U) := hU.primeIdealOf ⟨η', hηU⟩
  have hP : hU.fromSpec P = η' := hU.fromSpec_primeIdealOf _
  let ψ : cycAway N →+* Γ(Y, U) := (Spec.preimage (hU.fromSpec ≫ sY)).hom
  have hψ : spMap ψ = hU.fromSpec ≫ sY := Spec.map_preimage _
  have hft : ψ.FiniteType := by
    have : LocallyOfFiniteType (spMap ψ) := by rw [hψ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have hker : Ideal.comap ψ P.asIdeal = ⊥ := by
    have h1 : spMap ψ P = sY (hU.fromSpec P) := by rw [hψ]; rfl
    change (spMap ψ P).asIdeal = ⊥
    rw [h1, hP]; exact hgen
  letI : Algebra (cycAway N) Γ(Y, U) := ψ.toAlgebra
  let Ω := FractionRing (Γ(Y, U) ⧸ P.asIdeal)
  let φ : Γ(Y, U) →+* Ω := (algebraMap (Γ(Y, U) ⧸ P.asIdeal) Ω).comp (Ideal.Quotient.mk P.asIdeal)
  have hφker : ∀ a, φ a = 0 ↔ a ∈ P.asIdeal := fun a => by
    simp only [φ, RingHom.comp_apply]
    rw [(IsFractionRing.injective (Γ(Y, U) ⧸ P.asIdeal) Ω).eq_iff' (map_zero _), Ideal.Quotient.eq_zero_iff_mem]
  letI : Algebra (cycAway N) Ω := (φ.comp ψ).toAlgebra
  let f : Γ(Y, U) →ₐ[cycAway N] Ω := { φ with commutes' := fun _ => rfl }
  have hinj : Function.Injective (algebraMap (cycAway N) Ω) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have : x ∈ Ideal.comap ψ P.asIdeal := (hφker (ψ x)).1 hx
    rwa [hker, Ideal.mem_bot] at this
  haveI : CharZero Ω := charZero_of_injective_algebraMap hinj
  haveI : ArithBase (cycAway N) Ω := ⟨GlobalTheory.CycAwayReg.isDedekindDomain_cycAway N, finiteType_cycAway N, inferInstance, hinj⟩
  refine ⟨Ω, inferInstance, inferInstance, inferInstance, f.range, spMap f.rangeRestrict.toRingHom ≫ hU.fromSpec,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Algebra.map_top]
    haveI : Algebra.FiniteType (cycAway N) Γ(Y, U) := hft
    exact Algebra.FiniteType.out.map f
  · intro z
    obtain ⟨x, s, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Y, U) ⧸ P.asIdeal) z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective s
    exact ⟨f a, ⟨a, rfl⟩, f c, ⟨c, rfl⟩, rfl⟩
  · rw [Category.assoc, ← hψ, ← Spec.map_comp]
    rfl
  · intro w
    have hw : spMap f.rangeRestrict.toRingHom (spMap f.range.val.toRingHom w) = P := by
      refine PrimeSpectrum.ext ?_
      change Ideal.comap (f.rangeRestrict.toRingHom) (Ideal.comap f.range.val.toRingHom w.asIdeal) = P.asIdeal
      rw [@Ideal.eq_bot_of_prime _ _ w.asIdeal (PrimeSpectrum.isPrime (show PrimeSpectrum Ω from w))]
      ext a
      simp only [Ideal.mem_comap, Ideal.mem_bot]
      exact hφker a
    show q (hU.fromSpec (spMap f.rangeRestrict.toRingHom (spMap f.range.val.toRingHom w))) = q η'
    rw [hw, hP]
  · have e : spMap f.range.val.toRingHom ≫ spMap f.rangeRestrict.toRingHom =
        spMap (f.range.val.toRingHom.comp f.rangeRestrict.toRingHom) := (Spec.map_comp _ _).symm
    refine stalkMap_finite_of_chart Ω Γ(Y, U) q hU.fromSpec (f.range.val.toRingHom.comp f.rangeRestrict.toRingHom)
      (fun z => ?_) _ (by rw [← e]; simp only [Category.assoc])
    obtain ⟨x, s, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Y, U) ⧸ P.asIdeal) z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective s
    exact ⟨a, c, rfl⟩

end GlobalTheory.Poinc.Chart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartFiniteEtaleCoverGenericPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chart_finite_etale_cover_generic_point : ∀ (n N : ℕ) (X Y : Scheme.{0}) (sX : X ⟶ Sp (cycAway n)) (sY : Y ⟶ Sp (cycAway N)) (q : Y ⟶ X), 0 < n → 0 < N → Smooth sX → Smooth sY → IsFinite q → Etale q → Surjective q → ∀ η ∈ genericPoints X, ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra (cycAway N) Ω) (_ : ArithBase (cycAway N) Ω) (R : Subalgebra (cycAway N) Ω) (y : Sp R ⟶ Y), R.FG ∧ (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) ∧ y ≫ sY = spMap (algebraMap (cycAway N) R) ∧ (∀ w, (spMap R.val.toRingHom ≫ y ≫ q) w = η) ∧ ((spMap R.val.toRingHom ≫ y ≫ q).stalkMap (genericPoint (Sp Ω))).hom.Finite := by
  first | exact @GlobalTheory.Poinc.Chart.exists_chart | exact GlobalTheory.Poinc.Chart.exists_chart | (intros; apply GlobalTheory.Poinc.Chart.exists_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulMemCodimOneRegularChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem gp_comp {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (h : X ⟶ Sp R) :
    gp X ≫ h = spMap (cst h) := by
  apply ext_of_isAffine
  rw [gp, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, ← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of R)).inv,
    ← Scheme.ΓSpecIso_inv_naturality]
  ext a
  have e : CommRingCat.ofHom (cst h) =
      (Scheme.ΓSpecIso _).inv ≫ h.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial := rfl
  simp [e]

theorem exists_pow_mul_mem {O K : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (hd : ringKrullDim O ≤ 1) {a : O} (ha : a ∈ maximalIdeal O) (v : K) :
    ∃ N : ℕ, ∃ c : O, algebraMap O K a ^ N * v = algebraMap O K c := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := O) v
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  haveI : Ring.KrullDimLE 1 O := Ring.krullDimLE_iff.2 (by exact_mod_cast hd)
  have hrad : a ∈ (Ideal.span {y}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro J ⟨hJ, hJp⟩
    have hne : J ≠ ⊥ := fun h => hy0 (by
      have := hJ (Ideal.mem_span_singleton_self y); rw [h] at this; exact (Submodule.mem_bot _).1 this)
    have : J.IsMaximal := Ideal.isMaximal_of_isPrime_of_ne_bot J hne
    rw [IsLocalRing.eq_maximalIdeal this]; exact ha
  obtain ⟨N, hN⟩ := hrad
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hN
  refine ⟨N, c * x, ?_⟩
  have hy' : algebraMap O K y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  rw [← map_pow, ← hc, map_mul, map_mul]
  field_simp

theorem regAt_pow {X : Scheme.{0}} [IsIntegral X] {z : X} {g : X.functionField} (h : RegAt z g) (n : ℕ) :
    RegAt z (g ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact (unitAt_one z).regAt
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem eq_of_specializes {X : Scheme.{0}} [IsIntegral X] {z w : X} (hd : ringKrullDim (X.presheaf.stalk z) ≤ 1)
    (hwz : w ⤳ z) (hw : w ≠ genericPoint X) : w = z := by
  by_contra hne
  have hw' : w ∈ Set.range (X.fromSpecStalk z) := by rw [Scheme.range_fromSpecStalk]; exact hwz
  obtain ⟨p, rfl⟩ := hw'
  have hη : genericPoint X ∈ Set.range (X.fromSpecStalk z) := by
    rw [Scheme.range_fromSpecStalk]; exact (genericPoint_spec X).specializes trivial
  obtain ⟨q, hq⟩ := hη
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk z) := Ring.krullDimLE_iff.2 (by exact_mod_cast hd)
  have hp : p.asIdeal = ⊥ := by
    by_contra h
    haveI := p.isPrime
    have hm := Ideal.isMaximal_of_isPrime_of_ne_bot p.asIdeal h
    have : p = closedPoint _ := PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hm)
    apply hne; rw [this, Scheme.fromSpecStalk_closedPoint]
  have hpq : p ⤳ q := (PrimeSpectrum.le_iff_specializes p q).1 (by
    show p.asIdeal ≤ q.asIdeal; rw [hp]; exact bot_le)
  have h1 : X.fromSpecStalk z p ⤳ genericPoint X := hq ▸ hpq.map (X.fromSpecStalk z).continuous
  have h2 : genericPoint X ⤳ X.fromSpecStalk z p := (genericPoint_spec X).specializes trivial
  exact hw (h1.antisymm h2).eq

theorem θ_comp_c₀ (σ : Setup) (x : Sp σ.R) :
    (σ.θ x).comp σ.c₀ = (cst (σ.C x).G.hom).comp (σ.ρ x) := by
  obtain ⟨l, hl₁, hl₂⟩ := σ.hθ x
  have w := (σ.cart x).w
  simp only [Category.assoc] at w
  have e : spMap ((σ.θ x).comp σ.c₀) = spMap ((cst (σ.C x).G.hom).comp (σ.ρ x)) := by
    calc spMap ((σ.θ x).comp σ.c₀) = spMap (σ.θ x) ≫ spMap σ.c₀ := by
          simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
      _ = l ≫ σ.φ x ≫ σ.A.hom ≫ awayMap σ.f := by
          rw [Setup.c₀, ← gp_comp, ← Category.assoc, ← hl₂]; simp only [Category.assoc]
      _ = l ≫ (σ.V x).ι ≫ (σ.C x).G.hom ≫ spMap (σ.ρ x) := by rw [w]
      _ = gp _ ≫ (σ.C x).G.hom ≫ spMap (σ.ρ x) := by rw [← Category.assoc l, hl₁]
      _ = spMap ((cst (σ.C x).G.hom).comp (σ.ρ x)) := by
          rw [← Category.assoc, gp_comp]; simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have e' := congrArg CommRingCat.Hom.hom (Spec.map_inj.1 e)
  simpa using e'

theorem zeroAt_cst {R : Type} [CommRing R] {Y : Scheme.{0}} [IsIntegral Y] (h : Y ⟶ Sp R) (r : R) (z : Y)
    (hz : r ∈ (h z).asIdeal) : ZeroAt z (cst h r) := by
  rw [zeroAt_iff]
  refine ⟨regAt_fnOf (U := ⊤) trivial trivial _, fun hu => ?_⟩
  have h1 := (unitAt_fnOf_iff (x := z) (U := ⊤) trivial (gen_mem (x := z) trivial) _).1 hu
  rw [RingHom.comp_apply, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine] at h1
  exact h1 hz

theorem exists_pow_mul_mem_codimOne_regular_chart : ∀ (σ : Setup) (x : Sp σ.R) (u : σ.A.left.functionField), ∃ m : ℕ, σ.c₀ σ.f ^ m * u ∈ σ.W x := by
  intro σ x u
  haveI := (σ.C x).semi
  haveI : Smooth (σ.C x).G.hom := IsSemiAbelian.smooth
  haveI : QuasiCompact (σ.C x).G.hom := IsSemiAbelian.quasiCompact
  haveI : IsLocallyNoetherian (σ.C x).G.left := LocallyOfFiniteType.isLocallyNoetherian (σ.C x).G.hom
  haveI : CompactSpace (σ.C x).G.left := QuasiCompact.compactSpace_of_compactSpace (σ.C x).G.hom
  haveI : IsNoetherian (σ.C x).G.left := {}
  haveI : TopologicalSpace.NoetherianSpace (σ.C x).G.left := IsNoetherian.noetherianSpace
  have hg : σ.θ x (σ.c₀ σ.f) = cst (σ.C x).G.hom (σ.ρ x σ.f) := RingHom.congr_fun (θ_comp_c₀ σ x) σ.f
  set g := cst (σ.C x).G.hom (σ.ρ x σ.f)
  set v := σ.θ x u
  let P : Set (σ.C x).G.left := {z | ¬ RegAt z v}
  have hP : IsClosed P := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨U, hzU, a, ha⟩ := RegAt.exists_fnOf (not_not.1 hz)
    exact ⟨U, fun y hy => not_not.2 (ha ▸ regAt_fnOf hy _ a), U.isOpen, hzU⟩
  obtain ⟨S, hS, hirr, hPS⟩ := TopologicalSpace.NoetherianSpace.exists_finite_set_closeds_irreducible ⟨P, hP⟩
  let F : Set (σ.C x).G.left := ⋃ t ∈ S, {w | IsGenericPoint w (t : Set _)}
  have hF : F.Finite := hS.biUnion fun t _ => Set.Subsingleton.finite fun a ha b hb => ha.eq hb
  have hPt : ∀ t ∈ S, (t : Set (σ.C x).G.left) ⊆ P := fun t ht => by
    have : t ≤ sSup S := le_sSup ht
    rw [← hPS] at this
    exact this
  let C : TopologicalSpace.Closeds (σ.C x).G.left :=
    ⟨⋃ t ∈ S, (t : Set _), hS.isClosed_biUnion fun t _ => t.isClosed⟩
  have hPC : P ⊆ (C : Set _) := by
    have : sSup S ≤ C := sSup_le fun t ht y hy => Set.mem_iUnion₂.2 ⟨t, ht, hy⟩
    rw [← hPS] at this
    exact this
  have key : ∀ z, Vert (σ.C x).G.hom (σ.ρ x σ.f) z → z ∈ P → z ∈ F := by
    intro z hz hzP
    obtain ⟨t, ht, hzt⟩ := Set.mem_iUnion₂.1 (hPC hzP)
    have hw : IsGenericPoint (hirr t ht).genericPoint (t : Set _) := by
      have := (hirr t ht).isGenericPoint_genericPoint_closure
      rwa [t.isClosed.closure_eq] at this
    have hwP : (hirr t ht).genericPoint ∈ P := hPt t ht hw.mem
    have hwη : (hirr t ht).genericPoint ≠ genericPoint _ := fun h => hwP (h ▸ regAt_genericPoint v)
    have := eq_of_specializes hz.1.le (hw.specializes hzt) hwη
    exact Set.mem_iUnion₂.2 ⟨t, ht, this ▸ hw⟩
  have hpt : ∀ z, Vert (σ.C x).G.hom (σ.ρ x σ.f) z → ∃ N : ℕ, RegAt z (g ^ N * v) := by
    intro z hz
    obtain ⟨a, ha, hag⟩ := zeroAt_cst (σ.C x).G.hom (σ.ρ x σ.f) z hz.2
    obtain ⟨N, c, hc⟩ := exists_pow_mul_mem hz.1.le ha v
    exact ⟨N, c, by rw [← hc, hag]⟩
  classical
  let N : (σ.C x).G.left → ℕ := fun z => if h : Vert (σ.C x).G.hom (σ.ρ x σ.f) z then Classical.choose (hpt z h) else 0
  refine ⟨hF.toFinset.sup N, fun z hz => ?_⟩
  have hgz : RegAt z g := (zeroAt_cst (σ.C x).G.hom (σ.ρ x σ.f) z hz.2).regAt
  rw [map_mul, map_pow, hg]
  by_cases hzP : z ∈ P
  · have hle : N z ≤ hF.toFinset.sup N := Finset.le_sup (hF.mem_toFinset.2 (key z hz hzP))
    have hN : RegAt z (g ^ N z * v) := by
      simp only [N, dif_pos hz]; exact Classical.choose_spec (hpt z hz)
    rw [← Nat.sub_add_cancel hle, pow_add, _root_.mul_assoc]
    exact (regAt_pow hgz _).mul hN
  · exact (regAt_pow hgz _).mul (not_not.1 hzP)

end GlobalTheory.Desc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsSmoothCone
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsSmoothCone
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc.MinSys

open Matrix

theorem finite_of_pos {r : ℕ} (G : LinearMap.BilinForm ℤ (Fin r → ℤ)) (hs : ∀ a b, G a b = G b a)
    (hn : ∀ x, 0 ≤ G x x) (hp : ∀ x, x ≠ 0 → 0 < G x x) (B : ℤ) : {x | G x x ≤ B}.Finite := by
  classical
  set S : Matrix (Fin r) (Fin r) ℤ := LinearMap.BilinForm.toMatrix' G with hS
  have hGS : ∀ x, G x x = x ⬝ᵥ S *ᵥ x := fun x => by
    rw [← Matrix.toBilin'_apply', hS, Matrix.toBilin'_toMatrix']
  have hdet : S.det ≠ 0 := by
    intro h
    obtain ⟨z, hz, hSz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    have h1 := hp z hz
    rw [hGS, hSz, dotProduct_zero] at h1
    exact lt_irrefl _ h1
  have hpsd : (S.map (Int.cast : ℤ → ℝ)).PosSemidef := by
    have h := GlobalTheory.Poinc.QWDom.gram_posSemidef G hs hn (fun u => Pi.single u 1)
    convert h using 1
    ext u v
    simp [hS, LinearMap.BilinForm.toMatrix'_apply]
  have hpd : (S.map (Int.cast : ℤ → ℝ)).PosDef := by
    rw [hpsd.posDef_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ← Int.cast_det]
    exact_mod_cast hdet
  obtain ⟨c, hc, hP⟩ := GlobalTheory.Poinc.QWDom.exists_pos_posSemidef_sub_smul_one hpd
  have key : ∀ x : Fin r → ℤ, c * ∑ u, ((x u : ℝ)) ^ 2 ≤ (G x x : ℝ) := by
    intro x
    have h := hP.dotProduct_mulVec_nonneg (fun u => (x u : ℝ))
    simp only [star_trivial, sub_mulVec, dotProduct_sub, sub_nonneg] at h
    have e1 : (fun u => (x u : ℝ)) ⬝ᵥ (S.map (Int.cast : ℤ → ℝ)) *ᵥ (fun u => (x u : ℝ)) = ((x ⬝ᵥ S *ᵥ x : ℤ) : ℝ) := by
      simp [dotProduct, mulVec, Matrix.map_apply]
    have e2 : (fun u => (x u : ℝ)) ⬝ᵥ (c • (1 : Matrix (Fin r) (Fin r) ℝ)) *ᵥ (fun u => (x u : ℝ)) =
        c * ∑ u, ((x u : ℝ)) ^ 2 := by
      simp [dotProduct, Matrix.mulVec, Matrix.one_apply, Finset.mul_sum, sq]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e1, e2] at h
    rw [hGS]
    exact h
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (B : ℝ) / c ≤ M := exists_nat_ge _
  rw [div_le_iff₀ hc] at hM
  refine (Set.Finite.pi' (fun _ : Fin r => Set.finite_Icc (-(M : ℤ)) M)).subset fun x hx => ?_
  intro u
  have hxB : (G x x : ℝ) ≤ B := by exact_mod_cast hx
  have h1 : ((x u : ℝ)) ^ 2 ≤ ∑ v, ((x v : ℝ)) ^ 2 :=
    Finset.single_le_sum (f := fun v => ((x v : ℝ)) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ u)
  have h2 : c * ((x u : ℝ)) ^ 2 ≤ c * M := by
    have := (mul_le_mul_of_nonneg_left h1 hc.le).trans ((key x).trans hxB)
    linarith
  have h3 : ((x u : ℝ)) ^ 2 ≤ M := le_of_mul_le_mul_left h2 hc
  have h4 : (x u) ^ 2 ≤ (M : ℤ) := by exact_mod_cast h3
  have h5 := Int.le_self_sq (x u)
  have h6 := Int.le_self_sq (-(x u))
  rw [neg_sq] at h6
  exact ⟨by linarith, by linarith⟩

theorem qW_sum_nsmul {s m : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X] (cf : Fin m → ℕ)
    (γ : Fin m → LinearMap.BilinForm ℤ X) (y : Fin s → X) :
    qW W (∑ j, cf j • γ j) y = ∑ j, (cf j : ℤ) * qW W (γ j) y := by
  simp only [qW, LinearMap.sum_apply, LinearMap.smul_apply, nsmul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem qW_nsmul {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X] (k : ℕ)
    (b : LinearMap.BilinForm ℤ X) (y : Fin s → X) : qW W (k • b) y = (k : ℤ) * qW W b y := by
  simp only [qW, LinearMap.smul_apply, nsmul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  ring

theorem finite_minimiser_systems : ∀ (φ : InvFun ℤ), ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → ∀ r : ℕ, ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ)), IsCone id φ γ → (∀ x, x ≠ 0 → 0 < ∑ j, γ j x x) → ∃ Sμ : Finset ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)), ∀ (b : LinearMap.BilinForm ℤ (Fin r → ℤ)) (k : ℕ) (cf : Fin m → ℕ), 0 < k → (∀ j, 0 < cf j) → k • b = ∑ j, cf j • γ j → ∀ μ : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b (μ c) ≤ qW W b α) → μ ∈ Sμ := by
  intro φ W hW N _ _ r m γ hC hdef
  classical
  obtain ⟨c0, hc0, hge⟩ := GlobalTheory.Poinc.QWDom.qW_ge 8 W hW
  have hsym : ∀ j a b, γ j a b = γ j b a := fun j => (hC.mem j).1
  have hnn : ∀ j y, 0 ≤ γ j y y := hC.nonneg
  have hq0 : ∀ j (α : Fin 8 → Fin r → ℤ), 0 ≤ qW W (γ j) α := fun j α => by
    have h := hge (Fin r → ℤ) (γ j) (hsym j) (hnn j) α
    have h1 : (0 : ℝ) ≤ c0 * ((∑ u, γ j (α u) (α u) : ℤ) : ℝ) :=
      mul_nonneg hc0.le (by exact_mod_cast Finset.sum_nonneg fun u _ => hnn j (α u))
    exact_mod_cast h1.trans h
  set G : LinearMap.BilinForm ℤ (Fin r → ℤ) := ∑ j, γ j with hG
  have hGapp : ∀ a b, G a b = ∑ j, γ j a b := fun a b => by simp [hG, LinearMap.sum_apply]
  have hGsym : ∀ a b, G a b = G b a := fun a b => by simp only [hGapp, hsym _ a b]
  have hGnn : ∀ y, 0 ≤ G y y := fun y => by rw [hGapp]; exact Finset.sum_nonneg fun j _ => hnn j y
  have hGpos : ∀ x, x ≠ 0 → 0 < G x x := fun x hx => by rw [hGapp]; exact hdef x hx
  have hGq : ∀ α, qW W G α = ∑ j, qW W (γ j) α := fun α => by
    have := qW_sum_nsmul W (fun _ => 1) γ α
    simpa [hG] using this
  have hfinG : ∀ B : ℤ, {α : Fin 8 → Fin r → ℤ | qW W G α ≤ B}.Finite := by
    intro B
    obtain ⟨M, hM⟩ : ∃ M : ℕ, (B : ℝ) / c0 ≤ M := exists_nat_ge _
    rw [div_le_iff₀ hc0] at hM
    refine (Set.Finite.pi' fun _ : Fin 8 => finite_of_pos G hGsym hGnn hGpos M).subset fun α hα u => ?_
    have h := hge (Fin r → ℤ) G hGsym hGnn α
    have h1 : G (α u) (α u) ≤ ∑ v, G (α v) (α v) :=
      Finset.single_le_sum (f := fun v => G (α v) (α v)) (fun v _ => hGnn (α v)) (Finset.mem_univ u)
    have hα' : (qW W G α : ℝ) ≤ B := by exact_mod_cast hα
    have h1' : ((G (α u) (α u) : ℤ) : ℝ) ≤ ((∑ v, G (α v) (α v) : ℤ) : ℝ) := by exact_mod_cast h1
    have h2 : c0 * (G (α u) (α u) : ℝ) ≤ c0 * M := by
      have := (mul_le_mul_of_nonneg_left h1' hc0.le).trans (h.trans hα')
      linarith
    have h3 : (G (α u) (α u) : ℝ) ≤ M := le_of_mul_le_mul_left h2 hc0
    show G (α u) (α u) ≤ ((M : ℕ) : ℤ)
    exact_mod_cast h3
  let T : (Fin 8 → Fin r → ZMod N) → Type := fun c =>
    {α : Fin 8 → Fin r → ℤ // ∀ u i, ((α u i : ℤ) : ZMod N) = c u i}
  have hD : ∀ c, ∃ F : Finset (T c), ∀ α : T c, ∃ β ∈ F,
      (fun j => (qW W (γ j) β.1).toNat) ≤ (fun j => (qW W (γ j) α.1).toNat) :=
    fun c => GlobalTheory.dickson_finite_below_every m (fun (α : T c) j => (qW W (γ j) α.1).toNat)
  choose F hF using hD
  let Bd : (Fin 8 → Fin r → ZMod N) → ℤ := fun c => ∑ β ∈ F c, qW W G β.1
  have hfin : {μ : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ) | ∀ c, μ c ∈ {α | qW W G α ≤ Bd c}}.Finite :=
    Set.Finite.pi' fun c => hfinG (Bd c)
  refine ⟨hfin.toFinset, fun b k cf hk hcf hkb μ hμ hmin => ?_⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  intro c
  obtain ⟨β, hβF, hβ⟩ := hF c ⟨μ c, hμ c⟩
  have hle : ∀ j, qW W (γ j) β.1 ≤ qW W (γ j) (μ c) := fun j => by
    have h1 : (qW W (γ j) β.1).toNat ≤ (qW W (γ j) (μ c)).toNat := hβ j
    have := hq0 j β.1
    have := hq0 j (μ c)
    omega
  have hkq : ∀ α, (k : ℤ) * qW W b α = ∑ j, (cf j : ℤ) * qW W (γ j) α := fun α => by
    rw [← qW_nsmul, hkb, qW_sum_nsmul]
  have h2 : ∑ j, (cf j : ℤ) * qW W (γ j) (μ c) ≤ ∑ j, (cf j : ℤ) * qW W (γ j) β.1 := by
    rw [← hkq, ← hkq]
    exact mul_le_mul_of_nonneg_left (hmin c β.1 β.2) (by positivity)
  have h3 : ∀ j, qW W (γ j) (μ c) - qW W (γ j) β.1 ≤
      (cf j : ℤ) * qW W (γ j) (μ c) - (cf j : ℤ) * qW W (γ j) β.1 := fun j => by
    have h4 := hle j
    have h5 : (1 : ℤ) ≤ cf j := by exact_mod_cast hcf j
    nlinarith
  have h6 : ∑ j, qW W (γ j) (μ c) ≤ ∑ j, qW W (γ j) β.1 := by
    have h7 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => h3 j
    simp only [Finset.sum_sub_distrib] at h7
    linarith
  have h8 : qW W G β.1 ≤ Bd c :=
    Finset.single_le_sum (f := fun β : T c => qW W G β.1)
      (fun β _ => by rw [hGq]; exact Finset.sum_nonneg fun j _ => hq0 j β.1) hβF
  rw [hGq] at h8 ⊢
  linarith

end GlobalTheory.Poinc.MinSys
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsSmoothConeStatement
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_minimiser_systems_smooth_cone : ∀ (φ : InvFun ℤ), ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → ∀ r : ℕ, ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ)), IsCone id φ γ → (∀ x, x ≠ 0 → 0 < ∑ j, γ j x x) → ∃ Sμ : Finset ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)), ∀ (b : LinearMap.BilinForm ℤ (Fin r → ℤ)) (k : ℕ) (cf : Fin m → ℕ), 0 < k → (∀ j, 0 < cf j) → k • b = ∑ j, cf j • γ j → ∀ μ : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b (μ c) ≤ qW W b α) → μ ∈ Sμ := by
  first | exact @GlobalTheory.Poinc.MinSys.finite_minimiser_systems | exact GlobalTheory.Poinc.MinSys.finite_minimiser_systems | (intros; apply GlobalTheory.Poinc.MinSys.finite_minimiser_systems <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoAbelianSchemeDVROfGenericIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoAbelianSchemeDVROfGenericIso
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GenericIsoAb

theorem lbIso_of_generic_pullback : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Scheme.{0}) (a : A ⟶ Sp L) (φ : A ⟶ G.left), IsAbelianScheme G → IsPullback φ a G.hom (spMap (algebraMap W L)) → ∀ M M' : LB G.left, M.IsLB → M'.IsLB → LBIso (M.pull φ) (M'.pull φ) → LBIso M M' := by
  intro W L _ _ _ _ _ _ G _ A a φ hG hφ M M' hM hM' h
  have hi : pullback.fst G.hom (spMap (algebraMap W L)) = hφ.isoPullback.inv ≫ φ := hφ.isoPullback_inv_fst.symm
  have h' : LBIso (M.pull (pullback.fst G.hom (spMap (algebraMap W L))))
      (M'.pull (pullback.fst G.hom (spMap (algebraMap W L)))) :=
    GlobalTheory.GenericSpread.lbIso_pull_of_comp hφ.isoPullback.inv hi h
  exact GlobalTheory.GenericIsoConst.lbIso_of_generic W L G hG M M' hM hM' h'

end GlobalTheory.GenericIsoAb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoAbelianSchemeDVROfGenericIsoStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_abelianSchemeDVR_of_generic_iso : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Scheme.{0}) (a : A ⟶ Sp L) (φ : A ⟶ G.left), IsAbelianScheme G → IsPullback φ a G.hom (spMap (algebraMap W L)) → ∀ M M' : LB G.left, M.IsLB → M'.IsLB → LBIso (M.pull φ) (M'.pull φ) → LBIso M M' := by
  first | exact @GlobalTheory.GenericIsoAb.lbIso_of_generic_pullback | exact GlobalTheory.GenericIsoAb.lbIso_of_generic_pullback | (intros; apply GlobalTheory.GenericIsoAb.lbIso_of_generic_pullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeAlt
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.DualCon

theorem Rep.baseChange (S : Scheme.{0}) (A B S' S'' B'' : Over S) [GrpObj A] (b : B ⟶ S')
    (P : LB (A ⊗ B).left) (h : S'' ⟶ S') (k : B'' ⟶ B) (b'' : B'' ⟶ S'') (hR : Rep A b P)
    (hpb : IsPullback k b'' b h) : Rep A b'' (ev P (fst A B'') (snd A B'' ≫ k)) := by
  have hP : P.IsLB := hR.fam.isLB
  have hP' : (ev P (fst A B'') (snd A B'' ≫ k)).IsLB := pull_isLB hP _
  have key : ∀ (Y : Over S) (a : Y ⟶ A) (y : Y ⟶ B''), evc hP' a y = evc hP a (y ≫ k) := by
    intro Y a y
    rw [evc_ev hP, lift_fst, lift_snd_assoc]
  have iso : ∀ (T : Over S) (N : LB (A ⊗ T).left) (hN : N.IsLB) (y : T ⟶ B''),
      LBIso N (ev (ev P (fst A B'') (snd A B'' ≫ k)) (fst A T) (snd A T ≫ y)) ↔
        LBIso N (ev P (fst A T) (snd A T ≫ y ≫ k)) := by
    intro T N hN y
    rw [← cls_eq_iff hN (pull_isLB hP' _), ← cls_eq_iff hN (pull_isLB hP _), cls_ev hP', cls_ev hP, key,
      Category.assoc]
  refine ⟨⟨hP', (isAdditive_iff hP').2 fun Y a a' t ↦ ?_⟩, fun T t N hN ↦ ?_⟩
  · rw [key, key, key]
    exact (isAdditive_iff hP).1 hR.fam.add Y a a' (t ≫ k)
  · obtain ⟨x, ⟨hx1, hx2⟩, hu⟩ := hR.univ T (t ≫ h) N hN
    refine ⟨hpb.lift x t hx1, ⟨hpb.lift_snd _ _ _, (iso T N hN.isLB _).2 ?_⟩, fun y ⟨hy1, hy2⟩ ↦ ?_⟩
    · rw [hpb.lift_fst]
      exact hx2
    · have e : y ≫ k = x := hu (y ≫ k) ⟨by rw [Category.assoc, hpb.w, ← Category.assoc, hy1],
        (iso T N hN.isLB y).1 hy2⟩
      exact hpb.hom_ext (by rw [e, hpb.lift_fst]) (by rw [hy1, hpb.lift_snd])

end GlobalTheory.DualCon
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLineBundlePullbackBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLineBundlePullbackBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SymBaseChange

theorem inv_left_fst (S T : Scheme.{0}) (G : Over S) [GrpObj G] (j : T ⟶ S) :
    (GrpObj.inv : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G).left ≫ pullback.fst G.hom j =
      pullback.fst G.hom j ≫ (GrpObj.inv : G ⟶ G).left := by
  exact pullback.lift_fst _ _ _

theorem symm_pull : ∀ (S T : Scheme.{0}) (G : Over S) [GrpObj G] (j : T ⟶ S) (L : LB G.left), L.IsLB → LBIso (L.pull (GrpObj.inv : G ⟶ G).left) L → LBIso ((L.pull (pullback.fst G.hom j)).pull (GrpObj.inv : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G).left) (L.pull (pullback.fst G.hom j)) := by
  intro S T G _ j L hL h
  have e := inv_left_fst S T G j
  have h1 := GenSpread.lbIso_pull_pull hL (a := pullback.fst G.hom j) (GrpObj.inv : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G).left rfl
  have h2 := GenSpread.lbIso_pull_pull hL (a := (GrpObj.inv : G ⟶ G).left) (pullback.fst G.hom j) e
  have h3 := GenSpread.lbIso_pullback h (pullback.fst G.hom j)
  exact LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB hL _) (LBIso.symm h1)
    (LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) h2 h3)

end GlobalTheory.SymBaseChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLineBundlePullbackBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_lineBundle_pullback_baseChange : ∀ (S T : Scheme.{0}) (G : Over S) [GrpObj G] (j : T ⟶ S) (L : LB G.left), L.IsLB → LBIso (L.pull (GrpObj.inv : G ⟶ G).left) L → LBIso ((L.pull (pullback.fst G.hom j)).pull (GrpObj.inv : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G).left) (L.pull (pullback.fst G.hom j)) := by
  first | exact @GlobalTheory.SymBaseChange.symm_pull | exact GlobalTheory.SymBaseChange.symm_pull | (intros; apply GlobalTheory.SymBaseChange.symm_pull <;> assumption)
end
end
