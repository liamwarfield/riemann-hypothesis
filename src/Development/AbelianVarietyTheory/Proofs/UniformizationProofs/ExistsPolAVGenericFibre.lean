module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TrivOnOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfCompatibleAbelianThickenings
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UtestGeomNonempty

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPolAVGenericFibre
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenericPol

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_lift {K : Type} [Field K] {X Z : Scheme.{0}} (x : Spec (CommRingCat.of K) ⟶ X) (j : Z ⟶ X)
    (h : Set.range x ⊆ Set.range j) :
    ∃ (K' : Type) (_ : Field K') (i : K →+* K') (z : Spec (CommRingCat.of K') ⟶ Z), specOf i ≫ x = z ≫ j := by
  obtain ⟨z, hz⟩ := h ⟨(default : PrimeSpectrum K), rfl⟩
  obtain ⟨p, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := x) (g := j) _ z hz.symm
  let u := (pullback x j).fromSpecResidueField p
  refine ⟨(pullback x j).residueField p, inferInstance, (Spec.preimage (u ≫ pullback.fst x j)).hom,
    u ≫ pullback.snd x j, ?_⟩
  have e : specOf (Spec.preimage (u ≫ pullback.fst x j)).hom = u ≫ pullback.fst x j :=
    Spec.map_preimage _
  rw [e]
  exact (Category.assoc _ _ _).trans ((congrArg (u ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {H : Host E}

theorem proper_ample_kTriv {X Z : Scheme.{0}} {T : SAB H X} {T' : SAB H Z} {j : Z ⟶ X} (mj : SABMap T' T j)
    (hp : IsProper T'.G.hom) (hA : RelAmple T'.G T'.PP.L) (hK : KTriv T'.G T'.PP.L) {K : Type} [Field K]
    {x : Spec (CommRingCat.of K) ⟶ X} {t : SAB H (Spec (CommRingCat.of K))} (m : SABMap t T x)
    (h : Set.range x ⊆ Set.range j) : IsProper t.G.hom ∧ RelAmple t.G t.PP.L ∧ KTriv t.G t.PP.L := by
  obtain ⟨K', _, i, z, e⟩ := exists_lift x j h
  obtain ⟨PP', cub, sym, adj, prim, m₁, -⟩ := sabPull CubePf.cubePull (specOf i) t
  generalize (⟨(Over.pullback (specOf i)).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
    Geo.Tor.OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩ : SAB H _) = t' at m₁
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₁
  obtain ⟨m', -⟩ := sabCancel pullCubCancel E H _ _ _ T T' t' j z mj (e ▸ n)
  obtain ⟨w, g, -⟩ := m'.lin
  obtain ⟨w₁, g₁, -⟩ := m₁.lin
  obtain ⟨U, hU, hc, -⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (U := ⊤)
    (x := z (IsLocalRing.closedPoint K')) trivial
  have hy : ∀ y, z y ∈ U := fun y =>
    (congrArg (fun V => y ∈ V) (Scheme.preimage_eq_top_of_closedPoint_mem z hc)).mpr trivial
  have := t.semi.smooth
  have := t.semi.separated
  have := t.semi.quasiCompact
  exact GlobalTheory.AmpleDescent.proper_relAmple_kTriv_of_fieldExtension K K' i t.G t'.G m₁.φ m₁.cart t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB ⟨w₁, g₁⟩
    (MorphismProperty.of_isPullback (P := @IsProper) m'.cart.1 hp)
    (relAmple_pull m'.cart.1 T'.PP.isLB t'.PP.isLB ((isGen_iff w).1 g) U hU hy hA)
    (kTriv_pull m'.cart T'.PP.isLB t'.PP.isLB ((isGen_iff w).1 g) hK)

def toPolAV {S : Scheme.{0}} (t : SAB H S) (g : ℕ) (hg : SmoothOfRelativeDimension g t.G.hom) (hp : IsProper t.G.hom)
    (hA : RelAmple t.G t.PP.L) (hK : KTriv t.G t.PP.L) : PolAV S where
  A := t.G
  isAb := ⟨t.semi.comm, t.semi.smooth, hp, t.semi.geomConnected⟩
  g := g
  smoothDim := hg
  L := t.PP.L
  isLB := t.PP.isLB
  rigid := ⟨t.PP.rig, t.PP.rigGen⟩
  sym := by
    obtain ⟨-, w, hw, -⟩ := t.sym
    exact fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff w).1 hw) _⟩
  ample := hA
  ktriv := hK

theorem rosatiAdj {S : Scheme.{0}} (t : SAB H S) (a : NumberField.RingOfIntegers E) :
    RosatiAdj t.G t.PP.L (t.act.act a) (t.act.act (H.bar a)) := by
  obtain ⟨u, hu⟩ := GlobalTheory.NormRos.exists_gen_rosati t.PP.isLB _ _ (t.adj a)
  exact fun _ => ⟨⊤, trivial, LB.pullGen _ _ _ u _, DVR.pullGen_isGen _ _ _ _ hu _⟩

end GlobalTheory.GenericPol


open GlobalTheory.GenericPol ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem GlobalTheory.exists_polAV_genericFibre : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (Dm : Geo.Tor.Datum H) (l : Geo.Tor.Level H) (Xo : Geo.Tor.Moduli Dm l) (c : Geo.Tor.Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Geo.Tor.Model Xo c β) (R : Type) [CommRing R] [IsDomain R] (χ : Geo.Tor.Sp R ⟶ Y.X) (t : Geo.Tor.SAB H (Geo.Tor.Sp R)) (_ : Geo.Tor.SABMap t Y.t χ), Set.range (jK R ≫ χ) ⊆ Set.range Y.j → ∀ g : ℕ, SmoothOfRelativeDimension g t.G.hom → ∃ (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (eA : (Over.pullback (jK R)).obj t.G ≅ A.A) (oA : letI := H.starRing; A.OAct (NumberField.RingOfIntegers E)), A.g = g ∧ IsMonHom eA.hom ∧ Geo.Tor.LBIso (A.L.pull eA.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK R))) ∧ (letI := H.starRing; ∀ a, (Over.pullback (jK R)).map (t.act.act a) ≫ eA.hom = eA.hom ≫ oA.act a) := by
  intro E _ _ _ H Dm l Xo c O _ β Y R _ _ χ t m h g hg
  let := H.starRing
  obtain ⟨PP', cub, sym, adj, prim, m₁, hm₁⟩ := sabPull CubePf.cubePull (jK R) t
  let t' : SAB H (Spec (CommRingCat.of (FractionRing R))) :=
    ⟨(Over.pullback (jK R)).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
      Geo.Tor.OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩
  let m₀ : SABMap t' t (jK R) := m₁
  have hm₀ : m₀.cm.F = pullback.fst t.G.hom (jK R) := hm₁
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₀
  obtain ⟨hp, hA, hK⟩ := proper_ample_kTriv Y.m Y.oF.proper Y.oF.ample Y.oF.ktriv n h
  have hg' : SmoothOfRelativeDimension g t'.G.hom := by
    show SmoothOfRelativeDimension g (pullback.snd t.G.hom (jK R))
    exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hg
  obtain ⟨w, hw, -⟩ := m₀.lin
  have hL : LBIso t'.PP.L (t.PP.L.pull (pullback.fst t.G.hom (jK R))) := hm₀ ▸ ⟨w, hw⟩
  refine ⟨toPolAV t' g hg' hp hA hK, Iso.refl _, ⟨t'.act.toRingAct, rosatiAdj t'⟩, rfl, ?_, ?_, fun a => ?_⟩
  · exact inferInstanceAs (IsMonHom (𝟙 t'.G))
  · exact LBIso.chartPull (Geo.Tor.chartPullPull t'.PP.L (𝟙 _) (𝟙 _) rfl) (Geo.Tor.chartPullId _) hL
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqTopOfClosedFibre
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AbTriv

variable {X X' S S' : Scheme.{0}} {N : LB X}

theorem exists_normalised (hN : N.IsLB) {p : X ⟶ S} {e : S ⟶ X} (he : e ≫ p = 𝟙 S)
    (c : LB.Gen (N.pull e)) (hc : c.IsGen) {π : X' ⟶ X} {p' : X' ⟶ S'} {g : S' ⟶ S}
    (h : IsPullback π p' p g) (ht : Triv (N.pull π)) :
    ∃ t : LB.Gen (N.pull π), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (b : Z ⟶ S) (z : Z) (J),
      Good N z J → r ≫ π = b ≫ e → val t r z J = val c b z J := by
  obtain ⟨t, ht⟩ := ht
  let n : X' ⟶ X' := h.lift ((π ≫ p) ≫ e) p' (by rw [Category.assoc, he, Category.comp_id, h.w])
  have n₁ : n ≫ π = (π ≫ p) ≫ e := h.lift_fst _ _ _
  have n₂ : n ≫ p' = p' := h.lift_snd _ _ _
  obtain ⟨t', ht', hv⟩ := exists_gen hN (K' := PUnit) (φ' := fun _ => π) (ε' := fun _ => 1)
    (fun V _ k => by
      refine (Fintype.prod_sum_type _).trans ?_
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, n₁, mul_inv_cancel,
        _root_.mul_one])
    (LB.mulGen N _ _ _ _ t (LB.mulGen N _ _ _ _ (LB.pullGen N _ _ c (π ≫ p))
      (LB.invGen N _ _ (LB.pullGen N _ _ t n))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hc _)
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht n))))
  refine ⟨t', ht', fun Z r b z J hJ hr => ?_⟩
  have hb : r ≫ π ≫ p = b := by rw [← Category.assoc, hr, Category.assoc, he, Category.comp_id]
  have hn : r ≫ n = r := h.hom_ext
    (by rw [Category.assoc, n₁, ← Category.assoc, hb, hr]) (by rw [Category.assoc, n₂])
  rw [hv Z r z J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, hn, hb, mul_comm (val c b z J),
    mul_inv_cancel_left]

theorem triv_of_pull_id (h : Triv (N.pull (𝟙 X))) : Triv N := by
  obtain ⟨t, ht⟩ := h
  have le : ∀ i, N.U i ≤ (N.pull (𝟙 X)).U (fun _ => i) := fun i x hx => mem_pull.2 hx
  refine ⟨⟨fun i => res (le i) (t.s fun _ => i)⟩, fun i j => unit_ext fun x hx => ?_⟩
  have e := gen_trans ht (𝟙 X) x (le i hx.1) (le j hx.2)
  simp only [trF, Finset.univ_unique, Finset.prod_singleton, zpow_one, Category.id_comp] at e
  refine ((gm_res _ x _ hx _).trans (gm_res _ x _ hx.1 _)).trans (e.trans (Eq.symm ?_))
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) rfl ((gm_res _ x _ hx _).trans (gm_res _ x _ hx.2 _)))

theorem eq_top_of_closed_fibre {V : Type} [CommRing V] [IsLocalRing V] (p : X ⟶ Spec (CommRingCat.of V))
    [UniversallyClosed p] (U : X.Opens) (h : ∀ x, p x = IsLocalRing.closedPoint V → x ∈ U) : U = ⊤ := by
  have hc : IsClosed (p '' (U : Set X)ᶜ) := p.isClosedMap _ U.isOpen.isClosed_compl
  have := DVR.eq_top_of_closedPoint_mem (V := V) ⟨_, hc.isOpen_compl⟩ (by
    rintro ⟨x, hx, e⟩
    exact hx (h x e))
  refine eq_top_iff.2 fun x _ => by_contra fun hx => ?_
  have hm : p x ∈ (⊤ : (Spec (CommRingCat.of V)).Opens) := trivial
  rw [← this] at hm
  exact hm ⟨x, hx, rfl⟩

theorem closedPoint_mem_range {V : Type} [CommRing V] [IsLocalRing V] (e : ℕ) :
    IsLocalRing.closedPoint V ∈ Set.range (thick V (IsLocalRing.maximalIdeal V) e) := by
  have h := range_comap_of_surjective _ _
    (Ideal.Quotient.mk_surjective (I := IsLocalRing.maximalIdeal V ^ (e + 1)))
  refine h.ge ?_
  rw [Ideal.mk_ker]
  exact Ideal.pow_le_self (Nat.succ_ne_zero e)

theorem triv_of_forall_thick : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (B : Over (Spec (CommRingCat.of V))) [GrpObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ N : LB B.left, N.IsLB → (∀ e, Triv (N.pull (fstG (IsLocalRing.maximalIdeal V) e B).left)) → Triv N := by
  intro hG V _ _ _ hV B _ hB hp N hN ht
  let I := IsLocalRing.maximalIdeal V
  let o : Spec (CommRingCat.of V) ⟶ B.left := (η[B]).left
  have ho : o ≫ B.hom = 𝟙 _ := Over.w η[B]
  obtain ⟨c, hc⟩ := DVR.exists_gen_of_local N hN (K := PUnit) (fun _ => o) (fun _ => 1)
  have pb : ∀ e, IsPullback (fstG I e B).left (thickObj V I e B).hom B.hom (thick V I e) :=
    fun e => IsPullback.of_hasPullback B.hom (thick V I e)
  choose t tg tv using fun e => exists_normalised hN ho c hc (pb e) (ht e)
  have tm : ∀ e, thickMap V I e B ≫ (fstG I (e + 1) B).left = (fstG I e B).left := fun e =>
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have compat : ∀ e z J, Good N z J → val (t (e + 1)) (thickMap V I e B) z J = val (t e) (𝟙 _) z J := by
    intro e z J hJ
    let a := (pb e).lift (thick V I e ≫ o) (𝟙 _) (by rw [Category.assoc, ho, Category.comp_id, Category.id_comp])
    have a₁ : a ≫ (fstG I e B).left = thick V I e ≫ o := (pb e).lift_fst _ _ _
    have key := gen_unique' hN (fun U _ k => by simp only [tm e]) (thickObj V I e B).hom a ((pb e).lift_snd _ _ _)
      (hG _ _ (TLinPf.isAb_pullback (thick V I e) B hB)).2 (tg e)
      (DVR.pullGen_isGen _ _ _ _ (tg (e + 1)) (thickMap V I e B))
      (fun y J hJ => (tv e _ a _ y J hJ a₁).trans ((val_pull hJ _ _ _).trans
        (tv (e + 1) _ _ _ y J hJ (by rw [Category.assoc, tm e, a₁]))).symm) _ (𝟙 _) z J hJ
    rw [val_pull hJ, Category.id_comp] at key
    exact key.symm
  obtain ⟨s, hs, -⟩ := GlobalTheory.SecAlg.existsUnique_sec V I hV B hB.smooth hp N hN (fun e => genSec (t e) (tg e))
    (fun e z J hJ => (sval_genSec _ _ _ z hJ).trans
      ((congrArg Units.val (compat e z J hJ)).trans (sval_genSec _ _ _ z hJ).symm))
  have := hB.proper
  have top : nonzeroLocus s = ⊤ := eq_top_of_closed_fibre B.hom _ fun x hx => by
    have hm : x ∈ Set.range (pullback.fst B.hom (thick V I 0)) := by
      rw [Scheme.Pullback.range_fst, Set.mem_preimage, hx]
      exact closedPoint_mem_range 0
    obtain ⟨z, rfl⟩ := hm
    choose J hJ using fun ψ : ((Over.map (thick V I 0)).obj (thickObj V I 0 B)).left ⟶ B.left =>
      exists_chart hN (ψ z)
    refine (TwistZero.mem_nonzeroLocus_iff s (fstG I 0 B).left z hJ).2 ?_
    rw [hs 0 z J hJ, sval_genSec _ _ _ z hJ]
    exact Units.isUnit _
  refine triv_of_pull_id (TwistZero.triv_of_sec hN s fun y J hJ => ?_)
  exact (TwistZero.mem_nonzeroLocus_iff s (𝟙 _) y hJ).1 (by rw [top]; trivial)

end GlobalTheory.AbTriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeLocallyTrivialProductLineBu
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeLocallyTrivialProductLineBu
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TrivSubscheme

theorem exists_idealSheaf {T : Scheme.{0}} (P : ∀ Y : Scheme.{0}, (Y ⟶ T) → Prop)
    (hcomp : ∀ (Y Z : Scheme.{0}) (x : Y ⟶ T) (h : Z ⟶ Y), P Y x → P Z (h ≫ x))
    (hloc : ∀ (Y : Scheme.{0}) (x : Y ⟶ T),
      (∀ y : Y, ∃ V : Y.affineOpens, y ∈ V.1 ∧ P _ (V.2.fromSpec ≫ x)) → P Y x)
    (haff : ∀ U : T.affineOpens, ∃ I : Ideal Γ(T, U), ∀ (S : CommRingCat.{0}) (g : Γ(T, U) ⟶ S),
      P _ (Spec.map g ≫ U.2.fromSpec) ↔ I ≤ RingHom.ker g.hom) :
    ∃ I : T.IdealSheafData, ∀ (Y : Scheme.{0}) (x : Y ⟶ T), P Y x ↔ I ≤ x.ker := by
  choose J hJ using haff
  have hmap : ∀ (U V : T.affineOpens) (h : V.1 ≤ U.1),
      (J U).map (T.presheaf.map (homOfLE h).op).hom = J V := by
    intro U V h
    have key : ∀ K : Ideal Γ(T, V), (J U).map (T.presheaf.map (homOfLE h).op).hom ≤ K ↔ J V ≤ K := by
      intro K
      have h₁ := hJ V _ (CommRingCat.ofHom (Ideal.Quotient.mk K))
      have h₂ := hJ U _ (T.presheaf.map (homOfLE h).op ≫ CommRingCat.ofHom (Ideal.Quotient.mk K))
      rw [Spec.map_comp, Category.assoc, IsAffineOpen.map_fromSpec U.2 V.2, h₁, CommRingCat.hom_comp,
        ← RingHom.comap_ker, CommRingCat.hom_ofHom, Ideal.mk_ker] at h₂
      rw [Ideal.map_le_iff_le_comap, h₂]
    exact le_antisymm ((key _).2 le_rfl) ((key _).1 le_rfl)
  refine ⟨⟨J, fun U f => hmap U (T.affineBasicOpen f) _, _, rfl⟩, fun Y x => ?_⟩
  have hV : ∀ (U : T.affineOpens) (V : Y.affineOpens) (e : V.1 ≤ x ⁻¹ᵁ U.1),
      P _ (V.2.fromSpec ≫ x) ↔ J U ≤ RingHom.ker (x.appLE U.1 V.1 e).hom := fun U V e => by
    rw [← hJ, IsAffineOpen.SpecMap_appLE_fromSpec x U.2 V.2 e]
  have hex : ∀ (W : Y.Opens) (y : Y), y ∈ W → ∃ V : Y.affineOpens, y ∈ V.1 ∧ V.1 ≤ W := fun W y hy => by
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hle⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy W.isOpen
    exact ⟨⟨V, hV⟩, hyV, hle⟩
  constructor
  · intro hx
    refine Scheme.IdealSheafData.le_ofIdeals_iff.2 fun U a ha => ?_
    refine Y.IsSheaf.section_ext fun y hy => ?_
    obtain ⟨V, hyV, hle⟩ := hex _ y hy
    refine ⟨V.1, hle, hyV, ?_⟩
    exact ((hV U V hle).1 (hcomp _ _ _ _ hx) ha).trans (map_zero _).symm
  · intro hx
    refine hloc Y x fun y => ?_
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
      T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (x y)) isOpen_univ
    obtain ⟨V, hyV, hle⟩ := hex (x ⁻¹ᵁ U) y hyU
    refine ⟨V, hyV, (hV ⟨U, hU⟩ V hle).2 fun a ha => ?_⟩
    have h₁ : (x.app U).hom a = 0 := x.ideal_ker_le ⟨U, hU⟩ (hx ⟨U, hU⟩ ha)
    rw [RingHom.mem_ker, Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
    exact (congrArg _ h₁).trans (map_zero _)

theorem triv_pull_iff {X Y Z : Scheme.{0}} (M : LB X) (f : Y ⟶ X) (h : Z ⟶ Y) :
    Triv ((M.pull f).pull h) ↔ Triv (M.pull (h ≫ f)) :=
  ⟨fun ⟨t, ht⟩ => exists_isGen_linComb_of_pull M _ _ _ t ht, CubeOpen.triv_pull_pull f h⟩

variable {X T : Scheme.{0}} (p : X ⟶ T) (F : LB X)

def TrivOver {Y : Scheme.{0}} (x : Y ⟶ T) : Prop := Triv (F.pull (pullback.fst p x))

def LocTrivOver (Y : Scheme.{0}) (x : Y ⟶ T) : Prop :=
  ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ TrivOver p F (U.ι ≫ x)

variable {p F}

theorem TrivOver.triv {Y Z : Scheme.{0}} {x : Y ⟶ T} (H : TrivOver p F x) (k : Z ⟶ X) (z : Z ⟶ Y)
    (e : k ≫ p = z ≫ x) : Triv (F.pull k) :=
  CubeOpen.triv_comp (pullback.lift k z e) (pullback.lift_fst _ _ _) H

theorem TrivOver.comp {Y Z : Scheme.{0}} {x : Y ⟶ T} (H : TrivOver p F x) (h : Z ⟶ Y) {w : Z ⟶ T}
    (e : h ≫ x = w) : TrivOver p F w :=
  H.triv _ (pullback.snd _ _ ≫ h) (by rw [pullback.condition, Category.assoc, e])

theorem LocTrivOver.comp (Y Z : Scheme.{0}) (x : Y ⟶ T) (h : Z ⟶ Y) (H : LocTrivOver p F Y x) :
    LocTrivOver p F Z (h ≫ x) := fun z => by
  obtain ⟨U, hU, ht⟩ := H (h z)
  exact ⟨h ⁻¹ᵁ U, hU, ht.comp (h ∣_ U) (by rw [morphismRestrict_ι_assoc])⟩

theorem locTrivOver_of_affine (Y : Scheme.{0}) (x : Y ⟶ T)
    (H : ∀ y : Y, ∃ V : Y.affineOpens, y ∈ V.1 ∧ LocTrivOver p F _ (V.2.fromSpec ≫ x)) :
    LocTrivOver p F Y x := fun y => by
  obtain ⟨V, hy, hV⟩ := H y
  obtain ⟨q, rfl⟩ := V.2.range_fromSpec.ge hy
  obtain ⟨U, hU, ht⟩ := hV q
  haveI : IsOpenImmersion V.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec (U := V.1) V.2
  have hr : Set.range (V.2.fromSpec ''ᵁ U).ι ⊆ Set.range (U.ι ≫ V.2.fromSpec) := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, rfl⟩
  refine ⟨V.2.fromSpec ''ᵁ U, ⟨q, hU, rfl⟩, ht.comp (IsOpenImmersion.lift _ _ hr) ?_⟩
  rw [← Category.assoc U.ι, IsOpenImmersion.lift_fac_assoc]

theorem locTrivOver_iff {Y X' : Scheme.{0}} {x : Y ⟶ T} {π : X' ⟶ X} {f' : X' ⟶ Y} (h : IsPullback π f' p x) :
    LocTrivOver p F Y x ↔ ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ Triv (F.pull ((f' ⁻¹ᵁ U).ι ≫ π)) := by
  refine forall_congr' fun y => exists_congr fun U => and_congr_right fun _ => ⟨fun ht => ?_, fun ht => ?_⟩
  · exact ht.triv _ (f' ∣_ U) (by rw [morphismRestrict_ι_assoc, Category.assoc, h.w])
  · have hp := (isPullback_morphismRestrict f' U).flip.paste_horiz h
    exact CubeOpen.triv_comp (hp.lift _ _ pullback.condition) (hp.lift_fst _ _ _) ht

theorem exists_closed_locTriv : GlobalFnsSt → ∀ (R : Type) [CommRing R] (T B : Over (Spec (CommRingCat.of R))) [GrpObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ F : LB (T ⊗ B).left, F.IsLB → ∃ (H : Over (Spec (CommRingCat.of R))) (j : H ⟶ T), IsClosedImmersion j.left ∧ ∀ (T' : Over (Spec (CommRingCat.of R))) (x : T' ⟶ T), (∀ p : T'.left, ∃ U : T'.left.Opens, p ∈ U ∧ Triv ((F.pull (x ▷ B).left).pull ((fst T' B).left ⁻¹ᵁ U).ι)) ↔ ∃ y : T' ⟶ H, y ≫ j = x := by
  intro hG R _ T B _ hB hproj F hF
  have h₀ : IsPullback (pullback.snd T.hom B.hom) (fst T B).left B.hom T.hom :=
    (IsPullback.of_hasPullback T.hom B.hom).flip
  obtain ⟨I, hI⟩ := exists_idealSheaf (LocTrivOver (fst T B).left F) LocTrivOver.comp locTrivOver_of_affine
    (fun U => by
      let t : Spec (CommRingCat.of Γ(T.left, U)) ⟶ Spec (CommRingCat.of R) := U.2.fromSpec ≫ T.hom
      have h₁ : IsPullback (pullback.fst B.hom t) (pullback.snd B.hom t) B.hom (U.2.fromSpec ≫ T.hom) :=
        IsPullback.of_hasPullback _ _
      let φ := h₀.lift _ _ (h₁.w.trans (Category.assoc _ _ _).symm)
      have h₂ : IsPullback φ (pullback.snd B.hom t) (fst T B).left U.2.fromSpec :=
        IsPullback.of_right (by rw [h₀.lift_fst]; exact h₁) (h₀.lift_snd _ _ _) h₀
      obtain ⟨I, hI⟩ := TrivRep.exists_ideal_locTriv hG Γ(T.left, U) ((Over.pullback t).obj B)
        (CubeGen.isAb_baseChange hB t) (CubeProj.isProjBy_baseChange hproj h₁) (F.pull φ) (LB.isLB_pull hF φ)
      refine ⟨I, fun S g => ?_⟩
      have h₃ := IsPullback.of_hasPullback (pullback.snd B.hom t) (Spec.map g)
      rw [← hI S g.hom _ _ _ h₃, locTrivOver_iff (h₃.paste_horiz h₂)]
      refine forall_congr' fun y => exists_congr fun V => and_congr_right fun _ => ?_
      rw [← Category.assoc]
      exact ((triv_pull_iff _ _ _).trans (triv_pull_iff _ _ _)).symm)
  refine ⟨Over.mk (I.subschemeι ≫ T.hom), Over.homMk I.subschemeι rfl,
    inferInstanceAs (IsClosedImmersion I.subschemeι), fun T' x => ?_⟩
  have h₄ : IsPullback (x ▷ B).left (fst T' B).left (fst T B).left x.left := by
    refine IsPullback.of_right ?_ (Over.whiskerRight_left_fst x) h₀
    rw [Over.whiskerRight_left_snd, Over.w]
    exact (IsPullback.of_hasPullback T'.hom B.hom).flip
  simp only [triv_pull_iff]
  rw [← locTrivOver_iff h₄, hI]
  constructor
  · intro h
    have h' : I.subschemeι.ker ≤ x.left.ker := by rwa [Scheme.IdealSheafData.ker_subschemeι]
    refine ⟨Over.homMk (IsClosedImmersion.lift I.subschemeι x.left h') ?_, ?_⟩
    · exact (IsClosedImmersion.lift_fac_assoc _ _ _ _).trans (Over.w x)
    · exact Over.OverMorphism.ext (IsClosedImmersion.lift_fac _ _ _)
  · rintro ⟨y, rfl⟩
    exact I.ker_subschemeι.ge.trans (Scheme.Hom.le_ker_comp y.left I.subschemeι)

end GlobalTheory.TrivSubscheme
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeLocallyTrivialProductLineBuStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedSubscheme_locallyTrivial_product_lineBundle : GlobalFnsSt → ∀ (R : Type) [CommRing R] (T B : Over (Spec (CommRingCat.of R))) [GrpObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ F : LB (T ⊗ B).left, F.IsLB → ∃ (H : Over (Spec (CommRingCat.of R))) (j : H ⟶ T), IsClosedImmersion j.left ∧ ∀ (T' : Over (Spec (CommRingCat.of R))) (x : T' ⟶ T), (∀ p : T'.left, ∃ U : T'.left.Opens, p ∈ U ∧ Triv ((F.pull (x ▷ B).left).pull ((fst T' B).left ⁻¹ᵁ U).ι)) ↔ ∃ y : T' ⟶ H, y ≫ j = x := by
  first | exact @GlobalTheory.TrivSubscheme.exists_closed_locTriv | exact GlobalTheory.TrivSubscheme.exists_closed_locTriv | (intros; apply GlobalTheory.TrivSubscheme.exists_closed_locTriv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationPolarisedAbelianSchemesIso
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationPolarisedAbelianSchemesIso
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnifCompare

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem gm_eq_of_flat_surjective {X Y : Scheme.{0}} (π : X ⟶ Y) [Flat π] [Surjective π]
    {U V : Y.Opens} (a : Γ(Y, U)ˣ) (b : Γ(Y, V)ˣ)
    (h : ∀ x : X, π x ∈ U → π x ∈ V → gm π x U a = gm π x V b)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (hU : r z ∈ U) (hV : r z ∈ V) :
    gm r z U a = gm r z V b := by
  have e : pullU π (U ⊓ V) (res inf_le_left a) = pullU π (U ⊓ V) (res inf_le_right b) := by
    apply unit_ext
    intro x hx
    have hx' : π x ∈ U ⊓ V := hx
    have h₁ := gm_pull (𝟙 X) π x (U ⊓ V) hx' (res inf_le_left a)
    have h₂ := gm_pull (𝟙 X) π x (U ⊓ V) hx' (res inf_le_right b)
    rw [Category.id_comp] at h₁ h₂
    exact h₁.trans ((gm_res π x _ hx' a).trans ((h x hx'.1 hx'.2).trans
      ((gm_res π x _ hx' b).symm.trans h₂.symm)))
  have e' : (res inf_le_left a : Γ(Y, U ⊓ V)ˣ) = res inf_le_right b :=
    Units.ext (FunDescent.app_injective π (U ⊓ V) (congrArg Units.val e))
  have hz : r z ∈ U ⊓ V := ⟨hU, hV⟩
  exact (gm_res r z _ hz a).symm.trans ((congrArg (gm r z _) e').trans (gm_res r z _ hz b))

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}


omit [IsDomain R] in
theorem trans_comp_proj (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

variable {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem trans_comp_q (e : ℕ) :
    thickMap R I e G ≫ (U.gt (e + 1)).q.left = (U.gt e).q.left ≫ thickMap R I e D.toPre.P.A := by
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans ((U.gt_q e).trans
      ((congrArg ((U.gt e).q.left ≫ ·) (trans_comp_proj e D.toPre.P.A).symm).trans
        (Category.assoc _ _ _).symm))
  · have h₁ : (U.gt (e + 1)).q.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w (U.gt (e + 1)).q
    have h₀ : (U.gt e).q.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w (U.gt e).q
    have k : ∀ B : Over (Spec (CommRingCat.of R)), thickMap R I e B ≫ pullback.snd _ _ =
        pullback.snd _ _ ≫ thickTrans R I e := fun B => pullback.lift_snd _ _ _
    exact (Category.assoc _ _ _).trans ((congrArg (thickMap R I e G ≫ ·) h₁).trans ((k G).trans
      ((congrArg (· ≫ thickTrans R I e) h₀.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg ((U.gt e).q.left ≫ ·) (k _).symm).trans (Category.assoc _ _ _).symm)))))

theorem gw_trans (e : ℕ) (y : (thickObj R I e G).left) (jM : D.toPre.P.L.ι) (jL : U.LG.L.ι)
    (hM : (U.gt e).pG.left y ∈ D.toPre.P.L.U jM) (hL : (fstG I e G).left y ∈ U.LG.L.U jL) :
    gw (U.w (e + 1)) (thickMap R I e G) y jM (fun _ => jL) = gw (U.w e) (𝟙 _) y jM (fun _ => jL) := by
  have hM' : (U.gt (e + 1)).pG.left (thickMap R I e G y) ∈ D.toPre.P.L.U jM :=
    (congrArg (fun g => g y ∈ D.toPre.P.L.U jM) (U.gt_q e)).mpr hM
  have hL' : (fstG I (e + 1) G).left (thickMap R I e G y) ∈ U.LG.L.U jL :=
    (congrArg (fun g => g y ∈ U.LG.L.U jL) (trans_comp_proj e G)).mpr hL
  have hm : y ∈ thickMap R I e G ⁻¹ᵁ ((D.toPre.P.L.pull (U.gt (e + 1)).pG.left).U (fun _ => jM) ⊓
        (U.LG.L.pull (fstG I (e + 1) G).left).U (fun _ => jL)) ⊓
      ((D.toPre.P.L.pull (U.gt e).pG.left).U (fun _ => jM) ⊓
        (U.LG.L.pull (fstG I e G).left).U (fun _ => jL)) :=
    ⟨⟨mem_pull.2 hM', mem_pull.2 hL'⟩, mem_pull.2 hM, mem_pull.2 hL⟩
  have H := congrArg (gm (𝟙 _) y _)
    (U.w_compat e (fun _ => jM, fun _ => jL) _ inf_le_left inf_le_right)
  have h₁ := gm_pull (𝟙 _) (thickMap R I e G) y _ hm.1 ((U.w (e + 1)).s (fun _ => jM, fun _ => jL))
  rw [Category.id_comp] at h₁
  exact h₁.symm.trans ((gm_res (𝟙 _) y inf_le_left hm _).symm.trans
    (H.trans (gm_res (𝟙 _) y inf_le_right hm _)))

end GlobalTheory.UnifCompare

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor UnifCompare

theorem unifPre_polarised_iso :
    GlobalFnsSt → SecBaseChangeSt → AmpleSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (wL : LB.Iso U'.LG.L (U.LG.L.pull (𝟙 G.left))) (he : eSec G ≫ 𝟙 G.left = 𝟙 _ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) U'.LG.rig (rigPullOf (𝟙 G.left) (𝟙 _) he U.LG.L U.LG.rig) → ∃ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso D'.toPre.P.L (D.toPre.P.L.pull Φ.hom.left)), (w.IsGen ∧ ∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) r z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I e G).left) z jL jL')) := by
  intro hGF hS hA R _ _ _ I hR D D' A A' G _ _ hG U U' wL he hgen hrig
  choose β hβm hβ using unifPre_abelianPart_iso R I hR D D' A A' G hG U U'
  choose v hvg hv using fun e =>
    T.uniformisation_polarisations_agree_at_level hGF R I hR D D' A A' G hG U U' wL he hgen hrig e (β e) (hβm e) (hβ e)
  have hβl : ∀ e, (U'.gt e).q.left ≫ (β e).hom.left = (U.gt e).q.left := fun e =>
    congrArg (·.left) (hβ e)
  have hp : ∀ e, (U'.gt e).q.left ≫ (β e).hom.left ≫ (fstG I e D.toPre.P.A).left =
      (U.gt e).pG.left := fun e =>
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (fstG I e D.toPre.P.A).left) (hβl e))
  have hc : ∀ e, thickMap R I e D'.toPre.P.A ≫ (β (e + 1)).hom.left =
      (β e).hom.left ≫ thickMap R I e D.toPre.P.A := by
    intro e
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    have : Epi (U'.gt e).q.left := Flat.epi_of_flat_of_surjective _
    rw [← cancel_epi (U'.gt e).q.left, ← Category.assoc, ← trans_comp_q, Category.assoc, hβl,
      trans_comp_q, ← Category.assoc, hβl]
  obtain ⟨hN, -, -, hC⟩ := hR
  obtain ⟨Φ, w, hw, H⟩ := T.exists_iso_of_compatible_abelianThickenings hS hA R I D.toPre.P D'.toPre.P β v hvg hc (by
    intro e Z r z j j' hj hj'
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    have hm : ∀ y : (thickObj R I e D'.toPre.P.A).left,
        y ∈ (D.toPre.P.L.pull ((β e).hom.left ≫ (fstG I e D.toPre.P.A).left)).U (fun _ => j) ⊓
          (D'.toPre.P.L.pull (fstG I e D'.toPre.P.A).left).U (fun _ => j') →
        thickMap R I e D'.toPre.P.A y ∈
          (D.toPre.P.L.pull ((β (e + 1)).hom.left ≫ (fstG I (e + 1) D.toPre.P.A).left)).U (fun _ => j) ⊓
          (D'.toPre.P.L.pull (fstG I (e + 1) D'.toPre.P.A).left).U (fun _ => j') := by
      intro y hy
      have k : thickMap R I e D'.toPre.P.A ≫ (β (e + 1)).hom.left ≫ (fstG I (e + 1) D.toPre.P.A).left =
          (β e).hom.left ≫ (fstG I e D.toPre.P.A).left :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (fstG I (e + 1) D.toPre.P.A).left) (hc e)).trans
          ((Category.assoc _ _ _).trans (congrArg ((β e).hom.left ≫ ·) (trans_comp_proj e _))))
      exact ⟨mem_pull.2 ((congrArg (fun g => g y ∈ D.toPre.P.L.U j) k).mpr (mem_pull.1 hy.1)),
        mem_pull.2 ((congrArg (fun g => g y ∈ D'.toPre.P.L.U j') (trans_comp_proj e _)).mpr
          (mem_pull.1 hy.2))⟩
    have hz : r z ∈ (D.toPre.P.L.pull ((β e).hom.left ≫ (fstG I e D.toPre.P.A).left)).U (fun _ => j) ⊓
          (D'.toPre.P.L.pull (fstG I e D'.toPre.P.A).left).U (fun _ => j') :=
      ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
    refine (gm_pull r _ z _ (hm _ hz) _).symm.trans
      (gm_eq_of_flat_surjective (U'.gt e).q.left _ _ (fun x _ hx => ?_) r z (hm _ hz) hz)
    refine (gm_pull _ _ x _ (hm _ hx) _).trans ?_
    obtain ⟨jL, hL⟩ := exists_chart U.LG.isLB ((fstG I e G).left x)
    obtain ⟨jL', hL'⟩ := exists_chart U'.LG.isLB ((fstG I e G).left x)
    have hM : (U.gt e).pG.left x ∈ D.toPre.P.L.U j :=
      (congrArg (fun g => g x ∈ D.toPre.P.L.U j) (hp e)).mp (mem_pull.1 hx.1)
    have hM' : (U'.gt e).pG.left x ∈ D'.toPre.P.L.U j' := mem_pull.1 hx.2
    have h₀ := hv e _ (𝟙 _) x j j' jL jL' hM hM' hL hL'
    have h₁ := hv (e + 1) _ (thickMap R I e G) x j j' jL jL'
      ((congrArg (fun g => g x ∈ D.toPre.P.L.U j) (U.gt_q e)).mpr hM)
      ((congrArg (fun g => g x ∈ D'.toPre.P.L.U j') (U'.gt_q e)).mpr hM')
      ((congrArg (fun g => g x ∈ U.LG.L.U jL) (trans_comp_proj e G)).mpr hL)
      ((congrArg (fun g => g x ∈ U'.LG.L.U jL') (trans_comp_proj e G)).mpr hL')
    rw [gw_trans U' e x j' jL' hM' hL', gw_trans U e x j jL hM hL, trans_comp_q, trans_comp_proj] at h₁
    rw [Category.id_comp, Category.id_comp] at h₀
    exact mul_right_cancel (h₁.trans h₀.symm))
  refine ⟨Φ, w, hw, fun e => ⟨?_, fun Z r z jM jM' jL jL' hM hM' hL hL' => ?_⟩⟩
  · exact (Category.assoc _ _ _).trans ((congrArg ((U'.gt e).q.left ≫ ·) (H e).1).trans (hp e))
  · have h := (H e).2 Z (r ≫ (U'.gt e).q.left) z jM jM'
      ((congrArg (fun g => g (r z) ∈ D.toPre.P.L.U jM) (hp e)).mpr hM) hM'
    rw [Category.assoc] at h
    exact (congrArg (· * _) h).trans (hv e Z r z jM jM' jL jL' hM hM' hL hL')

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationPolarisedAbelianSchemesIsoStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_polarised_abelianSchemes_iso : GlobalFnsSt → SecBaseChangeSt → AmpleSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (wL : LB.Iso U'.LG.L (U.LG.L.pull (𝟙 G.left))) (he : eSec G ≫ 𝟙 G.left = 𝟙 _ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) U'.LG.rig (rigPullOf (𝟙 G.left) (𝟙 _) he U.LG.L U.LG.rig) → ∃ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso D'.toPre.P.L (D.toPre.P.L.pull Φ.hom.left)), (w.IsGen ∧ ∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) r z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I e G).left) z jL jL')) := by
  first | exact @GlobalTheory.unifPre_polarised_iso | exact GlobalTheory.unifPre_polarised_iso | (intros; apply GlobalTheory.unifPre_polarised_iso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSectionLinearCombinationOfCompatibleThicke
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSectionLinearCombinationOfCompatibleThicke
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SecAlgLinComb
open GlobalTheory.CompleteBaseExpansion GlobalTheory.BaseExpansionExists

theorem exists_sec_linComb : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : Over (Spec (CommRingCat.of R))), Smooth Y.hom → IsProjBy Y.hom → ∀ (W : Scheme.{0}) (L : LB W) (K : Type) [Fintype K] (φ : K → (Y.left ⟶ W)) (ε : K → ℤ) (φ' : ∀ e, K → ((thickObj R I e Y).left ⟶ W)), L.IsLB → (∀ e k, pullback.fst Y.hom (thick R I e) ≫ φ k = φ' e k) → ∀ f : ∀ e, LB.Sec (LB.LinComb L (φ' e) ε), (∀ e z J, Good L z J → sval (f (e + 1)) (thickMap R I e Y) z J = sval (f e) (𝟙 _) z J) → ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e Y).left) (z : Z) (J), Good L z J → sval s (r ≫ pullback.fst Y.hom (thick R I e)) z J = sval (f e) r z J := by
  intro R _ _ I hI Y hsm hp W L K _ φ ε φ' hL hφ f hf
  obtain rfl : φ' = fun e k => (fstG I e Y).left ≫ φ k := funext fun e => funext fun k => (hφ e k).symm
  choose f' hf' using fun e => exists_in (φ := φ) (fstG I e Y).left (f e)
  obtain ⟨s', hs', -⟩ := GlobalTheory.SecAlg.existsUnique_sec R I hI Y hsm hp _ (DVR.linComb_isLB _ hL _ _) f'
    fun e z J hJ => by
      refine (hf' _ _ _ z _ (hJ.mem (fun _ : PUnit => (fstG I (e + 1) Y).left) _)).trans
        (Eq.trans ?_ (hf' _ _ _ z _ (hJ.mem (fun _ : PUnit => (fstG I e Y).left) _)).symm)
      have E : thickMap R I e Y ≫ (fstG I (e + 1) Y).left = 𝟙 _ ≫ (fstG I e Y).left :=
        ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).trans (Category.id_comp _).symm
      beta_reduce
      rw [E]
      exact gs_eq_of_sval hL _ _ _ _ (fun i => (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ φ i) E).trans (Category.assoc _ _ _))) z (hf e z) _
        (pull_le _ _ (hJ.mem (fun _ : PUnit => (fstG I e Y).left) _))
  obtain ⟨s₁, hs₁⟩ := exists_out (𝟙 _) s'
  obtain ⟨s, hs⟩ := exists_sec hL (φ' := φ) (ε' := ε)
    (fun U _ h => by simp only [Category.id_comp]) s₁
  have key : ∀ e z J, Good L z J → sval s (fstG I e Y).left z J = sval (f e) (𝟙 _) z J := by
    refine fun e z J hJ => (hs _ _ z J hJ).trans ((hs₁ _ _ z _ (hJ.mem _ _)).trans ?_)
    have hN : Good (LB.LinComb L φ ε) z (fun ψ i => J (ψ ≫ φ i)) :=
      fun ψ => hJ.mem _ ψ
    refine Eq.trans ?_ ((hs' e z _ hN).trans
      ((hf' _ _ _ z _ (hN.mem (fun _ : PUnit => (fstG I e Y).left) _)).trans ?_))
    · exact (sval_of s' _ z _ _ (fun _ => funext fun i => congrArg J (Category.assoc _ _ _))).symm
    · exact (sval_of (f e) _ z J _ (fun i => congrArg J (Category.assoc _ _ _).symm)).symm
  refine ⟨s, fun e Z r z J hJ => (sval_eq_of_id (key e) r z hJ).trans ?_⟩
  exact congrArg (fun p => sval (f e) p z J) (Category.comp_id _)

end GlobalTheory.SecAlgLinComb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSectionLinearCombinationOfCompatibleThickeStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_linearCombination_of_compatible_thickenings : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : Over (Spec (CommRingCat.of R))), Smooth Y.hom → IsProjBy Y.hom → ∀ (W : Scheme.{0}) (L : LB W) (K : Type) [Fintype K] (φ : K → (Y.left ⟶ W)) (ε : K → ℤ) (φ' : ∀ e, K → ((thickObj R I e Y).left ⟶ W)), L.IsLB → (∀ e k, pullback.fst Y.hom (thick R I e) ≫ φ k = φ' e k) → ∀ f : ∀ e, LB.Sec (LB.LinComb L (φ' e) ε), (∀ e z J, Good L z J → sval (f (e + 1)) (thickMap R I e Y) z J = sval (f e) (𝟙 _) z J) → ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e Y).left) (z : Z) (J), Good L z J → sval s (r ≫ pullback.fst Y.hom (thick R I e)) z J = sval (f e) r z J := by
  first | exact @GlobalTheory.SecAlgLinComb.exists_sec_linComb | exact GlobalTheory.SecAlgLinComb.exists_sec_linComb | (intros; apply GlobalTheory.SecAlgLinComb.exists_sec_linComb <;> assumption)
end
end
