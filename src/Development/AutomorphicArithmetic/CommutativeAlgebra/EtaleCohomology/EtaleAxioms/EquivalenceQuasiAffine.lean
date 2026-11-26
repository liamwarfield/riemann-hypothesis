module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLevelRepresentable
public import Development.EtaleCohomology.EtaleSheaves.DescentPf
public import Development.EtaleCohomology.EtaleSheaves.SecPrePf
public import Development.EtaleCohomology.EtaleSheaves.LocSHPf
public import Development.EtaleCohomology.EtaleSheaves.LeafMVVanishPf
public import Development.EtaleCohomology.EtaleSheaves.AffinePf
public import Development.EtaleCohomology.EtaleSheaves.TwGenNZACPf
public import Development.EtaleCohomology.EtaleSheaves.LZHensFinitePf
public import Development.EtaleCohomology.EtaleSheaves.TorSecPf

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.PrimMapComp
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.AcycQAPf

namespace LateralTheory.E.Deg0Pf

theorem exists_prim (q : ℕ) [NeZero q] (S : Type) [CommRing S] (hA : AIC S) (hq : IsUnit (q : S)) :
    Nonempty (Prim q S) := by
  obtain ⟨z, hz⟩ : ∃ z : S, (Polynomial.cyclotomic q S).eval z = 0 := by
    rcases subsingleton_or_nontrivial S with hs | hs
    · exact ⟨0, Subsingleton.elim _ _⟩
    · exact hA _ (Polynomial.cyclotomic.monic q S) (by
        rw [Polynomial.natDegree_cyclotomic]
        exact Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q)))
  refine ⟨⟨z, hq, ?_⟩⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hz

theorem prim_map_comp {q : ℕ} {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
    (ζ : Prim q A) : (ζ.map f).map g = ζ.map (g.comp f) := rfl

theorem rL_comp {S : Type} [CommRing S] (f g : S) :
    (rL f g).comp (algebraMap S (Localization.Away f)) = algebraMap S (Localization.Away (f * g)) := by
  ext a; exact IsLocalization.Away.awayToAwayRight_eq f g a

theorem rR_comp {S : Type} [CommRing S] (f g : S) :
    (rR f g).comp (algebraMap S (Localization.Away g)) = algebraMap S (Localization.Away (f * g)) := by
  ext a; exact IsLocalization.Away.awayToAwayLeft_eq g f a

theorem Deg0_of : LateralTheory.E.AcycQAPf.Deg0 := by
  intro hQ hH hL h9 q _ i S _ hS hq f g hfg c
  obtain ⟨e, he⟩ := hH h9 q i
  obtain ⟨ζ⟩ := exists_prim q S (hQ S hS).1 hq
  obtain ⟨a, b, hab⟩ := hL q S hS f g hfg ((e _ (ζ.map (algebraMap S (Localization.Away (f * g))))).symm c)
  refine ⟨e _ (ζ.map (algebraMap S (Localization.Away f))) a, e _ (ζ.map (algebraMap S (Localization.Away g))) b, ?_⟩
  rw [he, he, prim_map_comp, prim_map_comp, rL_comp, rR_comp, ← map_sub, ← hab, AddEquiv.apply_symm_apply]

end LateralTheory.E.Deg0Pf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.StdCoverPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.StdCoverPf

theorem mono_spMap {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B)
    [Mono (Spec.map (CommRingCat.ofHom φ))] : Mono (spMap φ) := by
  have h : Mono (yoneda.map (Spec.map (CommRingCat.ofHom φ))) := inferInstance
  haveI : ∀ X, Mono ((spMap φ).app X) := fun _ => h
  exact NatTrans.mono_of_mono_app _

abbrev Xs {S : Type} [CommRing S] (f g : S) (b : Bool) : Scheme.{0} :=
  Spec (CommRingCat.of (Localization.Away (bif b then f else g)))

abbrev ι {S : Type} [CommRing S] (f g : S) (b : Bool) : Xs f g b ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (bif b then f else g))))

theorem cover_mem {S : Type} [CommRing S] (f g : S) (hfg : Ideal.span {f, g} = ⊤) :
    Sieve.ofArrows (Xs f g) (ι f g) ∈ Scheme.etaleTopology.{0} (Spec (CommRingCat.of S)) := by
  apply Precoverage.generate_mem_toGrothendieck
  refine (Scheme.ofArrows_mem_precoverage_iff (P := @Etale) (f := ι f g)).2 ⟨fun pt => ?_, fun b => inferInstance⟩
  let p : PrimeSpectrum S := pt
  have hp : f ∉ p.asIdeal ∨ g ∉ p.asIdeal := by
    by_contra hc
    push_neg at hc
    have : Ideal.span {f, g} ≤ p.asIdeal := by
      rw [Ideal.span_le]; intro z hz
      rcases hz with rfl | hz
      · exact hc.1
      · rw [Set.mem_singleton_iff] at hz; exact hz ▸ hc.2
    rw [hfg] at this
    exact p.isPrime.ne_top (top_le_iff.mp this)
  rcases hp with h | h
  · have hm : p ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away f))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]; exact h
    obtain ⟨q, hq⟩ := hm
    exact ⟨true, q, hq⟩
  · have hm : p ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]; exact h
    obtain ⟨q, hq⟩ := hm
    exact ⟨false, q, hq⟩

theorem key (R : Type) [CommRing R] (S : Type) [CommRing S] (f g : S) (hfg : Ideal.span {f, g} = ⊤) {G : Shv R}
    (u v : (free R).obj (yoneda.obj (Spec (CommRingCat.of S))) ⟶ G)
    (hb : ∀ b, (free R).map (yoneda.map (ι f g b)) ≫ u = (free R).map (yoneda.map (ι f g b)) ≫ v) : u = v := by
  let adj := sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))
  apply (adj.homEquiv ((freeP R).obj (yoneda.obj (Spec (CommRingCat.of S)))) G).injective
  have hb' : ∀ b, (freeP R).map (yoneda.map (ι f g b)) ≫ adj.homEquiv _ G u =
      (freeP R).map (yoneda.map (ι f g b)) ≫ adj.homEquiv _ G v := by
    intro b
    have h0 : (presheafToSheaf _ _).map ((freeP R).map (yoneda.map (ι f g b))) ≫ u =
        (presheafToSheaf _ _).map ((freeP R).map (yoneda.map (ι f g b))) ≫ v := hb b
    have h1 := congrArg (adj.homEquiv _ G) h0
    erw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_left] at h1
    exact h1
  generalize adj.homEquiv _ G u = u' at hb' ⊢
  generalize adj.homEquiv _ G v = v' at hb' ⊢
  ext X : 2
  apply ModuleCat.free_hom_ext
  intro x0
  have hT := Scheme.etaleTopology.pullback_stable x0.down (cover_mem f g hfg)
  have e := G.property.hom_ext ⟨_, hT⟩
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} R) _ (u'.app X (ModuleCat.freeMk x0))))
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} R) _ (v'.app X (ModuleCat.freeMk x0)))) ?_
  · have := congrArg (fun e => e.hom 1) e
    simp only [ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul] at this
    exact this
  rintro ⟨W, k, hk⟩
  obtain ⟨Z, h, _, ⟨b⟩, hh⟩ := hk
  ext1
  apply LinearMap.ext_ring
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.toSpanSingleton_apply, one_smul]
  have hm : (((freeP R).obj (yoneda.obj (Spec (CommRingCat.of S)))).map k.op).hom (ModuleCat.freeMk x0) =
      (((freeP R).map (yoneda.map (ι f g b))).app (op W)).hom (ModuleCat.freeMk (ULift.up h)) := by
    simp only [freeP, ModuleCat.freeMk]
    erw [Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.mapDomain_single]
    change Finsupp.single (ULift.up (k ≫ x0.down)) _ = Finsupp.single (ULift.up (h ≫ ι f g b)) _
    rw [hh]
  change ((u'.app X ≫ (G.obj.map k.op)).hom (ModuleCat.freeMk x0)) =
    ((v'.app X ≫ (G.obj.map k.op)).hom (ModuleCat.freeMk x0))
  erw [← u'.naturality, ← v'.naturality]
  change (u'.app (op W)).hom ((((freeP R).obj (yoneda.obj (Spec (CommRingCat.of S)))).map k.op).hom (ModuleCat.freeMk x0)) =
    (v'.app (op W)).hom ((((freeP R).obj (yoneda.obj (Spec (CommRingCat.of S)))).map k.op).hom (ModuleCat.freeMk x0))
  rw [hm]
  change ((((freeP R).map (yoneda.map (ι f g b))) ≫ u').app (op W)).hom (ModuleCat.freeMk (ULift.up h)) =
    ((((freeP R).map (yoneda.map (ι f g b))) ≫ v').app (op W)).hom (ModuleCat.freeMk (ULift.up h))
  rw [hb' b]

theorem epi_cover (R : Type) [CommRing R] (S : Type) [CommRing S] (f g : S) (hfg : Ideal.span {f, g} = ⊤)
    (n : SimplexCategoryᵒᵖ) :
    Epi (biprod.desc ((free R).map ((spMap (algebraMap S (Localization.Away f))).app n))
      ((free R).map ((spMap (algebraMap S (Localization.Away g))).app n))) := by
  constructor
  intro G u v h
  have hf := congrArg (biprod.inl ≫ ·) h
  have hg := congrArg (biprod.inr ≫ ·) h
  simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc] at hf hg
  exact key R S f g hfg u v (fun b => by cases b; exacts [hg, hf])

end LateralTheory.E.StdCoverPf

open LateralTheory.E.StdCoverPf in
theorem LateralTheory.E.MVPf.StdCover_of : LateralTheory.E.MVPf.StdCover := by
  intro R _ S _ f g hfg
  exact ⟨mono_spMap _, mono_spMap _, epi_cover R S f g hfg⟩
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LCMapPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.LocallyConstantH0

namespace LateralTheory.E.LCMapPf

def TwNat : Prop := ∀ (q : ℕ) (i : ℤ) (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)),
  Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom)

def LCSep : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (B : Type) [CommRing B] (Y : Type)
  (φ : LocallyConstant (PrimeSpectrum B) Y) (a b : Sec F (Spec (CommRingCat.of B))),
  (∀ (V : Scheme.{0}) (g : V ⟶ Spec (CommRingCat.of B)) (c : Y), (∀ v : V, φ (g.base v) = c) → Sec.res g a = Sec.res g b) → a = b

def LCGlue : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (B : Type) [CommRing B] (Y : Type)
  (φ : LocallyConstant (PrimeSpectrum B) Y) (s : Y → Sec F (Spec (CommRingCat.of B))),
  ∃ t : Sec F (Spec (CommRingCat.of B)), ∀ (V : Scheme.{0}) (g : V ⟶ Spec (CommRingCat.of B)) (c : Y),
    (∀ v : V, φ (g.base v) = c) → Sec.res g t = Sec.res g (s c)

theorem twNat : TwNat := by
  intro q i V U g ζ
  have h := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op
  have h2 := congrArg (fun k => k.hom (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj Γ(U, ⊤))) h
  simp only [ModuleCat.hom_comp] at h2
  simp only [LinearMap.coe_comp] at h2
  unfold twGen ofRings.sec
  refine h2.symm.trans (congrArg ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom ?_)
  simp only [twF, Functor.comp_map]
  rw [ModuleCat.hom_ofHom]
  first
  | (erw [Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]; done)
  | (erw [Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]; rfl)
  | exact congrArg (Submodule.Quotient.mk (p := twRel q i _)) (Finsupp.mapDomain_single (f := Prim.map g.appTop.hom) (a := ζ) (b := (1 : ULift (ZMod q))))

theorem nsmul_val {q : ℕ} [NeZero q] (i : ℤ) (U : Scheme.{0}) (x : Sec (tw q i) U) (c : ZMod q) :
    c.val • x = (ULift.up c : ULift (ZMod q)) • x := by
  rw [← Nat.cast_smul_eq_nsmul (ULift (ZMod q))]
  congr 1
  ext
  exact (ULift.down_natCast _).trans (ZMod.natCast_zmod_val c)

def sG {q : ℕ} (i : ℤ) {B : Type} [CommRing B] (ζ : Prim q B) (c : ZMod q) : Sec (tw q i) (Spec (CommRingCat.of B)) :=
  (ULift.up c : ULift (ZMod q)) • twGen i (gam ζ)

theorem res_smul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (r : ULift R) (x : Sec F U) :
    Sec.res g (r • x) = r • Sec.res g x := by
  simp [Sec.res]

theorem res_add {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x + y) = Sec.res g x + Sec.res g y := by
  simp [Sec.res]

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  simp [Sec.res]

theorem res_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.res (𝟙 U) x = x := by
  simp [Sec.res]

def tG (hG : LCGlue) {q : ℕ} (i : ℤ) {B : Type} [CommRing B] (ζ : Prim q B) (φ : LocallyConstant (PrimeSpectrum B) (ZMod q)) :
    Sec (tw q i) (Spec (CommRingCat.of B)) :=
  Classical.choose (hG (ZMod q) (tw q i) B (ZMod q) φ (sG i ζ))

theorem tG_spec (hG : LCGlue) {q : ℕ} (i : ℤ) {B : Type} [CommRing B] (ζ : Prim q B)
    (φ : LocallyConstant (PrimeSpectrum B) (ZMod q)) (V : Scheme.{0}) (g : V ⟶ Spec (CommRingCat.of B)) (c : ZMod q)
    (h : ∀ v : V, φ (g.base v) = c) : Sec.res g (tG hG i ζ φ) = Sec.res g (sG i ζ c) :=
  Classical.choose_spec (hG (ZMod q) (tw q i) B (ZMod q) φ (sG i ζ)) V g c h

theorem tG_add (hG : LCGlue) (hS : LCSep) {q : ℕ} (i : ℤ) {B : Type} [CommRing B] (ζ : Prim q B)
    (φ ψ : LocallyConstant (PrimeSpectrum B) (ZMod q)) : tG hG i ζ (φ + ψ) = tG hG i ζ φ + tG hG i ζ ψ := by
  let χ : LocallyConstant (PrimeSpectrum B) (ZMod q × ZMod q) :=
    ⟨fun x => (φ x, ψ x), IsLocallyConstant.comp₂ φ.2 ψ.2 Prod.mk⟩
  refine hS (ZMod q) (tw q i) B _ χ _ _ ?_
  intro V g c hc
  have h1 : ∀ v : V, φ (g.base v) = c.1 := fun v => congrArg Prod.fst (hc v)
  have h2 : ∀ v : V, ψ (g.base v) = c.2 := fun v => congrArg Prod.snd (hc v)
  have h3 : ∀ v : V, (φ + ψ) (g.base v) = c.1 + c.2 := fun v => by
    show φ (g.base v) + ψ (g.base v) = _
    rw [h1, h2]
  rw [tG_spec hG i ζ _ V g _ h3, res_add, tG_spec hG i ζ _ V g _ h1, tG_spec hG i ζ _ V g _ h2, ← res_add]
  congr 1
  unfold sG
  rw [← add_smul]
  rfl

theorem LCMap_of_parts (hT : TwNat) (hS : LCSep) (hG : LCGlue) : LCMap := by
  intro q _ i
  refine ⟨fun B _ ζ => AddMonoidHom.mk' (tG hG i ζ) (tG_add hG hS i ζ), ?_, ?_⟩
  · intro B C _ _ f ζ φ
    change Sec.res _ (tG hG i ζ φ) = tG hG i (ζ.map f) (lcMap f φ)
    refine hS (ZMod q) (tw q i) C _ (lcMap f φ) _ _ ?_
    intro V g c hc
    have hc' : ∀ v : V, φ ((g ≫ Spec.map (CommRingCat.ofHom f)).base v) = c := fun v => by
      exact hc v
    rw [← res_comp, tG_spec hG i ζ φ V _ c hc', tG_spec hG i (ζ.map f) _ V g c hc]
    unfold sG
    rw [res_smul, res_smul, hT, hT]
    have hP : Prim.map (g ≫ Spec.map (CommRingCat.ofHom f)).appTop.hom (gam ζ) = Prim.map g.appTop.hom (gam (ζ.map f)) := by
      apply Subtype.ext
      change (g ≫ Spec.map (CommRingCat.ofHom f)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom ζ.1) =
        g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (f ζ.1))
      have hn := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      congr 1
      rw [← CommRingCat.comp_apply, ← hn]
      rfl
    rw [hP]
  · intro B _ ζ c
    change tG hG i ζ _ = _
    have h := tG_spec hG i ζ (LocallyConstant.const _ c) _ (𝟙 _) c (fun v => rfl)
    rw [res_id, res_id] at h
    rw [h, nsmul_val]
    rfl

def fibS (B : Type) [CommRing B] {Y : Type} (φ : LocallyConstant (PrimeSpectrum B) Y) : Sieve (Spec (CommRingCat.of B)) where
  arrows V g := ∃ c, ∀ v : V, φ (g.base v) = c
  downward_closed := by
    rintro V W g ⟨c, hc⟩ k
    exact ⟨c, fun w => hc (k.base w)⟩

theorem fibS_mem (B : Type) [CommRing B] {Y : Type} (φ : LocallyConstant (PrimeSpectrum B) Y) :
    fibS B φ ∈ Scheme.etaleTopology (Spec (CommRingCat.of B)) := by
  refine (Scheme.mem_grothendieckTopology_iff (P := @Etale)).mpr ?_
  let O : PrimeSpectrum B → (Spec (CommRingCat.of B)).Opens := fun x =>
    ⟨φ ⁻¹' {φ x}, φ.isLocallyConstant.isOpen_fiber _⟩
  refine ⟨Scheme.Cover.mkOfCovers (PrimeSpectrum B) (fun x => (O x).toScheme) (fun x => (O x).ι)
    (fun x => ⟨x, ⟨x, rfl⟩, by simp⟩), ?_⟩
  rintro _ _ ⟨x⟩
  refine ⟨φ x, fun v => ?_⟩
  have hv := v.2
  first
  | exact hv
  | (simp only [Scheme.Cover.mkOfCovers_f, Scheme.Opens.ι_apply]; exact hv)
  | (simp [O, Scheme.Cover.mkOfCovers_f] at hv ⊢; exact hv)

theorem isSheafT {R : Type} [CommRing R] (F : Shv R) :
    Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
  (isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose Scheme.etaleTopology (forget (ModuleCat.{1} (ULift.{1} R)))).obj F).property

theorem sec_empty {R : Type} [CommRing R] (F : Shv R) (Z : Scheme.{0}) [IsEmpty Z] (a b : Sec F Z) : a = b :=
  ((isSheafT F) _ (Scheme.bot_mem_grothendieckTopology Z)).isSeparatedFor.ext (fun _ _ h => h.elim)

theorem lcSep : LCSep := by
  intro R _ F B _ Y φ a b h
  exact ((isSheafT F) _ (fibS_mem B φ)).isSeparatedFor.ext (fun V g hg => h V g hg.choose hg.choose_spec)

theorem lcGlue : LCGlue := by
  intro R _ F B _ Y φ s
  let x : Presieve.FamilyOfElements (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) (fibS B φ).arrows :=
    fun V g hg => Sec.res g (s hg.choose)
  have key : ∀ (V : Scheme.{0}) (g : V ⟶ Spec (CommRingCat.of B)) (c d : Y), (∀ v : V, φ (g.base v) = c) →
      (∀ v : V, φ (g.base v) = d) → Sec.res g (s c) = Sec.res g (s d) := by
    intro V g c d hc hd
    by_cases hV : Nonempty V
    · obtain ⟨v⟩ := hV
      rw [← hc v, ← hd v]
    · have : IsEmpty V := not_nonempty_iff.1 hV
      exact sec_empty F V _ _
  have hx : x.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro V W g k hg
    change Sec.res (k ≫ g) (s _) = Sec.res k (Sec.res g (s _))
    rw [← res_comp]
    exact key W (k ≫ g) _ _ ((fibS B φ).downward_closed hg k).choose_spec (fun w => hg.choose_spec (k.base w))
  obtain ⟨t, ht, -⟩ := (isSheafT F) _ (fibS_mem B φ) x hx
  refine ⟨t, fun V g c hc => ?_⟩
  have h1 := ht g ⟨c, hc⟩
  refine h1.trans (key V g _ _ (Exists.choose_spec (p := fun c => ∀ v : V, φ (g.base v) = c) ⟨c, hc⟩) hc)

theorem LCMap_of : LCMap := LCMap_of_parts twNat lcSep lcGlue

end LateralTheory.E.LCMapPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LCGoodPf
open LateralTheory.E.t_E1Cut

namespace LateralTheory.E.LCGoodPf

theorem closed_empty {C : Type} [CommRing C] {J : Ideal C} (hJ : J ≤ Ideal.jacobson ⊥)
    (Z : Set (PrimeSpectrum C)) (hZ : IsClosed Z)
    (h : ∀ z : PrimeSpectrum (C ⧸ J), PrimeSpectrum.comap (Ideal.Quotient.mk J) z ∉ Z) : Z = ∅ := by
  obtain ⟨I, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Z).1 hZ
  by_cases hI : I = ⊤
  · subst hI; simp
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  exfalso
  have hJM : J ≤ M := le_trans hJ (sInf_le ⟨bot_le, hM⟩)
  have hp : (⟨M, hM.isPrime⟩ : PrimeSpectrum C) ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J)) := by
    have hker : RingHom.ker (Ideal.Quotient.mk J) ≤ M := by rw [Ideal.mk_ker]; exact hJM
    have := hM.isPrime
    have hpr : (M.map (Ideal.Quotient.mk J)).IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
    refine ⟨⟨M.map (Ideal.Quotient.mk J), hpr⟩, ?_⟩
    ext1
    show Ideal.comap _ (Ideal.map _ M) = M
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    refine sup_eq_left.2 ?_
    rw [← RingHom.ker_eq_comap_bot]; exact hker
  obtain ⟨z, hz⟩ := hp
  apply h z
  rw [hz]
  exact hIM

theorem lcMap_apply {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {Y : Type}
    (φ : LocallyConstant (PrimeSpectrum A) Y) (z : PrimeSpectrum B) :
    lcMap f φ z = φ (PrimeSpectrum.comap f z) := rfl

theorem isClosed_ne {X Y : Type} [TopologicalSpace X] (a b : LocallyConstant X Y) :
    IsClosed {x | a x ≠ b x} := by
  have : IsLocallyConstant (fun x => (a x = b x : Prop)) :=
    IsLocallyConstant.comp₂ a.isLocallyConstant b.isLocallyConstant (fun u v => (u = v : Prop))
  have h2 := this.isClosed_fiber False
  convert h2 using 1
  ext x; simp

theorem LCGood_of : LCGood := by
  intro C _ J hG Y
  obtain ⟨hJ, hlift⟩ := hG
  constructor
  · intro a b hab
    have hZ := closed_empty hJ _ (isClosed_ne a b) (fun z hz => hz (by
      have := congrArg (fun φ => φ z) hab
      simpa [lcMap_apply] using this))
    ext x
    by_contra hx
    have : x ∈ ({x | a x ≠ b x} : Set _) := hx
    rw [hZ] at this; exact this
  · intro ψ

    have hU : ∀ y : Y, ∃ U : Set (PrimeSpectrum C), IsClopen U ∧
        PrimeSpectrum.comap (Ideal.Quotient.mk J) ⁻¹' U = ψ ⁻¹' {y} := by
      intro y
      obtain ⟨e, he, hF⟩ := PrimeSpectrum.isClopen_iff.1 (ψ.isLocallyConstant.isClopen_fiber y)
      obtain ⟨x, hx, hxe⟩ := hlift e he
      refine ⟨PrimeSpectrum.basicOpen x, PrimeSpectrum.isClopen_iff.2 ⟨x, hx, rfl⟩, ?_⟩
      have hF' : ψ ⁻¹' {y} = (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum (C ⧸ J))) := hF
      rw [hF', ← hxe]
      ext p
      simp
    choose U hUc hUp using hU
    have hmem : ∀ z y, PrimeSpectrum.comap (Ideal.Quotient.mk J) z ∈ U y ↔ ψ z = y := by
      intro z y
      have := congrArg (fun s => z ∈ s) (hUp y)
      simpa using this
    have hcover : ∀ x, ∃ y, x ∈ U y := by
      have hE := closed_empty hJ (⋃ y, U y)ᶜ
        (isOpen_iUnion (fun y => (hUc y).isOpen)).isClosed_compl
        (fun z hz => hz (Set.mem_iUnion.2 ⟨ψ z, (hmem z _).2 rfl⟩))
      intro x
      by_contra hx
      push Not at hx
      have : x ∈ (⋃ y, U y)ᶜ := by simpa using hx
      rw [hE] at this
      exact this
    have huniq : ∀ x y y', x ∈ U y → x ∈ U y' → y = y' := by
      intro x y y' h1 h2
      by_contra hne
      have := closed_empty hJ (U y ∩ U y') ((hUc y).isClosed.inter (hUc y').isClosed)
        (fun z hz => hne (((hmem z y).1 hz.1).symm.trans ((hmem z y').1 hz.2)))
      have hx : x ∈ U y ∩ U y' := ⟨h1, h2⟩
      rw [this] at hx; exact hx
    classical
    let g : PrimeSpectrum C → Y := fun x => Classical.choose (hcover x)
    have hg : ∀ x y, g x = y ↔ x ∈ U y := by
      intro x y
      constructor
      · rintro rfl; exact Classical.choose_spec (hcover x)
      · intro h; exact huniq x _ _ (Classical.choose_spec (hcover x)) h
    have hgl : IsLocallyConstant g := by
      rw [IsLocallyConstant.iff_isOpen_fiber]
      intro y
      have : g ⁻¹' {y} = U y := by ext x; simp [hg]
      rw [this]; exact (hUc y).isOpen
    refine ⟨⟨g, hgl⟩, ?_⟩
    ext z
    rw [lcMap_apply]
    exact (hg _ _).2 ((hmem z _).2 rfl)

end LateralTheory.E.LCGoodPf
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.EtLiftPf
noncomputable section
open MvPolynomial

namespace LateralTheory.E.EtLiftPf

set_option linter.style.haveILetI false

theorem EtLift_of : LateralTheory.E.t_E1Cut.EtLift := by
  intro T S C _ _ _ _ _ π hπ
  letI : Algebra T S := π.toAlgebra
  letI : Algebra T C := ((algebraMap S C).comp π).toAlgebra
  haveI : IsScalarTower T S C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨ι, σ, _, _, P, hP⟩ := (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.1 ‹_›).out
  haveI : P.HasCoeffs T := ⟨fun x _ => hπ x⟩
  let M := P.ModelOfHasCoeffs T
  let P0 := P.toPreSubmersivePresentation.ofHasCoeffs T
  let J : M := P0.jacobian
  let C' := Localization.Away J
  let Q := Algebra.PreSubmersivePresentation.localizationAway C' J
  let R0 := Q.comp P0
  have hJu : IsUnit (algebraMap M C' J) := IsLocalization.Away.algebraMap_isUnit J
  have hJ : R0.jacobian = algebraMap M C' J * algebraMap M C' J := by
    simp only [R0, Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian, Q,
      Algebra.PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
    rfl
  let R1 : Algebra.SubmersivePresentation T C' (Unit ⊕ ι) (Unit ⊕ σ) :=
    { R0 with jacobian_isUnit := by rw [hJ]; exact hJu.mul hJu }
  have hdim : R1.dimension = 0 := by
    have := Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension Q P0
    have hQ : Q.dimension = 0 := Algebra.Presentation.localizationAway_dimension_zero J
    have hP0 : P0.dimension = 0 := hP
    exact this.trans (by rw [hQ, hP0])
  haveI : Algebra.Etale T C' := by
    haveI := R1.isStandardSmoothOfRelativeDimension hdim
    infer_instance

  let φM : M →ₐ[T] C := Ideal.Quotient.liftₐ _ (MvPolynomial.aeval P.val) (by
    intro a ha
    have hle : Ideal.span (Set.range (P.relationOfHasCoeffs T)) ≤
        RingHom.ker (MvPolynomial.aeval (R := T) P.val) := by
      rw [Ideal.span_le]; rintro _ ⟨r, rfl⟩
      exact P.toPresentation.aeval_val_relationOfHasCoeffs T r
    exact hle ha)
  have hφmk : ∀ p : MvPolynomial ι T, φM (Ideal.Quotient.mk _ p) = MvPolynomial.aeval P.val p :=
    fun p => rfl
  have hφJ : φM J = P.jacobian := by
    classical
    cases nonempty_fintype σ
    rw [← P.aeval_jacobianOfHasCoeffs T]
    show φM P0.jacobian = _
    rw [P0.jacobian_eq_jacobiMatrix_det]
    unfold Algebra.SubmersivePresentation.jacobianOfHasCoeffs
    exact (hφmk _).trans (by congr 1; convert rfl)
  let ρ : C' →+* C := IsLocalization.Away.lift J (hφJ ▸ P.jacobian_isUnit)
  have hρM : ∀ m : M, ρ (algebraMap M C' m) = φM m := fun m => IsLocalization.lift_eq _ m
  refine ⟨C', inferInstance, inferInstance, ρ, inferInstance, ?_, ?_, ?_⟩
  · intro c
    obtain ⟨q, hq⟩ := MvPolynomial.map_surjective π hπ (P.σ c)
    refine ⟨algebraMap M C' (Ideal.Quotient.mk _ q), ?_⟩
    rw [hρM, hφmk, ← MvPolynomial.aeval_map_algebraMap S]
    change MvPolynomial.aeval P.val (MvPolynomial.map π q) = c
    rw [hq, P.aeval_val_σ]
  · ext t
    show ρ (algebraMap T C' t) = _
    rw [IsScalarTower.algebraMap_apply T M C', hρM, AlgHom.commutes]
    rfl
  · let K : Ideal C' := (RingHom.ker π).map (algebraMap T C')
    have hT : ∀ t, ρ (algebraMap T C' t) = algebraMap S C (π t) := by
      intro t; rw [IsScalarTower.algebraMap_apply T M C', hρM, AlgHom.commutes]; rfl
    apply le_antisymm
    swap
    · rw [Ideal.map_le_iff_le_comap]
      intro t ht
      rw [Ideal.mem_comap, RingHom.mem_ker, hT, RingHom.mem_ker.1 ht, map_zero]
    let e := RingHom.quotientKerEquivOfSurjective hπ
    let θ : S →+* C' ⧸ K :=
      (Ideal.quotientMap K (algebraMap T C') Ideal.le_comap_map).comp e.symm.toRingHom
    have hθ : ∀ t, θ (π t) = Ideal.Quotient.mk K (algebraMap T C' t) := by
      intro t
      have : e.symm (π t) = Ideal.Quotient.mk _ t := by
        rw [RingEquiv.symm_apply_eq]; rfl
      show Ideal.quotientMap K (algebraMap T C') Ideal.le_comap_map (e.symm (π t)) = _
      rw [this, Ideal.quotientMap_mk]
    let xv : ι → C' ⧸ K := fun i => Ideal.Quotient.mk K (algebraMap M C' (Ideal.Quotient.mk _ (X i)))
    let χ : MvPolynomial ι S →+* C' ⧸ K := MvPolynomial.eval₂Hom θ xv
    have hkey : ∀ q : MvPolynomial ι T, χ (MvPolynomial.map π q) =
        Ideal.Quotient.mk K (algebraMap M C' (Ideal.Quotient.mk _ q)) := by
      intro q
      have h2 : χ.comp (MvPolynomial.map π) =
          ((Ideal.Quotient.mk K).comp (algebraMap M C')).comp (Ideal.Quotient.mk _) := by
        apply MvPolynomial.ringHom_ext
        · intro t
          simp only [RingHom.comp_apply, MvPolynomial.map_C, χ, MvPolynomial.coe_eval₂Hom,
            MvPolynomial.eval₂_C, hθ]
          rw [IsScalarTower.algebraMap_apply T M C']
          rfl
        · intro i
          simp [χ, xv]
      exact RingHom.congr_fun h2 q
    have hker : ∀ a ∈ P.ker, χ a = 0 := by
      intro a ha
      rw [← P.span_range_relation_eq_ker] at ha
      have hle : Ideal.span (Set.range P.relation) ≤ RingHom.ker χ := by
        rw [Ideal.span_le]; rintro _ ⟨r, rfl⟩
        rw [SetLike.mem_coe, RingHom.mem_ker, ← P.toPresentation.map_relationOfHasCoeffs T r]
        change χ (MvPolynomial.map π _) = 0
        rw [hkey, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self r)), map_zero, map_zero]
      exact hle ha
    let ψ : C →+* C' ⧸ K := (Ideal.Quotient.lift P.ker χ hker).comp P.quotientEquiv.symm.toRingHom
    have hψP : ∀ p, ψ (algebraMap P.Ring C p) = χ p := by
      intro p
      show Ideal.Quotient.lift P.ker χ hker (P.quotientEquiv.symm (algebraMap _ _ p)) = χ p
      rw [← P.quotientEquiv_mk, AlgEquiv.symm_apply_apply]
      rfl
    have hψ : ψ.comp ρ = Ideal.Quotient.mk K := by
      apply IsLocalization.ringHom_ext (Submonoid.powers J)
      apply Ideal.Quotient.ringHom_ext
      refine RingHom.ext fun q => ?_
      simp only [RingHom.comp_apply]
      rw [hρM, hφmk, ← MvPolynomial.aeval_map_algebraMap S, ← hkey, ← hψP,
        Algebra.Generators.algebraMap_apply]
      rfl
    intro z hz
    rw [RingHom.mem_ker] at hz
    have h3 := RingHom.congr_fun hψ z
    simp only [RingHom.comp_apply, hz, map_zero] at h3
    exact Ideal.Quotient.eq_zero_iff_mem.1 h3.symm
end LateralTheory.E.EtLiftPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.QAClosedPf
noncomputable section
open Polynomial GlobalTheory.EtC

namespace LateralTheory.E.QAClosedPf

open LateralTheory.E.t_E1Cut

theorem aic_of_surj {T S : Type} [CommRing T] [CommRing S] (π : T →+* S) (hT : AIC T)
    (hπ : Function.Surjective π) : AIC S := by
  intro p hp hdeg
  have hl : p ∈ lifts π := (lifts_iff_coeff_lifts p).2 fun n => hπ _
  obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hl hp
  obtain ⟨a, ha⟩ := hT q hqm (hqd ▸ hdeg)
  refine ⟨π a, ?_⟩
  rw [← hq, eval_map, eval₂_at_apply, ha, map_zero]

theorem aic_away {T : Type} [CommRing T] [IsDomain T] (hT : AIC T) (t : T) (ht : t ≠ 0) :
    AIC (Localization.Away t) := by
  classical
  have : IsDomain (Localization.Away t) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors ht)
  intro p hp hdeg
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (Submonoid.powers t)
    (p.support.image p.coeff)
  set c : Localization.Away t := algebraMap T _ b
  have hcu : IsUnit c := IsLocalization.map_units _ b
  have hl : p.scaleRoots c ∈ lifts (algebraMap T (Localization.Away t)) := by
    refine (lifts_iff_coeff_lifts _).2 fun i => ?_
    rw [coeff_scaleRoots]
    by_cases hi : i ∈ p.support
    · have hle : i ≤ p.natDegree := le_natDegree_of_mem_supp i hi
      rcases lt_or_eq_of_le hle with hlt | heq
      · obtain ⟨z, hz⟩ := hb _ (Finset.mem_image_of_mem _ hi)
        refine ⟨z * b ^ (p.natDegree - i - 1), ?_⟩
        rw [map_mul, hz, Algebra.smul_def, map_pow]
        rw [show c ^ (p.natDegree - i) = c * c ^ (p.natDegree - i - 1) by
          rw [← pow_succ']; congr 1; omega]
        simp only [c]
        ring
      · subst heq
        refine ⟨1, ?_⟩
        rw [hp.coeff_natDegree, Nat.sub_self, pow_zero, one_mul, map_one]
    · rw [Polynomial.notMem_support_iff.1 hi]
      exact ⟨0, by simp⟩
  obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hl ((monic_scaleRoots_iff c).2 hp)
  rw [natDegree_scaleRoots] at hqd
  obtain ⟨a, ha⟩ := hT q hqm (hqd ▸ hdeg)
  refine ⟨hcu.unit⁻¹ * algebraMap T _ a, ?_⟩
  have h1 : eval (algebraMap T _ a) (p.scaleRoots c) = 0 := by
    rw [← hq, eval_map, eval₂_at_apply, ha, map_zero]
  have h2 : algebraMap T (Localization.Away t) a = (RingHom.id _) c * (hcu.unit⁻¹ * algebraMap T _ a) := by
    rw [RingHom.id_apply, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
  rw [eval, h2, scaleRoots_eval₂_mul] at h1
  rw [eval]
  exact (mul_eq_zero.1 h1).resolve_left (by simpa using (hcu.pow _).ne_zero)

theorem QAClosed_of : QAClosed := by
  intro S _ hS
  obtain ⟨T, _, _, π, hT, hπ⟩ := hS
  refine ⟨aic_of_surj π hT hπ, ?_, ?_⟩
  · intro f
    obtain ⟨t, rfl⟩ := hπ f
    by_cases ht : t = 0
    · have hu : IsUnit (algebraMap S (Localization.Away (π t)) (π t)) :=
        IsLocalization.Away.algebraMap_isUnit _
      rw [show algebraMap S (Localization.Away (π t)) (π t) = 0 by rw [ht, map_zero, map_zero]] at hu
      have : Subsingleton (Localization.Away (π t)) := subsingleton_of_zero_eq_one (isUnit_zero_iff.1 hu)
      exact ⟨T, inferInstance, inferInstance, (algebraMap S _).comp π, hT, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
    · have : IsDomain (Localization.Away t) :=
        IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors ht)
      have : IsLocalization (Submonoid.map π (Submonoid.powers t)) (Localization.Away (π t)) := by
        rw [Submonoid.map_powers]; infer_instance
      exact ⟨Localization.Away t, inferInstance, inferInstance, _, aic_away hT t ht,
        IsLocalization.map_surjective_of_surjective (Submonoid.powers t) (Localization.Away t)
          (Localization.Away (π t)) hπ⟩
  · intro J
    exact ⟨T, inferInstance, inferInstance, (Ideal.Quotient.mk J).comp π, hT,
      (Ideal.Quotient.mk_surjective).comp hπ⟩

end LateralTheory.E.QAClosedPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.EqvQAPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.EqvQAPf

theorem prim_of_aic (q : ℕ) [NeZero q] (S : Type) [CommRing S] (hS : AIC S) (hq : IsUnit (q : S)) :
    Nonempty (Prim q S) := by
  rcases subsingleton_or_nontrivial S with hs | hs
  · exact ⟨⟨0, hq, Subsingleton.elim _ _⟩⟩
  have hm : ((Polynomial.cyclotomic q ℤ).map (Int.castRingHom S)).Monic :=
    (Polynomial.cyclotomic.monic q ℤ).map _
  have hd : 0 < ((Polynomial.cyclotomic q ℤ).map (Int.castRingHom S)).natDegree := by
    rw [(Polynomial.cyclotomic.monic q ℤ).natDegree_map, Polynomial.natDegree_cyclotomic]
    exact Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  obtain ⟨a, ha⟩ := hS _ hm hd
  exact ⟨⟨a, hq, by rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]; simpa using ha⟩⟩

theorem bij_of_sub {A B : Type*} [AddZeroClass A] [AddZeroClass B] [Subsingleton A] [Subsingleton B] (f : A →+ B) :
    Function.Bijective f :=
  ⟨fun x y _ => Subsingleton.elim x y, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

end LateralTheory.E.EqvQAPf

open LateralTheory.E.t_E1Cut in
theorem LateralTheory.E.t_E1Cut.EqvQA_of (hAcyc : AcycQA) (hQA : QAClosed) (hH0 : EtaleDegreeZeroCohomologyEquivLocallyConstantFunctions) (hLC : LCGood) : EqvQA := by
  intro h1 h9 hb1 hb2 q _ S _ J hS hJ hq i n
  have hqJ : IsUnit (q : S ⧸ J) := by simpa using hq.map (Ideal.Quotient.mk J)
  have hSJ : QA (S ⧸ J) := (hQA S hS).2.2 J
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · haveI := (h9 (ZMod q) (tw q i)).1 (sp S) n hn
    haveI := (h9 (ZMod q) (tw q i)).1 (sp (S ⧸ J)) n hn
    exact LateralTheory.E.EqvQAPf.bij_of_sub _
  · obtain ⟨ζ⟩ := LateralTheory.E.EqvQAPf.prim_of_aic q S (hQA S hS).1 hq
    obtain ⟨e, he⟩ := hH0 h9 q i
    have key : ∀ φ, pull _ (spMap (Ideal.Quotient.mk J)) (tw q i) 0 (e S ζ φ) =
        e (S ⧸ J) (ζ.map (Ideal.Quotient.mk J)) (lcMap (Ideal.Quotient.mk J) φ) :=
      fun φ => he S (S ⧸ J) (Ideal.Quotient.mk J) ζ φ
    have hcomp : (pull _ (spMap (Ideal.Quotient.mk J)) (tw q i) 0) =
        (e (S ⧸ J) (ζ.map (Ideal.Quotient.mk J))) ∘
          (fun φ => lcMap (Ideal.Quotient.mk J) φ) ∘ (e S ζ).symm := by
      funext x
      obtain ⟨φ, rfl⟩ := (e S ζ).surjective x
      simp only [Function.comp_apply, AddEquiv.symm_apply_apply]
      exact key φ
    rw [hcomp]
    exact (e _ _).bijective.comp ((hLC S J hJ (ZMod q)).comp (e S ζ).symm.bijective)
  · haveI := hAcyc h1 h9 hb1 hb2 q S hS hq n i hn
    haveI := hAcyc h1 h9 hb1 hb2 q (S ⧸ J) hSJ hqJ n i hn
    exact LateralTheory.E.EqvQAPf.bij_of_sub _
end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsOrthogonalIdempotentsIsDomainOfEtale
noncomputable section

open TensorProduct Polynomial

private theorem isIntegrallyClosed_of_AIC (T : Type) [CommRing T] [IsDomain T]
    (hT : GlobalTheory.EtC.AIC T) : IsIntegrallyClosed T := by
  rw [isIntegrallyClosed_iff (FractionRing T)]
  intro x hx
  obtain ⟨p, hp, hpx⟩ := hx
  induction h : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ d ih =>
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · subst h0
      have h1 : p = 1 := hp.natDegree_eq_zero.1 h
      simp [h1] at hpx
    · obtain ⟨a, ha⟩ := hT p hp (h ▸ hpos)
      obtain ⟨q, hq⟩ := dvd_iff_isRoot.2 ha
      have hqm : q.Monic := (monic_X_sub_C a).of_mul_monic_left (hq ▸ hp)
      have hdeg : p.natDegree = 1 + q.natDegree := by
        rw [hq, (monic_X_sub_C a).natDegree_mul hqm, natDegree_X_sub_C]
      rw [hq, eval₂_mul] at hpx
      rcases mul_eq_zero.1 hpx with h1 | h1
      · refine ⟨a, ?_⟩
        simp only [eval₂_sub, eval₂_X, eval₂_C] at h1
        exact (sub_eq_zero.1 h1).symm
      · exact ih q.natDegree (by omega) q hqm h1 rfl

private theorem exists_of_idem (T C : Type) [CommRing T] [IsDomain T] [IsIntegrallyClosed T]
    [CommRing C] [Algebra T C] [Algebra.Etale T C] (z : C ⊗[T] FractionRing T) (hz : z * z = z) :
    ∃ s : C, algebraMap C (C ⊗[T] FractionRing T) s = z := by
  have hint : IsIntegral C z := by
    refine ⟨X ^ 2 - X, monic_X_pow_sub (n := 2) (lt_of_le_of_lt degree_X_le (by norm_num)), ?_⟩
    simp [eval₂_sub, pow_two, hz]
  obtain ⟨t, ht⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth (R := T) (S := C)
    (B := FractionRing T)).2 ⟨z, hint⟩
  have ht' : Algebra.TensorProduct.map (AlgHom.id C C)
      (integralClosure T (FractionRing T)).val t = z := congrArg Subtype.val ht
  rw [← ht']
  clear ht ht'
  induction t with
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]⟩
  | tmul x y =>
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := T) y.2
    refine ⟨r • x, ?_⟩
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val, ← hr,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [Algebra.algebraMap_eq_smul_one, smul_tmul]

private theorem core (T C : Type) [CommRing T] [IsDomain T] [IsIntegrallyClosed T]
    [CommRing C] [Algebra T C] [Algebra.Etale T C] {n : ℕ}
    (g : C ⊗[T] FractionRing T ≃+* (Fin n → FractionRing T)) :
    ∃ (e : Fin n → C), CompleteOrthogonalIdempotents e ∧
      ∀ j, IsDomain (Localization.Away (e j)) := by
  classical
  let G : C →+* (Fin n → FractionRing T) :=
    g.toRingHom.comp (algebraMap C (C ⊗[T] FractionRing T))
  have hι : Function.Injective (algebraMap C (C ⊗[T] FractionRing T)) :=
    Algebra.TensorProduct.includeLeft_injective (S := T)
      (IsFractionRing.injective T (FractionRing T))
  have hG : Function.Injective G := g.injective.comp hι
  have hex : ∀ j : Fin n, ∃ s : C, G s = Pi.single j 1 := by
    intro j
    obtain ⟨s, hs⟩ := exists_of_idem T C (g.symm (Pi.single j 1)) (by
      apply g.injective
      rw [map_mul, g.apply_symm_apply, ← Pi.single_mul, one_mul])
    exact ⟨s, by simp [G, hs]⟩
  choose c hc using hex
  have hcoi : CompleteOrthogonalIdempotents c := by
    refine ⟨⟨fun i => hG ?_, fun i j hij => hG ?_⟩, hG ?_⟩
    · rw [map_mul, hc, ← Pi.single_mul, one_mul]
    · rw [map_mul, hc, hc, map_zero]
      ext k
      by_cases h : k = i
      · subst h; simp [Pi.single_eq_of_ne hij]
      · simp [Pi.single_eq_of_ne h]
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [map_sum, map_one]
        simp only [hc]
        exact Finset.univ_sum_single 1
  refine ⟨c, hcoi, fun j => ?_⟩
  have hidem : IsIdempotentElem (c j) := hcoi.idem j
  let φ : C →+* FractionRing T := (Pi.evalRingHom _ j).comp G
  have hφ : φ (c j) = 1 := by simp [φ, hc]
  have hu : IsUnit (φ (c j)) := by rw [hφ]; exact isUnit_one
  let ψ : Localization.Away (c j) →+* FractionRing T := IsLocalization.Away.lift (c j) hu
  have hψ : ∀ x, ψ (algebraMap C _ x) = φ x := fun x => IsLocalization.Away.lift_eq (c j) hu x
  have hsurj : Function.Surjective (algebraMap C (Localization.Away (c j))) :=
    IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem (c j) hidem
  have hone : algebraMap C (Localization.Away (c j)) (c j) = 1 :=
    (IsIdempotentElem.iff_eq_one_of_isUnit (IsLocalization.Away.algebraMap_isUnit (c j))).1
      (hidem.map _)
  have hinj : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨x, rfl⟩ := hsurj a
    rw [hψ] at ha
    have hx : x * c j = 0 := by
      apply hG
      rw [map_mul, hc, map_zero]
      ext k
      by_cases h : k = j
      · subst h
        simpa [φ] using ha
      · simp [Pi.single_eq_of_ne h]
    have := congrArg (algebraMap C (Localization.Away (c j))) hx
    rwa [map_mul, hone, mul_one, map_zero] at this
  exact hinj.isDomain ψ

theorem UpperTheory.exists_orthogonalIdempotents_isDomain_of_etale :
    ∀ (T C : Type) [CommRing T] [IsDomain T] [CommRing C] [Algebra T C] [Algebra.Etale T C], GlobalTheory.EtC.AIC T →
      ∃ (n : ℕ) (e : Fin n → C), CompleteOrthogonalIdempotents e ∧ ∀ j, IsDomain (Localization.Away (e j)) := by
  intro T C _ _ _ _ _ hT
  haveI := GlobalTheory.isAlgClosed_fractionRing_of_AIC T hT
  haveI := isIntegrallyClosed_of_AIC T hT
  let e0 := Algebra.FormallyEtale.equivPiOfIsSepClosed (FractionRing T) (FractionRing T ⊗[T] C)
  haveI := Algebra.FormallyUnramified.finite_of_free (FractionRing T) (FractionRing T ⊗[T] C)
  haveI : IsArtinianRing (FractionRing T ⊗[T] C) := isArtinian_of_tower (FractionRing T) inferInstance
  obtain ⟨n, ⟨eq⟩⟩ := Finite.exists_equiv_fin (PrimeSpectrum (FractionRing T ⊗[T] C))
  let g : C ⊗[T] FractionRing T ≃+* (Fin n → FractionRing T) :=
    ((Algebra.TensorProduct.comm T C (FractionRing T)).toRingEquiv.trans e0.toRingEquiv).trans
      (RingEquiv.piCongrLeft (fun _ : Fin n => FractionRing T) eq)
  obtain ⟨e, h1, h2⟩ := core T C g
  exact ⟨n, e, h1, h2⟩

end
end

namespace UpperTheory.Et.QuasiAffineEquivalence

theorem a0 : LateralTheory.E.t_E1Cut.QAClosed := LateralTheory.E.QAClosedPf.QAClosed_of
theorem a1 : LateralTheory.E.ZarLocalPf.LocSH := LateralTheory.E.LocSHPf.LocSH_of
theorem a2 : LateralTheory.E.ZarLocalPf.LocDiag := LateralTheory.E.LocDiagPf.LocDiag_of
theorem a3 : LateralTheory.E.t_E1Cut.ZarLocal := LateralTheory.E.ZarLocalPf.ZarLocal_of a1 a2
theorem a4 : LateralTheory.E.MVPf.MVSpc := LateralTheory.E.LeafMVVanishPf.mvSpc
theorem a5 : LateralTheory.E.MVPf.StdCover := LateralTheory.E.MVPf.StdCover_of
theorem a6 : LateralTheory.E.MVPf.StdPB := LateralTheory.E.MVPf.StdPB_of
theorem a7 : LateralTheory.E.t_E1Cut.MV := LateralTheory.E.t_E1Cut.MV_of a4 a5 a6
theorem a8 : LateralTheory.E.LocallyConstantH0.LCMap := LateralTheory.E.LCMapPf.LCMap_of
theorem a9 : LateralTheory.E.LCBijPf.TwGenNZAC := LateralTheory.E.TwGenNZACPf.TwGenNZAC_of
theorem a10 : LateralTheory.E.LCSurjPf.LocForm := LateralTheory.E.LocFormPf.LocForm_of
theorem a11 : LateralTheory.E.LCSurjPf.Descent := LateralTheory.E.DescentPf.Descent_of a9
theorem a12 : LateralTheory.E.LCBijPf.LCSurj := LateralTheory.E.LCSurjPf.LCSurj_of a10 a11
theorem a13 : LateralTheory.E.LocallyConstantH0.LCBij := LateralTheory.E.LCBijPf.LCBij_of a9 a12
theorem a14 : LateralTheory.E.t_E1Cut.EtaleDegreeZeroCohomologyEquivLocallyConstantFunctions := LateralTheory.E.LocallyConstantH0.localConstant_H0 a8 a13
theorem a15 : LateralTheory.E.t_E1Cut.EtLift := LateralTheory.E.EtLiftPf.EtLift_of
theorem a16 : LateralTheory.E.EtAICPf.Split := fun T C _ _ _ _ _ h => UpperTheory.exists_orthogonalIdempotents_isDomain_of_etale T C h
theorem a17 : LateralTheory.E.EtAICPf.DomOpen := LateralTheory.E.DomOpenPf.DomOpen_of
theorem a18 : LateralTheory.E.t_E1Cut.EtAIC := LateralTheory.E.EtAICPf.EtAIC_of a16 a17
theorem a19 : LateralTheory.E.FinEtSectionPf.Pieces := LateralTheory.E.PiecesPf.Pieces_of a15 a18
theorem a20 : LateralTheory.E.FinEtSectionPf.FinOpen := LateralTheory.E.FinOpenPf.FinOpen_of
theorem a21 : LateralTheory.E.FinEtSectionPf.Glue := LateralTheory.E.Gluing₂.Glue_of a15 a18
theorem a22 : LateralTheory.E.t_E1Cut.FinEtSection := LateralTheory.E.FinEtSectionPf.FinEtSection_of a15 a18 a19 a20 a21
theorem a23 : LateralTheory.E.TorEtPf.ProjF := LateralTheory.E.ProjFPf.projF
theorem a24 : LateralTheory.E.TorEtPf.ProjG := LateralTheory.E.ProjGPf.ProjG_of
theorem a25 : LateralTheory.E.LCSplitPf.TorEt := LateralTheory.E.TorEtPf.TorEt_of_proj a23 a24
theorem a26 : LateralTheory.E.LCSplitPf.TorSec := LateralTheory.E.TorSecPf.TorSec_of
theorem a27 : LateralTheory.E.t_E1Cut.LCSplit := LateralTheory.E.LCSplitPf.LCSplit_of_tor a22 a25 a26
theorem a28 : LateralTheory.E.AcycQAPf.Deg0 := LateralTheory.E.Deg0Pf.Deg0_of
theorem a29 : LateralTheory.E.CoverPf.EmptyVan := LateralTheory.E.EmptyVan₂.EmptyVan_of
theorem a30 : LateralTheory.E.AcycQAPf.Cover := LateralTheory.E.CoverPf.Cover_of a29
theorem a31 : LateralTheory.E.t_E1Cut.AcycQA := LateralTheory.E.AcycQAPf.AcycQA_of a0 a3 a7 a14 a27 a28 a30
theorem a32 : LateralTheory.E.t_E1Cut.LCGood := LateralTheory.E.LCGoodPf.LCGood_of
theorem a33 : LateralTheory.E.t_E1Cut.EqvQA := LateralTheory.E.t_E1Cut.EqvQA_of a31 a0 a14 a32

theorem intersectionNumber_baseChange : LateralTheory.E.t_E1Cut.EqvQA := a33

end UpperTheory.Et.QuasiAffineEquivalence
