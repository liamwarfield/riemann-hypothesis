module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceChainsMayerVietorisShortExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTensorEtaleSheafComplexPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMayerVietorisConnectingExact
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMayerVietorisConnectingExact
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.MayerVietoris

theorem cpull_add {R : Type} [CommRing R] {K L : Cx R} (f g : K ⟶ L) (I : Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    cpull (f + g) I n x = cpull f I n x + cpull g I n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [cpre_mk, cpre_mk, cpre_mk, ← CohomologyClass.mk_add]
  congr 1; apply Cocycle.ext; simp [zcomp, Cochain.ofHom_add, Cochain.add_comp]

theorem cpull_neg {R : Type} [CommRing R] {K L : Cx R} (f : K ⟶ L) (I : Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    cpull (-f) I n x = -cpull f I n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [cpre_mk, cpre_mk, ← CohomologyClass.mk_neg]
  congr 1; apply Cocycle.ext; simp [zcomp, Cochain.ofHom_neg, Cochain.neg_comp]

theorem cpull_comp {R : Type} [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ) (x : CohomologyClass M I n) :
    cpull (f ≫ g) I n x = cpull f I n (cpull g I n x) := (GlobalTheory.EtC.ZcFun.main R).2.1 f g I n x

theorem cpull_lift {R : Type} [CommRing R] {K L M : Cx R} (a : M ⟶ K) (b : M ⟶ L) (I : Cx R) (n : ℤ)
    (y : CohomologyClass (K ⊞ L) I n) :
    cpull (biprod.lift a b) I n y = cpull a I n (cpull biprod.inl I n y) + cpull b I n (cpull biprod.inr I n y) := by
  rw [biprod.lift_eq, cpull_add, cpull_comp, cpull_comp]

def mvS (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) : ShortComplex (Cx R) :=
  ShortComplex.mk (biprod.lift ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g)))
    (biprod.desc ((chains R).map f) ((chains R).map g)) (by
      let : HasPullback f g := HasLimitsOfShape.has_limit (cospan f g)
      rw [biprod.lift_desc, Preadditive.neg_comp, ← Functor.map_comp, ← Functor.map_comp,
        pullback.condition (C := Spc) (f := f) (g := g)]
      simp)

theorem mvS_exact (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (h : Cover2 R f g) :
    (mvS R f g).ShortExact := by
  obtain ⟨w, hw⟩ := GlobalTheory.T.etaleSpaceChains_mayerVietoris_shortExact R f g h
  exact hw

def mvMap (R : Type) [CommRing R] {U V E U' V' E' : Spc} (f : U ⟶ E) (g : V ⟶ E) (f' : U' ⟶ E') (g' : V' ⟶ E')
    (p : E ⟶ E') (u : U ⟶ U') (v : V ⟶ V') (hu : f ≫ p = u ≫ f') (hv : g ≫ p = v ≫ g') :
    mvS R f g ⟶ mvS R f' g' where
  τ₁ := (chains R).map (pullback.map f g f' g' u v p hu hv)
  τ₂ := biprod.map ((chains R).map u) ((chains R).map v)
  τ₃ := (chains R).map p
  comm₁₂ := by
    apply biprod.hom_ext <;> simp [mvS, ← Functor.map_comp]
  comm₂₃ := by
    apply biprod.hom_ext' <;> simp [mvS, ← Functor.map_comp, hu, hv]

end GlobalTheory.EtC.MayerVietoris
end

theorem GlobalTheory.EtC.mayerVietoris : ∀ (R : Type) [CommRing R] (F : Shv R), ∃ d : ∀ {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g → ∀ n : ℤ, H R (pullback f g) F n →+ H R E F (n + 1), (∀ {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (h : Cover2 R f g) (n : ℤ), (∀ a b, pull R (pullback.fst f g) F n a = pull R (pullback.snd f g) F n b ↔ ∃ x, pull R f F n x = a ∧ pull R g F n x = b) ∧ (∀ c, d f g h n c = 0 ↔ ∃ a b, c = pull R (pullback.fst f g) F n a - pull R (pullback.snd f g) F n b) ∧ ∀ x, (pull R f F (n + 1) x = 0 ∧ pull R g F (n + 1) x = 0) ↔ ∃ c, d f g h n c = x) ∧ ∀ {U V E U' V' E' : Spc} (f : U ⟶ E) (g : V ⟶ E) (f' : U' ⟶ E') (g' : V' ⟶ E') (p : E ⟶ E') (u : U ⟶ U') (v : V ⟶ V') (hu : f ≫ p = u ≫ f') (hv : g ≫ p = v ≫ g') (h : Cover2 R f g) (h' : Cover2 R f' g') (n : ℤ) c, pull R p F (n + 1) (d f' g' h' n c) = d f g h n (pull R (pullback.map f g f' g' u v p hu hv) F n c) := by
  intro R _ F
  obtain ⟨D, hex, hnat⟩ := GlobalTheory.T.hypercohomology_longExact_first_of_injective R (res R F) (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F).2.1
  refine ⟨fun f g h n => D (GlobalTheory.EtC.MayerVietoris.mvS R f g) (GlobalTheory.EtC.MayerVietoris.mvS_exact R f g h) n, ?_, ?_⟩
  · intro U V E f g h n
    obtain ⟨e1, e2, e3⟩ := hex _ (GlobalTheory.EtC.MayerVietoris.mvS_exact R f g h) n
    have bij := fun m => GlobalTheory.EtC.cpull_biprod_bijective R ((chains R).obj U) ((chains R).obj V) (res R F) m

    have hg : ∀ m (x : H R E F m), cpull biprod.inl (res R F) m (cpull (GlobalTheory.EtC.MayerVietoris.mvS R f g).g (res R F) m x) = pull R f F m x ∧
        cpull biprod.inr (res R F) m (cpull (GlobalTheory.EtC.MayerVietoris.mvS R f g).g (res R F) m x) = pull R g F m x := by
      intro m x
      constructor
      · refine (GlobalTheory.EtC.MayerVietoris.cpull_comp (K := (chains R).obj U) (L := (chains R).obj U ⊞ (chains R).obj V) biprod.inl (biprod.desc ((chains R).map f) ((chains R).map g)) _ m x).symm.trans ?_
        rw [biprod.inl_desc]; rfl
      · refine (GlobalTheory.EtC.MayerVietoris.cpull_comp (K := (chains R).obj V) (L := (chains R).obj U ⊞ (chains R).obj V) biprod.inr (biprod.desc ((chains R).map f) ((chains R).map g)) _ m x).symm.trans ?_
        rw [biprod.inr_desc]; rfl
    have hf : ∀ y, cpull (GlobalTheory.EtC.MayerVietoris.mvS R f g).f (res R F) n y =
        pull R (pullback.fst f g) F n (cpull biprod.inl (res R F) n y) - pull R (pullback.snd f g) F n (cpull biprod.inr (res R F) n y) := by
      intro y
      have := GlobalTheory.EtC.MayerVietoris.cpull_lift (K := (chains R).obj U) (L := (chains R).obj V) ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g)) (res R F) n y
      rw [GlobalTheory.EtC.MayerVietoris.cpull_neg] at this
      rw [sub_eq_add_neg]; exact this
    have k1 : ∀ y, (pull R (pullback.fst f g) F n (cpull biprod.inl (res R F) n y) - pull R (pullback.snd f g) F n (cpull biprod.inr (res R F) n y) = 0) ↔ ∃ x, cpull (GlobalTheory.EtC.MayerVietoris.mvS R f g).g (res R F) n x = y :=
      fun y => (Iff.of_eq (congrArg (· = 0) (hf y))).symm.trans (e1 y)
    refine ⟨?_, ?_, ?_⟩
    · intro a b
      obtain ⟨y, hy⟩ := (bij n).2 (a, b)
      simp only [Prod.mk.injEq] at hy
      obtain ⟨rfl, rfl⟩ := hy
      refine sub_eq_zero.symm.trans ((k1 y).trans ⟨?_, ?_⟩)
      · rintro ⟨x, rfl⟩; exact ⟨x, (hg n x).1.symm, (hg n x).2.symm⟩
      · rintro ⟨x, h1, h2⟩
        exact ⟨x, (bij n).1 (Prod.ext ((hg n x).1.trans h1) ((hg n x).2.trans h2))⟩
    · intro c
      show D (GlobalTheory.EtC.MayerVietoris.mvS R f g) (GlobalTheory.EtC.MayerVietoris.mvS_exact R f g h) n c = 0 ↔ _
      refine (e2 c).trans ⟨?_, ?_⟩
      · rintro ⟨y, rfl⟩; exact ⟨_, _, hf y⟩
      · rintro ⟨a, b, rfl⟩
        obtain ⟨y, hy⟩ := (bij n).2 (a, b)
        simp only [Prod.mk.injEq] at hy
        obtain ⟨rfl, rfl⟩ := hy
        exact ⟨y, hf y⟩
    · intro x
      show _ ↔ ∃ c, D (GlobalTheory.EtC.MayerVietoris.mvS R f g) (GlobalTheory.EtC.MayerVietoris.mvS_exact R f g h) n c = x
      refine Iff.trans ?_ (e3 x)
      constructor
      · rintro ⟨h1, h2⟩
        apply (bij (n + 1)).1
        exact Prod.ext (((hg (n + 1) x).1.trans h1).trans (map_zero _).symm) (((hg (n + 1) x).2.trans h2).trans (map_zero _).symm)
      · intro h0
        refine ⟨(hg (n + 1) x).1.symm.trans ?_, (hg (n + 1) x).2.symm.trans ?_⟩ <;> rw [h0] <;> exact map_zero _
  · intro U V E U' V' E' f g f' g' p u v hu hv h h' n c
    exact hnat _ _ _ _ (GlobalTheory.EtC.MayerVietoris.mvMap R f g f' g' p u v hu hv) n c
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMayerVietorisConnectingExactStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mayerVietoris_connecting_exact : ∀ (R : Type) [CommRing R] (F : Shv R), ∃ d : ∀ {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g → ∀ n : ℤ, H R (pullback f g) F n →+ H R E F (n + 1), (∀ {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (h : Cover2 R f g) (n : ℤ), (∀ a b, pull R (pullback.fst f g) F n a = pull R (pullback.snd f g) F n b ↔ ∃ x, pull R f F n x = a ∧ pull R g F n x = b) ∧ (∀ c, d f g h n c = 0 ↔ ∃ a b, c = pull R (pullback.fst f g) F n a - pull R (pullback.snd f g) F n b) ∧ ∀ x, (pull R f F (n + 1) x = 0 ∧ pull R g F (n + 1) x = 0) ↔ ∃ c, d f g h n c = x) ∧ ∀ {U V E U' V' E' : Spc} (f : U ⟶ E) (g : V ⟶ E) (f' : U' ⟶ E') (g' : V' ⟶ E') (p : E ⟶ E') (u : U ⟶ U') (v : V ⟶ V') (hu : f ≫ p = u ≫ f') (hv : g ≫ p = v ≫ g') (h : Cover2 R f g) (h' : Cover2 R f' g') (n : ℤ) c, pull R p F (n + 1) (d f' g' h' n c) = d f g h n (pull R (pullback.map f g f' g' u v p hu hv) F n c) := by
  first | (exact @GlobalTheory.EtC.mayerVietoris) | (exact GlobalTheory.EtC.mayerVietoris) | (intros; apply GlobalTheory.EtC.mayerVietoris  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleModuleSheafMapMonoEpiIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleModuleSheafMapMonoEpiIso
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.FreeMonoEpi

theorem freeP_map_mono (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q) [Mono f] : Mono ((freeP R).map f) := by
  rw [NatTrans.mono_iff_mono_app]
  intro U
  rw [ModuleCat.mono_iff_injective]
  have hf : Function.Injective (f.app U) := (mono_iff_injective (f.app U)).1 inferInstance
  have hu : Function.Injective (uliftFunctor.{1}.map (f.app U)) := by
    intro a b h; cases a; cases b; exact congrArg ULift.up (hf (congrArg ULift.down h))
  exact Finsupp.mapDomain_injective hu

theorem free_map_mono (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q) [Mono f] : Mono ((free R).map f) := by
  haveI := freeP_map_mono R f
  exact (presheafToSheaf _ _).map_mono ((freeP R).map f)

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res (k ≫ g) a = Sec.res k (Sec.res g a) := by
  simp [Sec.res]

theorem map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.map φ (Sec.res g a) = Sec.res g (Sec.map φ a) := by
  have := congrArg (fun h => ModuleCat.Hom.hom h a) (φ.hom.naturality g.op)
  simpa [Sec.map, Sec.res] using this

abbrev gsum (R : Type) [CommRing R] (P : PSh) (V : Scheme.{0}) (c : P.obj (op V) →₀ ULift.{1} R) : Sec ((free R).obj P) V :=
  c.sum fun x r => r • freeGen R P V x

theorem res_gsum (R : Type) [CommRing R] (P : PSh) {W V : Scheme.{0}} (k : W ⟶ V) (c : P.obj (op V) →₀ ULift.{1} R) :
    Sec.res k (gsum R P V c) = c.sum fun x r => r • freeGen R P W (P.map k.op x) := by
  simp only [gsum, Sec.res, map_finsuppSum, map_smul]
  refine Finsupp.sum_congr fun x _ => ?_
  congr 1
  exact (GlobalTheory.T.free_sections_ext_res_map R P ((free R).obj P)).2.2.1 W V k x

theorem res_gsum' (R : Type) [CommRing R] (P : PSh) {W V : Scheme.{0}} (k : W ⟶ V) (c : P.obj (op V) →₀ ULift.{1} R) :
    Sec.res k (gsum R P V c) = gsum R P W (Finsupp.mapDomain (P.map k.op) c) := by
  rw [res_gsum, gsum, Finsupp.sum_mapDomain_index (h := fun (x : P.obj (op W)) (r : ULift.{1} R) => r • freeGen R P W x)
    (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]

theorem map_gsum (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q) {V : Scheme.{0}} (c : P.obj (op V) →₀ ULift.{1} R) :
    Sec.map ((free R).map f) (gsum R P V c) = gsum R Q V (Finsupp.mapDomain (f.app (op V)) c) := by
  rw [gsum, gsum, Finsupp.sum_mapDomain_index (h := fun (x : Q.obj (op V)) (r : ULift.{1} R) => r • freeGen R Q V x)
    (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  simp only [Sec.map, map_finsuppSum, map_smul]
  refine Finsupp.sum_congr fun x _ => ?_
  congr 1
  exact (GlobalTheory.T.free_sections_ext_res_map R P ((free R).obj P)).2.2.2 Q f V x

theorem loc_all {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  GlobalTheory.T.etaleLocal_property_calculus_rules.1 U P h

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P) (hPQ : ∀ V g, P V g → Q V g) :
    Loc U Q :=
  GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 U P Q h hPQ

theorem loc_trans {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : Loc U fun V g => Loc V fun W k => P W (k ≫ g)) : Loc U P :=
  GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.2.1 U P h

theorem loc_fin {U : Scheme.{0}} {ι : Type} [Finite ι] (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : ∀ i, Loc U (P i)) : Loc U fun V g => ∀ i, P i V g :=
  GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.2.2.1 U ι P h

theorem free_map_epi (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q)
    (hs : ∀ U (y : Q.obj (op U)), Loc U fun V g => ∃ x, f.app (op V) x = Q.map g.op y) : Epi ((free R).map f) := by
  rw [(GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections R ((free R).map f)).2.2.1]
  intro U b
  apply loc_trans
  refine loc_mono ((GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R Q U).1 b) ?_
  rintro V g ⟨c, hc⟩
  have hl : Loc V fun W k => ∀ i : c.support, ∃ x, f.app (op W) x = Q.map k.op i.1 :=
    loc_fin (fun i : c.support => fun W k => ∃ x, f.app (op W) x = Q.map k.op i.1) (fun i => hs V i.1)
  refine loc_mono hl ?_
  intro W k hk
  choose x hx using hk
  refine ⟨∑ i : c.support, c i.1 • freeGen R P W (x i), ?_⟩
  have e1 : Sec.map ((free R).map f) (∑ i : c.support, c i.1 • freeGen R P W (x i)) =
      ∑ i : c.support, c i.1 • freeGen R Q W (Q.map k.op i.1) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Sec.map, map_sum, map_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [← hx i]; exact (GlobalTheory.T.free_sections_ext_res_map R P ((free R).obj P)).2.2.2 Q f W (x i)
  rw [e1, res_comp, hc, res_gsum, Finsupp.sum]
  exact Finset.sum_coe_sort c.support (fun y => c y • freeGen R Q W (Q.map k.op y))

theorem loc_kill {R : Type} [CommRing R] {P Q : PSh} (f : P ⟶ Q)
    (hi : ∀ U (x x' : P.obj (op U)), f.app (op U) x = f.app (op U) x' → Loc U fun _ g => P.map g.op x = P.map g.op x')
    {W : Scheme.{0}} (d : P.obj (op W) →₀ ULift.{1} R) (hd : Finsupp.mapDomain (f.app (op W)) d = 0) :
    Loc W fun _ k => Finsupp.mapDomain (P.map k.op) d = 0 := by
  classical
  have hl : Loc W fun W' k => ∀ i : d.support × d.support,
      f.app (op W) i.1.1 = f.app (op W) i.2.1 → P.map k.op i.1.1 = P.map k.op i.2.1 :=
    loc_fin _ fun i => by
      by_cases h : f.app (op W) i.1.1 = f.app (op W) i.2.1
      · exact loc_mono (hi W _ _ h) fun _ _ e _ => e
      · exact loc_all fun _ _ e => absurd e h
  refine loc_mono hl ?_
  intro W' k hk
  rcases d.support.eq_empty_or_nonempty with h0 | ⟨x0, _⟩
  · rw [Finsupp.support_eq_empty.1 h0, Finsupp.mapDomain_zero]
  let h : Q.obj (op W) → P.obj (op W') := fun y =>
    if hy : ∃ x ∈ d.support, f.app (op W) x = y then P.map k.op hy.choose else P.map k.op x0
  have e : Finsupp.mapDomain (P.map k.op) d = Finsupp.mapDomain (h ∘ f.app (op W)) d := by
    apply Finsupp.mapDomain_congr
    intro x hx
    have hy : ∃ x' ∈ d.support, f.app (op W) x' = f.app (op W) x := ⟨x, hx, rfl⟩
    show _ = h (f.app (op W) x)
    simp only [h, dif_pos hy]
    exact hk (⟨x, hx⟩, ⟨hy.choose, hy.choose_spec.1⟩) hy.choose_spec.2.symm
  rw [e, Finsupp.mapDomain_comp, hd, Finsupp.mapDomain_zero]

theorem free_map_mono_of_loc (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q)
    (hi : ∀ U (x x' : P.obj (op U)), f.app (op U) x = f.app (op U) x' → Loc U fun _ g => P.map g.op x = P.map g.op x') :
    Mono ((free R).map f) := by
  rw [(GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections R ((free R).map f)).2.1]
  intro U a ha
  apply loc_trans
  refine loc_mono ((GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R P U).1 a) ?_
  rintro V g ⟨c, hc⟩
  have h0 : gsum R Q V (Finsupp.mapDomain (f.app (op V)) c) = 0 := by
    rw [← map_gsum, show gsum R P V c = Sec.res g a from hc.symm, map_res, ha]; simp [Sec.res]
  apply loc_trans
  refine loc_mono ((GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R Q V).2 _ h0) ?_
  intro W k hk
  have hd : Finsupp.mapDomain (f.app (op W)) (Finsupp.mapDomain (P.map k.op) c) = 0 := by
    rw [← Finsupp.mapDomain_comp]
    rw [show (f.app (op W) ∘ P.map k.op) = (Q.map k.op ∘ f.app (op V)) from
      funext fun x => NatTrans.naturality_apply f k.op x]
    rw [Finsupp.mapDomain_comp]; exact hk
  refine loc_mono (loc_kill f hi _ hd) ?_
  intro W' k' hk'
  rw [res_comp, res_comp, hc, res_gsum', res_gsum', hk']
  simp [gsum]

end GlobalTheory.EtC.FreeMonoEpi

namespace GlobalTheory.EtC


open GlobalTheory.EtC.FreeMonoEpi in
theorem free_map_mono_epi_iso : ∀ (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q), (Mono f → Mono ((free R).map f)) ∧ ((∀ U (y : Q.obj (op U)), Loc U fun V g => ∃ x, f.app (op V) x = Q.map g.op y) → Epi ((free R).map f)) ∧ ((∀ U (y : Q.obj (op U)), Loc U fun V g => ∃ x, f.app (op V) x = Q.map g.op y) → (∀ U (x x' : P.obj (op U)), f.app (op U) x = f.app (op U) x' → Loc U fun _ g => P.map g.op x = P.map g.op x') → IsIso ((free R).map f)) := by
  intro R _ P Q f
  refine ⟨fun _ => free_map_mono R f, free_map_epi R f, fun hs hi => ?_⟩
  haveI := free_map_epi R f hs
  haveI := free_map_mono_of_loc R f hi
  exact isIso_of_mono_of_epi _

end GlobalTheory.EtC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleModuleSheafMapMonoEpiIsoStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freeEtaleModuleSheaf_map_mono_epi_iso : ∀ (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q), (Mono f → Mono ((free R).map f)) ∧ ((∀ U (y : Q.obj (op U)), Loc U fun V g => ∃ x, f.app (op V) x = Q.map g.op y) → Epi ((free R).map f)) ∧ ((∀ U (y : Q.obj (op U)), Loc U fun V g => ∃ x, f.app (op V) x = Q.map g.op y) → (∀ U (x x' : P.obj (op U)), f.app (op U) x = f.app (op U) x' → Loc U fun _ g => P.map g.op x = P.map g.op x') → IsIso ((free R).map f)) := by
  first | (exact @GlobalTheory.EtC.free_map_mono_epi_iso) | (exact GlobalTheory.EtC.free_map_mono_epi_iso) | (intros; apply GlobalTheory.EtC.free_map_mono_epi_iso  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemRange
open ReciprocityTheory.PGsh.Up GlobalTheory.Sandwich Matrix

namespace GlobalTheory.Sandwich.HodgeTateBound

section General

variable {A O : Type} [CommRing A] [CommRing O] {h : ℕ}

end General

open Matrix in
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] in
private lemma mul_eq_smul_one_of_mul_eq_smul_one [IsDomain R] {A B : Matrix n n R} {c : R}
    (hc : c ≠ 0) (hBA : B * A = c • (1 : Matrix n n R)) : A * B = c • (1 : Matrix n n R) := by
  have hdet : A.det ≠ 0 := by
    intro h0
    have hprod : B.det * A.det = c ^ Fintype.card n := by
      rw [← det_mul, hBA, det_smul, det_one, mul_one]
    rw [h0, mul_zero] at hprod
    exact pow_ne_zero _ hc hprod.symm
  have key : A.det • (A * B) = A.det • (c • (1 : Matrix n n R)) := by
    calc A.det • (A * B) = (A * B) * (A * adjugate A) := by
          rw [mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
      _ = A * (B * A) * adjugate A := by simp only [Matrix.mul_assoc]
      _ = A.det • (c • (1 : Matrix n n R)) := by
          rw [hBA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, mul_adjugate, smul_smul,
            smul_smul, mul_comm]
  ext i j
  have hij := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at hij
  exact mul_left_cancel₀ hdet hij

open Matrix in
variable {A O : Type*} [CommRing A] [CommRing O] {h : ℕ} in
private lemma smul_mem_range_of_mem_ker_of_mul_eq (θ : A →+* O) (hθ : Function.Surjective θ)
    {ξ ν : A} (hker : RingHom.ker θ = Ideal.span {ξ}) (hξ : ∀ y : A, y * ξ = 0 → y = 0)
    {P Q : Matrix (Fin h) (Fin h) A} (hQP : Q * P = (ξ * ν) • (1 : Matrix (Fin h) (Fin h) A))
    (t : Fin h → O) (ht : t ∈ LinearMap.ker (toLin' (P.map θ))) :
    θ ν • t ∈ LinearMap.range (toLin' (Q.map θ)) := by
  choose s hs using fun i => hθ (t i)
  have hst : (θ ∘ s) = t := funext hs
  rw [LinearMap.mem_ker, toLin'_apply] at ht
  have hmem : ∀ i, (P *ᵥ s) i ∈ Ideal.span {ξ} := by
    intro i
    rw [← hker, RingHom.mem_ker, RingHom.map_mulVec, hst]
    exact congrFun ht i
  choose g hg using fun i => Ideal.mem_span_singleton'.mp (hmem i)
  have hQg : Q *ᵥ g = ν • s := by
    funext i
    apply sub_eq_zero.mp
    apply hξ
    have h1 : Q *ᵥ (P *ᵥ s) = (ξ * ν) • s := by
      rw [mulVec_mulVec, hQP, Matrix.smul_mulVec, one_mulVec]
    have h2 : P *ᵥ s = fun j => g j * ξ := funext fun j => (hg j).symm
    have h3 := congrFun h1 i
    rw [h2] at h3
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h3 ⊢
    have h4 : ∑ j, Q i j * (g j * ξ) = (∑ j, Q i j * g j) * ξ := by
      rw [Finset.sum_mul]
      simp only [mul_assoc]
    rw [h4] at h3
    linear_combination h3
  refine ⟨θ ∘ g, ?_⟩
  rw [toLin'_apply]
  funext i
  rw [← RingHom.map_mulVec, hQg]
  simp [← hs]

open Matrix in
variable {O : Type*} [CommRing O] {h : ℕ} in
private lemma map_iInf_eigenspace_le_of_intertwine {ι : Type*} {X Y : ι → Matrix (Fin h) (Fin h) O}
    {Z : Matrix (Fin h) (Fin h) O} (c : ι → O) (hZ : ∀ a, Y a * Z = Z * X a) :
    (⨅ a, Module.End.eigenspace (toLin' (X a)) (c a)).map (toLin' Z) ≤
      ⨅ a, Module.End.eigenspace (toLin' (Y a)) (c a) := by
  rintro _ ⟨x, hx, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_iInf] at hx
  rw [Submodule.mem_iInf]
  intro a
  have hxa := hx a
  rw [Module.End.mem_eigenspace_iff, toLin'_apply] at hxa ⊢
  rw [toLin'_apply, mulVec_mulVec, hZ, ← mulVec_mulVec, hxa, mulVec_smul]


open Matrix in
theorem _root_.GlobalTheory.Sandwich.HodgeTateBound.bound : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C]
    [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O →
    ∀ ε : PreTilt O p, IsPrimitiveRoot (_root_.GlobalTheory.Sandwich.root ε).untilt p →
    ∀ (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ], ∀ (h : ℕ) (D : _root_.GlobalTheory.Sandwich.Datum ε h Λ),
    D.F * D.G =
        _root_.GlobalTheory.Sandwich.mu ε • (1 : Matrix (Fin h) (Fin h) (_root_.GlobalTheory.Sandwich.Ainf p O)) ∧
      LinearMap.range D.al ≤ D.Fil ∧
      D.Lie ≤ LinearMap.ker D.al ∧
      (∀ f ∈ D.Fil, WittVector.fontaineTheta O p (_root_.GlobalTheory.Sandwich.nu ε) • f ∈
        LinearMap.range D.al) ∧
      (∀ t ∈ LinearMap.ker D.al,
        WittVector.fontaineTheta O p (_root_.GlobalTheory.Sandwich.nu ε) • t ∈ D.Lie) ∧
      (∀ τ : Λ →+* O, (D.Tsub τ).map D.al ≤
          D.Fil ⊓ D.Hsub τ ∧
        (D.Hsub τ).map D.bb ≤
          D.Lie ⊓ D.Tsub τ ∧
        D.Lie ⊓ D.Tsub τ ≤
          D.W τ) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ h D
  haveI : IsDomain (_root_.GlobalTheory.Sandwich.Ainf p O) := _root_.GlobalTheory.AinfXi.isDomain_ainf hv
  have hker := _root_.GlobalTheory.AinfXi.ker_theta hv ε hε
  have hξ := _root_.GlobalTheory.AinfXi.xi_nzd hv ε hε
  have hsurj : Function.Surjective (WittVector.fontaineTheta O p) := _root_.ReciprocityTheory.PGsh.Ainf.theta_surj p O hv
  have hμ := _root_.GlobalTheory.Sandwich.xi_mul_nu ε
  have hθξ : WittVector.fontaineTheta O p (_root_.GlobalTheory.Sandwich.xi ε) = 0 := by
    rw [← RingHom.mem_ker, hker]
    exact Ideal.mem_span_singleton_self _
  have hθμ : WittVector.fontaineTheta O p (_root_.GlobalTheory.Sandwich.mu ε) = 0 := by
    rw [← hμ, map_mul, hθξ, zero_mul]
  have hξ0 : _root_.GlobalTheory.Sandwich.xi ε ≠ 0 := by
    intro h0
    exact one_ne_zero (hξ 1 (by rw [h0, mul_zero]))
  have hν0 : _root_.GlobalTheory.Sandwich.nu ε ≠ 0 := by
    intro h0
    have h1 : WittVector.fontaineTheta O p (_root_.GlobalTheory.Sandwich.nu ε) =
        PreTilt.untilt (_root_.GlobalTheory.Sandwich.root ε) - 1 := by
      simp [_root_.GlobalTheory.Sandwich.nu, WittVector.fontaineTheta_teichmuller]
    rw [h0, map_zero] at h1
    exact hε.ne_one (Fact.out : p.Prime).one_lt (sub_eq_zero.mp h1.symm)
  have hμ0 : _root_.GlobalTheory.Sandwich.mu ε ≠ 0 := by
    rw [← hμ]
    exact mul_ne_zero hξ0 hν0
  have hGF := D.G_mul_F
  have hFG := mul_eq_smul_one_of_mul_eq_smul_one hμ0 hGF
  have hA : D.G.map (WittVector.fontaineTheta O p) *
      D.F.map (WittVector.fontaineTheta O p) = 0 := by
    rw [← Matrix.map_mul, hGF]
    ext i j
    simp [hθμ]
  have hB : D.F.map (WittVector.fontaineTheta O p) *
      D.G.map (WittVector.fontaineTheta O p) = 0 := by
    rw [← Matrix.map_mul, hFG]
    ext i j
    simp [hθμ]
  have hpad : ∀ M : Matrix (Fin h) (Fin h) ℤ_[p],
      (M.map (_root_.GlobalTheory.Sandwich.ofPadic p O)).map (WittVector.fontaineTheta O p) = M.map (_root_.GlobalTheory.Sandwich.padicToO p O) := by
    intro M
    ext i j
    simp [_root_.GlobalTheory.Sandwich.padicToO]
  have hact := D.F_act
  have hGact : ∀ a, (D.ρT a).map (_root_.GlobalTheory.Sandwich.ofPadic p O) * D.G =
      D.G * D.ρM a := by
    intro a
    have e : _root_.GlobalTheory.Sandwich.mu ε •
        ((D.ρT a).map (_root_.GlobalTheory.Sandwich.ofPadic p O) * D.G) =
        _root_.GlobalTheory.Sandwich.mu ε • (D.G * D.ρM a) := by
      calc _ = D.G * D.F *
              (D.ρT a).map (_root_.GlobalTheory.Sandwich.ofPadic p O) * D.G := by
            rw [hGF, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]
        _ = D.G * (D.F *
              (D.ρT a).map (_root_.GlobalTheory.Sandwich.ofPadic p O)) * D.G := by
            simp only [Matrix.mul_assoc]
        _ = D.G * (D.ρM a * D.F) *
              D.G := by rw [hact a]
        _ = D.G * D.ρM a *
              (D.F * D.G) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hFG, Matrix.mul_smul, Matrix.mul_one]
    refine Matrix.ext fun i j => ?_
    have hij := congrFun (congrFun e i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at hij
    exact mul_left_cancel₀ hμ0 hij
  simp only [_root_.GlobalTheory.Sandwich.Datum.al, _root_.GlobalTheory.Sandwich.Datum.bb,
    _root_.GlobalTheory.Sandwich.Datum.Fil, _root_.GlobalTheory.Sandwich.Datum.Lie,
    _root_.GlobalTheory.Sandwich.Datum.Tsub, _root_.GlobalTheory.Sandwich.Datum.Hsub,
    _root_.GlobalTheory.Sandwich.Datum.W]
  have hrange : LinearMap.range (toLin' (D.F.map (WittVector.fontaineTheta O p))) ≤
      LinearMap.ker (toLin' (D.G.map (WittVector.fontaineTheta O p))) := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, toLin'_apply, toLin'_apply, mulVec_mulVec, hA, zero_mulVec]
  have hlie : LinearMap.range (toLin' (D.G.map (WittVector.fontaineTheta O p))) ≤
      LinearMap.ker (toLin' (D.F.map (WittVector.fontaineTheta O p))) := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, toLin'_apply, toLin'_apply, mulVec_mulVec, hB, zero_mulVec]
  refine ⟨hFG, hrange, hlie, ?_, ?_, ?_⟩
  · exact smul_mem_range_of_mem_ker_of_mul_eq _ hsurj hker hξ (by rw [hFG, hμ])
  · exact smul_mem_range_of_mem_ker_of_mul_eq _ hsurj hker hξ (by rw [hGF, hμ])
  · intro τ
    refine ⟨le_inf (LinearMap.map_le_range.trans hrange) ?_,
      le_inf LinearMap.map_le_range ?_, fun x hx => ⟨hx.2, hlie hx.1⟩⟩
    · refine map_iInf_eigenspace_le_of_intertwine τ fun a => ?_
      rw [← Matrix.map_mul, ← hact a, Matrix.map_mul, hpad]
    · refine map_iInf_eigenspace_le_of_intertwine τ fun a => ?_
      rw [← hpad, ← Matrix.map_mul, hGact a, Matrix.map_mul]

end GlobalTheory.Sandwich.HodgeTateBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotDComp
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

def invP (q : ℕ) : PSh where
  obj U := PLift (IsUnit (q : Γ(U.unop, ⊤)))
  map f := TypeCat.ofHom fun h => ⟨by simpa using h.down.map f.unop.appTop.hom⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def fibQ (q N : ℕ) : Spc := pullback (trivV N (disc.obj (invP q))) (PGL.pr N)

def lineQ (q N : ℕ) : fibQ q N ⟶ ofCat (glCat 1) := pullback.snd _ _ ≫ PGL.line N

variable (R : Type) [CommRing R]

def cotPre (q N : ℕ) (I : Cx R) (n : ℤ) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of (ULift.{1} R) (Cochain ((chains R).obj (sch.obj U.unop ⨯ fibQ q N)) I n)
  map f := ModuleCat.ofHom
    { toFun := fun α => (Cochain.ofHom ((chains R).map (prod.map (sch.map f.unop) (𝟙 (fibQ q N))))).comp α (zero_add n)
      map_add' := fun α β => Cochain.comp_add _ _ _ _
      map_smul' := fun r α => Cochain.comp_smul _ _ _ _ }
  map_id U := by
    ext α : 2
    simp
  map_comp f g := by
    ext α : 2
    change (Cochain.ofHom ((chains R).map (prod.map (sch.map (g.unop ≫ f.unop)) (𝟙 (fibQ q N))))).comp α (zero_add n) =
      (Cochain.ofHom ((chains R).map (prod.map (sch.map g.unop) (𝟙 (fibQ q N))))).comp
        ((Cochain.ofHom ((chains R).map (prod.map (sch.map f.unop) (𝟙 (fibQ q N))))).comp α (zero_add n)) (zero_add n)
    rw [show prod.map (sch.map (g.unop ≫ f.unop)) (𝟙 (fibQ q N)) =
      prod.map (sch.map g.unop) (𝟙 (fibQ q N)) ≫ prod.map (sch.map f.unop) (𝟙 (fibQ q N)) by simp,
      Functor.map_comp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

def cotD (q N : ℕ) (I : Cx R) (n : ℤ) : cotPre R q N I n ⟶ cotPre R q N I (n + 1) where
  app U := ModuleCat.ofHom
    { toFun := fun α => δ n (n + 1) α
      map_add' := fun α β => δ_add _ _ _ _
      map_smul' := fun r α => δ_smul _ _ _ _ }
  naturality U U' f := by
    ext α : 2
    revert α
    intro (α : Cochain ((chains R).obj (sch.obj U.unop ⨯ fibQ q N)) I n)
    change δ n (n + 1) ((Cochain.ofHom ((chains R).map (prod.map (sch.map f.unop) (𝟙 (fibQ q N))))).comp α (zero_add n)) =
      (Cochain.ofHom ((chains R).map (prod.map (sch.map f.unop) (𝟙 (fibQ q N))))).comp (δ n (n + 1) α) (zero_add (n + 1))
    rw [δ_zero_cochain_comp _ _ _ rfl, δ_ofHom, Cochain.zero_comp, smul_zero, add_zero]

theorem cotD_comp (q N : ℕ) (I : Cx R) (n : ℤ) : cotD R q N I n ≫ cotD R q N I (n + 1) = 0 := by
  ext U : 2
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  change δ (n + 1) (n + 1 + 1) (δ n (n + 1) α) = 0
  exact δ_δ _ _ _ _

def Jcx (q N : ℕ) (I : Cx R) : Cx R :=
  CochainComplex.of (fun n => (presheafToSheaf Scheme.etaleTopology.{0} _).obj (cotPre R q N I n))
    (fun n => (presheafToSheaf Scheme.etaleTopology.{0} _).map (cotD R q N I n))
    (fun n => by rw [← Functor.map_comp, cotD_comp, Functor.map_zero])

variable {R}

def Jsec {q N : ℕ} {I : Cx R} {n : ℤ} {U : Scheme.{0}} (c : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n) :
    Sec ((Jcx R q N I).X n) U :=
  ((toSheafify Scheme.etaleTopology.{0} (cotPre R q N I n)).app (op U)).hom c

def twCast {q : ℕ} {i i' : ℤ} (h : i = i') {s : ℤ} {V : Scheme.{0}} (x : Sec ((res (ZMod q) (tw q i)).X s) V) :
    Sec ((res (ZMod q) (tw q i')).X s) V := h ▸ x

end GlobalTheory.EtC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImageCocycleSemilinearSheafComplexMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImageCocycleSemilinearSheafComplexMap
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem SemiMap.op_image_spec : ∀ (S R : Type) [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J),
    (∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n), ∃ β : Cocycle ((chains R).obj E) J n, ρ.IsImage α.1 β.1) ∧
    ∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n),
      ρ.IsImage α.1 β.1 → ρ.op.app E n (CohomologyClass.mk α) = CohomologyClass.mk β :=
  fun _ _ _ _ _ _ ρ => ⟨fun E n α => (cup_op_spec.2 ρ E n α).1, fun E n α β h => (cup_op_spec.2 ρ E n α).2 β h⟩

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImageCocycleSemilinearSheafComplexMapStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap : ∀ (S R : Type) [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J), (∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n), ∃ β : Cocycle ((chains R).obj E) J n, ρ.IsImage α.1 β.1) ∧ ∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n), ρ.IsImage α.1 β.1 → ρ.op.app E n (CohomologyClass.mk α) = CohomologyClass.mk β := by
  first | (exact @GlobalTheory.EtC.SemiMap.op_image_spec) | (exact GlobalTheory.EtC.SemiMap.op_image_spec) | (intros; apply GlobalTheory.EtC.SemiMap.op_image_spec  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLocOAff
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

theorem hasLoc_OAff : ∀ {R' : Type} [CommRing R'] {X' : Scheme.{0}} (s' : X' ⟶ Sp R'),
    Desc.HasLoc (OAff s') := by
  intro R' _ X' s' T b
  let U := T.unop
  let b' : Γ(X', U.1) := b
  let V : X'.affineOpens := ⟨X'.basicOpen b', U.2.basicOpen b'⟩
  have hVU : V ≤ U := X'.basicOpen_le b'
  let l : T ⟶ Opposite.op V := (homOfLE hVU).op
  haveI := U.2.isLocalization_basicOpen b'
  refine ⟨Opposite.op V, l, ?_, ?_, ?_, ?_⟩
  · exact IsLocalization.Away.algebraMap_isUnit (S := Γ(X', X'.basicOpen b')) b'
  · intro y
    let y' : Γ(X', X'.basicOpen b') := y
    obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, e⟩ := IsLocalization.surj (Submonoid.powers b') y'
    refine ⟨n, x, ?_⟩
    show y' * (algebraMap Γ(X', U.1) Γ(X', X'.basicOpen b') b') ^ n =
      algebraMap Γ(X', U.1) Γ(X', X'.basicOpen b') x
    rw [← map_pow]
    exact e
  · intro x hx
    let x' : Γ(X', U.1) := x
    have hx : algebraMap Γ(X', U.1) Γ(X', X'.basicOpen b') x' = 0 := hx
    obtain ⟨⟨_, n, rfl⟩, e⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers b') _ x').1 hx
    exact ⟨n, e⟩
  · intro S u hu
    have hSU : S.unop.1 ≤ U.1 := leOfHom u.unop
    have hu' : IsUnit ((X'.presheaf.map (homOfLE hSU).op).hom b') := hu
    have h1 := X'.basicOpen_res b' (homOfLE hSU).op
    rw [Scheme.basicOpen_of_isUnit _ hu'] at h1
    have hSV : S.unop ≤ V := by
      change S.unop.1 ≤ X'.basicOpen b'
      rw [h1]; exact inf_le_right
    refine ⟨(homOfLE hSV).op, Subsingleton.elim _ _, fun _ _ ↦ Subsingleton.elim _ _⟩

end GlobalTheory.CechDR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceOfSmoothOfGeometricallyConnected
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceOfSmoothOfGeometricallyConnected
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem irreducibleSpace_of_smooth_of_geometricallyConnected_domain :
    ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R))), Smooth G.hom →
      GeometricallyConnected G.hom → Nonempty G.left → IrreducibleSpace G.left := by
  intro R _ _ G hs hc _
  let K := FractionRing R
  let g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R K))
  let F : Scheme := pullback G.hom g
  have hsnd : Smooth (pullback.snd G.hom g) :=
    MorphismProperty.of_isPullback (P := @Smooth) (IsPullback.of_hasPullback G.hom g) hs
  have hcon : ConnectedSpace F :=
    GeometricallyConnected.geometrically_connectedSpace (f := G.hom) g (pullback.fst _ _)
      (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  have hirr : IrreducibleSpace F :=
    irreducibleSpace_of_smooth_field_of_connectedSpace K _ (pullback.snd G.hom g) hsnd hcon
  have hgf : Flat g := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R))
  have hG : Flat G.hom := inferInstance

  have hη : genericPoint (Spec (CommRingCat.of R)) ∈ Set.range g :=
    (Flat.generalizingMap g).stableUnderGeneralization_range
      (genericPoint_specializes (g (closedPoint K))) ⟨closedPoint K, rfl⟩
  let ξ : G.left := pullback.fst G.hom g (genericPoint F)
  have hspec : ∀ z : G.left, ξ ⤳ z := by
    intro z
    obtain ⟨z', hz', e⟩ := Flat.generalizingMap G.hom (genericPoint_specializes (G.hom z))
    have hr : z' ∈ Set.range (pullback.fst G.hom g) := by
      rw [Scheme.Pullback.range_fst, Set.mem_preimage, e]; exact hη
    obtain ⟨w, rfl⟩ := hr
    exact ((genericPoint_specializes w).map (pullback.fst G.hom g).continuous).trans hz'
  have hcl : closure ({ξ} : Set G.left) = Set.univ :=
    Set.eq_univ_of_forall fun z => specializes_iff_mem_closure.mp (hspec z)
  rw [irreducibleSpace_def]
  have := (isIrreducible_singleton (x := ξ)).closure
  rw [hcl] at this
  exact this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceOfSmoothOfGeometricallyConnectedStatement
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducibleSpace_of_smooth_geometricallyConnected_domain : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R))), Smooth G.hom → GeometricallyConnected G.hom → Nonempty G.left → IrreducibleSpace G.left := by
  first | exact @GlobalTheory.irreducibleSpace_of_smooth_of_geometricallyConnected_domain | exact GlobalTheory.irreducibleSpace_of_smooth_of_geometricallyConnected_domain | (intros; apply GlobalTheory.irreducibleSpace_of_smooth_of_geometricallyConnected_domain <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafComplexSemilinearMapCompBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafComplexSemilinearMapCompBijective
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.OpComp

theorem ev_comp_ofHom' {R : Type} [CommRing R] {E : Spc} {I K : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n)
    (u : I ⟶ K) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (R := R) (α.comp (Cochain.ofHom u) (add_zero n)) p s h U x =
      Sec.map (u.f s) (ev (R := R) α p s h U x) := by
  simp only [ev, Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rfl

def invSemi {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J)
    (hb : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) : SemiMap J I where
  app U s := (AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm.toAddMonoidHom
  nat g s a := by
    apply (hb _ s).1
    change ρ.app _ s (Sec.res g ((AddEquiv.ofBijective (ρ.app _ s) (hb _ s)).symm a)) =
      ρ.app _ s ((AddEquiv.ofBijective (ρ.app _ s) (hb _ s)).symm (Sec.res g a))
    rw [← ρ.nat]
    have e1 := (AddEquiv.ofBijective (ρ.app _ s) (hb _ s)).apply_symm_apply a
    have e2 := (AddEquiv.ofBijective (ρ.app _ s) (hb _ s)).apply_symm_apply (Sec.res g a)
    simp only [AddEquiv.ofBijective_apply] at e1 e2
    rw [e1, e2]
  comm U s t a := by
    apply (hb U t).1
    change ρ.app U t (Sec.map (I.d s t) ((AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm a)) =
      ρ.app U t ((AddEquiv.ofBijective (ρ.app U t) (hb U t)).symm (Sec.map (J.d s t) a))
    rw [← ρ.comm]
    have e1 := (AddEquiv.ofBijective (ρ.app U s) (hb U s)).apply_symm_apply a
    have e2 := (AddEquiv.ofBijective (ρ.app U t) (hb U t)).apply_symm_apply (Sec.map (J.d s t) a)
    simp only [AddEquiv.ofBijective_apply] at e1 e2
    rw [e1, e2]

theorem invSemi_app {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J)
    (hb : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U) :
    (invSemi ρ hb).app U s (ρ.app U s a) = a := by
  change (AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm (AddEquiv.ofBijective (ρ.app U s) (hb U s) a) = a
  exact (AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm_apply_apply a

theorem app_invSemi {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J)
    (hb : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) (U : Scheme.{0}) (s : ℤ) (b : Sec (J.X s) U) :
    ρ.app U s ((invSemi ρ hb).app U s b) = b := by
  change AddEquiv.ofBijective (ρ.app U s) (hb U s) ((AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm b) = b
  exact (AddEquiv.ofBijective (ρ.app U s) (hb U s)).apply_symm_apply b

theorem op_comp_bij : ∀ (S R : Type) [CommRing S] [CommRing R] {I : Cx S} {J J' : Cx R} (ρ : SemiMap I J) (ρ' : SemiMap I J') (u : J ⟶ J'), (∀ (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U), ρ'.app U s a = Sec.map (u.f s) (ρ.app U s a)) → (∀ (E : Spc) (n : ℤ) x, ρ'.op.app E n x = cpush _ u n (ρ.op.app E n x)) ∧ ((∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) → ∀ (E : Spc) (n : ℤ), Function.Bijective (ρ.op.app E n)) := by
  intro S R _ _ I J J' ρ ρ' u hu
  refine ⟨fun E n x => ?_, fun hb E n => ?_⟩
  · obtain ⟨α, rfl⟩ := x.mk_surjective
    obtain ⟨β, hβ⟩ := ρ.image_exists E n α
    rw [ρ.op_spec E n α β hβ]
    change _ = CohomologyClass.mk (zcomp β (Cocycle.ofHom u) (add_zero n))
    refine ρ'.op_spec E n α _ (fun p s h U y => ?_)
    change ev (R := R) (β.1.comp (Cochain.ofHom u) (add_zero n)) p s h U y = _
    rw [ev_comp_ofHom', hβ, hu]
  · set σ := invSemi ρ hb
    have h1 : ∀ x, σ.op.app E n (ρ.op.app E n x) = x := by
      intro x
      obtain ⟨α, rfl⟩ := x.mk_surjective
      obtain ⟨β, hβ⟩ := ρ.image_exists E n α
      rw [ρ.op_spec E n α β hβ]
      refine σ.op_spec E n β α (fun p s h U y => ?_)
      rw [hβ, invSemi_app]
    have h2 : ∀ y, ρ.op.app E n (σ.op.app E n y) = y := by
      intro y
      obtain ⟨β, rfl⟩ := y.mk_surjective
      obtain ⟨α, hα⟩ := σ.image_exists E n β
      rw [σ.op_spec E n β α hα]
      refine ρ.op_spec E n α β (fun p s h U y => ?_)
      rw [hα, app_invSemi]
    exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

end GlobalTheory.EtC.OpComp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafComplexSemilinearMapCompBijectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective : ∀ (S R : Type) [CommRing S] [CommRing R] {I : Cx S} {J J' : Cx R} (ρ : SemiMap I J) (ρ' : SemiMap I J') (u : J ⟶ J'), (∀ (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U), ρ'.app U s a = Sec.map (u.f s) (ρ.app U s a)) → (∀ (E : Spc) (n : ℤ) x, ρ'.op.app E n x = cpush _ u n (ρ.op.app E n x)) ∧ ((∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) → ∀ (E : Spc) (n : ℤ), Function.Bijective (ρ.op.app E n)) := by
  first | (exact @GlobalTheory.EtC.OpComp.op_comp_bij) | (exact GlobalTheory.EtC.OpComp.op_comp_bij) | (intros; apply GlobalTheory.EtC.OpComp.op_comp_bij  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepOfFactoringCover
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory

theorem sep_of_factoring_cover : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (T : C) (x : F.obj T), (∀ t (u : T ⟶ G.obj t), mp F u x = 0) → x = 0) := by
  intro R _ C _ C' _ F G H hcov T x hx
  obtain ⟨n, b, hb, h⟩ := hcov T
  refine Desc.sep_std (H := H) (hb := hb) x fun S u ⟨i, hi⟩ ↦ ?_
  obtain ⟨t, v, w, rfl⟩ := h i S u hi
  rw [mp_comp, hx t v, map_zero]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSheafIsLocallyFlat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSheafIsLocallyFlat
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.flatS_tw : ∀ (q : ℕ) [NeZero q] (i : ℤ),
    _root_.GlobalTheory.EtC.FlatS (_root_.GlobalTheory.EtC.tw q i) := by
  intro q _ i
  obtain ⟨h1, h2, -⟩ := _root_.GlobalTheory.EtC.toSheafify_loc_bij_lift (ZMod q)
    (Scheme.Γ ⋙ _root_.GlobalTheory.EtC.twF q i)
  refine ⟨_, toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ _root_.GlobalTheory.EtC.twF q i), h1, h2,
    fun U hU => ?_⟩
  obtain ⟨x⟩ := hU
  haveI : Nontrivial Γ(U, ⊤) := (U.presheaf.germ ⊤ x trivial).hom.domain_nontrivial
  haveI := (_root_.GlobalTheory.TwFree.twist_free q i Γ(U, ⊤)).1
  change Module.Flat (ULift.{1} (ZMod q))
    ((_root_.GlobalTheory.EtC.Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) ⧸
      _root_.GlobalTheory.EtC.twRel q i Γ(U, ⊤))
  infer_instance

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSheafIsLocallyFlatStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistSheaf_isLocallyFlat : ∀ (q : ℕ) [NeZero q] (i : ℤ), FlatS (tw q i) := by
  first | (exact @GlobalTheory.EtC.flatS_tw) | (exact GlobalTheory.EtC.flatS_tw) | (intros; apply GlobalTheory.EtC.flatS_tw  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatFamilyExtend
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory

theorem compat_family_extend : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (x : F.obj T), (∀ t (u : T ⟶ G.obj t), mp F u x = 0) → x = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp F (G.map a) (s t u)) → ∃ x : F.obj T, ∀ t u, mp F u x = s t u) → ∀ g' : ∀ t, F.obj (G.obj t), (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), g' t' = mp F (G.map a) (g' t)) → ∃ g : C0 F, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), g T' = mp F φ (g T)) ∧ ∀ t, g (G.obj t) = g' t := by
  intro R _ C _ C' _ F G hsep hglue g' hg'
  choose g hg using fun T : C ↦ hglue T (fun t _ ↦ g' t) fun t t' _ a ↦ hg' a
  refine ⟨g, fun T T' φ ↦ ?_, fun t ↦ ?_⟩
  · refine sub_eq_zero.1 (hsep T' _ fun t u ↦ ?_)
    rw [map_sub, ← mp_comp, hg, hg, sub_self]
  · have h := hg (G.obj t) t (𝟙 _)
    rwa [mp_id] at h

end GlobalTheory
end
