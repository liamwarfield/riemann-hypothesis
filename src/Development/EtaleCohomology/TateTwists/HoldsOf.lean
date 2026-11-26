module

public import Development.EtaleCohomology.TateTwists.Delta
public import Development.EtaleCohomology.TateTwists.EtaleChainCochainEvalBasicPropertiesHold
public import Development.EtaleCohomology.TateTwists.EtaleKummerTorsorRootsOfUnityListTorsionExistsOf

@[expose] public section

section -- merged from Development.EtaleCohomology.TateTwists.KumAddPf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def IsKumCoc (q : ℕ) [NeZero q] {X : Scheme.{0}} (u : (Γ(X, ⊤))ˣ)
    (γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1) : Prop :=
  (∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0) ∧
  ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
    ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)

def kum_uniq : Prop :=
  ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
    ∀ γ γ' : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1,
      IsKumCoc q u γ → IsKumCoc q u γ' → CohomologyClass.mk γ = CohomologyClass.mk γ'

def kum_mul_coc : Prop :=
  ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) (u v : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
    ∀ γu γv : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1,
      IsKumCoc q u γu → IsKumCoc q v γv →
      ∃ γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1,
        IsKumCoc q (u * v) γ ∧ CohomologyClass.mk γ = CohomologyClass.mk γu + CohomologyClass.mk γv

def kum_pow_coc : Prop :=
  ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
    ∃ γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1,
      IsKumCoc q (u ^ q) γ ∧ CohomologyClass.mk γ = 0

theorem kum_add_of (he : kum_exists) (hu : kum_uniq) (hm : kum_mul_coc) (hp : kum_pow_coc) : kum_add := by
  intro q _ X u v hq
  obtain ⟨γu, eu, ku⟩ := kum_spec_of_exists he q X u hq
  obtain ⟨γv, ev', kv⟩ := kum_spec_of_exists he q X v hq
  obtain ⟨γuv, euv, kuv⟩ := kum_spec_of_exists he q X (u * v) hq
  obtain ⟨γp, epw, kpw⟩ := kum_spec_of_exists he q X (u ^ q) hq
  refine ⟨?_, ?_⟩
  · obtain ⟨γ, hγ, hsum⟩ := hm q X u v hq γu γv ku kv
    rw [← euv, ← eu, ← ev', ← hsum]
    exact hu q X (u * v) hq γuv γ kuv hγ
  · obtain ⟨γ, hγ, h0⟩ := hp q X u hq
    rw [← epw, ← h0]
    exact hu q X (u ^ q) hq γp γ kpw hγ

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleSheafInjectiveResolutionInitialShortComplex
section -- merged from Development.EtaleCohomology.TateTwists.EtaleInjectiveResolutionSectionsLocallyExact
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleInjectiveResolutionSectionsLocallyExact : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ z : Sec ((res R F).X 0) U, Sec.map ((res R F).d 0 1) z = 0 ↔ ∃ a : Sec F U, Sec.map (resι R F) a = z) ∧ Function.Injective (Sec.map (resι R F) (U := U)) ∧ (∀ (m n k : ℤ), 0 < n → m + 1 = n → ∀ z : Sec ((res R F).X n) U, n + 1 = k → Sec.map ((res R F).d n k) z = 0 → Loc U fun V g => ∃ y : Sec ((res R F).X m) V, Sec.map ((res R F).d m n) y = Sec.res g z) ∧ ∀ n : ℤ, n < 0 → Subsingleton (Sec ((res R F).X n) U)
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ResSecPf

variable (R : Type) [CommRing R]

noncomputable abbrev secF (U : Scheme.{0}) : Shv R ⥤ ModuleCat.{1} (ULift.{1} R) :=
  sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U)

lemma exact_pos (F : Shv R) (m n k : ℤ) (hn : 0 < n) (hm : m + 1 = n) (hk : n + 1 = k) :
    (ShortComplex.mk ((res R F).d m n) ((res R F).d n k) (by simp)).Exact := by
  have h1 : (res R F).ExactAt n := by
    unfold res
    rw [← quasiIsoAt_iff_exactAt (injectiveResolution F).ι' n
      (HomologicalComplex.exactAt_single_obj _ _ _ _ (by omega))]
    infer_instance
  exact (HomologicalComplex.exactAt_iff' _ m n k (by simp; omega) (by simp; omega)).1 h1

lemma subsing (F : Shv R) (U : Scheme.{0}) (n : ℤ) (hn : n < 0) :
    Subsingleton (Sec ((res R F).X n) U) := by
  have hz : IsZero ((res R F).X n) := by
    unfold res
    exact CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by omega)
  have := (hz.of_iso (Iso.refl _)).eq_of_src (𝟙 _) 0
  constructor
  intro a b
  have e : ∀ x : Sec ((res R F).X n) U, x = 0 := by
    intro x
    have := congrArg (fun f => Sec.map f x) (hz.eq_of_src (𝟙 _) 0)
    simpa [Sec.map] using this
  rw [e a, e b]

lemma resι_e (F : Shv R) :
    resι R F ≫ ((injectiveResolution F).cochainComplexXIso 0 0 rfl).hom = (injectiveResolution F).ι.f 0 := by
  unfold resι
  rw [InjectiveResolution.ι'_f_zero]
  erw [Category.assoc, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]

lemma d01' (F : Shv R) : ((injectiveResolution F).cochainComplexXIso 0 0 rfl).hom ≫
    (injectiveResolution F).cocomplex.d 0 1 = (injectiveResolution F).cochainComplex.d 0 1 ≫
      ((injectiveResolution F).cochainComplexXIso 1 1 rfl).hom := by
  rw [InjectiveResolution.cochainComplex_d _ 0 1 0 1 rfl rfl]
  simp

lemma etaleSheaf_injectiveResolution_initial_shortComplex_comp_zero (F : Shv R) : resι R F ≫ (res R F).d 0 1 = 0 := by
  have h := (injectiveResolution F).ι'.comm 0 1
  unfold resι res
  refine (Category.assoc _ _ _).trans ?_
  erw [h]
  simp
  rfl

noncomputable abbrev S0 (F : Shv R) : ShortComplex (Shv R) := ShortComplex.mk _ _ (etaleSheaf_injectiveResolution_initial_shortComplex_comp_zero R F)

lemma etaleSheaf_injectiveResolution_initial_shortComplex_exact (F : Shv R) : (S0 R F).Exact := by
  let I := injectiveResolution F
  have hN : (ShortComplex.mk _ _ I.ι_f_zero_comp_complex_d).Exact :=
    ShortComplex.exact_of_f_is_kernel _ I.isLimitKernelFork
  refine (ShortComplex.exact_iff_of_iso ?_).2 hN
  refine ShortComplex.isoMk (Iso.refl _) (I.cochainComplexXIso 0 0 rfl) (I.cochainComplexXIso 1 1 rfl) ?_ ?_
  · exact (Category.id_comp _).trans (resι_e R F).symm
  · exact d01' R F

lemma mono_resι_var (F : Shv R) : Mono (resι R F) := by
  have : Mono ((injectiveResolution F).ι.f 0) := inferInstance
  have h := resι_e R F
  have : Mono (resι R F ≫ ((injectiveResolution F).cochainComplexXIso 0 0 rfl).hom) := by
    rw [h]; assumption
  exact mono_of_mono _ ((injectiveResolution F).cochainComplexXIso 0 0 rfl).hom

def exact_loc : Prop := ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.Exact →
  ∀ U (b : Sec S.X₂ U), Sec.map S.g b = 0 → Loc U fun V g => ∃ a : Sec S.X₁ V, Sec.map S.f a = Sec.res g b

lemma part1 (F : Shv R) (U : Scheme.{0}) (z : Sec ((res R F).X 0) U) :
    Sec.map ((res R F).d 0 1) z = 0 ↔ ∃ a : Sec F U, Sec.map (resι R F) a = z := by
  constructor
  · intro hz
    have hE : ((S0 R F).map (secF R U)).Exact :=
      (etaleSheaf_injectiveResolution_initial_shortComplex_exact R F).map_of_mono_of_preservesKernel _ (mono_resι_var R F) inferInstance
    rw [ShortComplex.moduleCat_exact_iff] at hE
    exact hE z hz
  · rintro ⟨a, rfl⟩
    have := congrArg (fun f => Sec.map f a) (etaleSheaf_injectiveResolution_initial_shortComplex_comp_zero R F)
    simpa [Sec.map] using this

lemma part2 (F : Shv R) (U : Scheme.{0}) : Function.Injective (Sec.map (resι R F) (U := U)) := by
  have := mono_resι_var R F
  have : Mono ((secF R U).map (resι R F)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 this

end LateralTheory.EtaleFoundations.ResSecPf

open LateralTheory.EtaleFoundations.ResSecPf in
theorem LateralTheory.EtaleFoundations.etaleSheaf_injectiveResolution_sections_exact_of_local_exactness (hL : exact_loc) : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionSectionsLocallyExact := by
  intro R _ F U
  refine ⟨part1 R F U, part2 R F U, ?_, fun n hn => subsing R F U n hn⟩
  intro m n k hn hm z hk hz
  exact hL R _ (exact_pos R F m n k hn hm hk) U z hz
end

section -- merged from Development.EtaleCohomology.TateTwists.KumMulCocPf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.KMC

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem loc_bind {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hb : ∀ V (g : V ⟶ U), P V g → Loc V (fun W k => Q W (k ≫ g))) : Loc U Q := by
  classical
  obtain ⟨S, hS, hP⟩ := h
  choose R hR hQ using fun V (g : V ⟶ U) (hg : S.arrows g) => hb V g (hP V g hg)
  refine ⟨Sieve.bind S.arrows (fun V g hg => R V g hg),
    Scheme.etaleTopology.bind_covering hS (fun V g hg => hR V g hg), ?_⟩
  rintro W h ⟨V, k, g, hg, hk, rfl⟩
  exact hQ V g hg W k hk

theorem umap_comp {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : (Γ(U, ⊤))ˣ) :
    Units.map (k ≫ g).appTop.hom.toMonoidHom a =
      Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom a) := by
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rfl

theorem unit_q {V U : Scheme.{0}} (q : ℕ) (g : V ⟶ U) (hq : IsUnit (q : Γ(U, ⊤))) : IsUnit (q : Γ(V, ⊤)) := by
  simpa using hq.map g.appTop.hom

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (s : Sec F U) :
    Sec.res k (Sec.res g s) = Sec.res (k ≫ g) s := by
  simp [Sec.res]

theorem res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (s : Sec F U) :
    Sec.res g (Sec.map φ s) = Sec.map φ (Sec.res g s) := by
  simp only [Sec.res, Sec.map]
  exact congrArg (fun f => f.hom s) (φ.hom.naturality g.op).symm

variable (q : ℕ)

theorem kumT_pow (hk : IsKum q (kumT q)) {V : Scheme.{0}} (ζ : Prim q Γ(V, ⊤)) :
    ∀ (n : ℕ) (v w : (Γ(V, ⊤))ˣ), (w : Γ(V, ⊤)) = ζ.1 ^ n * v → kumT q V w = kumT q V v + n • resGen 1 ζ := by
  intro n
  induction n with
  | zero => intro v w h; simp at h; rw [Units.ext h]; simp
  | succ n ih =>
    intro v w h
    have hu : IsUnit (ζ.1 ^ n * v) := by
      apply isUnit_of_mul_isUnit_right (x := ζ.1); rw [← mul_assoc, ← pow_succ']; rw [← h]; exact w.isUnit
    rw [hk.2 V ζ hu.unit w (by rw [h, hu.unit_spec, pow_succ', mul_assoc]), ih v hu.unit hu.unit_spec]
    rw [succ_nsmul]; abel

noncomputable def D (V : Scheme.{0}) (a b : (Γ(V, ⊤))ˣ) : Sec ((res _ (tw q 1)).X 0) V :=
  kumT q V (a * b) - kumT q V a - kumT q V b

theorem D_comm (V : Scheme.{0}) (a b : (Γ(V, ⊤))ˣ) : D q V a b = D q V b a := by
  simp only [D, mul_comm a b]; abel

theorem D_res (hk : IsKum q (kumT q)) {W V : Scheme.{0}} (k : W ⟶ V) (hq : IsUnit (q : Γ(V, ⊤))) (a b : (Γ(V, ⊤))ˣ) :
    Sec.res k (D q V a b) = D q W (Units.map k.appTop.hom.toMonoidHom a) (Units.map k.appTop.hom.toMonoidHom b) := by
  simp only [D, Sec.res, map_sub] at *
  have h := hk.1 W V k
  simp only [Sec.res] at h
  rw [h _ hq, h _ hq, h _ hq, map_mul]

theorem D_change (hk : IsKum q (kumT q)) (hp : EtalePrimitiveRootsExistLocally) (hs : EtaleSheafSectionsSeparatedAndGlue) [NeZero q]
    {V : Scheme.{0}} (hq : IsUnit (q : Γ(V, ⊤))) (a a' b : (Γ(V, ⊤))ˣ) (h : a' ^ q = a ^ q) :
    D q V a' b = D q V a b := by
  apply (hs _ _ V).1
  set c := a' * a⁻¹ with hcdef
  have hc : c ^ q = 1 := by rw [hcdef, mul_pow, h, inv_pow, mul_inv_cancel]
  have hac : a' = c * a := by rw [hcdef, inv_mul_cancel_right]
  refine loc_bind ((hp q V).1 hq) (fun W g hζ => ?_)
  obtain ⟨ζ⟩ := hζ
  refine loc_mono ((hp q W).2.2.1 ζ (g.appTop.hom c) (by rw [← map_pow, ← Units.val_pow_eq_pow_val, hc, Units.val_one, map_one])) (fun W' k hn => ?_)
  obtain ⟨n, hn⟩ := hn
  have hq' : IsUnit (q : Γ(V, ⊤)) := hq
  rw [D_res q hk (k ≫ g) hq, D_res q hk (k ≫ g) hq]
  simp only [umap_comp]
  set ζ'' : Prim q Γ(W', ⊤) := Prim.map k.appTop.hom ζ
  set A := Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom a)
  set A' := Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom a')
  set B := Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom b)
  have key : (A' : Γ(W', ⊤)) = ζ''.1 ^ n * A := by
    simp only [A, A', ζ'', Prim.map, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, hac,
      Units.val_mul, map_mul]
    rw [hn]
  unfold D
  rw [kumT_pow q hk ζ'' n (A * B) (A' * B) (by rw [Units.val_mul, Units.val_mul, key, mul_assoc]),
    kumT_pow q hk ζ'' n A A' key]
  abel

theorem D_change2 (hk : IsKum q (kumT q)) (hp : EtalePrimitiveRootsExistLocally) (hs : EtaleSheafSectionsSeparatedAndGlue) [NeZero q]
    {V : Scheme.{0}} (hq : IsUnit (q : Γ(V, ⊤))) (a a' b b' : (Γ(V, ⊤))ˣ) (ha : a' ^ q = a ^ q) (hb : b' ^ q = b ^ q) :
    D q V a' b' = D q V a b := by
  rw [D_change q hk hp hs hq a a' b' ha, D_comm, D_change q hk hp hs hq b b' a hb, D_comm]

def KP {V : Scheme.{0}} (u v : (Γ(V, ⊤))ˣ) (Z : Sec ((res _ (tw q 1)).X 0) V) : Prop :=
  ∀ (W : Scheme.{0}) (k : W ⟶ V) (a b : (Γ(W, ⊤))ˣ), a ^ q = Units.map k.appTop.hom.toMonoidHom u →
    b ^ q = Units.map k.appTop.hom.toMonoidHom v → Sec.res k Z = D q W a b

theorem KP_res {W V : Scheme.{0}} (k : W ⟶ V) {u v : (Γ(V, ⊤))ˣ} {Z : Sec ((res _ (tw q 1)).X 0) V}
    (hZ : KP q u v Z) : KP q (Units.map k.appTop.hom.toMonoidHom u) (Units.map k.appTop.hom.toMonoidHom v) (Sec.res k Z) := by
  intro W' k' a b ha hb
  rw [res_comp]
  exact hZ W' (k' ≫ k) a b (by rw [ha, umap_comp]) (by rw [hb, umap_comp])

theorem KP_uniq (hp : EtalePrimitiveRootsExistLocally) (hs : EtaleSheafSectionsSeparatedAndGlue) [NeZero q]
    {V : Scheme.{0}} (hq : IsUnit (q : Γ(V, ⊤))) {u v : (Γ(V, ⊤))ˣ} {Z₁ Z₂ : Sec ((res _ (tw q 1)).X 0) V}
    (h₁ : KP q u v Z₁) (h₂ : KP q u v Z₂) : Z₁ = Z₂ := by
  apply (hs _ _ V).1
  refine loc_bind ((hp q V).2.2.2 hq u) (fun W g ha => ?_)
  obtain ⟨a, ha⟩ := ha
  refine loc_mono ((hp q W).2.2.2 (unit_q q g hq) (Units.map g.appTop.hom.toMonoidHom v)) (fun W' k hb => ?_)
  obtain ⟨b, hb⟩ := hb
  have ha' : (Units.map k.appTop.hom.toMonoidHom a) ^ q = Units.map (k ≫ g).appTop.hom.toMonoidHom u := by
    rw [← map_pow, ha, umap_comp]
  have hb' : b ^ q = Units.map (k ≫ g).appTop.hom.toMonoidHom v := by rw [hb, umap_comp]
  rw [h₁ W' (k ≫ g) _ b ha' hb', h₂ W' (k ≫ g) _ b ha' hb']

theorem KP_exists (hk : IsKum q (kumT q)) (hp : EtalePrimitiveRootsExistLocally) (hs : EtaleSheafSectionsSeparatedAndGlue) [NeZero q]
    {V : Scheme.{0}} (hq : IsUnit (q : Γ(V, ⊤))) (u v : (Γ(V, ⊤))ˣ) : ∃ Z, KP q u v Z := by
  classical
  let S : Sieve V :=
    { arrows := fun W g => (∃ a : (Γ(W, ⊤))ˣ, a ^ q = Units.map g.appTop.hom.toMonoidHom u) ∧
        ∃ b : (Γ(W, ⊤))ˣ, b ^ q = Units.map g.appTop.hom.toMonoidHom v
      downward_closed := by
        rintro W W' g ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ k
        exact ⟨⟨Units.map k.appTop.hom.toMonoidHom a, by rw [← map_pow, ha, umap_comp]⟩,
          ⟨Units.map k.appTop.hom.toMonoidHom b, by rw [← map_pow, hb, umap_comp]⟩⟩ }
  have hS : S ∈ Scheme.etaleTopology V := by
    obtain ⟨S₁, h₁, P₁⟩ := (hp q V).2.2.2 hq u
    obtain ⟨S₂, h₂, P₂⟩ := (hp q V).2.2.2 hq v
    refine Scheme.etaleTopology.superset_covering ?_ (Scheme.etaleTopology.intersection_covering h₁ h₂)
    intro W g hg
    exact ⟨P₁ W g hg.1, P₂ W g hg.2⟩
  let sfun : ∀ (W : Scheme.{0}) (g : W ⟶ V), S.arrows g → Sec ((res _ (tw q 1)).X 0) W :=
    fun W g hg => D q W (Classical.choose (And.left hg)) (Classical.choose (And.right hg))
  obtain ⟨Z, hZ⟩ := (hs _ _ V).2 S hS sfun (by
    intro W W' g k hg
    rw [D_res q hk k (unit_q q g hq)]
    refine D_change2 q hk hp hs (unit_q q (k ≫ g) hq) _ _ _ _ ?_ ?_
    · rw [← map_pow, hg.1.choose_spec, ← umap_comp, (S.downward_closed hg k).1.choose_spec]
    · rw [← map_pow, hg.2.choose_spec, ← umap_comp, (S.downward_closed hg k).2.choose_spec])
  refine ⟨Z, fun W g a b ha hb => ?_⟩
  have hg : S.arrows g := ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  rw [hZ W g hg]
  exact D_change2 q hk hp hs (unit_q q g hq) _ _ _ _ (by rw [hg.1.choose_spec, ha]) (by rw [hg.2.choose_spec, hb])

theorem res_add {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (s t : Sec F U) :
    Sec.res g (s + t) = Sec.res g s + Sec.res g t := map_add _ _ _

noncomputable def yv {X : Scheme.{0}} (Y : ∀ U : Scheme.{0}, (U ⟶ X) → Sec ((res (ZMod q) (tw q 1)).X 0) U) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 0 = s → ∀ U : Scheme.{0}, Sx (sch.obj X) p U → Sec ((res (ZMod q) (tw q 1)).X s) U
  | 0, s, h, U, x => by
      obtain rfl : s = 0 := by simpa using h.symm
      exact Y U x
  | _ + 1, _, _, _, _ => 0

end LateralTheory.EtaleFoundations.KMC

namespace LateralTheory.EtaleFoundations
open KMC

theorem kum_mul_coc_of (hkT : EtaleKummerTriangleExists) (hp : EtalePrimitiveRootsExistLocally) (hs : EtaleSheafSectionsSeparatedAndGlue)
    (hmk : EtaleCochainExistsOfNaturalEvaluation) (hd : EtaleCochainEvaluationCoboundaryFormula) (hb : EtaleCochainEvaluationLinear) : kum_mul_coc := by
  intro q _ X u v hq γu γv ku kv
  have hk := hkT q
  have hY : ∀ (U : Scheme.{0}) (x : U ⟶ X), ∃ Z, KP q (Units.map x.appTop.hom.toMonoidHom u)
      (Units.map x.appTop.hom.toMonoidHom v) Z :=
    fun U x => KP_exists q hk hp hs (unit_q q x hq) _ _
  choose Y hYP using hY
  have hYnat : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : U ⟶ X), Sec.res g (Y U x) = Y V (g ≫ x) := by
    intro V U g x
    refine KP_uniq q hp hs (unit_q q (g ≫ x) hq) ?_ (hYP V (g ≫ x))
    have := KP_res q g (hYP U x)
    rwa [← umap_comp, ← umap_comp] at this
  obtain ⟨y, hy⟩ := hmk (ZMod q) (E := sch.obj X) (I := res _ (tw q 1)) (n := 0) (yv q Y) (by
    intro p s h V U g x
    cases p with
    | zero =>
      obtain rfl : s = 0 := by simpa using h.symm
      exact hYnat V U g x
    | succ p =>
      show Sec.res g 0 = 0
      exact map_zero _)
  let β : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1 :=
    Cocycle.mk (δ 0 1 y) 2 (by norm_num) (δ_δ 0 1 2 y)
  have e : (γu + γv + β).1 = γu.1 + γv.1 + δ 0 1 y := rfl
  have hadd1 : ∀ (α β' : Cochain ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1) (U : Scheme.{0}) (x : U ⟶ X),
      ev (α + β') 1 0 (by simp) U x = ev α 1 0 (by simp) U x + ev β' 1 0 (by simp) U x :=
    fun α β' U x => ((hb (ZMod q)).1 α β' 1 0 _ U x).1
  have hadd0 : ∀ (α β' : Cochain ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1) (U : Scheme.{0}) (x : U ⟶ X),
      ev (α + β') 0 1 (by simp) U x = ev α 0 1 (by simp) U x + ev β' 0 1 (by simp) U x :=
    fun α β' U x => ((hb (ZMod q)).1 α β' 0 1 _ U x).1
  have hδ0 : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev (δ 0 1 y) 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (Y U x) :=
    fun U x => ((hd (ZMod q) (n := 0) (m := 1) rfl y U).1 x).trans (congrArg _ (hy 0 0 _ U x))
  refine ⟨γu + γv + β, ⟨?_, ?_⟩, ?_⟩
  · intro U x
    rw [e]
    rw [hadd1, hadd1]
    rw [ku.1 U x, kv.1 U x, zero_add, zero_add]
    refine ((hd (ZMod q) (n := 0) (m := 1) rfl y U).2 0 (-1) 0 (by simp) (by simp) x).trans ?_
    have hy1 : ev y (0 + 1) (-1) (by simp) U x = 0 := hy 1 (-1) _ U x
    have hface : ∀ i, ev y 0 0 (by simp) U (Sx.face (E := sch.obj X) (p := 0) x i) = Y U x := fun i => hy 0 0 _ U _
    rw [hy1]
    simp only [hface]
    simp [Fin.sum_univ_two, Sec.map]
  · intro U x w hw
    rw [e]
    rw [hadd0, hadd0, hδ0]
    apply (hs _ _ U).1
    refine loc_mono ((hp q U).2.2.2 (unit_q q x hq) (Units.map x.appTop.hom.toMonoidHom u)) (fun W k ha => ?_)
    obtain ⟨a, ha⟩ := ha
    set K := Units.map k.appTop.hom.toMonoidHom w with hK
    have hbq : (K * a⁻¹) ^ q = Units.map k.appTop.hom.toMonoidHom (Units.map x.appTop.hom.toMonoidHom v) := by
      rw [mul_pow, inv_pow, hK, ← map_pow, hw, ha, map_mul, map_mul, mul_comm (Units.map _ (Units.map _ u)),
        mul_inv_cancel_right]
    have hab : a * (K * a⁻¹) = K := by rw [mul_comm K, mul_inv_cancel_left]
    have eu : Sec.res k (ev γu.1 0 1 (by simp) U x) = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q W a) :=
      ((hb (ZMod q)).2.1 γu.1 0 1 (by simp) W U k x).trans (ku.2 W (k ≫ x) a (by rw [ha, umap_comp]))
    have ev' : Sec.res k (ev γv.1 0 1 (by simp) U x) = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q W (K * a⁻¹)) :=
      ((hb (ZMod q)).2.1 γv.1 0 1 (by simp) W U k x).trans (kv.2 W (k ≫ x) _ (by rw [hbq, umap_comp]))
    rw [res_add, res_add, eu, ev', res_map, res_map, hYP U x W k a (K * a⁻¹) ha hbq, hk.1 W U k w (unit_q q x hq)]
    rw [← hK]
    unfold D
    rw [hab]
    simp only [Sec.map, map_sub]
    abel
  · rw [CohomologyClass.mk_add, CohomologyClass.mk_add,
      (CohomologyClass.mk_eq_zero_iff β).2 ((mem_coboundaries_iff β 0 (by norm_num)).2 ⟨y, rfl⟩), add_zero]

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.KumUniqPf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def uniq_prim_loc : Prop :=
  ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), (IsUnit (q : Γ(U, ⊤)) → Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))) ∧ (∀ ζ ξ : Prim q Γ(U, ⊤), Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) ∧ (∀ (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)), x ^ q = 1 → Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a) ∧ (IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ, Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u)

def sections_unique_of_local_agreement : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg

def uniq_ev_basic : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x, ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧ ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧ ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧ ∀ c : ℤ, ev (c • α) p s h U x = c • ev α p s h U x) ∧ (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)) ∧ (∀ α β : Cochain ((chains R).obj E) I n, (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β) ∧ (∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U), ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f)) ∧ ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x, ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x)

theorem sec_neg_eq (q : ℕ) [NeZero q] (s : ℤ) (hs : s < 0) (U : Scheme.{0})
    (a b : Sec ((res _ (tw q 1)).X s) U) : a = b := by
  have h0 : IsZero ((res _ (tw q 1)).X s) := by
    unfold res
    exact CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by omega)
  have h1 : IsZero (((res _ (tw q 1)).X s).obj.obj (op U)) :=
    ((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U)).map_isZero h0)
  have : Subsingleton (((res _ (tw q 1)).X s).obj.obj (op U)) :=
    (ModuleCat.isZero_iff_subsingleton).mp h1
  exact Subsingleton.elim a b

theorem root_res (q : ℕ) (X U V : Scheme.{0}) (u : (Γ(X, ⊤))ˣ) (x : U ⟶ X) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ)
    (hv : v ^ q = Units.map g.appTop.hom.toMonoidHom (Units.map x.appTop.hom.toMonoidHom u)) :
    v ^ q = Units.map (Sx.res (E := sch.obj X) (p := 0) g x : V ⟶ X).appTop.hom.toMonoidHom u := by
  have e : (Sx.res (E := sch.obj X) (p := 0) g x : V ⟶ X) = g ≫ x := rfl
  rw [hv, e]; ext; simp
  rfl

theorem kum_uniq_of (hl : uniq_prim_loc) (hg : sections_unique_of_local_agreement) (hb : uniq_ev_basic) : kum_uniq := by
  intro q _ X u hq γ γ' h h'
  have key : γ = γ' := by
    apply Subtype.ext
    apply (hb (ZMod q)).2.2.1
    intro p s hs U x
    rcases p with _ | _ | p
    · have hs' : s = 1 := by omega
      subst hs'
      have hqU : IsUnit ((q : ℕ) : Γ(U, ⊤)) := by
        have := hq.map x.appTop.hom
        simpa using this
      obtain ⟨S, hS, hP⟩ := (hl q U).2.2.2 hqU (Units.map x.appTop.hom.toMonoidHom u)
      apply (hg (ZMod q) _ U).1
      refine ⟨S, hS, fun V g hgS => ?_⟩
      obtain ⟨v, hv⟩ := hP V g hgS
      rw [(hb (ZMod q)).2.1, (hb (ZMod q)).2.1]
      have hv' := root_res q X U V u x g v hv
      rw [h.2 V _ v hv', h'.2 V _ v hv']
    · have hs' : s = 0 := by omega
      subst hs'
      rw [h.1 U x, h'.1 U x]
    · exact sec_neg_eq q s (by omega) U _ _
  rw [key]

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.KumPowCocPf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

abbrev LkumTex : Prop := ∀ (q : ℕ) [NeZero q], IsKum q (kumT q)

abbrev LevMk : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
  (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U),
  (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) →
  ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x

abbrev LevDelta : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m)
  (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}),
  (∀ (x : Sx E 0 U), ev (δ n m α) 0 m (by simp) U x = Sec.map (I.d n m) (ev α 0 n (by simp) U x)) ∧
  ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U),
    ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) +
      m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U (x.face i)

lemma units_map_appTop_comp {V U X : Scheme.{0}} (g : V ⟶ U) (x : U ⟶ X) (u : (Γ(X, ⊤))ˣ) :
    Units.map g.appTop.hom.toMonoidHom (Units.map x.appTop.hom.toMonoidHom u) =
      Units.map (g ≫ x).appTop.hom.toMonoidHom u := by
  ext; simp; rfl

lemma isUnit_q_pull {U X : Scheme.{0}} (q : ℕ) (x : U ⟶ X) (hq : IsUnit (q : Γ(X, ⊤))) :
    IsUnit (q : Γ(U, ⊤)) := by
  simpa using hq.map x.appTop.hom

theorem kum_pow_coc_of (hk : LkumTex) (hmk : LevMk) (hd : LevDelta) (he : kum_exists) : kum_pow_coc := by
  intro q _ X u hq
  let I := res _ (tw q 1)
  let a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 0 = s → ∀ U : Scheme.{0}, Sx (sch.obj X) p U → Sec (I.X s) U :=
    fun p s _ U x => if hs : s = 0 then (by subst hs; exact kumT q U (Units.map (x : U ⟶ X).appTop.hom.toMonoidHom u))
      else 0
  have ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx (sch.obj X) p U),
      Sec.res g (a p s h U x) = a p s h V (x.res g) := by
    intro p s h V U g x
    by_cases hs : s = 0
    · subst hs
      simp only [a, dif_pos]
      rw [(hk q).1 V U g _ (isUnit_q_pull q x hq)]
      exact congrArg (kumT q V) (units_map_appTop_comp g x u)
    · simp only [a, dif_neg hs, map_zero]
  obtain ⟨α, hα⟩ := hmk (ZMod q) a ha
  refine ⟨Cocycle.mk (δ 0 1 α) 2 (by norm_num) (δ_δ 0 1 2 α), ⟨?_, ?_⟩, ?_⟩
  · have key : ∀ (U : Scheme.{0}) (x : Sx (sch.obj X) (0 + 1) U), ev (δ 0 1 α) (0 + 1) 0 (by simp) U x = 0 := by
      intro U x
      rw [(hd (ZMod q) (n := 0) (m := 1) (by norm_num) α U).2 0 (-1) 0 (by simp) (by simp) x, hα]
      have z : a (0 + 1) (-1) (by simp) U x = 0 := dif_neg (by norm_num)
      have f0 : x.face 0 = x.face 1 := rfl
      rw [z, Fin.sum_univ_two, f0]
      simp [Sec.map]
    exact fun U x => key U x
  · intro U x v hv
    obtain ⟨γ0, _, hγ0⟩ := he q X (u ^ q) hq
    have e1 := hγ0 U x v hv
    have e2 := hγ0 U x (Units.map x.appTop.hom.toMonoidHom u) (by rw [map_pow])
    have h1 := (hd (ZMod q) (n := 0) (m := 1) (by norm_num) α U).1 x
    refine h1.trans ?_
    erw [hα]
    simp only [a, dif_pos]
    exact e2.symm.trans e1
  · rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨0, by norm_num, α, rfl⟩

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.ExactLocPf
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ExactLocPf

variable {R : Type} [CommRing R]

lemma kernel_lift_sec (S : ShortComplex (Shv R)) (U : Scheme.{0}) (b : Sec S.X₂ U)
    (hb : Sec.map S.g b = 0) : ∃ k : Sec (kernel S.g) U, Sec.map (kernel.ι S.g) k = b := by
  let T : ShortComplex (Shv R) := ShortComplex.mk (kernel.ι S.g) S.g (kernel.condition _)
  have hT : T.Exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel S.g)
  have : Mono T.f := by dsimp [T]; infer_instance
  have hE : (T.map (LateralTheory.EtaleFoundations.ResSecPf.secF R U)).Exact :=
    hT.map_of_mono_of_preservesKernel _ this inferInstance
  rw [ShortComplex.moduleCat_exact_iff] at hE
  exact hE b hb

lemma epi_lift (S : ShortComplex (Shv R)) (hS : S.Exact) :
    Epi (kernel.lift S.g S.f S.zero) := by
  exact hS.epi_kernelLift

end LateralTheory.EtaleFoundations.ExactLocPf

open LateralTheory.EtaleFoundations.ExactLocPf in
theorem LateralTheory.EtaleFoundations.ResSecPf.exact_loc_of : LateralTheory.EtaleFoundations.ResSecPf.exact_loc := by
  intro R _ S hS U b hb
  obtain ⟨k, hk⟩ := kernel_lift_sec S U b hb
  let p := kernel.lift S.g S.f S.zero
  have : Epi p := epi_lift S hS
  have hls : Sheaf.IsLocallySurjective p := (Sheaf.isLocallySurjective_iff_epi' (φ := p)).2 this
  refine ⟨Presheaf.imageSieve p.hom k, Presheaf.imageSieve_mem Scheme.etaleTopology p.hom (U := op U) k, ?_⟩
  rintro V g ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have e1 : S.f = p ≫ kernel.ι S.g := (kernel.lift_ι _ _ _).symm
  have e2 : Sec.map S.f a = Sec.map (kernel.ι S.g) (Sec.map p a) := by
    rw [e1]; rfl
  rw [e2, ← hk]
  change Sec.map (kernel.ι S.g) ((p.hom.app _).hom a) = _
  have ha' : (p.hom.app (op V)).hom a = ((kernel S.g).obj.map g.op).hom k := ha
  rw [ha']
  exact congrArg (fun f => f.hom k) ((kernel.ι S.g).hom.naturality g.op)
end

section -- merged from Development.EtaleCohomology.TateTwists.KumExistsPf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def L_kumT_ex : Prop := ∀ (q : ℕ) [NeZero q], IsKum q (kumT q)

def L_prim_loc : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), (IsUnit (q : Γ(U, ⊤)) → Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))) ∧ (∀ ζ ξ : Prim q Γ(U, ⊤), Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) ∧ (∀ (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)), x ^ q = 1 → Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a) ∧ (IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ, Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u)

def L_sec_glue : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg

def L_sch_cls : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (I : Cx R) (m n k : ℤ), m + 1 = n → n + 1 = k → (∀ z : Sec (I.X n) X, Sec.map (I.d n k) z = 0 → ∃ α : Cocycle ((chains R).obj (sch.obj X)) I n, (∀ (U : Scheme.{0}) (x : U ⟶ X), ev α.1 0 n (by simp) U x = Sec.res x z) ∧ ∀ (p : ℕ) s h U x, ev α.1 (p + 1) s h U x = 0) ∧ ∀ α : Cocycle ((chains R).obj (sch.obj X)) I n, Sec.map (I.d n k) (ev α.1 0 n (by simp) X (𝟙 X)) = 0 ∧ (CohomologyClass.mk α = 0 ↔ ∃ y : Sec (I.X m) X, Sec.map (I.d m n) y = ev α.1 0 n (by simp) X (𝟙 X))

def L_res_sec : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ z : Sec ((res R F).X 0) U, Sec.map ((res R F).d 0 1) z = 0 ↔ ∃ a : Sec F U, Sec.map (resι R F) a = z) ∧ Function.Injective (Sec.map (resι R F) (U := U)) ∧ (∀ (m n k : ℤ), 0 < n → m + 1 = n → ∀ z : Sec ((res R F).X n) U, n + 1 = k → Sec.map ((res R F).d n k) z = 0 → Loc U fun V g => ∃ y : Sec ((res R F).X m) V, Sec.map ((res R F).d m n) y = Sec.res g z) ∧ ∀ n : ℤ, n < 0 → Subsingleton (Sec ((res R F).X n) U)

section Basic
variable {R : Type} [CommRing R]

theorem sec_res_map {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  (ConcreteCategory.congr_hom (φ.hom.naturality g.op) x).symm

theorem sec_res_comp {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  show (F.obj.map (k ≫ g).op).hom x = (F.obj.map k.op).hom ((F.obj.map g.op).hom x)
  rw [op_comp, Functor.map_comp]
  rfl

theorem sec_res_zero {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 := map_zero _

theorem sec_map_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem sec_map_add {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x + y) = Sec.map φ x + Sec.map φ y := LinearMap.map_add _ _ _

theorem sec_map_zero {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (0 : F ⟶ G) x = 0 := by
  simp [Sec.map]

end Basic

theorem prim_pow {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨p, hp⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hp
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, ζ.2.2, zero_mul] at h
  exact sub_eq_zero.mp h

theorem prim_isUnit {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) : IsUnit ζ.1 :=
  IsUnit.of_pow_eq_one (prim_pow ζ) (NeZero.ne q)

theorem units_root {q : ℕ} {X U V : Scheme.{0}} (u : (Γ(X, ⊤))ˣ) (x : U ⟶ X) (g : V ⟶ U) (w : (Γ(U, ⊤))ˣ)
    (h : w ^ q = Units.map x.appTop.hom.toMonoidHom u) :
    (Units.map g.appTop.hom.toMonoidHom w) ^ q = Units.map (g ≫ x).appTop.hom.toMonoidHom u := by
  rw [← map_pow, h]
  ext
  simp
  rfl

section Kum
variable (q : ℕ) [NeZero q]

theorem d_resGen (hR : L_res_sec) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) :
    Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (resGen 1 ζ) = 0 :=
  ((hR (ZMod q) (tw q 1) U).1 _).2 ⟨twGen 1 ζ, rfl⟩

theorem dt_pow (hK : L_kumT_ex) (hR : L_res_sec) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (a : ℕ) :
    ∀ v w : (Γ(U, ⊤))ˣ, (w : Γ(U, ⊤)) = ζ.1 ^ a * v →
      Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q U w) = Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q U v) := by
  induction a with
  | zero =>
    intro v w h
    have : w = v := Units.ext (by simpa using h)
    subst this; rfl
  | succ a ih =>
    intro v w h
    let m : (Γ(U, ⊤))ˣ := (prim_isUnit ζ).unit ^ a * v
    have hm : (m : Γ(U, ⊤)) = ζ.1 ^ a * v := by simp [m]
    have hw : (w : Γ(U, ⊤)) = ζ.1 * m := by rw [h, hm, pow_succ]; ring
    rw [(hK q).2 U ζ m w hw, sec_map_add, d_resGen q hR, add_zero]
    exact ih v m hm

theorem dt_root (hK : L_kumT_ex) (hP : L_prim_loc) (hG : L_sec_glue) (hR : L_res_sec) {W : Scheme.{0}}
    (hqW : IsUnit (q : Γ(W, ⊤))) (w1 w2 : (Γ(W, ⊤))ˣ) (h : w1 ^ q = w2 ^ q) :
    Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q W w1) = Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q W w2) := by
  let ρ : (Γ(W, ⊤))ˣ := w2 * w1⁻¹
  have hρ : ρ ^ q = 1 := by
    simp only [ρ]; rw [mul_pow, inv_pow, ← h, mul_inv_cancel]
  apply (hG (ZMod q) _ W).1
  obtain ⟨S, hS, hPS⟩ := (hP q W).1 hqW
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨ζ⟩ := hPS V g hg
  have hqV : IsUnit (q : Γ(V, ⊤)) := by simpa using hqW.map g.appTop.hom
  have hr : (g.appTop.hom (ρ : Γ(W, ⊤))) ^ q = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hρ, Units.val_one, map_one]
  rw [sec_res_map, sec_res_map, (hK q).1 V W g w1 hqW, (hK q).1 V W g w2 hqW]
  apply (hG (ZMod q) _ V).1
  obtain ⟨T, hT, hPT⟩ := (hP q V).2.2.1 ζ _ hr
  refine ⟨T, hT, fun V' k hk => ?_⟩
  dsimp only
  obtain ⟨a, ha⟩ := hPT V' k hk
  rw [sec_res_map, sec_res_map, (hK q).1 V' V k _ hqV, (hK q).1 V' V k _ hqV]
  symm
  apply dt_pow q hK hR (Prim.map k.appTop.hom ζ) a
  have e : (w2 : Γ(W, ⊤)) = (ρ : Γ(W, ⊤)) * w1 := by simp [ρ]
  change k.appTop.hom (g.appTop.hom (w2 : Γ(W, ⊤))) = (k.appTop.hom ζ.1) ^ a * k.appTop.hom (g.appTop.hom (w1 : Γ(W, ⊤)))
  rw [e, map_mul, map_mul, ha]

end Kum

theorem kum_exists_of (hK : L_kumT_ex) (hP : L_prim_loc) (hG : L_sec_glue) (hC : L_sch_cls) (hR : L_res_sec) :
    kum_exists := by
  intro q _ X u hq
  have hqU : ∀ {U : Scheme.{0}} (x : U ⟶ X), IsUnit (q : Γ(U, ⊤)) := fun x => by simpa using hq.map x.appTop.hom
  have key : ∀ {U : Scheme.{0}} (x : U ⟶ X) (w1 w2 : (Γ(U, ⊤))ˣ), w1 ^ q = Units.map x.appTop.hom.toMonoidHom u →
      w2 ^ q = Units.map x.appTop.hom.toMonoidHom u →
      Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q U w1) = Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q U w2) :=
    fun x w1 w2 h1 h2 => dt_root q hK hP hG hR (hqU x) w1 w2 (h1.trans h2.symm)
  obtain ⟨S, hS, hroot⟩ := (hP q X).2.2.2 hq u
  choose v hv using hroot
  obtain ⟨z, hz⟩ := (hG (ZMod q) ((res (ZMod q) (tw q 1)).X 1) X).2 S hS
    (fun V g hg => Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q V (v V g hg))) (by
      intro V W g k hg
      rw [sec_res_map, (hK q).1 W V k _ (hqU g)]
      exact key (k ≫ g) _ _ (units_root u g k _ (hv V g hg)) (hv W (k ≫ g) _))
  have hdz : Sec.map ((res (ZMod q) (tw q 1)).d 1 2) z = 0 := by
    apply (hG (ZMod q) _ X).1
    refine ⟨S, hS, fun V g hg => ?_⟩
    dsimp only
    rw [sec_res_map, hz V g hg, sec_res_zero, ← sec_map_comp, HomologicalComplex.d_comp_d, sec_map_zero]
  obtain ⟨α, hα0, hα1⟩ := (hC (ZMod q) X (res (ZMod q) (tw q 1)) 0 1 2 (by norm_num) (by norm_num)).1 z hdz
  refine ⟨α, fun U x => hα1 0 0 _ U x, fun U x w hw => ?_⟩
  rw [hα0 U x]
  apply (hG (ZMod q) _ U).1
  refine ⟨S.pullback x, (Scheme.etaleTopology).pullback_stable x hS, fun V g hg => ?_⟩
  dsimp only
  rw [← sec_res_comp, hz V (g ≫ x) hg, sec_res_map, (hK q).1 V U g w (hqU x)]
  exact key (g ≫ x) _ _ (hv V (g ≫ x) hg) (units_root u x g w hw)

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.KumNatPf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def ev_basic : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x, ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧ ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧ ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧ ∀ c : ℤ, ev (c • α) p s h U x = c • ev α p s h U x) ∧ (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)) ∧ (∀ α β : Cochain ((chains R).obj E) I n, (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β) ∧ (∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U), ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f)) ∧ ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x, ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x)

def prim_loc : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), (IsUnit (q : Γ(U, ⊤)) → Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))) ∧ (∀ ζ ξ : Prim q Γ(U, ⊤), Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) ∧ (∀ (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)), x ^ q = 1 → Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a) ∧ (IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ, Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u)

def sec_glue : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg

theorem res_neg_isZero (R : Type) [CommRing R] (F : Shv R) (s : ℤ) (hs : s < 0) : IsZero ((res R F).X s) := by
  unfold res InjectiveResolution.cochainComplex
  exact HomologicalComplex.isZero_extend_X _ _ _ (by intro i h; change ((i : ℕ) : ℤ) = s at h; omega)

theorem units_map_comp {V U X : Scheme.{0}} (g : V ⟶ U) (x : U ⟶ X) (u : (Γ(X, ⊤))ˣ) :
    Units.map (g ≫ x).appTop.hom.toMonoidHom u =
      Units.map g.appTop.hom.toMonoidHom (Units.map x.appTop.hom.toMonoidHom u) := by
  ext; simp; rfl

theorem isUnit_q_map {U X : Scheme.{0}} (x : U ⟶ X) (q : ℕ) (hq : IsUnit (q : Γ(X, ⊤))) :
    IsUnit (q : Γ(U, ⊤)) := by
  simpa using hq.map x.appTop.hom

theorem kum_unique (hev : ev_basic) (hpl : prim_loc) (hsg : sec_glue) (q : ℕ) [NeZero q] (X : Scheme.{0})
    (u : (Γ(X, ⊤))ˣ) (hq : IsUnit (q : Γ(X, ⊤)))
    (γ γ' : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1)
    (h1 : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0)
    (h2 : ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
        ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v))
    (h1' : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ'.1 1 0 (by simp) U x = 0)
    (h2' : ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
        ev γ'.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) : γ = γ' := by
  apply Cocycle.ext
  apply (hev (ZMod q)).2.2.1
  intro p s h U x
  match p, s, h with
  | 0, s, h =>
    obtain rfl : s = 1 := by omega
    revert x
    show ∀ x : U ⟶ X, _
    intro x
    apply (hsg (ZMod q) _ U).1
    obtain ⟨S, hS, hroot⟩ := (hpl q U).2.2.2 (isUnit_q_map x q hq) (Units.map x.appTop.hom.toMonoidHom u)
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨v, hv⟩ := hroot V g hg
    have hv' : v ^ q = Units.map (g ≫ x).appTop.hom.toMonoidHom u := by rw [units_map_comp]; exact hv
    exact ((hev (ZMod q)).2.1 γ.1 0 1 h V U g x).trans ((h2 V (g ≫ x) v hv').trans
      ((h2' V (g ≫ x) v hv').symm.trans ((hev (ZMod q)).2.1 γ'.1 0 1 h V U g x).symm))
  | 1, s, h =>
    obtain rfl : s = 0 := by omega
    exact (h1 U x).trans (h1' U x).symm
  | p + 2, s, h =>
    have hz := res_neg_isZero (ZMod q) (tw q 1) s (by omega)
    have hv : γ.1.v (-((p + 2 : ℕ) : ℤ)) s h = γ'.1.v (-((p + 2 : ℕ) : ℤ)) s h := hz.eq_of_tgt _ _
    unfold ev
    rw [hv]

theorem kum_nat_of (he : kum_exists) (hev : ev_basic) (hpl : prim_loc) (hsg : sec_glue) : kum_nat := by
  intro q _ Y X f u hq
  obtain ⟨γ, hc, h1, h2⟩ := kum_spec_of_exists he q X u hq
  have hqY := isUnit_q_map f q hq
  obtain ⟨γ', hc', h1', h2'⟩ := kum_spec_of_exists he q Y (Units.map f.appTop.hom.toMonoidHom u) hqY
  rw [← hc, ← hc']
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (sch.map f))) γ (zero_add 1)) = _
  congr 1
  refine kum_unique hev hpl hsg q Y _ hqY _ γ' ?_ ?_ h1' h2'
  · intro U x
    exact ((hev (ZMod q)).2.2.2.1 (sch.map f) γ.1 1 0 (by simp) U x).trans (h1 U (x ≫ f))
  · intro U x v hv
    exact ((hev (ZMod q)).2.2.2.1 (sch.map f) γ.1 0 1 (by simp) U x).trans
      (h2 U (x ≫ f) v (by rw [hv, units_map_comp]))

end LateralTheory.EtaleFoundations
end

namespace LateralTheory.Fix.EtaleKummerClassExplicitCocycle
open LateralTheory.EtaleFoundations

theorem primLoc : EtalePrimitiveRootsExistLocally := etale_locally_roots_of_unity_structure_of_exists_and_kummer etale_locally_exists_primitive_root_of_unity_of_invertible_order etale_locally_kummer_roots_of_units_of_invertible_order
theorem resSec : EtaleInjectiveResolutionSectionsLocallyExact := etaleSheaf_injectiveResolution_sections_exact_of_local_exactness LateralTheory.EtaleFoundations.ResSecPf.exact_loc_of

theorem holds_of (hK : EtaleKummerTriangleExists) : EtaleKummerClassExplicitCocycle := by
  have he : kum_exists := kum_exists_of hK primLoc etale_sheaf_sections_glue_of_forget_isSheaf LateralTheory.Fix.EtaleSchemeGlobalSectionCohomologyClass.intersectionNumber_baseChange resSec
  exact etale_kummer_class_specification_of_existence_naturality_additivity he
    (kum_nat_of he etale_chain_cochain_eval_basic_properties_hold primLoc etale_sheaf_sections_glue_of_forget_isSheaf)
    (kum_add_of he (kum_uniq_of primLoc etale_sheaf_sections_glue_of_forget_isSheaf etale_chain_cochain_eval_basic_properties_hold)
      (kum_mul_coc_of hK primLoc etale_sheaf_sections_glue_of_forget_isSheaf etale_chain_cochain_exists_of_eval_data etale_chain_cochain_eval_differential_formula_holds etale_chain_cochain_eval_basic_properties_hold)
      (kum_pow_coc_of hK etale_chain_cochain_exists_of_eval_data etale_chain_cochain_eval_differential_formula_holds he))

end LateralTheory.Fix.EtaleKummerClassExplicitCocycle
