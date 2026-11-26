module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepOp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLCRes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPrimitiveCl
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UntiltIterateSymmEpsilon
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeomPtGeomMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NatDegreeLgLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRoot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechTripleSubfaceZero
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedRootOfRep
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeMap

theorem redRoot_of_rep : CrystallineSemistableComparison.E.RepRoot → CrystallineSemistableComparison.E.RepOp → CrystallineSemistableComparison.E.RepConc → CrystallineSemistableComparison.E.RedRoot := by
  intro hRoot hOp hConc inOp inRed Q q _ _ hq i X ζ ξ hξ
  have h1 : Rep (rootClass i ζ) (resGen i ζ) := (hRoot Q i X ζ).2
  have h2 : Rep (rootClass i ξ) (resGen i ξ) := (hRoot q i X ξ).2
  have h3 := hOp inOp _ _ _ _ (redMap Q q i) X 0 (rootClass i ζ) _ h1
  rw [inRed Q q hq i X ζ ξ hξ] at h3
  exact (hConc (ZMod q) _ X 0 (resGen i ξ)).2.2 _ _ h3 h2

end GlobalTheory.CompanionTheory.EdgeMap
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StTopOfStCol
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeMap

theorem stTop_of_stCol : CrystallineSemistableComparison.E.StCol → CrystallineSemistableComparison.E.StTop := by
  intro hCol R _ C _ F T hT j z hz s
  obtain ⟨hι, hdv, -, hex0, hex⟩ := hCol R C F T hT
  induction s with
  | zero =>
    intro k x hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨(hex0 j _).2 ⟨_, rfl⟩, by rw [hι, hz, map_zero]⟩
  | succ s ih =>
    intro k x hx
    obtain ⟨a, rfl, ha⟩ := hx
    have h1 := (ih (k + 1) _ ha).1
    rw [map_zsmul] at h1
    have h2 : T.dvC s (k + 1) (d _ k a) = 0 :=
      (IsUnit.smul_eq_zero ((isUnit_neg_one (α := ℤ)).pow k)).1 h1
    exact ⟨(hex s k _).2 ⟨a, rfl⟩, by rw [hdv]; exact h2⟩

end GlobalTheory.CompanionTheory.EdgeMap
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedResMor
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.EdgeRed

theorem res_res {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res h (Sec.res g x) = Sec.res (h ≫ g) x := by
  simp [Sec.res]

theorem res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have h := φ.hom.naturality g.op
  exact (congrArg (fun t => t.hom x) h).symm

variable {C C' : Type 1} [Category.{0} C] [Category.{0} C']

def redResMor (hS : KapSpec) (hK : KapRed) (hR : InRed) {Q q : ℕ} [NeZero Q] [NeZero q] (h : q ∣ Q)
    (P : Probe C Q) (P' : Probe C' q) (m : Mor P.L P'.L (RingHom.id ℤ))
    (g : ∀ c : C', P'.U c ⟶ P.U (m.G.obj c))
    (hg : ∀ {c c' : C'} (φ : c ⟶ c'), g c' ≫ (P.S.map (m.G.map φ)).unop = (P'.S.map φ).unop ≫ g c)
    (hτ : ∀ c (f : LocallyConstant (P.U (m.G.obj c)) (ZMod Q)),
      m.τ c f = lcRes q (g c) (f.map (ZMod.castHom h (ZMod q))))
    (hζ : ∀ c, (P'.ζ c).1 = (primRes (g c) (P.ζ _)).1 ^ (Q / q)) (i : ℤ) :
    ResMor (P.res i) (P'.res i) m where
  τ s c :=
    { toFun := fun x => Sec.res (g c) ((redMap Q q i).app (P.U (m.G.obj c)) (s : ℤ) x)
      map_zero' := by simp
      map_add' := fun x y => by simp }
  nat s {c c'} φ x := by
    change Sec.res (g c') ((redMap Q q i).app _ (s : ℤ) (Sec.res (P.S.map (m.G.map φ)).unop x)) =
      Sec.res (P'.S.map φ).unop (Sec.res (g c) ((redMap Q q i).app _ (s : ℤ) x))
    rw [← (redMap Q q i).nat, res_res, res_res, hg]
  ι c x := by
    change Sec.res (g c) ((redMap Q q i).app _ 0 (Sec.map (resι _ (tw Q i)) (kap i (P.ζ (m.G.obj c)) x))) =
      Sec.map (resι _ (tw q i)) (kap i (P'.ζ c) (m.τ c x))
    rw [(redMap Q q i).nat, res_map, (hS Q i _ (P.ζ (m.G.obj c)) x).2.2 _ (g c),
      hK hR Q q h i _ (primRes (g c) (P.ζ (m.G.obj c))) (P'.ζ c) (hζ c), hτ]
    rfl
  dv s c x := by
    change Sec.res (g c) ((redMap Q q i).app _ ((s + 1 : ℕ) : ℤ) (Sec.map ((GlobalTheory.EtC.res _ (tw Q i)).d (s : ℤ) ((s + 1 : ℕ) : ℤ)) x)) =
      Sec.map ((GlobalTheory.EtC.res _ (tw q i)).d (s : ℤ) ((s + 1 : ℕ) : ℤ)) (Sec.res (g c) ((redMap Q q i).app _ (s : ℤ) x))
    rw [← (redMap Q q i).comm, res_map]

theorem etRed : CrystallineSemistableComparison.E.EtSpec → CrystallineSemistableComparison.E.EdgeMap → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.RepOp → CrystallineSemistableComparison.E.KapSpec →
    CrystallineSemistableComparison.E.KapRed → CrystallineSemistableComparison.E.EtRed := by
  intro hSpec hEdge hRep hOpR hS hK hGen hR hOp Q q _ _ h C C' _ _ P P' X Y Y' m g hg hτ hy hζ i j x
  obtain ⟨a, ha⟩ := (hRep _ _ X (j : ℤ)).1 x
  have hE := (hSpec hGen Q C P X Y i j x).1 a ha
  have hE' := hEdge ℤ ℤ (RingHom.id ℤ) C C' P.L P'.L (P.res i) (P'.res i) m
    (redResMor hS hK hR h P P' m g hg hτ hζ i) j _ _ hE
  have hr : Rep (red Q q _ (j : ℤ) i x) ((redMap Q q i).app X (j : ℤ) a) :=
    hOpR hOp _ _ _ _ (redMap Q q i) X (j : ℤ) x a ha
  refine (hSpec hGen q C' P' X Y' i j (red Q q _ (j : ℤ) i x)).2 _ ⟨_, hr, ?_⟩
  convert hE' using 1
  funext t
  change Sec.res (Y'.y _) ((redMap Q q i).app X (j : ℤ) a) =
    Sec.res (g _) ((redMap Q q i).app _ (j : ℤ) (Sec.res (Y.y _) a))
  rw [← (redMap Q q i).nat, res_res, hy]

end GlobalTheory.CompanionTheory.EdgeRed
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StUniq
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeStair

theorem stUniq : CrystallineSemistableComparison.E.StCol → CrystallineSemistableComparison.E.StUniq := by
  intro hcol R _ C _ F T hT j z
  obtain ⟨hι, hdv, hinj, hex0, hex⟩ := hcol R C F T hT
  have key : ∀ (s k : ℕ) (x : Cn (T.K s) k), T.St z s k x → T.BZ s k x → z ∈ (cx F).B j := by
    intro s
    induction s with
    | zero =>
      intro k x hS hB
      obtain ⟨h, rfl⟩ := hS
      subst h
      cases j with
      | zero =>
        have h0 : T.ιC 0 z = 0 := hB
        have hz : z = 0 := hinj 0 (by rw [h0, map_zero])
        rw [hz]
        exact Submodule.zero_mem _
      | succ k =>
        obtain ⟨b, hb, hdb⟩ := hB
        obtain ⟨z', rfl⟩ := (hex0 k b).1 hb
        refine (⟨z', ?_⟩ : z ∈ LinearMap.range (d F k))
        apply hinj (k + 1)
        rw [← hι]
        exact hdb
    | succ s ih =>
      intro k x hS hB
      obtain ⟨a, rfl, hS'⟩ := hS
      cases k with
      | zero =>
        exact ih 1 _ hS' ⟨a, hB, by simp⟩
      | succ k =>
        obtain ⟨b, hb, hdb⟩ := hB
        obtain ⟨b', rfl⟩ := (hex s k b).1 hb
        refine ih (k + 2) _ hS' ⟨(-1 : ℤ) ^ (k + 1) • (a - d _ k b'), ?_, ?_⟩
        · rw [map_zsmul, map_sub, ← hdv, hdb, sub_self, smul_zero]
        · rw [map_zsmul, map_sub, d_d, sub_zero]
  intro s k x hS hB
  exact key s k x hS hB

end GlobalTheory.CompanionTheory.EdgeStair
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LcCover
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.LcCoverProof

theorem lcCover : CrystallineSemistableComparison.E.LcCover := by
  intro U ι f
  let O : ι → U.Opens := fun a => ⟨f ⁻¹' {a}, f.isLocallyConstant.isOpen_fiber a⟩
  have hcov : iSup O = ⊤ :=
    eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨f x, rfl⟩
  have hval : ∀ (a : ι) (v : (O a).toScheme), f ((O a).ι v) = a := fun a v => v.2
  refine ⟨fun a => (O a).toScheme, fun a => (O a).ι, hval, ?_, ?_, ?_⟩
  · intro V g a hg
    have hr : Set.range g ⊆ Set.range (O a).ι := by
      rintro _ ⟨v, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hg v
    exact ⟨IsOpenImmersion.lift (O a).ι g hr, IsOpenImmersion.lift_fac _ _ _⟩
  · intro x y h
    refine U.sheaf.eq_of_locally_eq' O ⊤ (fun a => homOfLE le_top) hcov.ge x y fun a => ?_
    have e : O a ≤ (O a).ι ''ᵁ ⊤ := by simp
    have hm : U.presheaf.map (homOfLE le_top : O a ⟶ ⊤).op =
        U.presheaf.map (homOfLE (x := (O a).ι ''ᵁ ⊤) le_top).op ≫ U.presheaf.map (homOfLE e).op := by
      rw [← Functor.map_comp]
      rfl
    have := congrArg (U.presheaf.map (homOfLE e).op).hom (h a)
    change (U.presheaf.map (homOfLE le_top : O a ⟶ ⊤).op).hom x =
      (U.presheaf.map (homOfLE le_top : O a ⟶ ⊤).op).hom y
    rw [hm]
    exact this
  · intro R _ G x
    have hG := (isSheaf_iff_isSheaf_of_type _ _).1
      ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R)))).1 G.property)
    have hS : Sieve.ofArrows (fun a => (O a).toScheme) (fun a => (O a).ι) ∈ Scheme.etaleTopology U :=
      Scheme.zariskiTopology_le_etaleTopology _
        (Scheme.Cover.mem_grothendieckTopology (U.openCoverOfIsOpenCover O hcov))
    have hsf := hG _ hS
    rw [Sieve.ofArrows, ← Presieve.isSheafFor_iff_generate, Presieve.isSheafFor_arrows_iff] at hsf
    refine hsf x ?_
    intro a b Z gi gj h
    by_cases hab : a = b
    · subst hab
      have : gi = gj := by rwa [cancel_mono] at h
      rw [this]
    · have hE : IsEmpty Z := ⟨fun z => hab (by
        have h1 := hval a (gi z)
        have h2 := hval b (gj z)
        rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply, h2] at h1
        exact h1.symm)⟩
      have hz := (Sheaf.isTerminalOfBotCover G Z (Scheme.bot_mem_grothendieckTopology Z)).isZero
      have := ModuleCat.subsingleton_of_isZero hz
      exact Subsingleton.elim _ _

end GlobalTheory.CompanionTheory.LcCoverProof
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KapSurjective
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.KapBij

section Res

variable {R : Type} [CommRing R] {F : Shv R}

theorem res_smul {V U : Scheme.{0}} (g : V ⟶ U) (c : ULift.{1} R) (a : Sec F U) :
    Sec.res g (c • a) = c • Sec.res g a :=
  map_smul _ _ _

theorem res_res {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res k (Sec.res g a) = Sec.res (k ≫ g) a := by
  show (F.obj.map k.op).hom ((F.obj.map g.op).hom a) = (F.obj.map (k ≫ g).op).hom a
  rw [op_comp, F.obj.map_comp]
  rfl

end Res

theorem nsmul_eq_up {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (c : ℕ) (t : M) :
    c • t = (ULift.up (c : ZMod q) : ULift.{1} (ZMod q)) • t := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  congr 1

theorem coef_eq_zero (hg : InGen) {q : ℕ} [NeZero q] (i : ℤ) {V : Scheme.{0}} [Nonempty V]
    (ζ : Prim q Γ(V, ⊤)) (a : ZMod q)
    (h : (ULift.up a : ULift.{1} (ZMod q)) • twGen i ζ = 0) : a = 0 := by
  have hq : q ∣ a.val := (hg q i).2.1 V ζ a.val (by
    rw [nsmul_eq_up (q := q), ZMod.natCast_zmod_val]
    exact h)
  rw [← ZMod.natCast_zmod_val a]
  exact (ZMod.natCast_eq_zero_iff _ _).2 hq

theorem coef_unique (hg : InGen) {q : ℕ} [NeZero q] (i : ℤ) {V : Scheme.{0}} [Nonempty V]
    (ζ : Prim q Γ(V, ⊤)) (a b : ZMod q)
    (h : (ULift.up a : ULift.{1} (ZMod q)) • twGen i ζ = (ULift.up b : ULift.{1} (ZMod q)) • twGen i ζ) :
    a = b := by
  refine sub_eq_zero.1 (coef_eq_zero hg i ζ _ ?_)
  have e : (ULift.up (a - b) : ULift.{1} (ZMod q)) = ULift.up a - ULift.up b := rfl
  rw [e, sub_smul, h, sub_self]

theorem coef_agree (hR : RepRoot) (hg : InGen) {q : ℕ} [NeZero q] (i : ℤ) {U : Scheme.{0}}
    (ζ : Prim q Γ(U, ⊤)) (x : Sec (tw q i) U) {V V' : Scheme.{0}} (g : V ⟶ U) (g' : V' ⟶ U)
    (c c' : ZMod q)
    (h : Sec.res g x = (ULift.up c : ULift.{1} (ZMod q)) • Sec.res g (twGen i ζ))
    (h' : Sec.res g' x = (ULift.up c' : ULift.{1} (ZMod q)) • Sec.res g' (twGen i ζ))
    (v : V) (v' : V') (hv : g v = g' v') : c = c' := by
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback v v' hv
  have : Nonempty ↑(pullback g g') := ⟨z⟩
  have e1 : Sec.res (pullback.fst g g' ≫ g) x =
      (ULift.up c : ULift.{1} (ZMod q)) • Sec.res (pullback.fst g g' ≫ g) (twGen i ζ) := by
    rw [← res_res, h, res_smul, res_res]
  have e2 : Sec.res (pullback.fst g g' ≫ g) x =
      (ULift.up c' : ULift.{1} (ZMod q)) • Sec.res (pullback.fst g g' ≫ g) (twGen i ζ) := by
    rw [pullback.condition, ← res_res, h', res_smul, res_res]
  rw [((hR q i U ζ).1 _ (pullback.fst g g' ≫ g)).1] at e1 e2
  exact coef_unique hg i _ c c' (e1.symm.trans e2)

theorem exists_chart (hR : RepRoot) (hg : InGen) {q : ℕ} [NeZero q] (i : ℤ) {U : Scheme.{0}}
    (ζ : Prim q Γ(U, ⊤)) (x : Sec (tw q i) U) (u : U) :
    ∃ (V : Scheme.{0}) (g : V ⟶ U), IsAffine V ∧ Etale g ∧ u ∈ Set.range g ∧
      ∃ c : ZMod q, Sec.res g x = (ULift.up c : ULift.{1} (ZMod q)) • Sec.res g (twGen i ζ) := by
  refine (loc_iff_etale_affine_points U
    (fun V g => ∃ c : ZMod q, Sec.res g x = (ULift.up c : ULift.{1} (ZMod q)) • Sec.res g (twGen i ζ))
    ?_).1 ?_ u
  · rintro V W g k ⟨c, hc⟩
    exact ⟨c, by rw [← res_res, hc, res_smul, res_res]⟩
  · obtain ⟨S, hS, hc⟩ := (hg q i).1 U ζ x
    refine ⟨S, hS, fun V g hgS => ?_⟩
    obtain ⟨c, hc⟩ := hc V g hgS
    refine ⟨(c : ZMod q), ?_⟩
    rw [hc, nsmul_eq_up (q := q), ((hR q i U ζ).1 V g).1]
    rfl

theorem kap_injective (hK : KapSpec) (hg : InGen) {q : ℕ} [NeZero q] (i : ℤ) {U : Scheme.{0}}
    (ζ : Prim q Γ(U, ⊤)) : Function.Injective (kap i ζ) := by
  refine (injective_iff_map_eq_zero (kap i ζ)).2 fun f hf => LocallyConstant.ext fun u => ?_
  let O : U.Opens := ⟨f ⁻¹' {f u}, f.isLocallyConstant.isOpen_fiber _⟩
  have : Nonempty O.toScheme := ⟨⟨u, rfl⟩⟩
  have hO : ∀ v : O.toScheme, f (O.ι v) = f u := fun v => by
    have : O.ι v ∈ Set.range O.ι := ⟨v, rfl⟩
    rw [Scheme.Opens.range_ι] at this
    exact this
  have h := (hK q i U ζ f).1 O.toScheme O.ι (f u) hO
  rw [hf] at h
  have h0 : Sec.res O.ι (0 : Sec (tw q i) U) = 0 := map_zero _
  rw [h0] at h
  exact coef_eq_zero hg i _ _ h.symm

theorem kap_surjective (hR : RepRoot) (hK : KapSpec) (hg : InGen) {q : ℕ} [NeZero q] (i : ℤ)
    {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) : Function.Surjective (kap i ζ) := by
  intro x
  choose V g hA hE hu c hc using exists_chart hR hg i ζ x
  choose y hy using hu
  have hagree : ∀ (u : U) (v : V u), c (g u v) = c u := fun u v =>
    coef_agree hR hg i ζ x (g (g u v)) (g u) _ _ (hc _) (hc u) (y _) v (hy _)
  have hop : ∀ u, IsOpen (Set.range (g u)) := fun u => by
    have := hE u
    exact (g u).isOpenMap.isOpen_range
  let f : LocallyConstant U (ZMod q) := ⟨c, (IsLocallyConstant.iff_exists_open c).2 fun u =>
    ⟨Set.range (g u), hop u, ⟨y u, hy u⟩, by
      rintro _ ⟨v, rfl⟩
      exact hagree u v⟩⟩
  refine ⟨f, ((sec_ext_glue _ _ U).1 _ _ ?_)⟩
  refine (loc_iff_etale_affine_points U (fun V g => Sec.res g (kap i ζ f) = Sec.res g x) ?_).2 fun u => ?_
  · intro V W g k h
    rw [← res_res, h, res_res]
  · refine ⟨V u, g u, hA u, hE u, ⟨y u, hy u⟩, ?_⟩
    have h := (hK q i U ζ f).1 (V u) (g u) (c u) (hagree u)
    rw [h, hc u, ((hR q i U ζ).1 _ (g u)).1]

theorem kapBij : LcCover → RepRoot → KapSpec → KapBij := fun _ hR hK hg q _ i _ ζ =>
  ⟨kap_injective hK hg i ζ, kap_surjective hR hK hg i ζ⟩

end GlobalTheory.CompanionTheory.KapBij
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecResMap
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.KapMulE

theorem sec_res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  change ((φ.hom.app (op U) ≫ G.obj.map g.op).hom x) = ((F.obj.map g.op ≫ φ.hom.app (op V)).hom x)
  rw [φ.hom.naturality]

theorem res_kap (hKS : KapSpec) {q : ℕ} (i : ℤ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤))
    (f : LocallyConstant U (ZMod q)) {V : Scheme.{0}} (k : V ⟶ U) (a : ZMod q) (h : ∀ v : V, f (k v) = a) :
    Sec.res k (Sec.map (resι _ (tw q i)) (kap i ζ f)) =
      (ULift.up a : ULift.{1} (ZMod q)) • resGen i (primRes k ζ) := by
  obtain ⟨h1, -, -⟩ := hKS q i U ζ f
  unfold CrystallineSemistableComparison.E.IsLC at h1
  rw [sec_res_map, h1 V k a h]
  simp only [GlobalTheory.EtC.Sec.map, GlobalTheory.EtC.resGen, map_smul]

theorem kapMul_of : LcCover → RepRoot → KapSpec → KapMul := by
  intro hLC _ hKS hIn
  unfold CrystallineSemistableComparison.E.InTw at hIn
  intro q _ i j U ζ f g
  have hP := hIn q i j
  let fg : LocallyConstant U (ZMod q × ZMod q) :=
    ⟨fun x => (f x, g x), f.isLocallyConstant.prodMk g.isLocallyConstant⟩
  obtain ⟨W, jj, hc, -, -, hglue⟩ := hLC U (ZMod q × ZMod q) fg
  have hpt : ∀ (a : ZMod q × ZMod q) (v : W a), f (jj a v) = a.1 ∧ g (jj a v) = a.2 := by
    intro a v
    have := hc a v
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  obtain ⟨y, -, hy⟩ := hglue (ZMod q) ((res (ZMod q) (tw q (i + j))).X 0)
    (fun a => Sec.res (jj a) (Sec.map (resι (ZMod q) (tw q (i + j))) ((kap (i + j) ζ) (f * g))))
  refine (hy _ fun a => ?_).trans (hy _ fun a => rfl).symm
  rw [(twPair q i j).nat]
  rw [res_kap hKS i ζ f (jj a) a.1 fun v => (hpt a v).1,
    res_kap hKS j ζ g (jj a) a.2 fun v => (hpt a v).2,
    res_kap hKS (i + j) ζ (f * g) (jj a) (a.1 * a.2) fun v => by
      rw [LocallyConstant.mul_apply, (hpt a v).1, (hpt a v).2]]
  rw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.smul_apply, hP (W a) (primRes (jj a) ζ), smul_smul, mul_comm]
  rfl

end GlobalTheory.CompanionTheory.KapMulE
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEvCongr
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC
open CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.CompanionTheory.EdgeRep

theorem mul_ev_congr {R : Type} [CommRing R] {I J K : GlobalTheory.EtC.Cx R} (μ : Pair I J K) {X : Scheme.{0}} {n m k s t : ℤ}
    (h : n + m = k) (hst : s + t = k) (hs : -((0 : ℕ) : ℤ) + n = s) (ht : -((0 : ℕ) : ℤ) + m = t)
    (α : Cochain ((chains R).obj (sch.obj X)) I n) (β : Cochain ((chains R).obj (sch.obj X)) J m) :
    μ.mul X s t k hst (ev α 0 s hs X (𝟙 X)) (ev β 0 t ht X (𝟙 X)) =
      μ.mul X n m k h (ev α 0 n (by simp) X (𝟙 X)) (ev β 0 m (by simp) X (𝟙 X)) := by
  obtain rfl : s = n := by simpa using hs.symm
  obtain rfl : t = m := by simpa using ht.symm
  rfl

theorem aw_value {R : Type} [CommRing R] {I J K : GlobalTheory.EtC.Cx R} (μ : Pair I J K) {X : Scheme.{0}} {n m k : ℤ}
    (h : n + m = k) (α : Cochain ((chains R).obj (sch.obj X)) I n) (β : Cochain ((chains R).obj (sch.obj X)) J m)
    (γ : Cochain ((chains R).obj (sch.obj X)) K k) (hγ : μ.IsAW h α β γ) :
    ev γ 0 k (by simp) X (𝟙 X) = μ.mul X n m k h (ev α 0 n (by simp) X (𝟙 X)) (ev β 0 m (by simp) X (𝟙 X)) := by
  have h0 := hγ 0 k (by simp) X (𝟙 X)
  rw [Fin.sum_univ_one] at h0
  rw [h0]
  have hu : (m * ((0 : Fin 1) : ℕ)).negOnePow = 1 := by simp
  rw [hu, one_smul]
  exact mul_ev_congr μ h _ _ _ α β

theorem repCup : CrystallineSemistableComparison.E.EvExt → CrystallineSemistableComparison.E.EvNat → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.RepConc → CrystallineSemistableComparison.E.InSch → CrystallineSemistableComparison.E.RepCup := by
  intro _ _ _ _ _ R _ I J K μ X n m k h x y a b hx hy
  obtain ⟨α, rfl, rfl⟩ := hx
  obtain ⟨β, rfl, rfl⟩ := hy
  obtain ⟨γ, hγ⟩ := μ.aw_exists (sch.obj X) h α β
  exact ⟨γ, (μ.cup_spec (sch.obj X) h α β γ hγ).symm, aw_value μ h α.1 β.1 γ.1 hγ⟩

end GlobalTheory.CompanionTheory.EdgeRep

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KapZero
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.EtNatProof

def resHom {R : Type} [CommRing R] (G : Shv R) {V U : Scheme.{0}} (g : V ⟶ U) : Sec G U →+ Sec G V :=
  (G.obj.map g.op).hom.toAddMonoidHom

theorem res_res {R : Type} [CommRing R] (G : Shv R) {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (a : Sec G U) :
    Sec.res f (Sec.res g a) = Sec.res (f ≫ g) a := by
  simp [Sec.res]

theorem res_map {R : Type} [CommRing R] {G G' : Shv R} (φ : G ⟶ G') {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec G U) :
    Sec.res g (Sec.map φ a) = Sec.map φ (Sec.res g a) := by
  have h := φ.hom.naturality g.op
  exact (congrArg (fun t => t.hom a) h).symm

theorem kap_zero (hKap : KapSpec) (hTw : TwZero) (hGen : InGen) (q : ℕ) [NeZero q] {U : Scheme.{0}}
    (ζ ξ : Prim q Γ(U, ⊤)) (f : LocallyConstant U (ZMod q)) : kap 0 ζ f = kap 0 ξ f := by
  refine ((hKap q 0 U ζ f).2.1 _ ?_).symm
  intro V g a hv
  rw [(hKap q 0 U ξ f).1 V g a hv, hTw hGen q V (primRes g ξ) (primRes g ζ)]

def resMor {q : ℕ} {C C' : Type 1} [Category.{0} C] [Category.{0} C'] (P : Probe C q) (P' : Probe C' q)
    (m : Mor P.L P'.L (RingHom.id ℤ)) (g : ∀ c : C', P'.U c ⟶ P.U (m.G.obj c))
    (hg : ∀ {c c' : C'} (φ : c ⟶ c'), g c' ≫ (P.S.map (m.G.map φ)).unop = (P'.S.map φ).unop ≫ g c)
    (i : ℤ)
    (hι : ∀ (c : C') (f : LocallyConstant (P.U (m.G.obj c)) (ZMod q)),
      Sec.res (g c) (kap i (P.ζ (m.G.obj c)) f) = kap i (P'.ζ c) (m.τ c f)) :
    ResMor (P.res i) (P'.res i) m where
  τ s c := resHom _ (g c)
  nat s {c c'} φ x := by
    change Sec.res (g c') (Sec.res (P.S.map (m.G.map φ)).unop x) = Sec.res (P'.S.map φ).unop (Sec.res (g c) x)
    rw [res_res, res_res, hg φ]
  ι c x := by
    change Sec.res (g c) (Sec.map (resι _ (tw q i)) (kap i (P.ζ (m.G.obj c)) x)) =
      Sec.map (resι _ (tw q i)) (kap i (P'.ζ c) (m.τ c x))
    rw [res_map, hι]
  dv s c x := by
    change Sec.res (g c) (Sec.map ((GlobalTheory.EtC.res _ (tw q i)).d (s : ℤ) ((s + 1 : ℕ) : ℤ)) x) =
      Sec.map ((GlobalTheory.EtC.res _ (tw q i)).d (s : ℤ) ((s + 1 : ℕ) : ℤ)) (Sec.res (g c) x)
    exact res_map _ _ _

theorem etNat : CrystallineSemistableComparison.E.EtSpec → CrystallineSemistableComparison.E.EdgeMap → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.KapSpec → CrystallineSemistableComparison.E.TwZero → CrystallineSemistableComparison.E.EtNat := by
  intro hEt hEM hRep hKap hTw hGen q _ C C' _ _ P P' X X' Y Y' u m g hg hτ hy i hi j x
  obtain ⟨a, ha⟩ := (hRep (ZMod q) (GlobalTheory.EtC.res _ (tw q i)) X (j : ℤ)).1 x
  have hE := (hEt hGen q C P X Y i j x).1 a ha
  have hι : ∀ (c : C') (f : LocallyConstant (P.U (m.G.obj c)) (ZMod q)),
      Sec.res (g c) (kap i (P.ζ (m.G.obj c)) f) = kap i (P'.ζ c) (m.τ c f) := by
    intro c f
    rw [(hKap q i _ (P.ζ (m.G.obj c)) f).2.2 _ (g c), hτ c f]
    rcases hi with rfl | hi
    · exact kap_zero hKap hTw hGen q _ _ _
    · rw [hi c]
  let n := resMor P P' m g hg i hι
  have hE' := hEM ℤ ℤ (RingHom.id ℤ) C C' P.L P'.L (P.res i) (P'.res i) m n j _ _ hE
  have hglob : n.pullC j 0 (Y.glob i j a) = Y'.glob i j (Sec.res u a) := by
    funext t
    change Sec.res (g (t.obj (Fin.last 0))) (Sec.res (Y.y (m.G.obj (t.obj (Fin.last 0)))) a) =
      Sec.res (Y'.y (t.obj (Fin.last 0))) (Sec.res u a)
    rw [res_res, res_res, hy]
  rw [hglob] at hE'
  have hR : Rep (pull _ (sch.map u) _ j x) (Sec.res u a) :=
    (hRep (ZMod q) (GlobalTheory.EtC.res _ (tw q i)) X (j : ℤ)).2.2.2.2 X' u x a ha
  exact (hEt hGen q C' P' X' Y' i j _).2 _ ⟨_, hR, hE'⟩

end GlobalTheory.CompanionTheory.EtNatProof

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StExOfStCol
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeStair

theorem stEx_of_stCol : CrystallineSemistableComparison.E.StCol → CrystallineSemistableComparison.E.StEx := by
  intro hcol R _ C _ F T hG s
  obtain ⟨hι, hdv, hinj, hex0, hex⟩ := hcol R C F T hG
  induction s with
  | zero =>
    intro k j hsk x hv hd
    have hjk : j = k := by omega
    subst hjk
    obtain ⟨z, hz⟩ := (hex0 j x).1 hv
    refine ⟨z, ?_, ⟨rfl, hz⟩⟩
    apply hinj (j + 1)
    rw [← hι, hz, hd, map_zero]
  | succ s ih =>
    intro k j hsk x hv hd
    obtain ⟨a, ha⟩ := (hex s k x).1 hv
    have h1 : T.dvC s (k + 1) ((-1 : ℤ) ^ k • d (T.K s) k a) = 0 := by
      rw [map_zsmul, ← hdv, ha, hd, smul_zero]
    have h2 : d (T.K s) (k + 1) ((-1 : ℤ) ^ k • d (T.K s) k a) = 0 := by
      rw [map_zsmul, d_d, smul_zero]
    obtain ⟨z, hz, hst⟩ := ih (k + 1) j (by omega) _ h1 h2
    exact ⟨z, hz, ⟨a, ha, hst⟩⟩

end GlobalTheory.CompanionTheory.EdgeStair
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResGenRes
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtRoot

open CochainComplex CochainComplex.HomComplex

theorem twGen_res {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (primRes g ζ) := by
  unfold twGen Sec.res ofRings.sec
  have h := NatTrans.naturality_apply (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)) g.op
    (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Scheme.Γ ⋙ twF q i).obj (op U))
  have h2 : ((Scheme.Γ ⋙ twF q i).map g.op).hom (Submodule.Quotient.mk (Finsupp.single ζ 1)) =
      (Submodule.Quotient.mk (Finsupp.single (primRes g ζ) 1) : (Scheme.Γ ⋙ twF q i).obj (op V)) := by
    simp only [Functor.comp_map, EtC.twF, ModuleCat.hom_ofHom]
    erw [Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    unfold primRes
    rw [Scheme.Γ_map_op]
  exact h.symm.trans (congrArg (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V))) h2)

theorem resGen_res {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (resGen i ζ) = resGen i (primRes g ζ) := by
  unfold resGen
  rw [← twGen_res i g ζ]
  unfold Sec.res Sec.map
  exact (NatTrans.naturality_apply (resι (ZMod q) (tw q i)).hom g.op (twGen i ζ)).symm

theorem repRoot : CrystallineSemistableComparison.E.RepConc → CrystallineSemistableComparison.E.ResZero → CrystallineSemistableComparison.E.RepRoot := by
  intro hC hZ q i X ζ
  refine ⟨fun V g => ⟨twGen_res i g ζ, resGen_res i g ζ⟩, ?_⟩
  have hd : Sec.map ((res (ZMod q) (tw q i)).d 0 1) (resGen i ζ) = 0 :=
    ((hZ (ZMod q) (tw q i) X).2.1 (resGen i ζ)).mpr ⟨twGen i ζ, rfl⟩
  obtain ⟨α, hα⟩ := (hC (ZMod q) (res (ZMod q) (tw q i)) X 0 (resGen i ζ)).1 hd
  obtain ⟨β, hβ1, hβ2⟩ := GlobalTheory.EtC.pick_spec
    (P := fun c => ∃ α : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res (ZMod q) (tw q i)) 0,
      CohomologyClass.mk α = c ∧
        ∀ (U : Scheme) (x : U ⟶ X), ev (R := ZMod q) (E := sch.obj X) (I := res (ZMod q) (tw q i)) (n := 0) (↑α) 0 0 (by simp) U x = Sec.res x (resGen i ζ))
    ⟨_, α, rfl, hα.1⟩
  unfold CrystallineSemistableComparison.E.Rep GlobalTheory.EtC.rootClass
  refine ⟨β, hβ1, (hβ2 X (𝟙 X)).trans ?_⟩
  unfold Sec.res
  simp

end GlobalTheory.CompanionTheory.EtRoot
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StairCupFirst
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.StairCupFirst

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R}
  {T₁ : Res.{1} F₁} {T₂ : Res.{1} F₂} {T₃ : Res.{1} F₃} {P : Pairing F₁ F₂ F₃}

theorem term_dvC {F : C ⥤ ModuleCat.{0} R} {T : Res.{1} F} (hT : T.Good) {s p n : ℕ}
    (σ : ComposableArrows C n) (a : Cn (T.K s) p) (g : Fin (p + 1) → Fin (n + 1)) (hg : Monotone g) :
    term (T.K (s + 1)) σ (T.dvC s p a) g hg = T.dv s _ (term (T.K s) σ a g hg) := by
  delta CrystallineSemistableComparison.CH.term CrystallineSemistableComparison.E.Res.dvC
  exact (hT.dv_nat s _ _).symm

theorem dvC_cupC (μ : ResPair T₁ T₂ T₃ P) (h₁ : T₁.Good) (h₂ : T₂.Good) {s t r k : ℕ} (h : s + t = r)
    (a : Cn (T₁.K s) k) (y : Cn (T₂.K t) 0) (hy : T₂.dvC t 0 y = 0) :
    T₃.dvC r k ((μ.μ s t r h).cupC (add_zero k) a y) =
      (μ.μ (s + 1) t (r + 1) (by omega)).cupC (add_zero k) (T₁.dvC s k a) y := by
  delta CrystallineSemistableComparison.E.Res.dvC CrystallineSemistableComparison.CH.Pairing.cupC
  funext σ
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mk₂_apply]
  have hz : ∀ (g : Fin (0 + 1) → Fin (k + 1)) (hg : Monotone g),
      CrystallineSemistableComparison.CH.term (T₂.K (t + 1)) σ (0 : Cn (T₂.K (t + 1)) 0) g hg = 0 := fun g hg => by
    delta CrystallineSemistableComparison.CH.term
    exact map_zero _
  rw [μ.leib, ← term_dvC h₂ σ y, hy, hz, map_zero, smul_zero, add_zero, ← term_dvC h₁ σ a]
  rfl

theorem stCupA : CrystallineSemistableComparison.E.CupLeib.{1} → CrystallineSemistableComparison.E.StCupA := by
  intro hL R _ C _ F₁ F₂ F₃ T₁ T₂ T₃ P μ h₁ h₂ i t n z y u hy hdy hst s
  induction s with
  | zero =>
    intro k r h x hx
    obtain ⟨hik, rfl⟩ := hx
    subst hik
    obtain rfl : r = t := by omega
    exact hst
  | succ s ih =>
    intro k r h x hx
    obtain ⟨a, rfl, hsa⟩ := hx
    obtain rfl : r = s + t + 1 := by omega
    show ∃ a', T₃.dvC (s + t) k a' = _ ∧
      T₃.St u (s + t) (k + 1) ((-1) ^ k • CrystallineSemistableComparison.CH.d (T₃.K (s + t)) k a')
    refine ⟨(μ.μ s t (s + t) rfl).cupC (add_zero k) a y, dvC_cupC μ h₁ h₂ rfl a y hy, ?_⟩
    have hcup := hL R C (T₁.K s) (T₂.K t) (T₃.K (s + t)) (μ.μ s t (s + t) rfl) k 0 k (add_zero k) a y
    rw [hcup, hdy, map_zero, smul_zero, add_zero, ← LinearMap.smul_apply, ← map_zsmul]
    exact ih (k + 1) (s + t) rfl _ hsa

end GlobalTheory.CompanionTheory.StairCupFirst
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernClassFamily
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.E

open CH GlobalTheory.EtC

theorem pull_smul_cls {R' : Type} [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    {F : C ⥤ ModuleCat.{0} R'} (G : C' ⥤ C) (t : R') (y : CH.H F 2)
    (z : Cn (G ⋙ F) 2) (hz : d (G ⋙ F) 2 z = 0) (h : (Mor.restrict F G).pull 2 y = (cx (G ⋙ F)).cls z hz) :
    ∃ hz' : d (G ⋙ F) 2 (t • z) = 0, (cx (G ⋙ F)).cls (t • z) hz' = (Mor.restrict F G).pull 2 (t • y) := by
  refine ⟨by rw [map_smul, hz, smul_zero], ?_⟩
  exact ((((Mor.restrict F G).pull 2).map_smul t y).trans (congrArg (t • ·) h)).symm

theorem pull_cls {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    {L : C ⥤ ModuleCat.{0} R} {F : C' ⥤ ModuleCat.{0} R'} (m : Mor L F σ) (z : Cn L 2) (hz : d L 2 z = 0) :
    ∃ hz' : d F 2 (m.pullC 2 z) = 0, m.pull 2 ((cx L).cls z hz) = (cx F).cls (m.pullC 2 z) hz' :=
  ⟨by rw [m.d_pullC, hz, map_zero], rfl⟩

theorem pull_cls' {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C D T P : Type 1} [Category.{0} C] [Category.{0} D]
    [Category.{0} T] [Category.{0} P] (G : C ⥤ D) (π : D ⥤ T) (ι : T ⥤ P) (A : P ⥤ CommAlgCat.{0} R')
    {L : C ⥤ ModuleCat.{0} R} (m : Mor L (modF (((G ⋙ π) ⋙ ι) ⋙ A)) σ) (z : Cn L 2) (hz : d L 2 z = 0) (a : CH.H L 2)
    (ha : a = (cx L).cls z hz) :
    ∃ hz' : d (G ⋙ modF ((π ⋙ ι) ⋙ A)) 2 (m.pullC 2 z) = 0,
      @Eq (CH.H (G ⋙ modF ((π ⋙ ι) ⋙ A)) 2) (m.pull 2 a) ((cx (G ⋙ modF ((π ⋙ ι) ⋙ A))).cls (m.pullC 2 z) hz') := by
  subst ha
  exact pull_cls m z hz

theorem isUnit_gb {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (M : Model l K) : IsUnit (l : Γ(gb M, ⊤)) := by
  have h : IsUnit (l : PadicAlgCl l) := isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have := h.map (((pullback.snd _ _ : gb M ⟶ Spec (CommRingCat.of (PadicAlgCl l))).appTop.hom).comp (toΓ _))
  rwa [map_natCast] at this

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {C : Type 1} [Category.{0} C]

theorem eG_cls (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (G : C ⥤ El M.P) (n : ℕ)
    (x : Ht (l ^ n) (sch.obj (gb M)) (2 : ℕ) 1) (z : Cn (probe H r (G ⋙ CategoryOfElements.π _) n).L 2)
    (hz : d (probe H r (G ⋙ CategoryOfElements.π _) n).L 2 z = 0)
    (he : (pts H r M G n).et 1 2 x = (cx (probe H r (G ⋙ CategoryOfElements.π _) n).L).cls z hz) :
    ∃ hz' : d (G ⋙ modF (AcrEl M.P n)) 2 (lcCo hN H r G n 2 z) = 0,
      eG hN H r M G n 1 2 x = (cx (G ⋙ modF (AcrEl M.P n))).cls (lcCo hN H r G n 2 z) hz' :=
  pull_cls' G (CategoryOfElements.π _) (testι l) (AcrA l n) (lcMor hN H r (G ⋙ CategoryOfElements.π _) n) z hz _ he

theorem tCo_cls (M : Model l K) (G : C ⥤ El M.P) (n : ℕ) (e : EtFam l K) (v : Hl l (sch.obj (gb M)) (2 : ℕ) 0)
    (z : Cn (G ⋙ modF (AcrEl M.P n)) 2) (hz : d (G ⋙ modF (AcrEl M.P n)) 2 z = 0)
    (h : (Mor.restrict (modF (AcrEl M.P n)) G).pull 2 (e M n 2 (v.1 n)) = (cx (G ⋙ modF (AcrEl M.P n))).cls z hz) :
    ∃ hz' : d (G ⋙ modF (AcrEl M.P n)) 2 (tCo G n 2 z) = 0,
      (cx (G ⋙ modF (AcrEl M.P n))).cls (tCo G n 2 z) hz' = (Mor.restrict (modF (AcrEl M.P n)) G).pull 2 (e.tMul M v n) :=
  pull_smul_cls G _ _ z hz h

theorem res_cls (h6 : FRes) (E : EtIn) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (G : C ⥤ El M.P) (n : ℕ)
    (x : Ht (l ^ n) (sch.obj (gb M)) (2 : ℕ) 1) (v : Ht (l ^ n) (sch.obj (gb M)) (2 : ℕ) 0)
    (hv : eM hN H r M n 0 2 v = eM hN H r M n 1 2 x) (y : CH.H (G ⋙ modF (AcrEl M.P n)) 2) (he : eG hN H r M G n 1 2 x = y) :
    (Mor.restrict (modF (AcrEl M.P n)) G).pull 2 (eM hN H r M n 0 2 v) = y :=
  (congrArg (fun a => (Mor.restrict (modF (AcrEl M.P n)) G).pull 2 a) hv).trans ((h6 E hN l H r K M C G n 1 2 x).trans he)

theorem isFirstChern_of_cocycle {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* OC l} {D : LineData X}
    {y : ∀ n, MH (PX q κ) n 2}
    (h : ∀ (C : Type 1) [Category.{0} C] (G : C ⥤ El (PX q κ)) (Λ : Lift G D) (n : ℕ),
      ∃ (z : Cn (G ⋙ modF (AcrEl (PX q κ) n)) 2), Λ.IsCoc n z ∧ ∃ hz : d (G ⋙ modF (AcrEl (PX q κ) n)) 2 z = 0,
        (cx (G ⋙ modF (AcrEl (PX q κ) n))).cls z hz = (Mor.restrict (modF (AcrEl (PX q κ) n)) G).pull 2 (y n)) :
    IsFirstChernClassOfLineBundle q κ D y := fun C _ G Λ n =>
  (h C G Λ n).elim fun z a => a.2.elim fun hz b => Exists.intro z (Exists.intro hz (And.intro a.1 b))

theorem step (h4 : EtaleFirstChernKummer) (h5 : FKum) (h6 : FRes) (E : EtIn) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K)
    (D : LineData M.X) (D' : LineData (gb M)) (π : D'.Y ⟶ D.Y)
    (hD : D.IsBC (pullback.fst _ _ ≫ pullback.fst _ _ : gb M ⟶ M.X) D' π) (L : cech D'.f ⟶ ofCat (glCat 1)) (hL : D'.IsMap L) (n : ℕ)
    (hI : GlobalTheory.EtC.Inv (l ^ n) (cech D'.f)) (x : Ht (l ^ n) (sch.obj (gb M)) 2 1) (hx : pull _ (cechAug D'.f) _ 2 x = c1 (l ^ n) L)
    (G : C ⥤ El M.P) (Λ : Lift G D) :
    ∃ z : Cn (G ⋙ modF (AcrEl M.P n)) 2, Λ.IsCoc n (tCo G n 2 z) ∧ ∃ hz : d (G ⋙ modF (AcrEl M.P n)) 2 z = 0,
      eG hN H r M G n 1 2 x = (cx (G ⋙ modF (AcrEl M.P n))).cls z hz := by
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  exact (h5 hN l H r K M D D' π hD C G Λ n).elim fun z a => a.1.elim fun k =>
    (h4 E.gen E.kum E.c1 (l ^ n) C _ (gb M) (pts H r M G n) D' L hL hI x hx z k).elim fun hz he =>
      Exists.intro (lcCo hN H r G n 2 z) (And.intro a.2 (eG_cls hN H r M G n x z hz he))

theorem firstChern_family_of_lifts (h1 : LineBC) (h2 : LineMap) (h3 : FirstChernCompatibleSystem) (h4 : EtaleFirstChernKummer) (h5 : FKum) (h6 : FRes) (h7 : FUntw) : FirstChernClassFamily :=
  fun E hN l _ H r K M D => (h1 (gb M) M.X (pullback.fst _ _ ≫ pullback.fst _ _) D).elim fun D' a => a.elim fun π hD =>
    (h2 _ D').elim fun L hL =>
      have b := @h3 E.a2 E.a11 l _ D'.Y (gb M) D'.f D'.sm D'.surj (isUnit_gb M) L
      b.2.elim fun x hx => (h7 E hN l H r K M x).elim fun v hv => Exists.intro v (isFirstChern_of_cocycle fun C _ G Λ n =>
        (step h4 h5 h6 E hN H r M D D' π hD L hL n (b.1 n) (x.1 n) (hx n) G Λ).elim fun z c => c.2.elim fun hz e2 =>
          Exists.intro (tCo G n 2 z) (And.intro c.1 (tCo_cls M G n (eFam hN H r K) v z hz
            (res_cls h6 E hN H r M G n (x.1 n) (v.1 n) (hv n) _ e2))))

end CrystallineSemistableComparison.E
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.CupLeib
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace CrystallineSemistableComparison.E

open CH

theorem cupLeib : CupLeib.{1} := fun _ _ _ _ _ _ _ P _ _ _ h x y => CrystallineSemistableComparison.P.leibniz P h x y

theorem cupCls : CupCls := fun _ _ _ _ _ _ _ P _ _ _ h x y hx hy => CrystallineSemistableComparison.P.cup_cls P h x y hx hy

theorem cupOne : CupOne := fun _ _ _ _ A p x => ((CrystallineSemistableComparison.P.cup_ring A).1 p x).2

theorem morCup : MorCup := by
  intro R R' _ _ σ C _ A A' m ρ hρ
  refine ⟨?_, fun p q n h x y => ?_⟩
  · refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => ?_))
    exact (hρ _ _).trans (map_one (ρ _))
  · exact CrystallineSemistableComparison.P.cup_pull (mulP A) (mulP A') m.G m.τ m.τ m.τ m.nat m.nat m.nat (fun T (a b : A.obj (m.G.obj T)) => by
      rw [hρ, hρ, hρ]; exact map_mul (ρ T) a b) h x y

end CrystallineSemistableComparison.E
end

set_option backward.isDefEq.respectTransparency false

namespace CrystallineSemistableComparison.E.Main

theorem inSch : InSch := GlobalTheory.EtC.sch_cls_cocycle_sec

theorem stAdd : StAdd := GlobalTheory.CompanionTheory.StairAdd.stAdd

theorem stCol : StCol := GlobalTheory.CompanionTheory.EdgeStair.stCol

theorem stEx : StEx := GlobalTheory.CompanionTheory.EdgeStair.stEx_of_stCol stCol

theorem stUniq : StUniq := GlobalTheory.CompanionTheory.EdgeStair.stUniq stCol

theorem stTop : StTop := GlobalTheory.CompanionTheory.EdgeMap.stTop_of_stCol stCol

theorem edgeUniq : EdgeUniq := GlobalTheory.CompanionTheory.EdgeClass.edgeUniq_of stCol stAdd stUniq

theorem edgeMap : EdgeMap := GlobalTheory.CompanionTheory.EdgeMapPull.edgeMap

theorem stCupA : StCupA := GlobalTheory.CompanionTheory.StairCupFirst.stCupA cupLeib

theorem stCupB : StCupB := GlobalTheory.CompanionTheory.Staircase.stCupB cupLeib stCol

theorem edgeCup : EdgeCup := GlobalTheory.CompanionTheory.EdgeMap.edgeCup_of_steps cupCls stTop stCupA stCupB

theorem lcCover : LcCover := GlobalTheory.CompanionTheory.LcCoverProof.lcCover

theorem locSplit : LocSplit := GlobalTheory.CompanionTheory.LocSplitProof.locSplit

theorem primAlg : PrimAlg := GlobalTheory.CompanionTheory.PrimAlgProof.primAlg

theorem rootPow : RootPow := GlobalTheory.CompanionTheory.RootPowLC.rootPow primAlg

theorem rootsEx : RootsEx := GlobalTheory.CompanionTheory.RootsC.rootsEx

theorem lcIdem : LcIdem := GlobalTheory.CompanionTheory.TiltIdem.lcIdem

theorem lcSpec : LcSpec := GlobalTheory.CompanionTheory.LcSp.lcSpec_of_lcIdem lcIdem

theorem lcNat : LcNat := GlobalTheory.CompanionTheory.LcNatProof.lcNat lcIdem lcSpec

theorem logEx : LogEx := GlobalTheory.CompanionTheory.CrisLog.logEx

theorem logAlg : LogAlg := GlobalTheory.CompanionTheory.LogAlgPf.logAlg

theorem logMul : LogMul := GlobalTheory.CompanionTheory.LogMulPf.logMul logAlg logEx

theorem logEps : LogEps := GlobalTheory.CompanionTheory.LogEpsP.logEps

theorem epsRoot : EpsRoot := GlobalTheory.CompanionTheory.EpsRootProof.epsRoot

theorem lcLog : LcLog := GlobalTheory.CompanionTheory.LcLogProof.lcLog lcIdem lcSpec lcCover logEx logMul logEps epsRoot

theorem lineBC : LineBC := GlobalTheory.CompanionTheory.LineBase.lineBC

theorem twUg : TwUg := GlobalTheory.CompanionTheory.TwUg.twUg_prop

theorem fPhi : FPhi := GlobalTheory.CompanionTheory.FrobLc.fPhi

theorem fKum : FKum := GlobalTheory.CompanionTheory.FKum.fKum rootPow lcLog

theorem liftEx : LiftEx := GlobalTheory.CompanionTheory.LineLift.liftEx

theorem firstChern_unique : FirstChernUniqueEtale := GlobalTheory.CompanionTheory.EtChern.chern_class_unique_of_lift_and_log liftEx logEx

theorem repBasic : RepBasic := GlobalTheory.CompanionTheory.EtEdge.repBasic evExt evNat inSch

theorem repConc : RepConc := GlobalTheory.CompanionTheory.EdgeMap.repConc_of_inputs evExt inSch repBasic

theorem repCup : RepCup := GlobalTheory.CompanionTheory.EdgeRep.repCup evExt evNat repBasic repConc inSch

theorem repOp : RepOp := GlobalTheory.CompanionTheory.EdgeRep.repOp evNat repConc repBasic

theorem resLoc : ResLoc := GlobalTheory.CompanionTheory.EdgeMap.resLoc

theorem resZero : ResZero := GlobalTheory.CompanionTheory.EtRes.resZero

theorem cechPt : CechPt := GlobalTheory.CompanionTheory.CechPts.cechPt_spec

theorem lineMap : LineMap := GlobalTheory.CompanionTheory.CechLine.lineMap_exists cechPt

theorem chern_class_compatible_system : FirstChernCompatibleSystem := GlobalTheory.CompanionTheory.ChernSys.chern_class_compatible_system cechPt

theorem firstChern_primitive_kummer : FirstChernCoboundary := GlobalTheory.CompanionTheory.KummerPrimitive.main evExt evNat evDel repConc repBasic cechPt

theorem resSplit : ResSplit := GlobalTheory.CompanionTheory.ResSplitProof.resSplit resLoc locSplit lcCover

theorem repRoot : RepRoot := GlobalTheory.CompanionTheory.EtRoot.repRoot repConc resZero

theorem redRoot : RedRoot := GlobalTheory.CompanionTheory.EdgeMap.redRoot_of_rep repRoot repOp repConc

theorem twZero : TwZero := GlobalTheory.CompanionTheory.TwZeroGen.twZero rootPow lcCover repRoot

theorem kapSpec : KapSpec := GlobalTheory.CompanionTheory.KapSpecProof.kapSpec lcCover repRoot

theorem kapBij : KapBij := GlobalTheory.CompanionTheory.KapBij.kapBij lcCover repRoot kapSpec

theorem kapMul : KapMul := GlobalTheory.CompanionTheory.KapMulE.kapMul_of lcCover repRoot kapSpec

theorem kapRed : KapRed := GlobalTheory.CompanionTheory.CstE.KapRedP.kapRed lcCover repRoot kapSpec

theorem kumPow : KumPow := GlobalTheory.CompanionTheory.KumPowProof.kumPow lcCover repRoot kapSpec primAlg

theorem resGood : ResGood := GlobalTheory.CompanionTheory.EdgeRes.resGood kapSpec kapBij resZero resSplit

theorem etSpec : EtSpec := GlobalTheory.CompanionTheory.EtSpecProof.etSpec resGood stEx edgeUniq repBasic resZero

theorem etNat : EtNat := GlobalTheory.CompanionTheory.EtNatProof.etNat etSpec edgeMap repBasic kapSpec twZero

theorem etRed : EtRed := GlobalTheory.CompanionTheory.EdgeRed.etRed etSpec edgeMap repBasic repOp kapSpec kapRed

theorem etCup : EtCup := GlobalTheory.CompanionTheory.EdgeProduct.etCup etSpec resGood edgeCup repBasic repCup kapMul

theorem etRoot : EtRoot := GlobalTheory.CompanionTheory.EdgeRoot.etRoot_of_spec etSpec repRoot kapSpec

theorem etale_chern_class_eq_kummer_class : EtaleFirstChernKummer := GlobalTheory.CompanionTheory.EtaleChernClass.etale_chern_class_eq_kummer_class etSpec resGood stCol firstChern_primitive_kummer kumPow

theorem fRed : FRed := GlobalTheory.CompanionTheory.EtReduction.fred_of_etRed etRed

theorem fEqui : FEqui := GlobalTheory.CompanionTheory.FEquiProof.fEqui etNat twUg

theorem fNat : FNat := GlobalTheory.CompanionTheory.FNatProof.fNat etNat

theorem fRes : FRes := GlobalTheory.CompanionTheory.FResProof.fRes etNat

theorem fCup : FCup := GlobalTheory.CompanionTheory.EtCupF.fCup etCup morCup lcSpec

theorem fRoot : FRoot := GlobalTheory.CompanionTheory.FRootCls.froot etRoot redRoot morCup lcSpec

theorem fUntw : FUntw := GlobalTheory.CompanionTheory.FUntwPf.main fCup fRoot cupOne

theorem firstChern_family : FirstChernClassFamily := firstChern_family_of_lifts lineBC lineMap chern_class_compatible_system etale_chern_class_eq_kummer_class fKum fRes fUntw

theorem etale_comparison_map : EtaleComparisonMapExists := etale_comparison_map_of_facts rootsEx lcNat fRed fEqui fPhi fNat fCup fRoot firstChern_family

end CrystallineSemistableComparison.E.Main
