module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLCRes
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.KapSpecProof

variable {R : Type} [CommRing R]

theorem res_comp {G : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec G U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  delta GlobalTheory.EtC.Sec.res
  rw [op_comp, Functor.map_comp]
  rfl

theorem primRes_comp {q : ℕ} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    primRes (k ≫ g) ζ = primRes k (primRes g ζ) := by
  apply Subtype.ext
  delta CrystallineSemistableComparison.E.primRes
  rfl

theorem sec_subsingleton (hL : LcCover) {U : Scheme.{0}} [IsEmpty U] (G : Shv R) :
    Subsingleton (Sec G U) := by
  let f0 : LocallyConstant U Empty :=
    ⟨fun u => isEmptyElim u, fun s => by
      convert isOpen_empty
      ext u
      exact isEmptyElim u⟩
  obtain ⟨W, j, -, -, -, hglue⟩ := hL U Empty f0
  obtain ⟨z, -, hz⟩ := hglue R G (fun a => a.elim)
  exact ⟨fun x x' => (hz x (fun a => a.elim)).trans (hz x' (fun a => a.elim)).symm⟩

theorem sec_ext (hL : LcCover) {ι : Type} {U : Scheme.{0}} (f : LocallyConstant U ι) (G : Shv R)
    (x y : Sec G U)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U) (a : ι), (∀ v : V, f (g v) = a) → Sec.res g x = Sec.res g y) :
    x = y := by
  obtain ⟨W, j, hWf, -, -, hglue⟩ := hL U ι f
  obtain ⟨z, -, hz⟩ := hglue R G (fun a => Sec.res (j a) x)
  exact (hz x (fun a => rfl)).trans (hz y (fun a => (h (W a) (j a) a (hWf a)).symm)).symm

variable {q : ℕ} {i : ℤ}

theorem isLC_unique (hL : LcCover) {U : Scheme.{0}} {ζ : Prim q Γ(U, ⊤)}
    {f : LocallyConstant U (ZMod q)} {x y : Sec (tw q i) U} (hx : IsLC i ζ f x) (hy : IsLC i ζ f y) :
    x = y := by
  refine sec_ext hL f _ x y fun V g a hga => ?_
  delta CrystallineSemistableComparison.E.IsLC at hx hy
  rw [hx V g a hga, hy V g a hga]

theorem isLC_exists (hL : LcCover) (hR : RepRoot) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤))
    (f : LocallyConstant U (ZMod q)) : ∃ x : Sec (tw q i) U, IsLC i ζ f x := by
  delta CrystallineSemistableComparison.E.IsLC
  have hres_smul : ∀ {V W : Scheme.{0}} (g : V ⟶ W) (c : ULift (ZMod q)) (y : Sec (tw q i) W),
      Sec.res g (c • y) = c • Sec.res g y := fun g c y => by
    delta GlobalTheory.EtC.Sec.res
    exact map_smul _ c y
  obtain ⟨W, j, -, hfac, -, hglue⟩ := hL U (ZMod q) f
  obtain ⟨x, hx, -⟩ := hglue (ZMod q) (tw q i)
    (fun a => (⟨a⟩ : ULift (ZMod q)) • twGen i (primRes (j a) ζ))
  refine ⟨x, fun V g a ha => ?_⟩
  obtain ⟨k, rfl⟩ := hfac V g a ha
  rw [res_comp, hx a, hres_smul, ((hR q i (W a) (primRes (j a) ζ)).1 V k).1, ← primRes_comp]

theorem isLC_add (hL : LcCover) (hR : RepRoot) {U : Scheme.{0}} {ζ : Prim q Γ(U, ⊤)}
    {f f' : LocallyConstant U (ZMod q)} {x x' : Sec (tw q i) U} (hx : IsLC i ζ f x)
    (hx' : IsLC i ζ f' x') : IsLC i ζ (f + f') (x + x') := by
  delta CrystallineSemistableComparison.E.IsLC at hx hx' ⊢
  intro V g a ha
  have hres_smul : ∀ {V W : Scheme.{0}} (g : V ⟶ W) (c : ULift (ZMod q)) (y : Sec (tw q i) W),
      Sec.res g (c • y) = c • Sec.res g y := fun g c y => by
    delta GlobalTheory.EtC.Sec.res
    exact map_smul _ c y
  have hcont : Continuous (fun v : V => g v) := g.continuous
  let F2 : LocallyConstant V (ZMod q × ZMod q) :=
    ⟨fun v => (f (g v), f' (g v)), IsLocallyConstant.comp₂ (f.isLocallyConstant.comp_continuous hcont)
      (f'.isLocallyConstant.comp_continuous hcont) Prod.mk⟩
  refine sec_ext hL F2 _ _ _ fun V' g' b hb => ?_
  rcases isEmpty_or_nonempty V' with hV | ⟨⟨v⟩⟩
  · haveI := sec_subsingleton hL (U := V') (tw q i)
    exact Subsingleton.elim _ _
  have hb1 : ∀ v, f ((g' ≫ g) v) = b.1 := fun v => congrArg Prod.fst (hb v)
  have hb2 : ∀ v, f' ((g' ≫ g) v) = b.2 := fun v => congrArg Prod.snd (hb v)
  have hres_add : ∀ (y y' : Sec (tw q i) U),
      Sec.res (g' ≫ g) (y + y') = Sec.res (g' ≫ g) y + Sec.res (g' ≫ g) y' := fun y y' => by
    delta GlobalTheory.EtC.Sec.res
    exact map_add _ y y'
  have hab : a = b.1 + b.2 := by
    rw [← ha (g' v), ← hb1 v, ← hb2 v]
    rfl
  rw [← res_comp, hres_add, hx V' (g' ≫ g) b.1 hb1, hx' V' (g' ≫ g) b.2 hb2, ← add_smul, hres_smul,
    ((hR q i V (primRes g ζ)).1 V' g').1, ← primRes_comp, hab]
  rfl

theorem isLC_res {U V : Scheme.{0}} {ζ : Prim q Γ(U, ⊤)}
    {f : LocallyConstant U (ZMod q)} {x : Sec (tw q i) U} (hx : IsLC i ζ f x) (g : V ⟶ U) :
    IsLC i (primRes g ζ) (lcRes q g f) (Sec.res g x) := by
  delta CrystallineSemistableComparison.E.IsLC at hx ⊢
  intro W h a ha
  rw [← res_comp, hx W (h ≫ g) a ?_, primRes_comp]
  intro w
  exact ha w

theorem kapSpec : LcCover → RepRoot → KapSpec := by
  intro hL hR q i U ζ f
  have hk : ∀ {U' : Scheme.{0}} (ζ' : Prim q Γ(U', ⊤)) (f' : LocallyConstant U' (ZMod q)),
      IsLC i ζ' f' (kap i ζ' f') := by
    intro U' ζ' f'
    have hex : ∃ κ : LocallyConstant U' (ZMod q) →+ Sec (tw q i) U', ∀ f'', IsLC i ζ' f'' (κ f'') := by
      choose c hc using fun f'' : LocallyConstant U' (ZMod q) => isLC_exists hL hR (i := i) ζ' f''
      refine ⟨{ toFun := c, map_zero' := ?_, map_add' := fun a b => ?_ }, hc⟩
      · have h := isLC_unique hL (hc (0 + 0)) (isLC_add hL hR (hc 0) (hc 0))
        simpa using h
      · exact isLC_unique hL (hc (a + b)) (isLC_add hL hR (hc a) (hc b))
    delta CrystallineSemistableComparison.E.kap
    exact GlobalTheory.EtC.pick_spec hex f'
  refine ⟨hk ζ f, fun x hx => isLC_unique hL hx (hk ζ f), fun V g => ?_⟩
  exact isLC_unique hL (isLC_res (hk ζ f) g) (hk _ _)

end GlobalTheory.CompanionTheory.KapSpecProof
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EdgeUnique
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtSpecProof

section Sections

variable {R : Type} [CommRing R]

theorem res_comp {G : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec G U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  simp [Sec.res]

theorem map_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  have h := φ.hom.naturality g.op
  exact congrArg (fun m => m.hom x) h

end Sections

variable {q : ℕ} {C : Type 1} [Category.{0} C] {P : Probe C q} {X : Scheme.{0}}

theorem map_glob (Y : P.Pts X) (i : ℤ) (j : ℕ) (a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X)
    {c c' : C} (φ : c ⟶ c') :
    (((P.res i).K j).map φ).hom (Sec.res (Y.y c) a) = Sec.res (Y.y c') a := by
  change Sec.res (P.S.map φ).unop (Sec.res (Y.y c) a) = _
  rw [← res_comp, Y.nat]

theorem d_glob (Y : P.Pts X) (i : ℤ) (j : ℕ) (a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X) :
    d ((P.res i).K j) 0 (Y.glob i j a) = 0 := by
  funext s
  have h : ∀ k : Fin 2, (((P.res i).K j).map (GlobalTheory.CatH.toLast k s)).hom (Y.glob i j a (GlobalTheory.CatH.face k s)) =
      Sec.res (Y.y (s.obj (Fin.last 1))) a := fun k => map_glob Y i j a _
  change ∑ k : Fin 2, (-1 : ℤ) ^ (k : ℕ) •
    (((P.res i).K j).map (GlobalTheory.CatH.toLast k s)).hom (Y.glob i j a (GlobalTheory.CatH.face k s)) = 0
  rw [Fin.sum_univ_two, h 0, h 1]
  simp

theorem dvC_glob (Y : P.Pts X) (i : ℤ) (j : ℕ) (a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X) :
    (P.res i).dvC j 0 (Y.glob i j a) =
      Y.glob i (j + 1) (Sec.map ((GlobalTheory.EtC.res _ (tw q i)).d (j : ℤ) ((j + 1 : ℕ) : ℤ)) a) := by
  funext s
  exact map_res _ _ _

theorem glob_add (Y : P.Pts X) (i : ℤ) (j : ℕ) (a b : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X) :
    Y.glob i j (a + b) = Y.glob i j a + Y.glob i j b := by
  funext s
  exact map_add _ _ _

theorem glob_sub (Y : P.Pts X) (i : ℤ) (j : ℕ) (a b : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X) :
    Y.glob i j (a - b) = Y.glob i j a - Y.glob i j b := by
  funext s
  exact map_sub _ _ _

theorem edge_exists {i : ℤ} {j : ℕ} (hT : (P.res i).Good) (hSE : StEx) (hRB : RepBasic) (Y : P.Pts X)
    {x : Ht q (sch.obj X) j i} {a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X} (hx : Rep x a) :
    ∃ h, (P.res i).Edge (Y.glob i j a) h := by
  have hcl := (hRB (ZMod q) (GlobalTheory.EtC.res _ (tw q i)) X (j : ℤ)).2.1 x a hx ((j + 1 : ℕ) : ℤ)
  have hdv : (P.res i).dvC j 0 (Y.glob i j a) = 0 := by
    rw [dvC_glob, hcl]
    funext s
    exact map_zero _
  obtain ⟨z, hz, hst⟩ := hSE ℤ C P.L (P.res i) hT j 0 j (add_zero j) (Y.glob i j a) hdv (d_glob Y i j a)
  exact ⟨(cx P.L).cls z hz, z, hz, hst, rfl⟩

theorem edge_unique {i : ℤ} {j : ℕ} (hT : (P.res i).Good) (hEU : EdgeUniq) (hRB : RepBasic) (hRZ : ResZero)
    (Y : P.Pts X) {x : Ht q (sch.obj X) j i} {a a' : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X}
    (hx : Rep x a) (hx' : Rep x a') {h h' : H P.L j} (he : (P.res i).Edge (Y.glob i j a) h)
    (he' : (P.res i).Edge (Y.glob i j a') h') : h = h' := by
  have hB := hRB (ZMod q) (GlobalTheory.EtC.res _ (tw q i)) X (j : ℤ)
  have h0 : Rep (0 : Ht q (sch.obj X) j i) (a - a') := by
    have := (hB.2.2.1 x x a a' hx hx').2
    rwa [sub_self] at this
  have hz := hB.2.2.2.1 (a - a') h0
  have hVB : (P.res i).VB j (Y.glob i j a - Y.glob i j a') := by
    cases j with
    | zero =>
      obtain ⟨b, hb⟩ := hz (-1) (by norm_num)
      have := (hRZ (ZMod q) (tw q i) X).2.2 (-1) (by norm_num)
      have hb0 : b = 0 := Subsingleton.elim _ _
      have hz0 : a - a' = 0 := by
        rw [← hb, hb0]
        exact map_zero _
      change Y.glob i 0 a - Y.glob i 0 a' = 0
      rw [← glob_sub, hz0]
      funext s
      exact map_zero _
    | succ s =>
      obtain ⟨b, hb⟩ := hz (s : ℤ) (by push_cast; rfl)
      refine ⟨Y.glob i s b, d_glob Y i s b, ?_⟩
      rw [dvC_glob, hb, glob_sub]
  exact (hEU ℤ C P.L (P.res i) hT j _ _ h h' he he').2 hVB

theorem etSpec : ResGood → StEx → EdgeUniq → RepBasic → ResZero → EtSpec := by
  intro hRG hSE hEU hRB hRZ hGen q _ C _ P X Y i j x
  have hT := hRG hGen q C P i
  have hB := hRB (ZMod q) (GlobalTheory.EtC.res _ (tw q i)) X (j : ℤ)
  have hex : ∀ x, ∃ h, Y.IsEt i j x h := fun x => by
    obtain ⟨a, ha⟩ := hB.1 x
    obtain ⟨h, hh⟩ := edge_exists hT hSE hRB Y ha
    exact ⟨h, a, ha, hh⟩
  have huniq : ∀ {x h h'}, Y.IsEt i j x h → Y.IsEt i j x h' → h = h' := by
    rintro x h h' ⟨a, ha, he⟩ ⟨a', ha', he'⟩
    exact edge_unique hT hEU hRB hRZ Y ha ha' he he'
  have hall : ∀ x, Y.IsEt i j x (Y.et i j x) := by
    refine pick_spec (P := fun e : Ht q (sch.obj X) j i →+ H P.L j => ∀ x, Y.IsEt i j x (e x)) ?_
    choose f hf using hex
    refine ⟨AddMonoidHom.mk' f fun u v => huniq (hf _) ?_, hf⟩
    obtain ⟨a, ha, he⟩ := hf u
    obtain ⟨b, hb, he'⟩ := hf v
    refine ⟨a + b, (hB.2.2.1 u v a b ha hb).1, ?_⟩
    rw [glob_add]
    exact (hEU ℤ C P.L (P.res i) hT j _ _ _ _ he he').1
  refine ⟨fun a ha => ?_, fun h hh => huniq hh (hall x)⟩
  obtain ⟨h, hh⟩ := edge_exists hT hSE hRB Y ha
  have e : h = Y.et i j x := huniq ⟨a, ha, hh⟩ (hall x)
  rwa [← e]

end GlobalTheory.CompanionTheory.EtSpecProof
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleChernClassEqKummerClass
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtaleChernClass

open GlobalTheory.CatH (face toLast)

universe w

section Cochains

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{w} R)

theorem d_zero_apply (f : Cn F 0) (s : ComposableArrows C 1) :
    d F 0 f s = (show F.obj (s.obj (Fin.last 1)) from f (face 0 s)) - (show F.obj (s.obj (Fin.last 1)) from (F.map (s.map' 0 1)).hom (f (face 1 s))) := by
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i s)).hom (f (face i s)) = _
  rw [Fin.sum_univ_two]
  have e0 : toLast (0 : Fin 2) s = 𝟙 _ := s.map_id _
  have e1 : toLast (1 : Fin 2) s = s.map' 0 1 := rfl
  rw [e0, e1, F.map_id]
  simp [sub_eq_add_neg]
  rfl

theorem d_one_apply (f : Cn F 1) (s : ComposableArrows C 2) :
    d F 1 f s = (show F.obj (s.obj (Fin.last 2)) from f (face 0 s)) - (show F.obj (s.obj (Fin.last 2)) from f (face 1 s)) +
      (show F.obj (s.obj (Fin.last 2)) from (F.map (s.map' 1 2)).hom (f (face 2 s))) := by
  change ∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i s)).hom (f (face i s)) = _
  rw [Fin.sum_univ_three]
  have e0 : toLast (0 : Fin 3) s = 𝟙 _ := s.map_id _
  have e1 : toLast (1 : Fin 3) s = 𝟙 _ := s.map_id _
  have e2 : toLast (2 : Fin 3) s = s.map' 1 2 := rfl
  rw [e0, e1, e2, F.map_id]
  simp [sub_eq_add_neg]
  rfl

end Cochains

theorem close_sum {M : Type*} [AddCommGroup M] (tce tbe tbc kv kw ku kvw i : M)
    (h₁ : tce - tbe + tbc = kv + kw - kvw) (h₂ : kvw = ku + i) :
    (-1 : ℤ) ^ 1 • ((tce - kw) - (tbe - ku) + (tbc - kv)) = i := by
  have e : tce = kv + kw - kvw + tbe - tbc := by rw [← h₁]; abel
  rw [e, h₂]
  simp only [pow_one, neg_smul, one_smul]
  abel

theorem u_congr {X : Scheme.{0}} (D : LineData X) {V : Scheme.{0}} {a a' b b' : V ⟶ D.Y}
    (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b' ≫ D.f) (ha : a = a') (hb : b = b') :
    D.u a b h = D.u a' b' h' := by
  subst ha hb; rfl

theorem etale_chern_class_eq_kummer_class : CrystallineSemistableComparison.E.EtSpec → CrystallineSemistableComparison.E.ResGood → CrystallineSemistableComparison.E.StCol → CrystallineSemistableComparison.E.FirstChernCoboundary → CrystallineSemistableComparison.E.KumPow →
    CrystallineSemistableComparison.E.EtaleFirstChernKummer := by
  intro hES hRG hSC hCP hKP hGen hKum hC1 q _ C _ P X Y D L hL hInv x hx z Λ
  obtain ⟨a, η, θ, hRep, hηn, hθn, hdη, hdiff, hcoc⟩ := hCP hC1 q X D L hL hInv x hx
  have hθc : ∀ (V : Scheme.{0}) (b b' c : V ⟶ D.Y) (h : b ≫ D.f = c ≫ D.f) (h' : b' ≫ D.f = c ≫ D.f),
      b = b' → θ V b c h = θ V b' c h' := by
    intro V b b' c h h' e
    subst e
    rfl
  have hG : (P.res 1).Good := hRG hGen q C P 1
  obtain ⟨hιd, hdd, hinj, -, -⟩ := hSC ℤ C P.L (P.res 1) hG
  have hpp : ∀ {c c' : C} (φ : c ⟶ c'), ((P.S.map φ).unop ≫ Λ.p c) ≫ D.f = Λ.p c' ≫ D.f := by
    intro c c' φ
    rw [Category.assoc, Λ.hp, Λ.hp, Y.nat]
  let A₀ : ∀ {c c' : C} (φ : c ⟶ c'), Sec ((res _ (tw q 1)).X 0) (P.U c') := fun {c c'} φ =>
    θ _ ((P.S.map φ).unop ≫ Λ.p c) (Λ.p c') (hpp φ) - kumT q _ (Λ.r φ)
  let a₁ : Cn ((P.res 1).K 1) 0 := fun s => η _ (Λ.p (s.obj 0))
  let a₀ : Cn ((P.res 1).K 0) 1 := fun s => A₀ (s.map' 0 1)
  have h1 : (P.res 1).dvC 1 0 a₁ = Y.glob 1 2 a := by
    funext s
    refine (hdη _ (Λ.p (s.obj 0))).trans ?_
    rw [Λ.hp]
    rfl
  have h2 : (-1 : ℤ) ^ 0 • d ((P.res 1).K 1) 0 a₁ = (P.res 1).dvC 0 1 a₀ := by
    funext s
    rw [pow_zero, one_smul, d_zero_apply]
    have e := hdiff _ ((P.S.map (s.map' 0 1)).unop ≫ Λ.p (s.obj 0)) (Λ.p (s.obj 1)) (hpp (s.map' 0 1)) _ (Λ.hr _)
    rw [← hηn] at e
    exact e
  have h3 : (-1 : ℤ) ^ 1 • d ((P.res 1).K 0) 1 a₀ = (P.res 1).ιC 2 z := by
    funext s
    rw [Pi.smul_apply, d_one_apply]
    let g := (P.S.map (s.map' 1 2)).unop
    have hg : g ≫ (P.S.map (s.map' 0 1)).unop = (P.S.map (s.map' 0 2)).unop := by
      have e : s.map' 0 2 = s.map' 0 1 ≫ s.map' 1 2 := s.map_comp _ _
      rw [e, P.S.map_comp, unop_comp]
    have hb : g ≫ (P.S.map (s.map' 0 1)).unop ≫ Λ.p (s.obj 0) =
        (P.S.map (s.map' 0 2)).unop ≫ Λ.p (s.obj 0) := by
      rw [← Category.assoc, hg]
    have hbc' : (g ≫ (P.S.map (s.map' 0 1)).unop ≫ Λ.p (s.obj 0)) ≫ D.f = (g ≫ Λ.p (s.obj 1)) ≫ D.f := by
      have e : ((P.S.map (s.map' 0 1)).unop ≫ Λ.p (s.obj 0)) ≫ D.f = Λ.p (s.obj 1) ≫ D.f := hpp (s.map' 0 1)
      rw [Category.assoc g, e, Category.assoc]
    have hbc : ((P.S.map (s.map' 0 2)).unop ≫ Λ.p (s.obj 0)) ≫ D.f = (g ≫ Λ.p (s.obj 1)) ≫ D.f := by
      rw [← hb]
      exact hbc'
    let v := Units.map g.appTop.hom.toMonoidHom (Λ.r (s.map' 0 1))
    let w := Λ.r (s.map' 1 2)
    let u := Λ.r (s.map' 0 2)
    have hv : v ^ q = D.u _ _ hbc := by
      change Units.map g.appTop.hom.toMonoidHom (Λ.r (s.map' 0 1)) ^ q = _
      rw [← map_pow, Λ.hr, ← D.nat]
      exact u_congr D _ _ hb rfl
    have hw : w ^ q = D.u (g ≫ Λ.p (s.obj 1)) (Λ.p (s.obj 2)) (hpp (s.map' 1 2)) := Λ.hr _
    have hc := hcoc _ _ _ _ hbc (hpp (s.map' 1 2)) v w hv hw
    have hk := hKP hKum q _ (P.ζ (s.obj (Fin.last 2))) (z s) (v * w * u⁻¹) u (Λ.hz s)
    rw [inv_mul_cancel_right] at hk
    have hn : ((((P.res 1).K 0).map (s.map' 1 2)).hom (a₀ (face 2 s))) =
        θ _ ((P.S.map (s.map' 0 2)).unop ≫ Λ.p (s.obj 0)) (g ≫ Λ.p (s.obj 1)) hbc - kumT q _ v := by
      have t₁ : Sec.res g (θ _ ((P.S.map (s.map' 0 1)).unop ≫ Λ.p (s.obj 0)) (Λ.p (s.obj 1)) (hpp (s.map' 0 1))) =
          θ _ ((P.S.map (s.map' 0 2)).unop ≫ Λ.p (s.obj 0)) (g ≫ Λ.p (s.obj 1)) hbc :=
        (hθn _ _ g _ _ _ hbc').trans (hθc _ _ _ _ _ _ hb)
      have t₂ : Sec.res g (kumT q _ (Λ.r (s.map' 0 1))) = kumT q _ v := (hKum q).1 _ _ g _ (P.ζ _).2.1
      exact (map_sub _ _ _).trans (congrArg₂ (· - ·) t₁ t₂)
    rw [hn]
    exact close_sum _ _ _ _ _ _ _ _ hc hk
  have hSt : (P.res 1).St z 2 0 (Y.glob 1 2 a) := ⟨a₁, h1, a₀, h2.symm, rfl, h3.symm⟩
  have hz : d P.L 2 z = 0 := by
    apply hinj 3
    rw [map_zero, ← hιd, ← h3, map_smul, d_d, smul_zero]
  exact ⟨hz, ((hES hGen q C P X Y 1 2 x).2 _ ⟨a, hRep, z, hz, hSt, rfl⟩).symm⟩

end GlobalTheory.CompanionTheory.EtaleChernClass
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LineMapExists
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.CechLine

variable {X : Scheme.{0}} (D : LineData X)

theorem u_self {V : Scheme.{0}} (a : V ⟶ D.Y) (h : a ≫ D.f = a ≫ D.f) : D.u a a h = 1 := by
  have h2 : D.u a a h * D.u a a h = D.u a a h * 1 := by
    rw [mul_one]
    exact D.coc a a a h h
  exact mul_left_cancel h2

theorem u_congr {V : Scheme.{0}} {a a' b b' : V ⟶ D.Y} (ha : a = a') (hb : b = b')
    (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b' ≫ D.f) : D.u a b h = D.u a' b' h' := by
  subst ha
  subst hb
  rfl

def lineFun {V : Scheme.{0}} {k : ℕ} (y : Fin (k + 1) → (V ⟶ D.Y)) (hy : ∀ i j, y i ≫ D.f = y j ≫ D.f) :
    ComposableArrows (SingleObj (GL (Fin 1) Γ(V, ⊤))) k where
  obj _ := SingleObj.star _
  map {i j} _ := Matrix.GeneralLinearGroup.scalar (Fin 1) (D.u (y i) (y j) (hy i j))
  map_id i := by rw [u_self]; exact map_one (Matrix.GeneralLinearGroup.scalar (Fin 1))
  map_comp {i j l} _ _ := by
    rw [SingleObj.comp_as_mul]
    refine Eq.trans ?_ (map_mul (Matrix.GeneralLinearGroup.scalar (Fin 1)) _ _)
    rw [mul_comm, D.coc]

variable {D}

theorem exists_pts (hC : CechPt) {k : ℕ} {U : Scheme.{0}} (z : Sx (cech D.f) k U) :
    ∃ y : Fin (k + 1) → (U ⟶ D.Y), ∃ x h, z = cechPt D.f k x y h := by
  obtain ⟨x, y, h, hz⟩ := (hC D.Y X D.f k U).1 z
  exact ⟨y, x, h, hz⟩

def pts (hC : CechPt) {k : ℕ} {U : Scheme.{0}} (z : Sx (cech D.f) k U) : Fin (k + 1) → (U ⟶ D.Y) :=
  (exists_pts hC z).choose

theorem pts_spec (hC : CechPt) {k : ℕ} {U : Scheme.{0}} (z : Sx (cech D.f) k U) :
    ∃ x h, z = cechPt D.f k x (pts hC z) h := by
  exact (exists_pts hC z).choose_spec

theorem pts_eq (hC : CechPt) {k : ℕ} {U : Scheme.{0}} (z : Sx (cech D.f) k U) (i j : Fin (k + 1)) :
    pts hC z i ≫ D.f = pts hC z j ≫ D.f := by
  obtain ⟨x, h, -⟩ := pts_spec hC z
  exact (h i).trans (h j).symm

theorem pts_cechPt (hC : CechPt) {k : ℕ} {U : Scheme.{0}} (x : U ⟶ X) (y : Fin (k + 1) → (U ⟶ D.Y))
    (h : ∀ i, y i ≫ D.f = x) : pts hC (cechPt D.f k x y h) = y := by
  obtain ⟨x', h', hz⟩ := pts_spec hC (cechPt D.f k x y h)
  exact ((hC D.Y X D.f k U).2.1 _ _ _ _ _ _ hz).symm

theorem pts_res (hC : CechPt) {k : ℕ} {U V : Scheme.{0}} (g : V ⟶ U) (z : Sx (cech D.f) k U) (i : Fin (k + 1)) :
    pts hC (Sx.res g z) i = g ≫ pts hC z i := by
  obtain ⟨x, h, hz⟩ := pts_spec hC z
  have e := ((hC D.Y X D.f k U).2.2 x (pts hC z) h).2.1 V g
  rw [← hz] at e
  rw [e, pts_cechPt]

theorem pts_along (hC : CechPt) {k p : ℕ} {U : Scheme.{0}} (z : Sx (cech D.f) k U)
    (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk k) (i : Fin (p + 1)) :
    pts hC (Sx.along z θ) i = pts hC z (θ.toOrderHom i) := by
  obtain ⟨x, h, hz⟩ := pts_spec hC z
  have e := ((hC D.Y X D.f k U).2.2 x (pts hC z) h).2.2 p θ
  rw [← hz] at e
  rw [e, pts_cechPt]

theorem scalar_map {A B : CommRingCat.{0}} (f : A ⟶ B) (u : (A : Type)ˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 1) (Units.map f.hom.toMonoidHom u) =
      Matrix.GeneralLinearGroup.map f.hom (Matrix.GeneralLinearGroup.scalar (Fin 1) u) := by
  ext i j
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

variable (D) in
theorem lineFun_res {U V : Scheme.{0}} {k : ℕ} (g : V ⟶ U) (y : Fin (k + 1) → (U ⟶ D.Y))
    (hy : ∀ i j, y i ≫ D.f = y j ≫ D.f) (y' : Fin (k + 1) → (V ⟶ D.Y))
    (hy' : ∀ i j, y' i ≫ D.f = y' j ≫ D.f) (e : ∀ i, y' i = g ≫ y i) :
    lineFun D y' hy' = (show Fin (k + 1) ⥤ (glCat 1).obj Γ(U, ⊤) from lineFun D y hy) ⋙
      ((glCat 1).map (Scheme.Γ.map g.op)).toFunctor := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun i j _ => ?_)
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  change Matrix.GeneralLinearGroup.scalar (Fin 1) (D.u (y' i) (y' j) (hy' i j)) =
    Matrix.GeneralLinearGroup.map (Scheme.Γ.map g.op).hom
      (Matrix.GeneralLinearGroup.scalar (Fin 1) (D.u (y i) (y j) (hy i j)))
  rw [← scalar_map]
  congr 1
  rw [u_congr D (e i) (e j) (hy' i j) (by rw [Category.assoc, Category.assoc, hy i j]),
    D.nat g (y i) (y j) (hy i j)]
  rfl


variable (D) in
def lineMap (hC : CechPt) : cech D.f ⟶ ofCat (glCat 1) where
  app n :=
    { app := fun U => TypeCat.ofHom fun z =>
        lineFun D (pts hC (show Sx (cech D.f) n.unop.len U.unop from z)) (pts_eq hC _)
      naturality := fun U U' g => by
        ext z
        exact lineFun_res D g.unop _ (pts_eq hC _) _ (pts_eq hC _) (fun i => pts_res hC g.unop _ i) }
  naturality n m θ := by
    ext U z
    change lineFun D (pts hC (Sx.along (show Sx (cech D.f) n.unop.len U.unop from z) θ.unop)) (pts_eq hC _) =
      (SimplexCategory.toCat.map θ.unop).toFunctor ⋙ lineFun D (pts hC (show Sx (cech D.f) n.unop.len U.unop from z)) (pts_eq hC _)
    refine CategoryTheory.Functor.hext (fun _ => rfl) (fun i j p => heq_of_eq ?_)
    exact congrArg (Matrix.GeneralLinearGroup.scalar (Fin 1))
      (u_congr D (pts_along hC _ θ.unop i) (pts_along hC _ θ.unop j) _ _)

theorem lineMap_exists : CrystallineSemistableComparison.E.CechPt → CrystallineSemistableComparison.E.LineMap := by
  intro hC X D
  refine ⟨lineMap D hC, ?_⟩
  unfold CrystallineSemistableComparison.E.LineData.IsMap
  intro V x a h
  have hp := pts_cechPt (D := D) hC x a h
  change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1)
    (D.u (pts hC (cechPt D.f 1 x a h) 0) (pts hC (cechPt D.f 1 x a h) 1) (pts_eq hC _ 0 1))) = _
  rw [u_congr D (congrFun hp 0) (congrFun hp 1) _ ((h 0).trans (h 1).symm)]
  ext
  simp [Matrix.GeneralLinearGroup.scalar]

end GlobalTheory.CompanionTheory.CechLine
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitOneSubPow
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.PrimAlgProof

open Polynomial

theorem exists_universal (q : ℕ) [NeZero q] :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (ξ : R), IsPrimitiveRoot ξ q ∧
      ∀ (A : Type) [CommRing A] (z : A), aeval z (cyclotomic q ℤ) = 0 →
        ∃ φ : R →+* A, φ ξ = z := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hlift : ∀ (A : Type) [CommRing A] (z : A), aeval z (cyclotomic q ℤ) = 0 →
      ∃ φ : AdjoinRoot (cyclotomic q ℤ) →+* A, φ (AdjoinRoot.root _) = z := by
    intro A _ z hz
    have h : (cyclotomic q ℤ).eval₂ (Int.castRingHom A) z = 0 := by
      rw [aeval_def] at hz
      simpa [eq_intCast] using hz
    exact ⟨AdjoinRoot.lift _ z h, AdjoinRoot.lift_root h⟩
  haveI hdom : IsDomain (AdjoinRoot (cyclotomic q ℤ)) :=
    AdjoinRoot.isDomain_of_prime (cyclotomic.irreducible hq).prime
  refine ⟨AdjoinRoot (cyclotomic q ℤ), inferInstance, hdom, AdjoinRoot.root _, ?_, hlift⟩
  obtain ⟨ψ, hψ⟩ := hlift ℂ (Complex.exp (2 * Real.pi * Complex.I / q)) (by
    have hp := Complex.isPrimitiveRoot_exp q (NeZero.ne q)
    have : IsRoot (cyclotomic q ℂ) (Complex.exp (2 * Real.pi * Complex.I / q)) :=
      (isRoot_cyclotomic_iff).2 hp
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact this)
  haveI : NeZero ((q : ℕ) : AdjoinRoot (cyclotomic q ℤ)) := ⟨fun h0 => by
    have := congrArg ψ h0
    rw [map_natCast, map_zero] at this
    exact NeZero.ne q (by exact_mod_cast this)⟩
  refine (isRoot_cyclotomic_iff).1 ?_
  have h := AdjoinRoot.eval₂_root (cyclotomic q ℤ)
  rw [eval₂_eq_eval_map, map_cyclotomic] at h
  exact h

theorem X_pow_sub_one_eq {R : Type} [CommRing R] [IsDomain R] (q : ℕ) [NeZero q] {ξ : R}
    (hξ : IsPrimitiveRoot ξ q) :
    (X ^ q - 1 : R[X]) = ∏ a : ZMod q, (X - C (ξ ^ a.val)) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [X_pow_sub_one_eq_prod hq hξ]
  symm
  refine Finset.prod_bij (fun a _ => ξ ^ a.val) ?_ ?_ ?_ ?_
  · intro a _
    rw [mem_nthRootsFinset hq]
    rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]
  · intro a _ b _ h
    exact ZMod.val_injective q (hξ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h)
  · intro μ hμ
    rw [mem_nthRootsFinset hq] at hμ
    obtain ⟨i, hi, rfl⟩ := hξ.eq_pow_of_pow_eq_one hμ
    exact ⟨(i : ZMod q), Finset.mem_univ _, by rw [ZMod.val_cast_of_lt hi]⟩
  · intro a _
    rfl

theorem cyclotomic_eq {R : Type} [CommRing R] [IsDomain R] (q : ℕ) [NeZero q] {ξ : R}
    (hξ : IsPrimitiveRoot ξ q) :
    cyclotomic q R = ∏ a : (ZMod q)ˣ, (X - C (ξ ^ (a : ZMod q).val)) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots hξ]
  symm
  refine Finset.prod_bij (fun a _ => ξ ^ (a : ZMod q).val) ?_ ?_ ?_ ?_
  · intro a _
    rw [mem_primitiveRoots hq]
    exact hξ.pow_of_coprime _ (ZMod.val_coe_unit_coprime a)
  · intro a _ b _ h
    exact Units.ext (ZMod.val_injective q (hξ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h))
  · intro μ hμ
    rw [mem_primitiveRoots hq] at hμ
    obtain ⟨i, hi, rfl⟩ := hξ.eq_pow_of_pow_eq_one hμ.pow_eq_one
    have hc : Nat.Coprime i q := (hξ.pow_iff_coprime hq i).1 hμ
    refine ⟨ZMod.unitOfCoprime i hc, Finset.mem_univ _, ?_⟩
    simp only [ZMod.coe_unitOfCoprime]
    rw [ZMod.val_cast_of_lt hi]
  · intro a _
    rfl

theorem isUnit_one_sub_pow {R A : Type} [CommRing R] [IsDomain R] [CommRing A] (n : ℕ) {ξ : R}
    (hξ : IsPrimitiveRoot ξ (n + 1)) (φ : R →+* A) (hu : IsUnit ((n + 1 : ℕ) : A))
    (k : ℕ) (hk : k < n) : IsUnit (1 - φ ξ ^ (k + 1)) := by
  have h := congrArg φ hξ.prod_one_sub_pow_eq_order
  rw [map_prod] at h
  have hn : φ ((n : R) + 1) = ((n + 1 : ℕ) : A) := by simp
  have hd : φ (1 - ξ ^ (k + 1)) ∣ ∏ i ∈ Finset.range n, φ (1 - ξ ^ (i + 1)) :=
    Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hk)
  rw [h, hn] at hd
  have := isUnit_of_dvd_unit hd hu
  simpa using this

theorem primAlg : CrystallineSemistableComparison.E.PrimAlg := by
  intro q _ A _ ζ
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  obtain ⟨R, _, _, ξ, hξ, hl⟩ := exists_universal q
  obtain ⟨φ, hφ⟩ := hl A ζ.1 ζ.2.2
  have hpow : ζ.1 ^ q = 1 := by rw [← hφ, ← map_pow, hξ.pow_eq_one, map_one]
  have hζu : IsUnit ζ.1 := by
    refine IsUnit.of_mul_eq_one (ζ.1 ^ (q - 1)) ?_
    rw [← pow_succ', Nat.sub_add_cancel hq, hpow]
  have h1 : ∀ k, 0 < k → k < q → IsUnit (1 - ζ.1 ^ k) := by
    intro k hk0 hkq
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne q)
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0.ne'
    subst hn
    have := isUnit_one_sub_pow n hξ φ ζ.2.1 m (by omega)
    rwa [hφ] at this
  have hlt : ∀ a b : ℕ, a < b → b < q → IsUnit (ζ.1 ^ a - ζ.1 ^ b) := by
    intro a b hab hb
    have : ζ.1 ^ a - ζ.1 ^ b = ζ.1 ^ a * (1 - ζ.1 ^ (b - a)) := by
      rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hab.le]
    rw [this]
    exact (hζu.pow a).mul (h1 _ (by omega) (by omega))
  refine ⟨hpow, ?_, ?_, ?_⟩
  · intro a b hab
    have hv : a.val ≠ b.val := fun h => hab (ZMod.val_injective q h)
    rcases lt_or_gt_of_ne hv with h | h
    · exact hlt _ _ h (ZMod.val_lt b)
    · have := (hlt _ _ h (ZMod.val_lt a)).neg
      rwa [neg_sub] at this
  · intro r
    have h := congrArg (fun p => eval r (p.map φ)) (X_pow_sub_one_eq q hξ)
    simpa [Polynomial.map_prod, eval_prod, hφ] using h
  · intro r
    have h := congrArg (fun p => eval r (p.map φ)) (cyclotomic_eq q hξ)
    simp only [map_cyclotomic, Polynomial.map_prod, eval_prod] at h
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic, h]
    simp [hφ]

end GlobalTheory.CompanionTheory.PrimAlgProof
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemBasicOpenOfIsUnitSub
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.RootPowLC

theorem mem_basicOpen_prod {U : Scheme.{0}} {ι : Type} (t : Finset ι) (s : ι → Γ(U, ⊤)) (u : U)
    (h : ∀ a ∈ t, u ∈ U.basicOpen (s a)) : u ∈ U.basicOpen (∏ a ∈ t, s a) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, U.basicOpen_of_isUnit isUnit_one]
    trivial
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Scheme.basicOpen_mul]
    exact ⟨h a (Finset.mem_insert_self a t), ih fun b hb => h b (Finset.mem_insert_of_mem hb)⟩

theorem exists_notMem_basicOpen {U : Scheme.{0}} {ι : Type} (t : Finset ι) (s : ι → Γ(U, ⊤))
    (h : ∏ a ∈ t, s a = 0) (u : U) : ∃ a ∈ t, u ∉ U.basicOpen (s a) := by
  by_contra hc
  push_neg at hc
  have hm := mem_basicOpen_prod t s u hc
  rw [h, Scheme.basicOpen_zero] at hm
  exact hm

theorem mem_basicOpen_of_isUnit_sub {U : Scheme.{0}} (x y : Γ(U, ⊤)) (h : IsUnit (x - y)) (u : U)
    (hx : u ∉ U.basicOpen x) : u ∈ U.basicOpen y := by
  rw [Scheme.mem_basicOpen_top] at hx ⊢
  have h1 : IsUnit (U.presheaf.germ ⊤ u trivial (x - y)) := h.map _
  rw [map_sub, sub_eq_add_neg] at h1
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h1 with h2 | h2
  · exact absurd h2 hx
  · simpa using h2.neg

theorem isUnit_appTop_of_mem {V U : Scheme.{0}} (g : V ⟶ U) (x : Γ(U, ⊤))
    (h : ∀ v : V, g v ∈ U.basicOpen x) : IsUnit (g.appTop.hom x) := by
  refine RingedSpace.isUnit_of_isUnit_germ V.toRingedSpace ⊤ _ fun v _ => ?_
  have e : V.basicOpen (g.appTop.hom x) = g ⁻¹ᵁ U.basicOpen x := (Scheme.preimage_basicOpen g x).symm
  have hv : v ∈ V.basicOpen (g.appTop.hom x) := by
    rw [e]
    exact h v
  exact (Scheme.mem_basicOpen_top V (g.appTop.hom x) v).1 hv

theorem exists_isPow (hP : PrimAlg) (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤))
    (r : Γ(U, ⊤)) (hr : r ^ q = 1) :
    ∃ f : LocallyConstant U (ZMod q), IsPow ζ f r ∧
      ∀ (u : U) (a : ZMod q), u ∉ U.basicOpen (r - ζ.1 ^ a.val) → f u = a := by
  classical
  have hprod : ∏ a : ZMod q, (r - ζ.1 ^ a.val) = 0 := by
    rw [← (hP q _ ζ).2.2.1 r, hr, sub_self]
  have hex : ∀ u : U, ∃ a : ZMod q, u ∉ U.basicOpen (r - ζ.1 ^ a.val) := by
    intro u
    obtain ⟨a, -, ha⟩ := exists_notMem_basicOpen Finset.univ (fun a : ZMod q => r - ζ.1 ^ a.val) hprod u
    exact ⟨a, ha⟩
  have huniq : ∀ (u : U) (a b : ZMod q), a ≠ b → u ∉ U.basicOpen (r - ζ.1 ^ a.val) →
      u ∈ U.basicOpen (r - ζ.1 ^ b.val) := by
    intro u a b hab ha
    apply mem_basicOpen_of_isUnit_sub _ _ _ u ha
    have hd : (r - ζ.1 ^ a.val) - (r - ζ.1 ^ b.val) = ζ.1 ^ b.val - ζ.1 ^ a.val := by ring
    rw [hd]
    exact (hP q _ ζ).2.1 b a (Ne.symm hab)
  obtain ⟨f0, hf0def⟩ : ∃ f0 : U → ZMod q, f0 = fun u => Classical.choose (hex u) := ⟨_, rfl⟩
  have hf0 : ∀ u, u ∉ U.basicOpen (r - ζ.1 ^ (f0 u).val) := by
    intro u
    rw [hf0def]
    exact Classical.choose_spec (hex u)
  have hf0_iff : ∀ u a, f0 u = a ↔ u ∉ U.basicOpen (r - ζ.1 ^ a.val) := by
    intro u a
    constructor
    · rintro rfl
      exact hf0 u
    · intro ha
      by_contra hne
      exact (hf0 u) (huniq u a (f0 u) (Ne.symm hne) ha)
  have hloc : IsLocallyConstant f0 := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro a
    have hfib : f0 ⁻¹' {a} = ⋂ b ∈ (Finset.univ.erase a : Finset (ZMod q)), (U.basicOpen (r - ζ.1 ^ b.val) : Set U) := by
      ext u
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Finset.mem_erase, Finset.mem_univ,
        and_true, SetLike.mem_coe]
      rw [hf0_iff]
      constructor
      · intro ha b hb
        exact huniq u a b (Ne.symm hb) ha
      · intro h ha
        obtain ⟨a', ha'⟩ := hex u
        by_cases heq : a' = a
        · exact ha' (heq ▸ ha)
        · exact ha' (h a' heq)
    rw [hfib]
    exact isOpen_biInter_finset fun b _ => (U.basicOpen (r - ζ.1 ^ b.val)).isOpen
  refine ⟨⟨f0, hloc⟩, ?_, fun u a ha => (hf0_iff u a).mpr ha⟩
  delta CrystallineSemistableComparison.E.IsPow
  intro V g a hga
  have hunitb : ∀ b : ZMod q, b ≠ a → IsUnit (g.appTop.hom (r - ζ.1 ^ b.val)) := fun b hb =>
    isUnit_appTop_of_mem g _ (fun v => huniq (g v) a b (Ne.symm hb) ((hf0_iff (g v) a).mp (hga v)))
  have hprodV : ∏ b : ZMod q, (g.appTop.hom r - g.appTop.hom ζ.1 ^ b.val) = 0 := by
    have h0 := congrArg g.appTop.hom hprod
    rw [map_prod, map_zero] at h0
    simpa only [map_sub, map_pow] using h0
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a)] at hprodV
  have hu : IsUnit (∏ b ∈ Finset.univ.erase a, (g.appTop.hom r - g.appTop.hom ζ.1 ^ b.val)) := by
    refine Finset.prod_induction _ IsUnit (fun x y hx hy => hx.mul hy) isUnit_one (fun b hb => ?_)
    have h1 := hunitb b (Finset.ne_of_mem_erase hb)
    simpa only [map_sub, map_pow] using h1
  have h0 : g.appTop.hom r - g.appTop.hom ζ.1 ^ a.val = 0 := hu.mul_left_eq_zero.mp hprodV
  show g.appTop.hom r = (g.appTop.hom ζ.1) ^ a.val
  exact sub_eq_zero.mp h0

theorem rootPow : CrystallineSemistableComparison.E.PrimAlg → CrystallineSemistableComparison.E.RootPow := by
  intro hP q _ U ζ
  refine ⟨fun r hr => ?_, fun ξ => ?_⟩
  · obtain ⟨f, hf, -⟩ := exists_isPow hP q U ζ r hr
    exact ⟨f, hf⟩
  · have hξq : ξ.1 ^ q = 1 := (hP q _ ξ).1
    obtain ⟨f, hf, hloc⟩ := exists_isPow hP q U ζ ξ.1 hξq
    refine ⟨f, hf, fun u => ?_⟩
    have hprod : ∏ a : ZMod q, (ξ.1 - ζ.1 ^ a.val) = 0 := by
      rw [← (hP q _ ζ).2.2.1 ξ.1, hξq, sub_self]
    obtain ⟨a, -, ha⟩ := exists_notMem_basicOpen Finset.univ
      (fun a : ZMod q => ξ.1 - ζ.1 ^ a.val) hprod u
    rw [hloc u a ha]
    by_contra hna
    set m := a.val with hm
    have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    have ha' : a = (m : ZMod q) := (ZMod.natCast_zmod_val a).symm
    have hcop : ¬ m.Coprime q := by
      intro hc
      exact hna (ha' ▸ (ZMod.isUnit_iff_coprime m q).2 hc)
    set g := Nat.gcd m q with hgdef
    have hg1 : g ≠ 1 := hcop
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_right m hq
    have hgq : g ∣ q := Nat.gcd_dvd_right m q
    have hgm : g ∣ m := Nat.gcd_dvd_left m q
    set k := q / g with hkdef
    have hkpos : 0 < k := Nat.div_pos (Nat.le_of_dvd hq hgq) hgpos
    have hklt : k < q := Nat.div_lt_self hq (by omega)
    have hζq : ζ.1 ^ q = 1 := (hP q _ ζ).1
    have hζmk : (ζ.1 ^ m) ^ k = 1 := by
      obtain ⟨m', hm'⟩ := hgm
      have e1 : m * k = q * m' := by
        rw [hm', hkdef, mul_comm g m', mul_assoc, Nat.mul_div_cancel' hgq, mul_comm]
      rw [← pow_mul, e1, pow_mul, hζq, one_pow]
    have hunit : IsUnit (ξ.1 ^ k - 1) := by
      have hne : ((k : ℕ) : ZMod q) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hd
        exact absurd (Nat.le_of_dvd hkpos hd) (by omega)
      have hu := (hP q _ ξ).2.1 (k : ZMod q) 0 hne
      rwa [ZMod.val_natCast_of_lt hklt, ZMod.val_zero, pow_zero] at hu
    have hdvd : ξ.1 - ζ.1 ^ m ∣ ξ.1 ^ k - 1 := by
      have hs := sub_dvd_pow_sub_pow ξ.1 (ζ.1 ^ m) k
      rwa [hζmk] at hs
    apply ha
    rw [Scheme.mem_basicOpen_top]
    exact isUnit_of_dvd_unit (map_dvd _ hdvd) (hunit.map _)

end GlobalTheory.CompanionTheory.RootPowLC
end
