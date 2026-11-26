module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfGenerization

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckePointsOfPartsComm
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckePointsOfParts
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjMapOfIsHeckeIsog
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HeckePoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B : Type} [CommRing B] {b : Base l B} {k : Type} [Field k] {s : Sp k ⟶ Sp B}

theorem exists_torsion_lift {Q Q' : Type} [CommGroup Q] [CommGroup Q'] (ψ : Q →* Q') (hs : Function.Surjective ψ)
    {q n : ℕ} (hq : ∀ x, ψ x = 1 → x ^ q = 1) (hn : 0 < n) (hc : n.Coprime q) (y : Q') (hy : y ^ n = 1) :
    ∃ x, x ^ n = 1 ∧ ψ x = y := by
  obtain ⟨u, rfl⟩ := hs y
  obtain ⟨r, -, hr⟩ := Nat.exists_mul_mod_eq_of_coprime 1 hc.symm hn.ne'
  refine ⟨u ^ (q * r), ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, pow_mul, hq _ ((map_pow _ _ _).trans hy), one_pow]
  · rw [map_pow, pow_eq_pow_of_modEq (show q * r ≡ 1 [MOD n] from hr) hy, pow_one]

theorem objMap_of_isHeckeIsog [IsAlgClosed k] [CharZero k] (hL : Out.Laws)
    (hfacts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L)
    (hDet : ∀ (k : Type) [Field k] [IsAlgClosed k] (P P' : Out.PolAV (Sp k)) (α : P.A ⟶ P'.A) (p d : ℕ), IsMonHom α → p.Prime → CharZero k → (∀ (n : ℕ) (x y : 𝟙_ (Over (Sp k)) ⟶ P.A) (c : kˣ), 0 < n → n.Coprime p → x ^ n = 1 → y ^ n = 1 → Out.WeilIs P.A P.L n x y (unitOn c) → Out.WeilIs P'.A P'.L n (x ≫ α) (y ≫ α) (unitOn (c ^ d))) → LBIso (abelian₂ P.A (lbPow P.L d)) (abelian₂ P.A (P'.L.pull α.left)))
    {o o₁ o₂ : Obj D l b s} {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ l.M') {C : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.t.G)}
    (hC : ∀ x ∈ C, x ^ p ^ 2 = 1) {ψ₁ : o.t.G ⟶ o₁.t.G} {ψ₂ : o.t.G ⟶ o₂.t.G} (h₁ : IsHeckeIsog o o₁ p C ψ₁)
    [IsFinite ψ₁.left] [Etale ψ₁.left] [Surjective ψ₁.left] (h₂ : IsHeckeIsog o o₂ p C ψ₂) :
    Nonempty (ObjMap o₁ o₂ (𝟙 _)) := by
  obtain ⟨hom₁, lin₁, sur₁, ker₁, weil₁, lev₁⟩ := h₁
  obtain ⟨hom₂, lin₂, sur₂, ker₂, weil₂, lev₂⟩ := h₂
  obtain ⟨hab, hdim, hrig, hsym⟩ := hfacts E H D l B b _ s o
  obtain ⟨hab₁, hdim₁, hrig₁, hsym₁⟩ := hfacts E H D l B b _ s o₁
  obtain ⟨hab₂, hdim₂, hrig₂, hsym₂⟩ := hfacts E H D l B b _ s o₂
  let P : Out.PolAV (Sp k) :=
    { A := o.t.G, isAb := hab, g := _, smoothDim := hdim,
      L := o.t.PP.L, isLB := o.t.PP.isLB, rigid := hrig, sym := hsym,
      ample := o.ample, ktriv := o.ktriv }
  let P₁ : Out.PolAV (Sp k) :=
    { A := o₁.t.G, isAb := hab₁, g := _, smoothDim := hdim₁,
      L := o₁.t.PP.L, isLB := o₁.t.PP.isLB, rigid := hrig₁, sym := hsym₁,
      ample := o₁.ample, ktriv := o₁.ktriv }
  let P₂ : Out.PolAV (Sp k) :=
    { A := o₂.t.G, isAb := hab₂, g := _, smoothDim := hdim₂,
      L := o₂.t.PP.L, isLB := o₂.t.PP.isLB, rigid := hrig₂, sym := hsym₂,
      ample := o₂.ample, ktriv := o₂.ktriv }
  have := o₁.proper
  have := o₂.proper
  obtain ⟨α, hα⟩ := exists_fac hab.smooth ψ₁ ψ₂ fun x hx => (ker₂ x).2 ((ker₁ x).1 hx)
  have homα : IsMonHom α := hL.rigidity _ _ _ hab₁ hab₂ α (by
    rw [← IsMonHom.one_hom ψ₁, Category.assoc, hα, IsMonHom.one_hom])
  have : Epi ψ₁.left := Flat.epi_of_flat_of_surjective _
  have : Epi ψ₁ := Over.epi_of_epi_left ψ₁
  have linα : ∀ a, o₁.t.act.act a ≫ α = α ≫ o₂.t.act.act a := fun a => by
    rw [← cancel_epi ψ₁, ← reassoc_of% lin₁, hα, reassoc_of% hα, lin₂]
  let ρ : (𝟙_ (Over (Sp k)) ⟶ o.t.G) →* (𝟙_ (Over (Sp k)) ⟶ o₁.t.G) :=
    MonoidHom.mk' (fun z => z ≫ ψ₁) fun a c => MonObj.mul_comp a c ψ₁
  have hlam : LBIso (abelian₂ o₁.t.G (lbPow o₁.t.PP.L 1)) (abelian₂ o₁.t.G (o₂.t.PP.L.pull α.left)) :=
    hDet k P₁ P₂ α p 1 homα hp inferInstance fun n x y c hn hc hx hy h => by
      have lift := exists_torsion_lift ρ sur₁ (fun x hx => hC x ((ker₁ x).1 hx)) hn (hc.pow_right 2)
      obtain ⟨x₀, tx, ex⟩ := lift x hx
      obtain ⟨y₀, ty, ey⟩ := lift y hy
      obtain rfl : x₀ ≫ ψ₁ = x := ex
      obtain rfl : y₀ ≫ ψ₁ = y := ey
      obtain ⟨c₀, hc₀, -⟩ := (hL.weil _ P n _).1 x₀ y₀ tx ty
      obtain ⟨c₀, rfl⟩ := (unitOn_bijective k).2 c₀
      have e : c = c₀ ^ p ^ 2 := (unitOn_bijective k).1
        (((hL.weil _ P₁ n _).1 _ _ hx hy).unique h (weil₁ n x₀ y₀ c₀ hc hc₀))
      have w := weil₂ n x₀ y₀ c₀ hc hc₀
      rw [← hα, ← Category.assoc, ← Category.assoc, ← e] at w
      rw [pow_one]
      exact w
  have hiso := iso_of_lam o₁.t o₂.t α linα hlam
  have := mono_of_kTriv α o₁.t.PP.isLB o₂.t.PP.isLB hiso o₁.ktriv
  have : IsIso α := isIso_of_mono α hab₂.smooth fun y => by
    obtain ⟨x, rfl⟩ := sur₂ y
    exact ⟨x ≫ ψ₁, by rw [Category.assoc, hα]⟩
  have : IsMonHom (asIso α).hom := homα
  obtain ⟨p₀, hp₀⟩ := exists_inv_mod hp hpM
  refine ⟨{ cm := CubeMap.ofHom α, cart := isGrpPullback_of_iso (asIso α), base := rfl
            act := fun a => congrArg (fun q => q.left) (linα a)
            lin := isPullCubical_of_iso hL.globalFns hab₁ α _ _ hiso
            eta := fun a => ?_, etaA := fun a => ?_ }⟩
  · rw [Category.id_comp, ← (lev₁ p₀ hp₀ a).1, ← (lev₂ p₀ hp₀ a).1, ← hα, ← Category.assoc]; rfl
  · rw [Category.id_comp, ← (lev₁ p₀ hp₀ a).2, ← (lev₂ p₀ hp₀ a).2, ← hα, ← Category.assoc]; rfl

end GlobalTheory.HeckePoint
end
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HeckePoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem fibPt_injective {X : Scheme.{0}} (G : Over X) {k : Type} [Field k] {y : Sp k ⟶ X} :
    Function.Injective (fibPt G (y := y)) := fun a b h => Over.OverMorphism.ext (by
  have := congrArg (· ≫ pullback.fst G.hom y) h
  simpa only [fibPt, pullback.lift_fst] using this)

end GlobalTheory.HeckePoint

namespace GlobalTheory

open HeckePoint

end GlobalTheory
end
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HeckePoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem exists_transfer_comm
    {B : Type} [CommRing B] {b : Base l B} {X : Scheme.{0}} {sX : X ⟶ Sp B} (u : Obj D l b sX) {k : Type} [Field k]
    {s : Sp k ⟶ Sp B} {o : Obj D l b s} {y : Sp k ⟶ X} (m : ObjMap o u y) :
    ∃ (ρ : (𝟙_ (Over (Sp k)) ⟶ o.t.G) ≃* (Over.mk y ⟶ u.t.G)) (e : o.t.G.left ≅ pullback u.t.G.hom y),
      e.hom ≫ pullback.snd _ _ = o.t.G.hom ∧ (∀ x, fibPt _ (ρ x) = x.left ≫ e.hom) ∧
      (∀ a x, ρ (x ≫ o.t.act.act a) = ρ x ≫ u.t.act.act a) ∧
      (∀ (n : ℤ) x x' (c : kˣ), Out.WeilIs o.t.G o.t.PP.L n x x' (unitOn c) ↔
        Out.WeilIs u.t.G u.t.PP.L n (ρ x) (ρ x') (unitOn c)) ∧
      (∀ a, ρ (o.eta a) = toUnit _ ≫ u.eta a) ∧ ∀ a, ρ (o.etaA a) = toUnit _ ≫ u.etaA a := by
  obtain ⟨ρ, hρ⟩ := exists_ptsEquiv m.cart (𝟙_ (Over (Sp k))) y (Category.id_comp _)
  have key : ∀ (T : Over (Sp k)) (y' : T.left ⟶ X) (_ : T.hom ≫ y = y') (n : ℤ) (x x' : T ⟶ o.t.G)
      (x₀ x₀' : Over.mk y' ⟶ u.t.G) (c : Γ(T.left, ⊤)ˣ), x₀.left = x.left ≫ m.cm.F → x₀'.left = x'.left ≫ m.cm.F →
      (Out.WeilIs o.t.G o.t.PP.L n x x' c ↔ Out.WeilIs u.t.G u.t.PP.L n x₀ x₀' c) := by
    intro T y' e
    subst e
    obtain ⟨w, hw, -⟩ := m.lin
    exact fun n x x' x₀ x₀' c => weilIs_grpPullback_of_comm _ _ _ _ y m.cm.F _ _ u.t.PP.isLB o.t.PP.isLB m.cart ⟨w, hw⟩ T n x x' x₀ x₀' c
  have tu : (toUnit (Over.mk y)).left = y := by simp
  refine ⟨ρ, m.cart.1.isoPullback, m.cart.1.isoPullback_hom_snd, fun x => ?_, fun a x => Over.OverMorphism.ext ?_,
    fun n x x' c => key _ y (Category.id_comp _) n x x' _ _ _ (hρ x) (hρ x'), fun a => Over.OverMorphism.ext ?_,
    fun a => Over.OverMorphism.ext ?_⟩
  · apply pullback.hom_ext
    · rw [fibPt, pullback.lift_fst, hρ, Category.assoc, m.cart.1.isoPullback_hom_fst]
    · rw [fibPt, pullback.lift_snd, Category.assoc, m.cart.1.isoPullback_hom_snd]
      exact (Over.w x).symm
  · rw [hρ, Over.comp_left, Over.comp_left, hρ, Category.assoc, m.act, Category.assoc]
  · rw [hρ, Over.comp_left, tu]; exact m.eta a
  · rw [hρ, Over.comp_left, tu]; exact m.etaA a

end GlobalTheory.HeckePoint

namespace GlobalTheory

open HeckePoint

theorem heckePoints_of_parts_comm :
    Out.Laws → (∀ (O : Type) [CommRing O] (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj
        G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (a : OAct O G) (a'
        : OAct O G'), IsGrpPullback G' G f φ → (∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act
        c).left) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S') (τ : O →+* k) (n
        : ℕ), LieMult a' x τ n ↔ LieMult a (x ≫ f) τ n) → (∀ (E : Type) [Field E] [NumberField
        E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing
        B] [CommRing B'] (b : Base l B) (b' : Base l B') (j : B →+* B') (S S' : Scheme.{0}) (s
        : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f
        : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap
        o' o f)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D
        : Datum H) (l : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b
        : Base l B) (b' : Base l B') (b'' : Base l B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s'
        : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (o : Obj D l b s) (o' : Obj D l b' s') (o''
        : Obj D l b'' s''), (∃ m : ObjMap o o (𝟙 S), m.toSABMap.φ = 𝟙 _) ∧ ∀ (f : S' ⟶ S) (f'
        : S'' ⟶ S') (m : ObjMap o' o f), (∀ m' : ObjMap o'' o' f', ∃ m'' : ObjMap o'' o (f' ≫
        f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) ∧ (∀ m'' : ObjMap o'' o (f' ≫
        f), ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ)) → (∀ (E
        : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B
        : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o
        : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 *
        (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → (∀ (E
        : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo
        : Moduli D l) (B : Type) [CommRing B] (b : Base l B) (j : KA l →+* B) (S : Scheme.{0}) (s
        : S ⟶ Sp B) (o : Obj D l b s), IsReduced S → j (baseKA l).ρ = b.ρ → j (baseKA
        l).ζ = b.ζ → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ
        f)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (𝔓
        : Ideal (𝓞 E)) (p : ℕ) (k : Type) [Field k] (Q Q' : Type) [CommGroup Q] [CommGroup Q'] (act
        : 𝓞 E → Q → Q) (act' : 𝓞 E → Q' → Q') (e : ℕ → Q → Q → kˣ → Prop) (e'
        : ℕ → Q' → Q' → kˣ → Prop) (I : TateIso D k Q act e) (ψ
        : Q →* Q'), 𝔓.IsMaximal → 𝔓 ⊔ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ → p.Prime → (p
        : 𝓞 E) ∈ 𝔓 → Function.Surjective ψ → (∀ a x, ψ (act a x) = act' a (ψ x)) → (∀ J : Ideal (𝓞
        E), J * 𝔓 = Ideal.span {(p
        : 𝓞 E)} → ∀ x, x ^ p = 1 → (∀ a ∈ J, act a x = 1) → ψ x = 1) → (∀ x, ψ x = 1 → x ^ p ^ 2 = 1 ∧ ∀ a ∈ Ideal.span {(p
        : 𝓞 E)} * 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E), act a x = 1) → (∀ x y, ψ x = 1 → ψ y = 1 → e (p ^
        2) x y 1) → Nat.card ψ.ker = p ^ (2 * (Module.finrank ℚ E / 2 * (D.p +
        D.q))) → (∀ n x y c c', 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e n x y c' → c = c') → (∀ n x y c, 0 < n → ψ x ^ n = 1 → ψ y ^ n = 1 → e (n
        * p ^ 2) x y c → e' n (ψ x) (ψ
        y) c) → ∃ I' : TateIso D k Q' act' e', I'.ζ = I.ζ ∧ ∀ n p' : ℕ, 0 < n → p * p' ≡ 1 [MOD
        n] → ∀ a, I'.ev n a = ψ (I.ev n (p' • a))) → (∀ (E : Type) [Field E] [NumberField
        E] [IsCMField E] (H : Host E) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (t
        : SAB H (Sp k)) (g p : ℕ) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶
        t.G)), 0 < p → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ x ∈ C, ∀ a, x ≫ t.act.act a ∈ C) → (∀ x ∈ C, x ^ p ^ 2 = 1) → (∀ x ∈ C, ∀ y ∈ C, Out.WeilIs t.G t.PP.L ((p
        ^ 2 : ℕ) : ℤ) x y 1) → Nat.card C = p ^ (2 * g) → ∃ (t' : SAB H (Sp k)) (ψ
        : t.G ⟶ t'.G), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ x : 𝟙_ (Over
        (Sp k)) ⟶ t.G, x ≫ ψ = 1 ↔ x ∈ C) ∧ (∀ a, t.act.act a ≫ ψ = ψ ≫ t'.act.act a) ∧ LBIso (lbPow
        t.PP.L (p ^ 2)) (t'.PP.L.pull ψ.left)) → (∀ (S : Scheme.{0}) (A B : Over S) [GrpObj
        A] [GrpObj B] (ψ : A ⟶ B) (L : LB A.left) (M : LB B.left) (d : ℕ) (n : ℤ) (T : Over S) (x y
        : T ⟶ A) (c c' : Γ(T.left,
        ⊤)ˣ), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → IsMonHom ψ → LBIso (lbPow L
        d) (M.pull ψ.left) → Out.WeilIs B M n (x ≫ ψ) (y ≫ ψ) c' → Out.WeilIs A L (n *
        d) x y c' ∧ (Out.WeilIs A L n x y c → c' = c ^ d)) → (∀ (O : Type) [CommRing O] (S
        : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (ψ : A ⟶ B) (a : OAct O A) (b
        : OAct O B), IsMonHom ψ → Etale ψ.left → (∀ c, a.act c ≫ ψ = ψ ≫ b.act c) → ∀ (k
        : Type) [Field k] (x : Sp k ⟶ S) (τ : O →+* k) (n
        : ℕ), LieMult a x τ n ↔ LieMult b x τ n) → (∀ (k : Type) [Field k] [IsAlgClosed k] (P P'
        : Out.PolAV (Sp k)) (α : P.A ⟶ P'.A) (p d : ℕ), IsMonHom α → p.Prime → CharZero k → (∀ (n
        : ℕ) (x y : 𝟙_ (Over (Sp k)) ⟶ P.A) (c
        : kˣ), 0 < n → n.Coprime p → x ^ n = 1 → y ^ n = 1 → Out.WeilIs P.A P.L n x y (unitOn
        c) → Out.WeilIs P'.A P'.L n (x ≫ α) (y ≫ α) (unitOn (c ^ d))) → LBIso (abelian₂ P.A (lbPow
        P.L d)) (abelian₂ P.A (P'.L.pull α.left))) → (∀ (k : Type) [Field k] [IsAlgClosed k] (P
        : Out.PolAV (Sp k)) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ P.A)), Finite C → ∃ (B : Over (Sp
        k)) (_ : GrpObj B) (ψ
        : P.A ⟶ B), IsAbelianScheme B ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ x : 𝟙_ (Over
        (Sp k)) ⟶ P.A, x ≫ ψ = 1 ↔ x ∈ C) ∧ ∀ (Y : Over (Sp k)) (f : P.A ⟶ Y), (∀ x ∈ C, ((toUnit
        P.A ≫ x) * 𝟙 P.A) ≫ f = f) → ∃! f' : B ⟶ Y, ψ ≫ f' = f) → ∀ (E : Type) [Field
        E] [NumberField E] [IsCMField E] (H : Host E) (D
        : Datum H), 1 ≤ D.p + D.q → ToroidalHeckeCompatibility (H := H) (D := D) := by
  intro hL _ hPull hComp hfacts _ hTate hQuot hWeil hLie hDet _ E _ _ _ H D _ l Xo 𝔓 p i h𝔓 hco hp hp𝔓 hpM k _ _ y C hC
  obtain ⟨c₁, c₂, c₃, c₄, c₅, -⟩ := hC
  have : CharZero k := charZero_of_injective_ringHom (Spec.preimage (y ≫ Xo.s)).hom.injective
  have pull : ∀ y' : Sp k ⟶ Xo.X, y' ≫ Xo.s = y ≫ Xo.s →
      ∃ o : Obj D l (baseKA l) (y ≫ Xo.s), Nonempty (ObjMap o Xo.univ y') := fun y' h =>
    hPull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (y ≫ Xo.s) y' rfl rfl
      (by rw [h, spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]) Xo.univ
  obtain ⟨o, ⟨m⟩⟩ := pull y rfl
  obtain ⟨ρ, e, e₁, e₂, e₃, e₄, e₅, e₆⟩ := exists_transfer_comm Xo.univ m
  let C' : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.t.G) := C.comap ρ.toMonoidHom
  have mem : ∀ x, x ∈ C' ↔ ρ x ∈ C := fun _ => Iff.rfl
  obtain ⟨hC', o₁, ψ₁, h₁, hfin, het, hsur⟩ := exists_isHeckeIsog hL hfacts hTate hQuot hWeil hLie o 𝔓 p h𝔓 hco hp
    hp𝔓 hpM C' (fun x hx a => (mem _).2 (by rw [e₃]; exact c₁ _ hx a))
    (fun J hJ x hx => c₂ J hJ fun a ha => (e₃ a x).symm.trans (by rw [hx a ha, map_one]))
    (fun x hx a ha => ρ.injective ((e₃ a x).trans ((c₃ hx a ha).trans (map_one ρ).symm)))
    (fun x hx x' hx' => by
      have := (e₄ ((p : ℤ) ^ 2) x x' 1).2
        ((congrArg (Out.WeilIs _ _ ((p : ℤ) ^ 2) (ρ x) (ρ x')) unitOn_one).mpr (c₄ _ hx _ hx'))
      rw [Nat.cast_pow]
      exact (congrArg (Out.WeilIs _ _ ((p : ℤ) ^ 2) x x') unitOn_one).mp this)
    ((Nat.card_congr (ρ.toEquiv.subtypeEquiv mem)).trans c₅)
  obtain ⟨y₁, ⟨hy₁, ⟨m₁⟩⟩, huniq⟩ := Xo.rep _ (y ≫ Xo.s) inferInstance o₁
  refine ⟨y₁, ⟨hy₁, ?_⟩, ?_⟩
  · obtain ⟨ρ₁, f, f₁, f₂, f₃, f₄, f₅, f₆⟩ := exists_transfer_comm Xo.univ m₁
    obtain ⟨hom₁, lin₁, sur₁, ker₁, weil₁, lev₁⟩ := h₁
    let σ : (𝟙_ (Over (Sp k)) ⟶ o.t.G) →* (𝟙_ (Over (Sp k)) ⟶ o₁.t.G) :=
      MonoidHom.mk' (fun z => z ≫ ψ₁) fun a c => MonObj.mul_comp a c ψ₁
    let ψp := ρ₁.toMonoidHom.comp (σ.comp ρ.symm.toMonoidHom)
    have hψ : ∀ x, ψp (ρ x) = ρ₁ (x ≫ ψ₁) := fun x => congrArg (fun z => ρ₁ (z ≫ ψ₁)) (ρ.symm_apply_apply x)
    refine ⟨e.inv ≫ ψ₁.left ≫ f.hom, ψp, ?_, fun x => ?_, fun a x => ?_, fun z => ?_, Subgroup.ext fun x => ?_,
      fun n x x' c hn h => ?_, fun p' hp' a => ?_⟩
    · rw [Category.assoc, Category.assoc, f₁, Over.w, Iso.inv_comp_eq, e₁]
    · obtain ⟨x, rfl⟩ := ρ.surjective x
      rw [hψ, e₂, f₂, Category.assoc, Iso.hom_inv_id_assoc, Over.comp_left, Category.assoc]
    · obtain ⟨x, rfl⟩ := ρ.surjective x
      rw [← e₃, hψ, hψ, ← f₃, Category.assoc, lin₁, Category.assoc]
    · obtain ⟨z, rfl⟩ := ρ₁.surjective z
      obtain ⟨x, rfl⟩ := sur₁ z
      exact ⟨ρ x, hψ x⟩
    · obtain ⟨x, rfl⟩ := ρ.surjective x
      rw [MonoidHom.mem_ker, hψ, map_eq_one_iff _ ρ₁.injective, ker₁, mem]
    · obtain ⟨x, rfl⟩ := ρ.surjective x
      obtain ⟨x', rfl⟩ := ρ.surjective x'
      rw [hψ, hψ]
      exact (f₄ _ _ _ _).1 (weil₁ n x x' c hn ((e₄ _ _ _ _).2 h))
    · rw [← e₅, ← e₆, hψ, hψ, (lev₁ p' hp' a).1, (lev₁ p' hp' a).2, f₅, f₆]
      exact ⟨rfl, rfl⟩
  · rintro y₂ ⟨hy₂, ψ, ψp, g₁, g₂, g₃, g₄, g₅, g₆, g₇⟩
    obtain ⟨o₂, ⟨m₂⟩⟩ := pull y₂ hy₂
    obtain ⟨ρ₂, f, f₁, f₂, f₃, f₄, f₅, f₆⟩ := exists_transfer_comm Xo.univ m₂
    let ψ₂ : o.t.G ⟶ o₂.t.G := Over.homMk (e.hom ≫ ψ ≫ f.inv) (by
      rw [← f₁, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, g₁, e₁])
    have hψ : ∀ x, ρ₂ (x ≫ ψ₂) = ψp (ρ x) := fun x => fibPt_injective _ (by
      rw [f₂, ← g₂, e₂]
      show (x.left ≫ e.hom ≫ ψ ≫ f.inv) ≫ f.hom = _
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
    have hab := isAbelianScheme_of_proper o.t o.proper
    have hab₂ := isAbelianScheme_of_proper o₂.t o₂.proper
    have := o₂.proper
    have one : ∀ (G : Over (Sp k)) [GrpObj G], (1 : 𝟙_ (Over (Sp k)) ⟶ G) = η[G] := fun G _ => by
      rw [Hom.one_def]; simp
    have h₂ : IsHeckeIsog o o₂ p C' ψ₂ := by
      refine ⟨hL.rigidity _ _ _ hab hab₂ ψ₂ ?_, fun a => hom_ext_pts hab.smooth fun x => ρ₂.injective ?_,
        fun z => ?_, fun x => ?_, fun n x x' c hn h => ?_, fun p' hp' a => ⟨ρ₂.injective ?_, ρ₂.injective ?_⟩⟩
      · rw [← one, ← one]
        exact ρ₂.injective (by rw [hψ, map_one, map_one, map_one])
      · rw [← Category.assoc, ← Category.assoc, hψ, f₃, hψ, e₃, g₃]
      · obtain ⟨x, hx⟩ := g₄ (ρ₂ z)
        obtain ⟨x, rfl⟩ := ρ.surjective x
        exact ⟨x, ρ₂.injective ((hψ x).trans hx)⟩
      · rw [mem, ← g₅, MonoidHom.mem_ker, ← hψ, map_eq_one_iff _ ρ₂.injective]
      · refine (f₄ _ _ _ _).2 ?_
        rw [hψ, hψ]
        exact g₆ n _ _ c hn ((e₄ _ _ _ _).1 h)
      · rw [hψ, e₅, f₅]; exact (g₇ p' hp' a).1
      · rw [hψ, e₆, f₆]; exact (g₇ p' hp' a).2
    obtain ⟨m'⟩ := objMap_of_isHeckeIsog hL hfacts hDet hp hpM hC' h₁ h₂
    obtain ⟨m'', -⟩ := ((hComp E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₂ o₁).2 y₂ (𝟙 _) m₂).1 m'
    rw [Category.id_comp] at m''
    exact huniq y₂ ⟨hy₂, ⟨m''⟩⟩

end GlobalTheory
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem heckePoints_of_laws :
    Out.Laws → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) →
      ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H),
        1 ≤ D.p + D.q → ToroidalHeckeCompatibility (H := H) (D := D) :=
  fun hL _ => heckePoints_of_parts_comm hL LiePull.lieMult_pull obj_pull ObjMaps.id_comp_cancel
    obj_isAbelianScheme_dim_rigidified_sym (moduli_rep_of_base ObjMaps.id_comp_cancel)
    (exists_tateIso_heckeQuotient SimAlg.sim_group) (exists_heckeQuotient_triple_of_laws hL)
    (weilIs_along_hom hL.globalFns) LieEtale.lieMult_iff_of_etale (lam_iso_of_weil_pairings hL)
    (exists_quotient_by_finite_group_of_points hL)

end GlobalTheory
