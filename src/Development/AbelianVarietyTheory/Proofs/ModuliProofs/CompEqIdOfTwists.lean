module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ThetaUnifAVOfLaws
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompEqIdOfTwists
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.Moduli.LevelAction

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem exists_inv_sabMap {S : Scheme.{0}} {t t' : SAB H S} (m : SABMap t' t (𝟙 S)) (i : SABMap t t (𝟙 S))
    (hi : i.φ = 𝟙 _) : ∃ k : SABMap t t' (𝟙 S), m.φ ≫ k.φ = 𝟙 _ := by
  have i' : {n : SABMap t t (𝟙 S ≫ 𝟙 S) // n.φ = 𝟙 _} := by
    rw [Category.comp_id]; exact ⟨i, hi⟩
  obtain ⟨k, hk⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m i'.1
  rw [i'.2] at hk
  refine ⟨k, ?_⟩
  haveI : IsIso m.φ := m.cart.1.isIso_fst_of_isIso
  rw [← cancel_mono m.φ, Category.assoc, ← hk, Category.comp_id, Category.id_comp]

theorem exists_comp_sabMap {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''}
    {f : S' ⟶ S} {g : S'' ⟶ S'} (m' : SABMap t'' t' g) (m : SABMap t' t f) {h : S'' ⟶ S} (e : g ≫ f = h) :
    ∃ n : SABMap t'' t h, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m'

section Add

variable {L Q : Type} [AddCommGroup L] [Group Q] {w : L → Q}

theorem map_zero_of_add (h : ∀ a c, w (a + c) = w a * w c) : w 0 = 1 := by
  have := h 0 0
  rw [add_zero] at this
  exact left_eq_mul.mp this

theorem map_nsmul_of_add (h : ∀ a c, w (a + c) = w a * w c) (n : ℕ) (a : L) : w (n • a) = w a ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, map_zero_of_add h]
  | succ n ih => rw [succ_nsmul, h, ih, pow_succ]

theorem map_eq_of_sub (h : ∀ a c, w (a + c) = w a * w c) {a c : L} (e : w (a - c) = 1) : w a = w c := by
  rw [← sub_add_cancel a c, h, e, _root_.one_mul]

end Add

theorem mem_of_modN (l : Level H) {x : D.La} (h : D.ModN l.M x) : x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  obtain ⟨b, rfl⟩ := h
  have h₁ : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.prod]; exact Ideal.mem_span_singleton_self _
  have h₂ : (l.M : 𝓞 E) ∈ l.Mb := by
    refine Submodule.mul_induction_on h₁ (fun x hx y _ => l.Mb.mul_mem_right y hx) fun x y hx hy => l.Mb.add_mem hx hy
  have h₃ : l.M • b = (l.M : 𝓞 E) • b := (Nat.cast_smul_eq_nsmul (𝓞 E) l.M b).symm
  rw [h₃]
  exact Submodule.smul_mem_smul h₂ Submodule.mem_top

section Obj

variable {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}

theorem eta_congr (o : Obj D l b s) {x y : D.La} (h : x - y ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) :
    o.eta x = o.eta y := map_eq_of_sub o.eta_add (o.eta_ker _ h)

theorem etaA_congr (o : Obj D l b s) {x y : D.La} (h : D.ModN l.A (x - y)) :
    o.etaA x = o.etaA y := by
  obtain ⟨c, hc⟩ := h
  exact map_eq_of_sub o.etaA_add (by rw [hc, o.etaA_ker])

end Obj

def Twists {l : Level H} (Xo : Moduli D l) (g : Sim D) (f : Xo.X ⟶ Xo.X) : Prop :=
  f ≫ Xo.s = Xo.s ∧ ∃ ν : SABMap Xo.univ.t Xo.univ.t f,
    (∀ a, (Xo.univ.eta (g.f l.M a)).left ≫ ν.φ = f ≫ (Xo.univ.eta a).left) ∧
    ∀ a, (Xo.univ.etaA (g.f l.A a)).left ≫ ν.φ = f ≫ (Xo.univ.etaA a).left

theorem exists_twists {l : Level H} (Xo : Moduli D l) (g : Sim D) (hred : IsReduced Xo.X)
    (i : SABMap Xo.univ.t Xo.univ.t (𝟙 _)) (hi : i.φ = 𝟙 _)
    (o' : Obj D l (baseKA l) Xo.s) (m : SABMap o'.t Xo.univ.t (𝟙 _))
    (h₁ : ∀ a, (o'.eta a).left ≫ m.φ = (Xo.univ.eta (g.f l.M a)).left)
    (h₂ : ∀ a, (o'.etaA a).left ≫ m.φ = (Xo.univ.etaA (g.f l.A a)).left) : ∃ f, Twists Xo g f := by
  obtain ⟨f, ⟨hf, ⟨n⟩⟩, -⟩ := Xo.rep _ Xo.s hred o'
  obtain ⟨k, hk⟩ := exists_inv_sabMap m i hi
  obtain ⟨ν, hν⟩ := exists_comp_sabMap k n.toSABMap (Category.id_comp f)
  refine ⟨f, hf, ν, fun a => ?_, fun a => ?_⟩
  · rw [hν, ← h₁, Category.assoc, ← Category.assoc m.φ, hk, Category.id_comp]; exact n.eta a
  · rw [hν, ← h₂, Category.assoc, ← Category.assoc m.φ, hk, Category.id_comp]; exact n.etaA a

theorem comp_eq_id_of_twists {l : Level H} (Xo : Moduli D l) {g g' : Sim D} (hred : IsReduced Xo.X)
    (i : ObjMap Xo.univ Xo.univ (𝟙 _)) {f f' : Xo.X ⟶ Xo.X} (h : Twists Xo g f) (h' : Twists Xo g' f')
    (hM : ∀ a, D.ModN l.M (g.f l.M (g'.f l.M a) - a)) (hA : ∀ a, D.ModN l.A (g.f l.A (g'.f l.A a) - a)) :
    f ≫ f' = 𝟙 _ := by
  obtain ⟨hf, ν, e₁, e₂⟩ := h
  obtain ⟨hf', ν', e₁', e₂'⟩ := h'
  obtain ⟨n, hn⟩ := exists_comp_sabMap ν ν' rfl
  refine (Xo.rep _ Xo.s hred Xo.univ).unique ⟨by rw [Category.assoc, hf', hf], ⟨⟨n, fun a => ?_, fun a => ?_⟩⟩⟩
    ⟨Category.id_comp _, ⟨i⟩⟩
  · show _ ≫ n.φ = _
    rw [hn, Category.assoc, ← e₁', ← Category.assoc, ← Category.assoc, ← e₁,
      eta_congr Xo.univ (mem_of_modN l (hM a))]
  · show _ ≫ n.φ = _
    rw [hn, Category.assoc, ← e₂', ← Category.assoc, ← Category.assoc, ← e₂, etaA_congr Xo.univ (hA a)]

theorem zeta_pow_div {A A₂ : ℕ} (hA : 0 < A₂) (h : A ∣ A₂) : zeta A₂ ^ (A₂ / A) = zeta A := by
  obtain ⟨d, rfl⟩ := h
  have hA' : 0 < A := Nat.pos_of_mul_pos_right hA
  have hd : 0 < d := Nat.pos_of_mul_pos_left hA
  rw [Nat.mul_div_cancel_left _ hA', zeta, zeta, ← Complex.exp_nat_mul]
  congr 1
  have : (A : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hA'.ne'
  have : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  push_cast
  field_simp

theorem modN_tower (g : Sim D) {n m : ℕ} (hm : 0 < m) (h : n ∣ m) (a : D.La) : D.ModN n (g.f m a - g.f n a) := by
  obtain ⟨d, rfl⟩ := h
  exact g.tower n d (Nat.pos_of_mul_pos_right hm) (Nat.pos_of_mul_pos_left hm) a

theorem sec_ext {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {x y : 𝟙_ (Over S') ⟶ t'.G} (h : x.left ≫ m.φ = y.left ≫ m.φ) : x = y :=
  Over.OverMorphism.ext (m.cart.1.hom_ext h (by rw [Over.w x, Over.w y]))

def lowerBase {l l₂ : Level H} (jK : KA l →+* KA l₂) : Base l (KA l₂) where
  unit := (baseKA l₂).unit
  ρ := (baseKA l₂).ρ
  ρ_sq := (baseKA l₂).ρ_sq
  ζ := jK (baseKA l).ζ
  ζ_prim := (baseKA l).ζ_prim.map_of_injective jK.injective

theorem lowerBase_zeta {l l₂ : Level H} (jK : KA l →+* KA l₂) (hl : l.A ∣ l₂.A)
    (hj : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) :
    (lowerBase jK).ζ = (baseKA l₂).ζ ^ (l₂.A / l.A) := by
  apply Subtype.ext
  have h₁ : (((lowerBase jK).ζ : KA l₂) : ℂ) = zeta l.A := hj (baseKA l).ζ
  have h₂ : (((baseKA l₂).ζ : KA l₂) : ℂ) = zeta l₂.A := rfl
  rw [h₁, SubmonoidClass.coe_pow, h₂, zeta_pow_div l₂.A_pos hl]

theorem lowerBase_rho {l l₂ : Level H} (jK : KA l →+* KA l₂)
    (hj : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) : jK (baseKA l).ρ = (lowerBase jK).ρ := by
  apply Subtype.ext
  have h₁ : (((lowerBase jK).ρ : KA l₂) : ℂ) = H.rt0 := rfl
  have h₂ : (((baseKA l).ρ : KA l) : ℂ) = H.rt0 := rfl
  rw [hj, h₁, h₂]

theorem similitude_acts : (∀ (k : Type) [Field k] (X : Scheme.{0}) (s : X ⟶ Sp k), Smooth s → IsReduced X ∧ IsNormalScheme X ∧ IsLocallyNoetherian X) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b' : Base l B') (b'' : Base l B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (o : Obj D l b s) (o' : Obj D l b' s') (o'' : Obj D l b'' s''), (∃ m : ObjMap o o (𝟙 S), m.toSABMap.φ = 𝟙 _) ∧ ∀ (f : S' ⟶ S) (f' : S'' ⟶ S') (m : ObjMap o' o f), (∀ m' : ObjMap o'' o' f', ∃ m'' : ObjMap o'' o (f' ≫ f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) ∧ (∀ m'' : ObjMap o'' o (f' ≫ f), ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B : Type) [CommRing B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o₂ : Obj D l₂ b₂ s), l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (o : Obj D l b s) (m : SABMap o₂.t o.t (𝟙 S)), (∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = 𝟙 S ≫ (o.eta a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = 𝟙 S ≫ (o.etaA a).left)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (B : Type) [CommRing B] (b : Base l B) (j : KA l →+* B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsReduced S → j (baseKA l).ρ = b.ρ → j (baseKA l).ζ = b.ζ → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ f)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s) (g : Sim D), 1 ≤ D.p + D.q → (l.A : ℤ) ∣ g.ν l.A - 1 → ∃ (o' : Obj D l b s) (m : SABMap o'.t o.t (𝟙 S)), (∀ a, (o'.eta a).left ≫ m.φ = (o.eta (g.f l.M a)).left) ∧ ∀ a, (o'.etaA a).left ≫ m.φ = (o.etaA (g.f l.A a)).left) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q → (∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ)) ∧ (∃ g : Sim D, ∀ n, g.f n = LinearMap.id ∧ g.ν n = 1) ∧ (∀ g g' : Sim D, ∃ g'' : Sim D, ∀ n, g''.f n = g.f n ∘ₗ g'.f n ∧ g''.ν n = g.ν n * g'.ν n) ∧ (∀ g : Sim D, ∃ g' : Sim D, ∀ n, 0 < n → (∀ a, D.ModN n (g'.f n (g.f n a) - a) ∧ D.ModN n (g.f n (g'.f n a) - a)) ∧ (n : ℤ) ∣ g.ν n * g'.ν n - 1)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) → ∀ g : Sim D, g.InGam l l₂ → ∃ ρ : Xo₂.X ≅ Xo₂.X, Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r := by
  intro hsm hcomp hlow hrep hsim halg E _ _ _ H D l l₂ Xo Xo₂ hpq hl r jK m ⟨hj, hr, hE, hEA⟩ g ⟨hν, hgM, hgA⟩
  have hred : IsReduced Xo₂.X := by
    haveI := Xo₂.smooth
    exact (hsm _ _ Xo₂.s (SmoothOfRelativeDimension.smooth D.dim _)).1
  have hM₂ : 0 < l₂.M := lt_of_lt_of_le (by norm_num) l₂.three_le
  obtain ⟨i, hi⟩ := (hcomp E H D l₂ _ _ _ _ _ _ _ _ _ _ _ _ Xo₂.univ Xo₂.univ Xo₂.univ).1
  obtain ⟨g', hg'⟩ := (halg E H D hpq).2.2.2 g
  have hν' : (l₂.A : ℤ) ∣ g'.ν l₂.A - 1 := by
    have h₁ := (hg' l₂.A l₂.A_pos).2
    have : g'.ν l₂.A - 1 = (g.ν l₂.A * g'.ν l₂.A - 1) - (g.ν l₂.A - 1) * g'.ν l₂.A := by ring
    rw [this]
    exact dvd_sub h₁ (hν.mul_right _)
  obtain ⟨o₁, m₁, a₁, b₁⟩ := hsim E H D l₂ _ _ _ _ Xo₂.univ g hpq hν
  obtain ⟨o₂, m₂, a₂, b₂⟩ := hsim E H D l₂ _ _ _ _ Xo₂.univ g' hpq hν'
  obtain ⟨f, hf⟩ := exists_twists Xo₂ g hred i.toSABMap hi o₁ m₁ a₁ b₁
  obtain ⟨f', hf'⟩ := exists_twists Xo₂ g' hred i.toSABMap hi o₂ m₂ a₂ b₂
  refine ⟨⟨f, f', comp_eq_id_of_twists Xo₂ hred i hf hf' (fun a => ((hg' _ hM₂).1 a).2)
      (fun a => ((hg' _ l₂.A_pos).1 a).2),
    comp_eq_id_of_twists Xo₂ hred i hf' hf (fun a => ((hg' _ hM₂).1 a).1)
      (fun a => ((hg' _ l₂.A_pos).1 a).1)⟩, hf, ?_⟩
  show f ≫ r = r
  obtain ⟨hfs, ν, e₁, e₂⟩ := hf
  have hζ := lowerBase_zeta jK hl.2.2 hj
  obtain ⟨o, k, c₁, c₂⟩ := hlow E H D l l₂ _ (lowerBase jK) (baseKA l₂) _ _ Xo₂.univ hl rfl hζ
  obtain ⟨id₀, hid₀⟩ := (hcomp E H D l _ _ _ _ _ _ _ _ _ _ _ _ o o o).1
  obtain ⟨k', hk'⟩ := exists_inv_sabMap k id₀.toSABMap hid₀
  have d₁ : ∀ a, (o.eta a).left ≫ k'.φ = (Xo₂.univ.eta a ^ (l₂.M / l.M)).left := fun a => by
    rw [← (c₁ a).trans (Category.id_comp _), Category.assoc, hk', Category.comp_id]
  have d₂ : ∀ a, (o.etaA a).left ≫ k'.φ = (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left := fun a => by
    rw [← (c₂ a).trans (Category.id_comp _), Category.assoc, hk', Category.comp_id]
  obtain ⟨n, hn⟩ := exists_comp_sabMap k' m (Category.id_comp r)
  obtain ⟨n₀, hn₀⟩ := exists_comp_sabMap k' ν (Category.id_comp f)
  obtain ⟨n', hn'⟩ := exists_comp_sabMap n₀ m rfl
  have t₁ : ∀ a, Xo₂.univ.eta a ^ (l₂.M / l.M) = Xo₂.univ.eta (g.f l₂.M ((l₂.M / l.M) • a)) := fun a => by
    rw [map_nsmul, map_nsmul_of_add Xo₂.univ.eta_add]
    apply sec_ext m
    rw [hE, hE, eta_congr Xo.univ (mem_of_modN l (modN_tower g hM₂ hl.1 a)), eta_congr Xo.univ (hgM a)]
  have t₂ : ∀ a, Xo₂.univ.etaA a ^ (l₂.A / l.A) = Xo₂.univ.etaA (g.f l₂.A ((l₂.A / l.A) • a)) := fun a => by
    rw [map_nsmul, map_nsmul_of_add Xo₂.univ.etaA_add]
    apply sec_ext m
    rw [hEA, hEA, etaA_congr Xo.univ (modN_tower g l₂.A_pos hl.2.2 a), etaA_congr Xo.univ (hgA a)]
  refine (hrep E H D l Xo _ (lowerBase jK) jK _ _ o hred (lowerBase_rho jK hj) rfl).unique
    ⟨by rw [Category.assoc, hr, ← Category.assoc, hfs], ⟨⟨n', fun a => ?_, fun a => ?_⟩⟩⟩
    ⟨hr, ⟨⟨n, fun a => ?_, fun a => ?_⟩⟩⟩
  · show _ ≫ n'.φ = _
    rw [hn', hn₀, ← Category.assoc, ← Category.assoc, d₁, t₁, e₁, map_nsmul_of_add Xo₂.univ.eta_add,
      Category.assoc, hE, Category.assoc]
  · show _ ≫ n'.φ = _
    rw [hn', hn₀, ← Category.assoc, ← Category.assoc, d₂, t₂, e₂, map_nsmul_of_add Xo₂.univ.etaA_add,
      Category.assoc, hEA, Category.assoc]
  · show _ ≫ n.φ = _
    rw [hn, ← Category.assoc, d₁, hE]
  · show _ ≫ n.φ = _
    rw [hn, ← Category.assoc, d₂, hEA]

end GlobalTheory.Moduli.LevelAction
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionPointsFieldExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionPointsFieldExtension
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TorsionFieldExt

variable {S : Scheme.{0}}

theorem comp_injective {K Ω : Type} [Field K] [Field Ω] {x : Sp K ⟶ S} {x' : Sp Ω ⟶ S}
    (u : Over.mk x' ⟶ Over.mk x) (A : Over S) : Function.Injective (fun y : Over.mk x ⟶ A => u ≫ y) := by
  let v : Sp Ω ⟶ Sp K := u.left
  have : Surjective v := ⟨fun z => ⟨(default : PrimeSpectrum Ω), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  have : Epi v := Flat.epi_of_flat_of_surjective v
  intro a b h
  have h' : v ≫ a.left = v ≫ b.left := congrArg (fun q => q.left) h
  exact Over.OverMorphism.ext ((cancel_epi v).1 h')

theorem card_torsion (hL : Out.Laws) (P : Out.PolAV S) {K : Type} [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) {n : ℕ}
    (hn : (n : K) ≠ 0) : Nat.card {y : Over.mk x ⟶ P.A // y ^ n = 1} = n ^ (2 * P.g) := by
  have hn' : 1 ≤ n := Nat.pos_of_ne_zero (by rintro rfl; exact hn Nat.cast_zero)
  obtain ⟨P', g, hg, hdim, hmul, -⟩ := hL.polBaseChange S _ x P
  have c := (hL.mulN _ P' n hn').2.2.2.2 K (𝟙 _) hn
  let Φ : (Over.mk (𝟙 (Sp K)) ⟶ P'.A) →* (Over.mk (𝟙 _ ≫ x) ⟶ P.A) :=
    MonoidHom.mk' (fun y => Out.toBase hg.w y) (hmul _)
  have hΦ : Function.Bijective Φ :=
    ⟨fun a b e => Over.OverMorphism.ext
      (hg.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun z =>
      ⟨Over.homMk (hg.lift z.left (𝟙 _) (Over.w z)) (hg.lift_snd _ _ _), Over.OverMorphism.ext (hg.lift_fst _ _ _)⟩⟩
  have e : Nat.card {y : Over.mk (𝟙 (Sp K)) ⟶ P'.A // y ^ n = 1} =
      Nat.card {y : Over.mk (𝟙 _ ≫ x) ⟶ P.A // y ^ n = 1} :=
    Nat.card_congr ((Equiv.ofBijective Φ hΦ).subtypeEquiv fun y => by
      show _ ↔ Φ y ^ n = 1
      rw [← map_pow, map_eq_one_iff Φ hΦ.1])
  rw [Category.id_comp] at e
  rw [← e, ← hdim]
  exact c

theorem exists_of_isAlgClosed (hL : Out.Laws) (P : Out.PolAV S) {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed K]
    [IsAlgClosed Ω] {x : Sp K ⟶ S} {x' : Sp Ω ⟶ S} (u : Over.mk x' ⟶ Over.mk x) {n : ℕ} (hK : (n : K) ≠ 0)
    (hΩ : (n : Ω) ≠ 0) (z : Over.mk x' ⟶ P.A) (hz : z ^ n = 1) :
    ∃ y : Over.mk x ⟶ P.A, y ^ n = 1 ∧ u ≫ y = z := by
  have hn' : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact hK Nat.cast_zero)
  have c₁ := card_torsion hL P x hK
  have c₂ := card_torsion hL P x' hΩ
  have : Finite {y : Over.mk x' ⟶ P.A // y ^ n = 1} := Nat.finite_of_card_ne_zero (by rw [c₂]; positivity)
  let F : {y : Over.mk x ⟶ P.A // y ^ n = 1} → {y : Over.mk x' ⟶ P.A // y ^ n = 1} := fun a =>
    ⟨u ≫ a.1, by rw [← MonObj.comp_pow, a.2, MonObj.comp_one]⟩
  have hF : Function.Bijective F := (Nat.bijective_iff_injective_and_card F).2
    ⟨fun a b h => Subtype.ext (comp_injective u _ (congrArg Subtype.val h)), c₁.trans c₂.symm⟩
  obtain ⟨a, ha⟩ := hF.2 ⟨z, hz⟩
  exact ⟨a.1, a.2, congrArg Subtype.val ha⟩

end GlobalTheory.TorsionFieldExt

namespace GlobalTheory

open TorsionFieldExt in
theorem torsion_points_field_extension : Out.Laws → ∀ (S : Scheme.{0}) (P : Out.PolAV S) (K Ω : Type) [Field K] [Field Ω] [IsAlgClosed K] (i : K →+* Ω) (x : Sp K ⟶ S), Function.Injective (fun y : Over.mk x ⟶ P.A => (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y) ∧ ∀ (n : ℕ) (z : Over.mk (spMap i ≫ x) ⟶ P.A), (n : K) ≠ 0 → z ^ n = 1 → ∃ y : Over.mk x ⟶ P.A, y ^ n = 1 ∧ (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y = z := by
  intro hL S P K Ω _ _ _ i x
  refine ⟨comp_injective _ _, fun n z hn hz => ?_⟩
  let j : Ω →+* AlgebraicClosure Ω := algebraMap _ _
  let v : Over.mk (spMap j ≫ spMap i ≫ x) ⟶ Over.mk (spMap i ≫ x) := Over.homMk (spMap j) rfl
  have hn' : (n : AlgebraicClosure Ω) ≠ 0 := by
    rw [← map_natCast (j.comp i)]
    exact (map_ne_zero _).2 hn
  obtain ⟨y, hy, e⟩ := exists_of_isAlgClosed hL P
    (v ≫ (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x)) hn hn' (v ≫ z)
    (by rw [← MonObj.comp_pow, hz, MonObj.comp_one])
  exact ⟨y, hy, comp_injective v _ ((Category.assoc _ _ _).symm.trans e)⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionPointsFieldExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.torsion_points_descend_field_extension : Out.Laws → ∀ (S : Scheme.{0}) (P : Out.PolAV S) (K Ω : Type) [Field K] [Field Ω] [IsAlgClosed K] (i : K →+* Ω) (x : Sp K ⟶ S), Function.Injective (fun y : Over.mk x ⟶ P.A => (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y) ∧ ∀ (n : ℕ) (z : Over.mk (spMap i ≫ x) ⟶ P.A), (n : K) ≠ 0 → z ^ n = 1 → ∃ y : Over.mk x ⟶ P.A, y ^ n = 1 ∧ (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y = z := by
  first | exact @GlobalTheory.torsion_points_field_extension | exact GlobalTheory.torsion_points_field_extension | (intros; apply GlobalTheory.torsion_points_field_extension <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TwoMulEqOfIsTypeFn
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

namespace GlobalTheory.PeriodDatum

noncomputable section

lemma lattice_equiv {La : Type} [AddCommGroup La] {g : ℕ} (P : La →+ (Fin g → ℂ)) (hinj : Function.Injective P)
    (hdisc : DiscreteTopology P.range) (hspan : Submodule.span ℝ (Set.range P) = ⊤) :
    Module.Finite ℤ La ∧ Module.finrank ℤ La = 2 * g ∧
      ∃ e : ℝ ⊗[ℤ] La ≃ₗ[ℝ] (Fin g → ℂ), ∀ x, e (1 ⊗ₜ x) = P x := by
  let L : Submodule ℤ (Fin g → ℂ) := LinearMap.range P.toIntLinearMap
  haveI : DiscreteTopology L := hdisc
  haveI : IsZLattice ℝ L := ⟨hspan⟩
  let f : La ≃ₗ[ℤ] L := LinearEquiv.ofInjective P.toIntLinearMap hinj
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  haveI : Module.Free ℤ L := ZLattice.module_free ℝ L
  haveI : Module.Finite ℤ La := Module.Finite.equiv f.symm
  haveI : Module.Free ℤ La := Module.Free.of_equiv f.symm
  have hr : Module.finrank ℤ La = Module.finrank ℝ (Fin g → ℂ) := by
    rw [f.finrank_eq, ZLattice.rank ℝ L]
  have hg : Module.finrank ℝ (Fin g → ℂ) = 2 * g := by
    rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, Module.finrank_fin_fun]
  let φ : ℝ ⊗[ℤ] La →ₗ[ℝ] (Fin g → ℂ) := P.toIntLinearMap.liftBaseChange ℝ
  have hφ : ∀ x, φ (1 ⊗ₜ x) = P x := fun x => by simp [φ]
  have hs : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨_, hφ x⟩
  have hd : Module.finrank ℝ (ℝ ⊗[ℤ] La) = Module.finrank ℝ (Fin g → ℂ) := by
    rw [Module.finrank_baseChange, hr]
  exact ⟨inferInstance, hr.trans hg, LinearEquiv.ofBijective φ
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).2 hs, hs⟩, hφ⟩

lemma hermForm_smul_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm (c • z) w = c * hermForm Hm z w := by
  simp [hermForm]

lemma hermForm_smul_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm z (c • w) = starRingEnd ℂ c * hermForm Hm z w := by
  simp [hermForm, Matrix.mulVec_smul]

lemma hermForm_add_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  simp [hermForm]

lemma hermForm_add_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  simp [hermForm, Matrix.mulVec_add]

lemma hermForm_self_im {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (z : Fin g → ℂ) :
    (hermForm Hm z z).im = 0 := by
  have := h.im_star_dotProduct_mulVec_self (star z)
  simpa [hermForm] using this

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma two_mul_eq_of_isTypeFn (H : Host E) {p q g : ℕ} {ty : Fin g → (E →+* ℂ)} (hty : IsTypeFn H p q ty) :
    2 * g = Module.finrank ℚ E * (p + q) := by
  classical
  let e := (Fintype.equivFin (E →+* ℂ)).symm
  have he : IsTypeFn H 1 1 e := fun τ => by
    have : Nat.card {i // e i = τ} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext (e.injective (a.2.trans b.2.symm))⟩, ⟨⟨e.symm τ, by simp⟩⟩⟩
    exact ⟨fun _ => this, fun _ => this⟩
  have h1 := PeriodNonempty.sum_type H hty 1
  have h2 := PeriodNonempty.sum_type H he 1
  simp only [map_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    Embeddings.card, Nat.cast_one] at h1 h2
  have : (2 * g : ℂ) = Module.finrank ℚ E * (p + q) := by rw [h1, h2]; ring
  exact_mod_cast this

theorem exists_datum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (La : Type)
    [AddCommGroup La] [Module (𝓞 E) La] (EF : LinearMap.BilinForm ℤ La) (p q g : ℕ) (ty : Fin g → (E →+* ℂ))
    (P : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), IsTypeFn H p q ty → Function.Bijective EF →
    (∀ (a : 𝓞 E) x y, EF (a • x) y = EF x (H.bar a • y)) →
    (∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i) → Function.Injective P → DiscreteTopology P.range →
    Submodule.span ℝ (Set.range P) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ x y, (hermForm Hm (P x) (P y)).im = EF x y) →
    ∃ (D' : Datum H) (e : D'.La ≃ₗ[𝓞 E] La), D'.p = p ∧ D'.q = q ∧ ∀ x y, D'.EF x y = EF (e x) (e y) := by
  intro E _ _ _ H La _ _ EF p q g ty P Hm hty hbij hadj hlin hinj hdisc hspan hH hpos him
  classical
  obtain ⟨hfin, hrk, e, he⟩ := lattice_equiv P hinj hdisc hspan
  haveI : Module.Finite (𝓞 E) La := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) La
  have htor : Submodule.torsion (𝓞 E) La = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨a, ha⟩, hx⟩
    have ha0 : (a : E) ≠ 0 := by
      simpa using nonZeroDivisors.ne_zero ha
    rw [Submodule.mem_bot]
    apply hinj
    funext i
    have h1 := hlin a x i
    have h2 : a • x = 0 := hx
    rw [h2, map_zero] at h1
    rw [map_zero]
    exact (mul_eq_zero.1 h1.symm).resolve_left ((map_ne_zero (ty i)).2 ha0)
  haveI : Module.Flat (𝓞 E) La := IsDedekindDomain.flat_iff_torsion_eq_bot.2 htor
  haveI : Module.FinitePresentation (𝓞 E) La := Module.finitePresentation_of_finite _ _
  have hproj : Module.Projective (𝓞 E) La := Module.Flat.projective_of_finitePresentation
  have hrank : Module.finrank (𝓞 E) La = p + q := by
    have h1 := finrank_int_eq_mul_of_finite (O := 𝓞 E) (M := La)
    rw [hrk, two_mul_eq_of_isTypeFn H hty, RingOfIntegers.rank] at h1
    exact (Nat.eq_of_mul_eq_mul_left Module.finrank_pos h1).symm
  have het : ∀ (r : ℝ) x, e (r ⊗ₜ x) = (r : ℂ) • P x := fun r x => by
    rw [← he, Complex.coe_smul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hB : ∀ x y, EF.baseChange ℝ x y = (hermForm Hm (e x) (e y)).im := fun x y => by
    induction x using TensorProduct.induction_on with
    | zero => simp [hermForm]
    | add x x' h h' => simp only [map_add (f := _), LinearMap.add_apply, h, h', hermForm_add_left, Complex.add_im]
    | tmul r x =>
      induction y using TensorProduct.induction_on with
      | zero => simp [hermForm]
      | add y y' h h' => simp only [map_add (f := _), h, h', hermForm_add_right, Complex.add_im]
      | tmul r' y =>
        rw [het, het, hermForm_smul_left, hermForm_smul_right, LinearMap.BilinForm.baseChange_tmul]
        simp [him]
        ring
  let d : (Fin g → ℂ) → Module.End ℂ (Fin g → ℂ) := fun c => Matrix.toLin' (Matrix.diagonal c)
  have hd : ∀ c z i, d c z i = c i * z i := fun c z i => by simp [d, Matrix.mulVec_diagonal]
  have hdt : ∀ c, LinearMap.trace ℝ _ (e.symm.conj ((d c).restrictScalars ℝ)) = 2 * (∑ i, c i).re := fun c => by
    rw [LinearMap.trace_conj', PeriodNonempty.trace_real]
    simp [d]
  let J : ℝ ⊗[ℤ] La →ₗ[ℝ] ℝ ⊗[ℤ] La := e.symm.conj ((d fun _ => Complex.I).restrictScalars ℝ)
  have hJ : ∀ x, e (J x) = Complex.I • e x := fun x => by
    funext i
    simp [J, LinearEquiv.conj_apply, hd]
  refine ⟨{ La := La, fin := inferInstance, proj := hproj, EF := EF, alt := fun x => ?_, unimod := hbij,
            adj := hadj, p := p, q := q, rank := hrank, dom := ⟨J, fun x => ?_, fun x y => ?_, fun x hx => ?_, ?_⟩ },
    LinearEquiv.refl _ _, rfl, rfl, fun _ _ => rfl⟩
  · have := him x x
    rw [hermForm_self_im hH] at this
    exact_mod_cast this.symm
  · apply e.injective
    rw [hJ, hJ, smul_smul, Complex.I_mul_I, map_neg, neg_smul, one_smul]
  · rw [hB, hB, hJ, hJ, hermForm_smul_left, hermForm_smul_right]
    simp
  · rw [hB, hJ, hermForm_smul_left]
    simpa using hpos (e x) (by simpa using hx)
  · intro a A t hA ht
    rw [← PeriodNonempty.sum_type H hty] at ht
    have hAe : ∀ x i, e (A x) i = ty i (a : E) * e x i := fun x i => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x x' h h' => simp only [map_add (f := _), Pi.add_apply, h, h', mul_add]
      | tmul r x =>
        have : (r ⊗ₜ[ℤ] x : ℝ ⊗[ℤ] La) = r • (1 ⊗ₜ[ℤ] x) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this, map_smul, hA, map_smul, map_smul, he, he]
        simp only [Pi.smul_apply, hlin, Complex.real_smul]
        ring
    have h1 : A = e.symm.conj ((d fun i => ty i (a : E)).restrictScalars ℝ) := by
      refine LinearMap.ext fun x => e.injective (funext fun i => ?_)
      simp [LinearEquiv.conj_apply, hd, hAe]
    have h2 : J ∘ₗ A = e.symm.conj ((d fun i => Complex.I * ty i (a : E)).restrictScalars ℝ) := by
      refine LinearMap.ext fun x => e.injective (funext fun i => ?_)
      simp [LinearEquiv.conj_apply, hd, hAe, hJ, mul_assoc]
    refine ⟨?_, ?_, ?_⟩
    · refine LinearMap.ext fun x => e.injective (funext fun i => ?_)
      simp only [LinearMap.comp_apply, hJ, hAe, Pi.smul_apply, smul_eq_mul]
      ring
    · rw [h1, hdt, ht]
    · rw [h2, hdt, ht, ← Finset.mul_sum]
      simp

end

end GlobalTheory.PeriodDatum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TateIsoDifferBySimilitude
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {k : Type} [Field k]
  {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem _root_.GlobalTheory.tateIso_ev_eq_iff (I : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso D k Q act e) {n : ℕ} (hn : 0 < n) (a b : D.La) :
    I.ev n a = I.ev n b ↔ D.ModN n (a - b) := by
  have key : I.ev n (a - b) * I.ev n b = I.ev n a := by rw [← I.add, sub_add_cancel]
  rw [show D.ModN n (a - b) ↔ ∃ c, a - b = n • c from Iff.rfl, ← I.ker n hn, ← key]
  exact mul_eq_right

theorem _root_.GlobalTheory.tateIso_ev_pow (I : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso D k Q act e) {n : ℕ} (hn : 0 < n) (a : D.La) :
    I.ev n a ^ n = 1 :=
  (I.onto n hn _).mpr ⟨a, rfl⟩

end

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} in
private lemma exists_linearMap_ev_eq_of_tateIso (I I' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso D k Q act e) {n : ℕ} (hn : 0 < n) :
    ∃ f : D.La →ₗ[𝓞 E] D.La, ∀ a, I.ev n (f a) = I'.ev n a := by
  classical
  haveI := D.proj
  let N : Submodule (𝓞 E) D.La := LinearMap.range ((n : 𝓞 E) • LinearMap.id)
  have hN : ∀ x, x ∈ N ↔ D.ModN n x := by
    intro x
    show (∃ y, (n : 𝓞 E) • y = x) ↔ ∃ y, x = n • y
    simp only [Nat.cast_smul_eq_nsmul]
    constructor <;> rintro ⟨y, hy⟩ <;> exact ⟨y, hy.symm⟩
  have hrel : ∀ x y, I.ev n x = I.ev n y ↔ x - y ∈ N := fun x y =>
    (_root_.GlobalTheory.tateIso_ev_eq_iff I hn x y).trans (hN _).symm
  have hs : ∀ a, ∃ b, I.ev n b = I'.ev n a :=
    fun a => (I.onto n hn _).mp (_root_.GlobalTheory.tateIso_ev_pow I' hn a)
  choose s hs using hs
  let g : D.La →ₗ[𝓞 E] D.La ⧸ N :=
    { toFun := fun a => N.mkQ (s a)
      map_add' := fun a b => by
        rw [← map_add (f := _), Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← hrel,
          I.add, hs, hs, hs, I'.add]
      map_smul' := fun c a => by
        rw [RingHom.id_apply, ← map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply,
          Submodule.Quotient.eq, ← hrel, I.lin, hs, hs, I'.lin] }
  obtain ⟨f, hf⟩ := Module.projective_lifting_property N.mkQ g (Submodule.mkQ_surjective N)
  refine ⟨f, fun a => ?_⟩
  have h1 : N.mkQ (f a) = N.mkQ (s a) := LinearMap.congr_fun hf a
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← hrel] at h1
  rw [h1, hs]

theorem _root_.GlobalTheory.tateIso_differ_by_similitude :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop), (∀ n x y c c', 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e n x y c' → c = c') → ∀ I I' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso D k Q act e, ∃ g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sim D, ∀ n, 0 < n → (∀ a, I'.ev n a = I.ev n (g.f n a)) ∧ I'.ζ n = I.ζ n ^ g.ν n := by
  intro E _ _ _ H D k _ Q _ act e he I I'
  have hf : ∀ n, ∃ f : D.La →ₗ[𝓞 E] D.La, 0 < n → ∀ a, I.ev n (f a) = I'.ev n a := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, fun h => absurd h (lt_irrefl 0)⟩
    · obtain ⟨f, hf⟩ := exists_linearMap_ev_eq_of_tateIso I I' hn
      exact ⟨f, fun _ => hf⟩
  choose f hf using hf
  have hk : ∀ n, ∃ ν : ℤ, 0 < n → I'.ζ n = I.ζ n ^ ν := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, fun h => absurd h (lt_irrefl 0)⟩
    · haveI : NeZero n := ⟨hn.ne'⟩
      have hprim : IsPrimitiveRoot ((I.ζ n : kˣ) : k) n :=
        IsPrimitiveRoot.coe_units_iff.mpr (I.ζ_prim n hn)
      have hpow : ((I'.ζ n : kˣ) : k) ^ n = 1 := by
        rw [← Units.val_pow_eq_pow_val, (I'.ζ_prim n hn).pow_eq_one, Units.val_one]
      obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hpow
      refine ⟨i, fun _ => ?_⟩
      ext
      rw [zpow_natCast, Units.val_pow_eq_pow_val, hi]
  choose ν hν using hk
  refine ⟨⟨f, ν, ?_, ?_, ?_⟩, fun n hn => ⟨fun a => (hf n hn a).symm, hν n hn⟩⟩
  · intro n m hn hm a
    rw [← _root_.GlobalTheory.tateIso_ev_eq_iff I hn, ← I.tower n m hn hm, hf (n * m) (Nat.mul_pos hn hm),
      hf n hn, I'.tower n m hn hm]
  · intro n hn
    obtain ⟨g, hg⟩ := exists_linearMap_ev_eq_of_tateIso I' I hn
    refine ⟨g, fun a => ⟨?_, ?_⟩⟩
    · rw [← _root_.GlobalTheory.tateIso_ev_eq_iff I' hn, hg, hf n hn]
    · rw [← _root_.GlobalTheory.tateIso_ev_eq_iff I hn, hf n hn, hg]
  · intro n hn a b
    have h1 := I.isom n hn (f n a) (f n b)
    have h2 := I'.isom n hn a b
    rw [hf n hn, hf n hn] at h1
    have hc := he n _ _ _ _ hn (_root_.GlobalTheory.tateIso_ev_pow I' hn a)
      (_root_.GlobalTheory.tateIso_ev_pow I' hn b) h1 h2
    rw [hν n hn, ← zpow_mul] at hc
    rw [← (I.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, hc, mul_inv_cancel]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLieBasisOfHolUnif
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding IsTan JetR
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.UnifLieBasis

open TangentOrigin
open ReciprocityTheory.ChartRestriction.G.Chart (JetR jetAug qD rD scaleD IsTan isTan_iff prodPts isLieComb_iff)

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem spMap_jetAug_surjective :
    Function.Surjective (spMap (jetAug ℂ (Fin 2) 1).toRingHom) := by
  intro q
  have : q ∈ Set.range (PrimeSpectrum.comap (jetAug ℂ (Fin 2) 1).toRingHom) := by
    rw [range_comap_of_surjective _ _ (fun a => ⟨algebraMap ℂ _ a, (jetAug ℂ (Fin 2) 1).commutes a⟩)]
    intro b hb
    refine q.2.mem_of_pow_mem (1 + 1) ?_
    have h := Ideal.pow_mem_pow (I := RingHom.ker (jetAug ℂ (Fin 2) 1)) hb (1 + 1)
    rw [Chart.ker_jetAug_pow, Ideal.mem_bot] at h
    rw [h]
    exact zero_mem _
  exact this

omit u in
theorem snd_evalPt_mul {v v' : epsR ℂ ⟶ A} (hv : IsTan (R := ℂ) (G := A) v) (hv' : IsTan (R := ℂ) (G := A) v')
    (U : A.left.Opens) (h0 : ⊤ ≤ (1 : Chart.sp (R₀ := ℂ) ℂ ⟶ A).left ⁻¹ᵁ U)
    (h : ⊤ ≤ v.left ⁻¹ᵁ U) (h' : ⊤ ≤ v'.left ⁻¹ᵁ U) (h'' : ⊤ ≤ (v * v').left ⁻¹ᵁ U) (f : Γ(A.left, U)) :
    (evalPt (R := DualNumber ℂ) (v * v').left U h'' f).snd =
      (evalPt (R := DualNumber ℂ) v.left U h f).snd + (evalPt (R := DualNumber ℂ) v'.left U h' f).snd := by
  let P : Chart.sp (R₀ := ℂ) (JetR ℂ (Fin 2) 1) ⟶ A := (Chart.spMap (qD 0) ≫ v) * (Chart.spMap (qD 1) ≫ v')
  have hP : Chart.spMap (jetAug ℂ (Fin 2) 1) ≫ P = 1 := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, Chart.spMap_comp, Chart.spMap_comp,
      Chart.jetAug_comp_qD, Chart.jetAug_comp_qD, hv, hv', _root_.mul_one]
  have hPU : ⊤ ≤ P.left ⁻¹ᵁ U := fun p _ => by
    obtain ⟨q, rfl⟩ := spMap_jetAug_surjective p
    rw [← hP] at h0
    exact h0 (Set.mem_univ q)
  have hval : ∀ l : ℂ × ℂ →ₗ[ℂ] ℂ, Chart.spMap (rD l) ≫ P =
      (Chart.spMap (scaleD (l ((1 : ℂ), (0 : ℂ)))) ≫ v) * (Chart.spMap (scaleD (l ((0 : ℂ), (1 : ℂ)))) ≫ v') := by
    intro l
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, Chart.spMap_comp, Chart.spMap_comp,
      Chart.restrictDiag_comp_incl_fst, Chart.restrictDiag_comp_incl_snd]
  have key : ∀ (l : ℂ × ℂ →ₗ[ℂ] ℂ) (w : epsR ℂ ⟶ A) (hw : ⊤ ≤ w.left ⁻¹ᵁ U), Chart.spMap (rD l) ≫ P = w →
      evalPt (R := DualNumber ℂ) w.left U hw f = rD l (evalPt (R := JetR ℂ (Fin 2) 1) P.left U hPU f) := by
    rintro l w hw rfl
    exact evalPt_spMap_comp (rD l : JetR ℂ (Fin 2) 1 →+* DualNumber ℂ) P.left U hPU hw f
  rw [key (LinearMap.fst ℂ ℂ ℂ) v h, key (LinearMap.snd ℂ ℂ ℂ) v' h',
    key (LinearMap.fst ℂ ℂ ℂ + LinearMap.snd ℂ ℂ ℂ) (v * v') h'', Chart.snd_rD_add]
  · rw [hval]
    simp only [LinearMap.add_apply, LinearMap.fst_apply, LinearMap.snd_apply, add_zero, zero_add]
    rw [Chart.scaleD_one, Chart.spMap_id, Category.id_comp, Category.id_comp]
  · rw [hval]
    simp only [LinearMap.fst_apply, LinearMap.snd_apply]
    rw [Chart.scaleD_one, Chart.spMap_id, Category.id_comp, Chart.spMap_scaleD_zero hv, _root_.one_mul]
  · rw [hval]
    simp only [LinearMap.fst_apply, LinearMap.snd_apply]
    rw [Chart.scaleD_one, Chart.spMap_id, Category.id_comp, Chart.spMap_scaleD_zero hv', _root_.mul_one]

theorem isDiff_add {w w' : Fin g → ℂ} {v v' : epsR ℂ ⟶ A} (hv : IsTan (R := ℂ) (G := A) v)
    (hv' : IsTan (R := ℂ) (G := A) v') (hd : u.IsDiff w v) (hd' : u.IsDiff w' v') : u.IsDiff (w + w') (v * v') := by
  intro U h'' f
  have ht := Chart.isTan_mul hv hv'
  have h0 := (tangent_mem_iff (u := u) ((isTan_iff _).1 ht) U).1 h''
  have h := (tangent_mem_iff (u := u) ((isTan_iff _).1 hv) U).2 h0
  have h' := (tangent_mem_iff (u := u) ((isTan_iff _).1 hv') U).2 h0
  have h1 : ⊤ ≤ (1 : Chart.sp (R₀ := ℂ) ℂ ⟶ A).left ⁻¹ᵁ U := by
    rw [← hv]
    exact fun p _ => h (Set.mem_univ _)
  rw [map_add (f := _), ← hd U h f, ← hd' U h' f]
  exact snd_evalPt_mul hv hv' U h1 h h' h'' f

theorem isDiff_smul {w : Fin g → ℂ} {v : epsR ℂ ⟶ A} (hv : IsTan (R := ℂ) (G := A) v) (hd : u.IsDiff w v) (c : ℂ) :
    u.IsDiff (c • w) (Chart.spMap (scaleD c) ≫ v) := by
  intro U h' f
  have h0 := (tangent_mem_iff (u := u) ((isTan_iff _).1 (Chart.isTan_scale c hv)) U).1 h'
  have h := (tangent_mem_iff (u := u) ((isTan_iff _).1 hv) U).2 h0
  rw [map_smul, ← hd U h f]
  refine (congrArg TrivSqZeroExt.snd
    (evalPt_spMap_comp (scaleD c : DualNumber ℂ →+* DualNumber ℂ) v.left U h h' f)).trans ?_
  exact TrivSqZeroExt.snd_map _ _

theorem isDiff_zero : u.IsDiff 0 (1 : epsR ℂ ⟶ A) := by
  intro U h f
  have ht : IsTan (R := ℂ) (G := A) (1 : epsR ℂ ⟶ A) := Chart.isTan_one
  have h1 : ⊤ ≤ (1 : Chart.sp (R₀ := ℂ) ℂ ⟶ A).left ⁻¹ᵁ U := by
    rw [← ht]
    exact fun p _ => h (Set.mem_univ _)
  have key : ∀ (w : epsR ℂ ⟶ A) (hw : ⊤ ≤ w.left ⁻¹ᵁ U), w = 1 →
      (evalPt (R := DualNumber ℂ) w.left U hw f).snd = (evalPt (R := DualNumber ℂ) (1 : epsR ℂ ⟶ A).left U h f).snd := by
    rintro w hw rfl
    rfl
  have h2 : ⊤ ≤ (1 * 1 : epsR ℂ ⟶ A).left ⁻¹ᵁ U := by rwa [_root_.mul_one]
  have := snd_evalPt_mul ht ht U h1 h h h2 f
  rw [key _ h2 (_root_.mul_one _)] at this
  rw [map_zero]
  exact left_eq_add.1 this

theorem isDiff_list_prod : ∀ {k : ℕ} (w : Fin k → Fin g → ℂ) (v : Fin k → (epsR ℂ ⟶ A)),
    (∀ i, IsTan (R := ℂ) (G := A) (v i)) → (∀ i, u.IsDiff (w i) (v i)) →
    IsTan (R := ℂ) (G := A) (List.ofFn v).prod ∧ u.IsDiff (∑ i, w i) (List.ofFn v).prod := by
  intro k
  induction k with
  | zero =>
    intro w v _ _
    simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
    exact ⟨Chart.isTan_one, isDiff_zero u⟩
  | succ k ih =>
    intro w v hv hd
    obtain ⟨h1, h2⟩ := ih (fun i => w i.succ) (fun i => v i.succ)
      (fun i => hv i.succ) (fun i => hd i.succ)
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact ⟨Chart.isTan_mul (hv 0) h1, isDiff_add u (hv 0) h1 (hd 0) h2⟩

theorem isTangent_comp (f : A ⟶ A) [IsMonHom f] {v : epsR ℂ ⟶ A} (hv : IsTangent v) : IsTangent (v ≫ f) := by
  unfold IsTangent at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, IsMonHom.one_hom]

theorem isDiff_comp (f : A ⟶ A) [IsMonHom f] (F : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ))
    (hF : ∀ z, u.ex (F z) = u.ex z ≫ f) {w : Fin g → ℂ} {v : epsR ℂ ⟶ A}
    (hv : IsTangent v) (hd : u.IsDiff w v) : u.IsDiff (F w) (v ≫ f) := by
  intro U h s
  have h1 := hd (f.left ⁻¹ᵁ U) h ((f.left.app U).hom s)
  have e : ((v ≫ f).left.appLE U ⊤ h).hom s =
      (v.left.appLE (f.left ⁻¹ᵁ U) ⊤ h).hom ((f.left.app U).hom s) := by
    have := Scheme.Hom.comp_appLE v.left f.left U ⊤ h
    exact congrArg (fun φ => φ.hom s) this
  have hdiff := differentiableAt_val u ((tangent_mem_iff (u := u) (isTangent_comp f hv) U).1 h) s
  have hfun : (fun z => valAt' (u.ex z).left (f.left ⁻¹ᵁ U) ((f.left.app U).hom s)) =
      (fun z => valAt' (u.ex z).left U s) ∘ F := by
    funext z
    rw [valAt'_comp, Function.comp_apply, hF]
    rfl
  have hch := (HasFDerivAt.comp (0 : Fin g → ℂ) (f := F)
    (by rw [map_zero]; exact hdiff.hasFDerivAt) F.hasFDerivAt).fderiv
  rw [hfun, hch] at h1
  rw [e]
  exact h1

end GlobalTheory.UnifLieBasis

open GlobalTheory.UnifLieBasis in
open ReciprocityTheory.ChartRestriction.G.Chart (IsTan isTan_iff prodPts isLieComb_iff isTan_scale) in
theorem GlobalTheory.exists_lieBasis_of_holUnif : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g), Smooth A.hom → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → ∃ v : Fin g → (epsR ℂ ⟶ A), IsLieBasis v ∧ ∀ (f : A ⟶ A) (c : Fin g → ℂ), IsMonHom f → (∀ z, u.ex (fun k => c k * z k) = u.ex z ≫ f) → ∀ i, (v i ≫ f).left = spMap (epsScale (c i)) ≫ (v i).left := by
  intro A _ L g u _ h1 h2
  choose v hv using fun i : Fin g => (h2 (Pi.single i 1)).exists
  have ht : ∀ i, IsTan (R := ℂ) (G := A) (v i) := fun i => (isTan_iff _).2 (hv i).1
  have hp : ∀ c : Fin g → ℂ, IsTangent (prodPts (R := ℂ) (G := A) c v) ∧ u.IsDiff c (prodPts (R := ℂ) (G := A) c v) := by
    intro c
    obtain ⟨a, b⟩ := isDiff_list_prod u (fun i => c i • (Pi.single i 1 : Fin g → ℂ)) _
      (fun i => isTan_scale (c i) (ht i)) (fun i => isDiff_smul u (ht i) (hv i).2 (c i))
    rw [← pi_eq_sum_univ' c] at b
    exact ⟨(isTan_iff _).1 a, b⟩
  refine ⟨v, ⟨fun i => (hv i).1, fun w hw => ?_⟩, fun f c hf hF i => ?_⟩
  · obtain ⟨c, hc, hcu⟩ := h1 w hw
    refine ⟨c, (isLieComb_iff c v w).2 ((h2 c).unique ⟨hw, hc⟩ (hp c)), fun c' hc' => hcu c' ?_⟩
    rw [(isLieComb_iff c' v w).1 hc']
    exact (hp c').2
  · let F : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) := ContinuousLinearMap.pi fun k => c k • ContinuousLinearMap.proj k
    have hd := isDiff_comp u f F hF (hv i).1 (hv i).2
    have e : F (Pi.single i 1) = c i • (Pi.single i 1 : Fin g → ℂ) := by
      funext k
      by_cases hk : k = i <;> simp [F, hk]
    rw [e] at hd
    exact congrArg CommaMorphism.left ((h2 _).unique ⟨isTangent_comp f (hv i).1, hd⟩
      ⟨(isTan_iff _).1 (isTan_scale (c i) (ht i)), isDiff_smul u (ht i) (hv i).2 (c i)⟩)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivOfLifting
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LatticeHom

theorem eq_zero_of_forall_smul_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Λ : Submodule ℤ E) (hd : DiscreteTopology Λ) {z : E} (hz : ∀ t : ℂ, t • z ∈ Λ) : z = 0 := by
  have hc : Continuous fun t : ℂ => (⟨t • z, hz t⟩ : Λ) := by fun_prop
  have h := (IsLocallyConstant.iff_continuous _).2 hc |>.apply_eq_of_preconnectedSpace 1 0
  simpa using congrArg Subtype.val h

theorem exists_linearEquiv_of_lifting {A : Over (Sp ℂ)} [GrpObj A] {L L₁ : LB A.left} {g : ℕ}
    (u : HolUnif A L g) (v : HolUnif A L₁ g)
    (hv : ∀ (n : ℕ) (a : (Fin n → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A)), (∀ (U : A.left.Opens) (f : Γ(A.left, U)),
      IsOpen {w | w ∈ (Set.univ : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U} ∧
        DifferentiableOn ℂ (fun w => valAt' (a w).left U f)
          {w | w ∈ (Set.univ : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U}) → a 0 = 1 →
      ∃ G : (Fin n → ℂ) → (Fin g → ℂ), G 0 = 0 ∧ AnalyticAt ℂ G 0 ∧ ∀ᶠ w in 𝓝 0, v.ex (G w) = a w) :
    ∃ T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, v.ex (T z) = u.ex z := by
  obtain ⟨G, hG0, hGa, hGe⟩ := hv g u.ex (fun U f => by simpa using u.hol U f)
    ((u.ker 0).2 u.Λ.zero_mem)
  have hT := EndoLinear.fderiv_lifts v.ex v.ex_add v.Λ v.ker v.discrete u.ex u.ex_add G hG0
    hGa.differentiableAt hGe
  have hi : Function.Injective (fderiv ℂ G 0).toLinearMap := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    refine eq_zero_of_forall_smul_mem u.Λ u.discrete fun t => ?_
    have hz' : fderiv ℂ G 0 z = 0 := hz
    rw [← u.ker, ← hT, map_smul, hz', smul_zero]
    exact (v.ker 0).2 v.Λ.zero_mem
  exact ⟨LinearEquiv.ofInjectiveEndo _ hi, hT⟩

theorem exists_linearEquiv_of_holUnif (hmul : Out.MulNSt) (P : Out.PolAV (Sp ℂ)) {L L' : LB P.A.left}
    (u : HolUnif P.A L P.g) (u' : HolUnif P.A L' P.g) :
    ∃ T : (Fin P.g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ), ∀ z, u'.ex (T z) = u.ex z := by
  have hval := @valAt'_rules
  have hvalaff := @existsUnique_point_of_ringHom
  obtain ⟨v, -, hv⟩ := @AbelianExp.exists_holUnif hmul hval (@holFamily_lift hval)
    (@isTopologicalGroup_complexPoints hval) (@PointsCompact.compactSpace_points_polAV hval hvalaff)
    (@HolChart.exists_holomorphic_chart hval hvalaff @exists_holomorphic_section_of_etale) P
  obtain ⟨T, hT⟩ := exists_linearEquiv_of_lifting u v hv
  obtain ⟨T', hT'⟩ := exists_linearEquiv_of_lifting u' v hv
  refine ⟨T.trans T'.symm, fun z => ?_⟩
  rw [← hT', ← hT]
  simp

end GlobalTheory.LatticeHom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DatumExistsPeriod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem datum_exists_period :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ)
      (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty → ∃ P, IsPeriod D ty P :=
  fun E _ _ _ H D g ty hty => PeriodNonempty.exists_isPeriod E H D g ty hty

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.BijectiveAppTopOfSmoothOfIsProperOfGeometrically
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem bijective_appTop_of_smooth_of_isProper_of_geometricallyConnected :
    ∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K), Smooth p → IsProper p →
      GeometricallyConnected p → Function.Bijective p.appTop.hom := by
  intro K _ X p hs hp hg

  haveI := hs
  haveI := hp
  haveI := hg
  haveI : GeometricallyIntegral p :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected X _ p hs hg
  haveI : IsIso p.appTop := ProperFunctions.isIso_appTop_of_field p
  exact ConcreteCategory.bijective_of_isIso p.appTop

end GlobalTheory
end
