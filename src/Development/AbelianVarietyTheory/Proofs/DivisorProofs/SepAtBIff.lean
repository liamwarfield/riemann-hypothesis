module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UValThruTopOfDisjoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqPowSmulOfPDivGroupTorsionTowerMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleUnitConstant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.USep

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c}

def IsCov (C : UCompact Xo c) {M : Scheme.{0}} (g : M ⟶ C.Z) (z₁ : M)
    (ζ : Sp (M.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)) : Prop :=
  IsNormalScheme M ∧
    (∃ (U : C.Z.Opens) (g' : M ⟶ U.toScheme), IsFinite g' ∧ g' ≫ U.ι = g ∧
      Set.range (pullback.fst C.z (spMap C.b)) ⊆ (U : Set C.Z)) ∧
    ζ ≫ pullback.fst _ _ = M.fromSpecStalk z₁ ≫ g ∧
    ∀ p : Sp (M.presheaf.stalk z₁), p.asIdeal = ⊥ → ζ p ∈ Set.range C.iF

section

variable {A : Type} [CommRing A] [IsLocalRing A] (ζ : Sp A ⟶ pullback C.z (spMap C.b)) {N₁ : ℕ}
  (Φ : VSys (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) !![(1 : ℤ)] N₁ A)

def HasTraits : Prop :=
  ∀ (T : UTrait Xo c) (ev : A →+* T.V), IsLocalHom ev → jK T.V ≫ spMap ev ≫ ζ = T.y ≫ C.iF →
    ∃ (y : Φ.Y) (f : T.V →+* Φ.V y) (e : Φ.X y ≃ₗ[𝓞 E] T.P.D.toPre.X), Φ.m y = 1 ∧ IsPrincipalIdealRing (Φ.V y) ∧
      Function.Injective f ∧ IsLocalHom f ∧ f.comp ev = Φ.ev y ∧
      ∀ k, Φ.t y k ^ 2 = f T.ϖ ∧ ∀ a b, Φ.δ y k a b = T.be (e a) (e b)

def IsMember {φ : InvFun (𝓞 E)} {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V)
    (ξ : Sp V ⟶ pullback C.z (spMap C.b)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃ₗ[𝓞 E] Cm.P.D.toPre.X)
    (h : Fin (Φ.m y) ≃ Fin Cm.m) : Prop :=
  Function.Injective ρ ∧ ρ.Finite ∧ spMap (Φ.ev y) ≫ ζ = spMap ρ ≫ ξ ∧
    (∀ k, Φ.t y k ^ 2 = ρ (Cm.s (h k)) ∧ ∀ a b, Φ.δ y k a b = ((l.M' : ℤ) • Cm.δ (h k)) (e a) (e b)) ∧
    ∃ (D : DegPre (Φ.V y)) (p : IsPullDeg ρ Cm.P.D.toPre D), GlobalTheory.Poinc.Sep.IsThetaTerms D N₁ p.xe.symm
      fun mu c => Φ.u y (fun _ => e.symm mu) c * mono !![(1 : ℤ)] (Φ.t y) (Φ.δ y) fun _ => e.symm mu

end

def DescAt {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) {K : Type} [Field K] (ev : V →+* K) (k₀ : Subfield K) : Prop :=
  ∃ (B₀ : Over (Sp k₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (Sp k₀ ⟶ B₀.left))
    (B' : Over (Sp K)) (_ : GrpObj B') (π₁ : B'.left ⟶ Q.P.A.left) (π₀ : B'.left ⟶ B₀.left)
    (w : LB.Iso (Q.P.L.pull π₁) (M₀.pull π₀)) (c' : Q.X → (Sp K ⟶ B'.left)),
    IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback B' Q.P.A (spMap ev) π₁ ∧ IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ ∧
    w.IsGen ∧ ∀ a, c' a ≫ B'.hom = 𝟙 _ ∧ c' a ≫ π₁ = spMap ev ≫ (Q.c a).left ∧ c' a ≫ π₀ = spMap k₀.subtype ≫ c₀ a

theorem sepAtB_iff {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) (τ₀ : GlobalTheory.UChart.Gens Q) {m N : ℕ}
    (s : Fin m ⊕ Fin N → V) {K : Type} [Field K] (ev : V →+* K) (k₀ : Subfield K) :
    GlobalTheory.UChart.SepAtB Q τ₀ s ev k₀ ↔ (∀ i, ev (s (.inl i)) = 0) ∧ DescAt Q ev k₀ ∧
      ∀ (W₀ : Type) [CommRing W₀] (ιb : W₀ →+* V), GlobalTheory.UChart.FromBase Q τ₀ ιb → (∀ a, ev (ιb a) ∈ k₀) →
        ∀ i, ev (s (.inr i)) ∈ k₀ := Iff.rfl

end GlobalTheory.USep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveQcPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UPel.HT.SiegUniqBase

section FlatPow
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj CategoryTheory.MonObj

theorem flat_surjective_qc_pow : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ k : ℕ, 0 < k → Flat ((𝟙 A) ^ k).left ∧ Surjective ((𝟙 A) ^ k).left ∧ QuasiCompact ((𝟙 A) ^ k).left := by
  intro S A _ hA k hk
  have hc := hA.comm
  obtain ⟨h1, h2⟩ := GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA S A hA k hk
  have e : (𝟙 A) ^ k = ReciprocityTheory.ChartRestriction.G.Out.mulA A k := rfl
  rw [e]
  refine ⟨h2, GlobalTheory.AbLaw.MulN.surjective_of_geomFibres _ fun K _ _ t => ?_, inferInstance⟩
  have hf : IsFinite ((Over.pullback t).map (ReciprocityTheory.ChartRestriction.G.Out.mulA A k)).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t _) h1
  rw [GlobalTheory.MulFiniteFlat.pullback_map_mulA] at hf ⊢
  have hB := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t A hA
  have hBc := hB.comm
  exact (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
    hB _ (GlobalTheory.AbLaw.MulN.isMonHom_mulA _ k) hf).2

end FlatPow

end GlobalTheory.UPel.HT.SiegUniqBase
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
noncomputable section

open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LowFilt

open GlobalTheory.LowDat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def IsOpp (D : Datum H) (Z Z' : Submodule (𝓞 E) D.La) : Prop :=
  Z ≤ perp D Z ∧ Z' ≤ perp D Z' ∧ (∀ φ : Z →+ ℤ, ∃! b : Z', ∀ a : Z, D.EF a b = φ a) ∧
    ∀ φ : Z' →+ ℤ, ∃! a : Z, ∀ b : Z', D.EF a b = φ b

variable {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

def Cois (D : Datum H) (y : D.La →ₗ[𝓞 E] X) (n : ℕ) : Prop :=
  (∀ x, ∃ a e, y a = x + n • e) ∧
    ∀ a, (∀ b, (∃ e, y b = n • e) → (n : ℤ) ∣ D.EF a b) → ∃ e, y a = n • e

def KerIs (D : Datum H) (y : D.La →ₗ[𝓞 E] X) (Z : Submodule (𝓞 E) D.La) (n : ℕ) : Prop :=
  ∀ a, (∃ e, y a = n • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + n • e

abbrev img (D : Datum H) (y : D.La →ₗ[𝓞 E] X) (Z : Submodule (𝓞 E) D.La) (I : Ideal (𝓞 E)) : Submodule (𝓞 E) X :=
  Z.map y ⊔ I • (⊤ : Submodule (𝓞 E) X)

def Improves (D : Datum H) (y : D.La →ₗ[𝓞 E] X) (n : ℕ) (𝔭 : Ideal (𝓞 E)) (Z Z' Z'' : Submodule (𝓞 E) D.La) : Prop :=
  IsOpp D Z Z'' ∧ (∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → img D y Z' 𝔮 ≤ img D y Z'' 𝔮) ∧
    ¬ img D y Z'' 𝔭 ≤ img D y Z' 𝔭

theorem bar_bar (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := H.starRing.star_involutive a

theorem ef_swap (D : Datum H) (a b : D.La) : D.EF a b = -D.EF b a := by
  have h := D.alt (a + b)
  simp only [map_add (f := _), LinearMap.add_apply, D.alt] at h
  linear_combination h

theorem mem_perp {D : Datum H} {Z : Submodule (𝓞 E) D.La} {a : D.La} : a ∈ perp D Z ↔ ∀ z ∈ Z, D.EF a z = 0 := Iff.rfl

variable {D : Datum H} {Z Z' : Submodule (𝓞 E) D.La}

theorem IsOpp.symm (h : IsOpp D Z Z') : IsOpp D Z' Z := by
  refine ⟨h.2.1, h.1, fun φ => ?_, fun φ => ?_⟩
  · obtain ⟨a, ha, hu⟩ := h.2.2.2 (-φ)
    refine ⟨a, fun b => by rw [ef_swap, ha]; simp, fun a' ha' => hu a' fun b => ?_⟩
    rw [ef_swap, ha']; simp
  · obtain ⟨a, ha, hu⟩ := h.2.2.1 (-φ)
    refine ⟨a, fun b => by rw [ef_swap, ha]; simp, fun a' ha' => hu a' fun b => ?_⟩
    rw [ef_swap, ha']; simp

theorem IsOpp.eq_zero (h : IsOpp D Z Z') {b : D.La} (hb : b ∈ Z') (h0 : b ∈ perp D Z) : b = 0 := by
  obtain ⟨c, -, hu⟩ := h.2.2.1 0
  have h1 := hu ⟨b, hb⟩ fun a => by rw [ef_swap, h0 _ a.2]; simp
  have h2 := hu 0 fun a => by simp
  exact congrArg Subtype.val (h1.trans h2.symm)

theorem IsOpp.exists_sub_mem_perp (h : IsOpp D Z Z') (a : D.La) : ∃ b ∈ Z', a - b ∈ perp D Z := by
  obtain ⟨b, hb, -⟩ := h.2.2.1 ((D.EF.flip a).toAddMonoidHom.comp Z.subtype.toAddMonoidHom)
  refine ⟨b, b.2, fun z hz => ?_⟩
  have := hb ⟨z, hz⟩
  simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, Submodule.subtype_apply, LinearMap.flip_apply] at this
  rw [ef_swap, map_sub, this]
  exact neg_eq_zero.2 (sub_self _)

theorem IsOpp.exists_decomp (h : IsOpp D Z Z') (a : D.La) :
    ∃ z ∈ Z, ∃ m ∈ perp D Z ⊓ perp D Z', ∃ b ∈ Z', a = z + m + b := by
  obtain ⟨b, hb, h1⟩ := h.exists_sub_mem_perp a
  obtain ⟨z, hz, h2⟩ := h.symm.exists_sub_mem_perp a
  refine ⟨z, hz, a - b - z, ⟨sub_mem h1 (h.1 hz), ?_⟩, b, hb, by abel⟩
  rw [sub_right_comm]
  exact sub_mem h2 (h.2.1 hb)

theorem IsOpp.isIsoSat (h : IsOpp D Z Z') : IsIsoSat D Z := by
  refine ⟨h.1, fun n x hn hx => ?_⟩
  obtain ⟨z, hz, m, hm, b, hb, rfl⟩ := h.exists_decomp x
  have cancel : ∀ (W : Submodule (𝓞 E) D.La) (v : D.La), n • v ∈ perp D W → v ∈ perp D W := fun W v hv w hw => by
    have := hv w hw
    rw [map_nsmul, LinearMap.smul_apply, smul_eq_zero] at this
    exact this.resolve_left hn
  have hb0 : b = 0 := h.eq_zero hb (by
    have := sub_mem (cancel Z _ (h.1 hx)) (add_mem (h.1 hz) hm.1)
    rwa [add_sub_cancel_left] at this)
  subst hb0
  have hm0 : n • m = 0 := h.symm.eq_zero
    (by have := sub_mem hx (nsmul_mem hz n); rwa [add_zero, smul_add, add_sub_cancel_left] at this) (nsmul_mem hm.2 n)
  have : m = 0 := D.unimod.1 (LinearMap.ext fun w => by
    have := congrArg (fun v => D.EF v w) hm0
    simp only [map_nsmul, LinearMap.smul_apply, map_zero, LinearMap.zero_apply, smul_eq_zero] at this
    simpa using this.resolve_left hn)
  simpa [this] using hz

theorem IsOpp.shear (h : IsOpp D Z Z') (t : Z' →ₗ[𝓞 E] D.La) (ht : ∀ b, t b - b ∈ perp D Z)
    (hiso : ∀ b b', D.EF (t b) (t b') = 0) : IsOpp D Z (LinearMap.range t) := by
  have key : ∀ (a : Z) (b : Z'), D.EF a (t b) = D.EF a b := fun a b => by
    have := ht b a a.2
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    rw [ef_swap, this, ← ef_swap]
  refine ⟨h.1, ?_, fun φ => ?_, fun φ => ?_⟩
  · rintro _ ⟨b, rfl⟩ _ ⟨b', rfl⟩
    exact hiso b b'
  · obtain ⟨b, hb, hu⟩ := h.2.2.1 φ
    refine ⟨⟨t b, b, rfl⟩, fun a => (key a b).trans (hb a), ?_⟩
    rintro ⟨_, b', rfl⟩ hb'
    exact Subtype.ext (congrArg t (hu b' fun a => (key a b').symm.trans (hb' a)))
  · obtain ⟨a, ha, hu⟩ := h.2.2.2 (φ.comp t.rangeRestrict.toAddMonoidHom)
    refine ⟨a, ?_, fun a' ha' => hu a' fun b => (key a' b).symm.trans (ha' ⟨t b, b, rfl⟩)⟩
    rintro ⟨_, b, rfl⟩
    exact (key a b).trans (ha b)

theorem isOpp_bot (D : Datum H) : IsOpp D ⊥ ⊥ :=
  ⟨bot_le, bot_le, fun φ => ⟨0, fun a => by rw [Subsingleton.elim a 0]; simp, fun _ _ => Subsingleton.elim _ _⟩,
    fun φ => ⟨0, fun a => by rw [Subsingleton.elim a 0]; simp, fun _ _ => Subsingleton.elim _ _⟩⟩

theorem cmHostUnit_add_conj_eq_one (H : Host E) : H.w0 + H.bar H.w0 = 1 := by
  have h1 := congrArg H.bar H.two_weight_eq_one_add_root
  rw [map_mul, map_add (f := _), map_one, GlobalTheory.CharRank.bar_rt_neg, map_ofNat] at h1
  have h2 := H.two_weight_eq_one_add_root
  exact mul_left_cancel₀ (two_ne_zero (α := 𝓞 E)) (by linear_combination h1 + h2)

theorem exists_skew_solve (hd : ∀ φ : Z →+ ℤ, ∃! b : Z', ∀ a : Z, D.EF a b = φ a) (β : LinearMap.BilinForm ℤ Z)
    (hβ : ∀ a b, β a b = -β b a) (hadj : ∀ (c : 𝓞 E) a b, β (c • a) b = β a (H.bar c • b)) :
    ∃ c : Z →ₗ[𝓞 E] Z', ∀ a b : Z, D.EF a (c b) + D.EF (c a) b = β a b := by
  choose c hc hu using fun b : Z => hd (AddMonoidHom.mk' (fun a => β (H.w0 • a) b) fun a a' => by simp)
  simp only [AddMonoidHom.mk'_apply] at hc hu
  refine ⟨{ toFun := c, map_add' := fun b b' => (hu _ _ fun a => ?_).symm,
            map_smul' := fun x b => (hu _ _ fun a => ?_).symm }, fun a b => ?_⟩
  · simp [hc]
  · have h1 := hc b (H.bar x • a)
    rw [Submodule.coe_smul, D.adj, bar_bar, smul_comm, hadj, bar_bar] at h1
    exact h1
  · show D.EF a (c b) + D.EF (c a) b = _
    rw [ef_swap D (c a), hc, hc, ← hβ]
    have h2 := hadj (H.bar H.w0) a b
    rw [bar_bar] at h2
    rw [← h2, ← LinearMap.add_apply, ← map_add (f := _), ← add_smul, cmHostUnit_add_conj_eq_one, one_smul]

theorem IsOpp.exists_rank_one (h : IsOpp D Z Z') {m : D.La} (hm : m ∈ perp D Z ⊓ perp D Z') (θ : 𝓞 E →+ ℤ)
    (hθ : ∀ t, θ t - θ (H.bar t) + D.EF (t • m) m = 0) :
    ∃ ζ : (Z' →ₗ[𝓞 E] 𝓞 E) →+ D.La, (∀ ℓ, ζ ℓ ∈ Z) ∧ (∀ ℓ (x : Z'), D.EF x (ζ ℓ) = θ (ℓ x)) ∧
      (∀ (c : 𝓞 E) ℓ, ζ (c • ℓ) = H.bar c • ζ ℓ) ∧
      ∀ ℓ : Z' →ₗ[𝓞 E] 𝓞 E, IsOpp D Z (LinearMap.range (Z'.subtype + ℓ.smulRight (m + ζ ℓ))) := by
  choose z hz hu using fun ℓ : Z' →ₗ[𝓞 E] 𝓞 E => h.symm.2.2.1 (θ.comp ℓ.toAddMonoidHom)
  simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe] at hz hu
  refine ⟨AddMonoidHom.mk' (fun ℓ => (z ℓ : D.La)) fun ℓ ℓ' => congrArg Subtype.val (hu _ (z ℓ + z ℓ') fun x => ?_).symm,
    fun ℓ => (z ℓ).2, hz, fun c ℓ => congrArg Subtype.val (hu _ (H.bar c • z ℓ) fun x => ?_).symm, fun ℓ => ?_⟩
  · simp [hz]
  · have := hz ℓ (c • x)
    rw [Submodule.coe_smul, D.adj, ℓ.map_smul] at this
    exact this
  · refine h.shear _ (fun b => ?_) fun b b' => ?_
    · simpa using (perp D Z).smul_mem (ℓ b) (add_mem hm.1 (h.1 (z ℓ).2))
    · have e1 : D.EF b b' = 0 := h.2.1 b.2 _ b'.2
      have e2 : ∀ (c : 𝓞 E) (x : Z'), D.EF (c • m) x = 0 := fun c x => (perp D Z').smul_mem c hm.2 _ x.2
      have e3 : ∀ c c' : 𝓞 E, D.EF (c • m) (c' • z ℓ) = 0 := fun c c' =>
        (perp D Z).smul_mem c hm.1 _ (Z.smul_mem c' (z ℓ).2)
      have e4 : ∀ c c' : 𝓞 E, D.EF (c • z ℓ) (c' • z ℓ) = 0 := fun c c' =>
        h.1 (Z.smul_mem c (z ℓ).2) _ (Z.smul_mem c' (z ℓ).2)
      have e5 : ∀ (c : 𝓞 E) (x : Z'), D.EF x (c • z ℓ) = θ (H.bar c * ℓ x) := fun c x => by
        have := hz ℓ (H.bar c • x)
        rw [Submodule.coe_smul, D.adj, bar_bar, ℓ.map_smul] at this
        exact this
      have e6 : D.EF (ℓ b • m) (ℓ b' • m) = D.EF ((H.bar (ℓ b') * ℓ b) • m) m := by
        rw [mul_smul, D.adj (H.bar (ℓ b')), bar_bar]
      have e7 := hθ (H.bar (ℓ b') * ℓ b)
      rw [map_mul H.bar, bar_bar, mul_comm (ℓ b')] at e7
      simp only [LinearMap.add_apply, Submodule.subtype_apply, LinearMap.smulRight_apply, AddMonoidHom.mk'_apply,
        smul_add, map_add]
      rw [ef_swap D b (ℓ b' • m), ef_swap D (ℓ b • (z ℓ : D.La)) b', ef_swap D (ℓ b • (z ℓ : D.La)) (ℓ b' • m),
        e1, e2, e2, e3, e3, e4, e5, e5, e6]
      linear_combination e7

theorem exists_theta_vec (D : Datum H) (m : D.La) :
    ∃ θ : 𝓞 E →+ ℤ, ∀ t, θ t - θ (H.bar t) + D.EF (t • m) m = 0 := by
  refine ⟨AddMonoidHom.mk' (fun t => -D.EF ((H.w0 * t) • m) m) fun a b => by simp [mul_add, add_smul, add_comm],
    fun t => ?_⟩
  have h1 : D.EF ((H.w0 * H.bar t) • m) m = -D.EF ((H.bar H.w0 * t) • m) m := by
    rw [D.adj, map_mul, bar_bar, ef_swap]
  have h2 : D.EF (t • m) m = D.EF ((H.w0 * t) • m) m + D.EF ((H.bar H.w0 * t) • m) m := by
    rw [← LinearMap.add_apply, ← map_add (f := _), ← add_smul, ← add_mul, cmHostUnit_add_conj_eq_one, one_mul]
  simp only [AddMonoidHom.mk'_apply]
  linear_combination h1 + h2

theorem range_le_of_mem {O P X : Type} [CommRing O] [AddCommGroup P] [Module O P] [AddCommGroup X] [Module O X]
    (f : P →ₗ[O] X) (ℓ : P →ₗ[O] O) (u : X) (I : Ideal O) (h : ∀ x, ℓ x ∈ I) :
    LinearMap.range f ⊔ I • (⊤ : Submodule O X) ≤ LinearMap.range (f + ℓ.smulRight u) ⊔ I • ⊤ := by
  refine sup_le ?_ le_sup_right
  rintro _ ⟨x, rfl⟩
  have : f x = (f + ℓ.smulRight u) x - ℓ x • u := by simp
  rw [this]
  exact sub_mem (Submodule.mem_sup_left ⟨x, rfl⟩) (Submodule.mem_sup_right (Submodule.smul_mem_smul (h x) trivial))

theorem range_le_of_ker {O P X : Type} [CommRing O] [AddCommGroup P] [Module O P] [AddCommGroup X] [Module O X]
    (f : P →ₗ[O] X) (ℓ : P →ₗ[O] O) (u : X) (I : Ideal O) (hI : I.IsMaximal) {v : P}
    (hv : f v ∈ I • (⊤ : Submodule O X)) (hl : ℓ v ∉ I) :
    u ∈ LinearMap.range (f + ℓ.smulRight u) ⊔ I • (⊤ : Submodule O X) ∧
      LinearMap.range f ⊔ I • (⊤ : Submodule O X) ≤ LinearMap.range (f + ℓ.smulRight u) ⊔ I • ⊤ := by
  have hu : u ∈ LinearMap.range (f + ℓ.smulRight u) ⊔ I • (⊤ : Submodule O X) := by
    obtain ⟨c, i, hi, hc⟩ := hI.exists_inv hl
    have : (f + ℓ.smulRight u) (c • v) - c • f v + i • u = u := by
      simp only [LinearMap.add_apply, map_smul, LinearMap.smulRight_apply, smul_add, add_sub_cancel_left, smul_smul]
      rw [← add_smul, hc, one_smul]
    have h2 : (f + ℓ.smulRight u) (c • v) - c • f v + i • u ∈
        LinearMap.range (f + ℓ.smulRight u) ⊔ I • (⊤ : Submodule O X) :=
      add_mem (sub_mem (Submodule.mem_sup_left ⟨_, rfl⟩) (Submodule.mem_sup_right (Submodule.smul_mem _ _ hv)))
        (Submodule.mem_sup_right (Submodule.smul_mem_smul hi trivial))
    rwa [this] at h2
  refine ⟨hu, sup_le ?_ le_sup_right⟩
  rintro _ ⟨x, rfl⟩
  have : f x = (f + ℓ.smulRight u) x - ℓ x • u := by simp
  rw [this]
  exact sub_mem (Submodule.mem_sup_left ⟨x, rfl⟩) (Submodule.smul_mem _ _ hu)

end GlobalTheory.LowFilt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArtinianRingTsze
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlue

variable {k : Type} [Field k] {d : ℕ}

theorem finite_tsze (k : Type) [Field k] (d : ℕ) : Module.Finite k (TrivSqZeroExt k (Fin d → k)) :=
  Module.Finite.of_surjective
    ((Algebra.linearMap k (TrivSqZeroExt k (Fin d → k))).coprod (TrivSqZeroExt.inrHom k (Fin d → k)))
    (fun x => ⟨(x.fst, x.snd), by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]⟩)

theorem isArtinianRing_tsze (k : Type) [Field k] (d : ℕ) : IsArtinianRing (TrivSqZeroExt k (Fin d → k)) :=
  haveI := finite_tsze k d; IsArtinianRing.of_finite k _

theorem exists_coords (V : Type) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]
    (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀) (l : primDR A₀ →ₗ[k] TrivSqZeroExt k V) :
    ∃ e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀,
      ∀ c, e ((GlobalTheory.FODef.constMorV k V A₀).pull c) = l c := by
  have hm := GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k V A₀ hA (GlobalTheory.FODef.sqZero k V) (GlobalTheory.FODef.constMorV k V A₀)
  let eqv := LinearEquiv.ofBijective _ hm
  refine ⟨(LinearMap.liftBaseChange (TrivSqZeroExt k V) l) ∘ₗ eqv.symm.toLinearMap, fun c => ?_⟩
  have : (GlobalTheory.FODef.constMorV k V A₀).pull c = eqv (1 ⊗ₜ c) :=
    (one_smul (TrivSqZeroExt k V) ((GlobalTheory.FODef.constMorV k V A₀).pull c)).symm
  rw [this, LinearMap.comp_apply, LinearEquiv.coe_coe, eqv.symm_apply_apply,
    LinearMap.liftBaseChange_tmul, one_smul]

def glueFil (A₀ : Over (Sp k)) [GrpObj A₀] (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀)) :
    Submodule (TrivSqZeroExt k (Fin d → k))
      (Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀) where
  carrier := {e | ∃ x ∈ Fil A₀, ∃ z : Fin d → HdR A₀, (∀ j, z j ∈ Fil A₀) ∧
      ∀ c : primDR A₀, e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) =
        TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (fun j => (f j x + z j) c)}
  add_mem' := by
    rintro e e' ⟨x, hx, z, hz, he⟩ ⟨x', hx', z', hz', he'⟩
    refine ⟨x + x', add_mem hx hx', z + z', fun j => add_mem (hz j) (hz' j), fun c => ?_⟩
    rw [LinearMap.add_apply, he c, he' c]
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, Pi.add_apply, map_add (f := _),
        LinearMap.add_apply, zero_add, Pi.zero_apply, add_zero]
      ring
  zero_mem' := ⟨0, zero_mem _, 0, fun _ => zero_mem _, fun c => by rw [LinearMap.zero_apply]; ext <;> simp⟩
  smul_mem' := by
    rintro r e ⟨x, hx, z, hz, he⟩
    refine ⟨r.fst • x, Submodule.smul_mem _ _ hx, fun j => r.fst • z j + r.snd j • x,
      fun j => add_mem (Submodule.smul_mem _ _ (hz j)) (Submodule.smul_mem _ _ hx), fun c => ?_⟩
    rw [LinearMap.smul_apply, he c, smul_eq_mul]
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
        TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, Pi.add_apply, Pi.smul_apply,
        map_smul, map_add, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, add_zero, zero_add,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Pi.zero_apply]
      ring

theorem exists_mem_glueFil (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀)) {x : HdR A₀} (hx : x ∈ Fil A₀) :
    ∃ e ∈ glueFil A₀ f, ∀ c, e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) =
      TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr ((LinearMap.pi fun j => f j x) c) := by
  obtain ⟨e, he⟩ := exists_coords (Fin d → k) A₀ hA
    ((Algebra.linearMap k (TrivSqZeroExt k (Fin d → k))) ∘ₗ x + (TrivSqZeroExt.inrHom k (Fin d → k)) ∘ₗ
      LinearMap.pi fun j => f j x)
  refine ⟨e, ⟨x, hx, 0, fun _ => zero_mem _, fun c => ?_⟩, fun c => ?_⟩
  · rw [he c]; ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  · rw [he c]; simp [TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.HTGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirigidifiedKthRootPullbackBundle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirigidifiedKthRootPullbackBundle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.SharpPull
namespace GlobalTheory.KthRoot

theorem finite_flat_surjective_mulN_any : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A],
    IsAbelianScheme A → ∀ n : ℕ, 0 < n →
      IsFinite (mulN A n).left ∧ Flat (mulN A n).left ∧ Surjective (mulN A n).left := by
  intro S A _ hA n hn
  have hc := hA.comm
  obtain ⟨h1, h2⟩ := GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA S A hA n hn
  have e : mulN A n = ReciprocityTheory.ChartRestriction.G.Out.mulA A n := GlobalTheory.MulFlatSurj.mulN_eq_pow A n
  rw [e]
  refine ⟨h1, h2, GlobalTheory.AbLaw.MulN.surjective_of_geomFibres _ fun K _ _ t => ?_⟩
  have hf : IsFinite ((Over.pullback t).map (ReciprocityTheory.ChartRestriction.G.Out.mulA A n)).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t _) h1
  rw [GlobalTheory.MulFiniteFlat.pullback_map_mulA] at hf ⊢
  have hB := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t A hA
  have hBc := hB.comm
  exact (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
    hB _ (GlobalTheory.AbLaw.MulN.isMonHom_mulA _ n) hf).2

theorem exists_descent_mulN : ∀ (Y : Scheme.{0}) (A D : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj D] (h : A ⟶ D) (k : ℕ) (U : Scheme.{0}) (t : U ⟶ Y) (AU : Over U) [GrpObj AU] [IsCommMonObj AU] (φ : AU.left ⟶ A.left), IsAbelianScheme A → IsMonHom h → 0 < k → IsGrpPullback AU A t φ → (∀ (T : Over Y) (s : T.left ⟶ U), s ≫ t = T.hom → ∀ a : T ⟶ A, a ^ k = 1 → a ≫ h = 1) → ∃ y : AU ⟶ (Over.pullback t).obj D, IsMonHom y ∧ (mulN AU k ≫ y).left ≫ pullback.fst D.hom t = φ ≫ h.left := by
  intro Y A D _ _ _ h k U t AU _ _ φ hA hh hk hpb hker
  have hAU : IsAbelianScheme AU :=
    { comm := inferInstance
      smooth := MorphismProperty.of_isPullback (P := @Smooth) hpb.1 hA.smooth
      proper := MorphismProperty.of_isPullback (P := @IsProper) hpb.1 hA.proper
      geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) hpb.1 hA.geomConnected }
  have hψ := isGrpPullback_pullback D t
  obtain ⟨hU, ehU⟩ := GlobalTheory.SharpPull.exists_lift hpb hψ h
  have : IsMonHom hU := GlobalTheory.SharpPull.isMonHom_lift hpb hψ ehU
  obtain ⟨hfin, hflat, hsurj⟩ := finite_flat_surjective_mulN_any U AU hAU k hk
  have hmon : IsMonHom (mulN AU k) := by
    rw [GlobalTheory.MulFlatSurj.mulN_eq_pow]
    exact GlobalTheory.AbLaw.MulN.isMonHom_mulA AU k
  obtain ⟨⟨y, hy, hyk⟩, -⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective U AU AU _ (mulN AU k) hU hmon
    inferInstance hflat hsurj inferInstance (fun T x hx => by
      apply GlobalTheory.SharpPull.push_inj hψ
      rw [GlobalTheory.SharpPull.push_comp hpb hψ ehU, map_one]
      refine hker (Over.mk (T.hom ≫ t)) T.hom rfl _ ?_
      have ex : x ^ k = x ≫ mulN AU k := by
        rw [GlobalTheory.MulFlatSurj.mulN_eq_pow, MonObj.comp_pow, Category.comp_id]
      rw [← map_pow, ex, hx, map_one])
  exact ⟨y, hy, by rw [hyk, ehU]⟩

theorem exists_birigid_root_of_descent : ∀ (Y : Scheme.{0}) (A D : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj D] (Q : LB (A ⊗ D).left) (h : A ⟶ D) (k : ℕ) (X : Scheme.{0}) (M : LB X) (c : (A ⊗ A).left ⟶ X), GlobalTheory.AbDual.IsDual A D Q → GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) → M.IsLB → LBIso (M.pull c) (Q.pull (lift (fst A A) (snd A A ≫ h)).left) → ∀ (U : Scheme.{0}) (t : U ⟶ Y) (AU : Over U) [GrpObj AU] [IsCommMonObj AU] (φ : AU.left ⟶ A.left) (φ₂ : (G2 AU).left ⟶ (G2 A).left), IsGrpPullback AU A t φ → IsSquare φ φ₂ → ∀ y : AU ⟶ (Over.pullback t).obj D, IsMonHom y → (mulN AU k ≫ y).left ≫ pullback.fst D.hom t = φ ≫ h.left → ∃ P : LB (G2 AU).left, P.IsLB ∧ (∃ t : (P.pull (lift (1 : AU ⟶ AU) (𝟙 AU)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (𝟙 AU) (1 : AU ⟶ AU)).left).Gen, t.IsGen) ∧ LBIso (M.pull (φ₂ ≫ c)) (lbPow P k) := by
  intro Y A D _ _ _ Q h k X M c hQ hadd hM hiso U t AU _ _ φ φ₂ hpb hsq y hy hyk
  have hψ := isGrpPullback_pullback D t
  let W : Over U := AU ⊗ AU
  let a₁ : Over.mk (W.hom ≫ t) ⟶ A := pushHom hpb W (fst AU AU)
  let d : Over.mk (W.hom ≫ t) ⟶ D := pushHom hψ W (snd AU AU ≫ y)
  let P : LB (G2 AU).left := Q.pull (lift a₁ d).left
  have hP : P.IsLB := pull_isLB hQ.isLB _

  have key : ∀ (T : Over U) (z : T ⟶ W), CechPic.pull z.left (cls P hP) =
      evc hQ.isLB (pushHom hpb T (z ≫ fst AU AU)) (pushHom hψ T (z ≫ snd AU AU ≫ y)) := by
    intro T z
    rw [cls_pull hQ.isLB, ← pull_comp, evc]
    congr 2
    apply left_ext
    · rw [Category.assoc, lift_left_fst, lift_left_fst]
      rfl
    · rw [Category.assoc, lift_left_snd, lift_left_snd]
      rfl

  refine ⟨P, hP, (cls_eq_zero_iff (pull_isLB hP _)).1 ?_, (cls_eq_zero_iff (pull_isLB hP _)).1 ?_, ?_⟩
  · rw [cls_pull hP, key, lift_fst, map_one]
    exact hQ.additive.evc_one hQ.isLB _
  · rw [cls_pull hP, key, lift_snd_assoc, MonObj.one_comp, map_one]
    exact evc_one_right hQ.isLB hQ.zero _
  · have hs : (swap Q).IsLB := pull_isLB hQ.isLB _
    have add2 : ∀ (Z : Over Y) (a : Z ⟶ A) (u v : Z ⟶ D),
        evc hQ.isLB a (u * v) = evc hQ.isLB a u + evc hQ.isLB a v := by
      intro Z a u v
      rw [← evc_swap hQ.isLB hs, ← evc_swap hQ.isLB hs, ← evc_swap hQ.isLB hs]
      exact (isAdditive_iff hs).1 hadd Z u v a
    have pow2 : ∀ (Z : Over Y) (a : Z ⟶ A) (u : Z ⟶ D) (n : ℕ),
        evc hQ.isLB a (u ^ n) = n • evc hQ.isLB a u := by
      intro Z a u n
      induction n with
      | zero => rw [pow_zero, zero_smul]; exact evc_one_right hQ.isLB hQ.zero a
      | succ n ih => rw [pow_succ, add2, ih, succ_nsmul]
    have ep : (𝟙 W ≫ snd AU AU ≫ y) ^ k = snd AU AU ≫ mulN AU k ≫ y := by
      rw [Category.id_comp, ← MonObj.comp_pow, GlobalTheory.MulFlatSurj.mulN_eq_pow, MonObj.pow_comp, Category.id_comp]
    have e1 : cls P hP = CechPic.pull (𝟙 W : W ⟶ W).left (cls P hP) := by rw [Over.id_left, pull_id]
    refine (cls_eq_iff (pull_isLB hM _) (isLB_lbPow hP k)).1 ?_
    rw [cls_lbPow hP, e1, key, ← pow2, ← map_pow, cls_pull hM, pull_comp, ← cls_pull hM c (pull_isLB hM c),
      (cls_eq_iff (pull_isLB hM c) (pull_isLB hQ.isLB _)).2 hiso, cls_pull hQ.isLB, evc, ← pull_comp]
    congr 2
    apply left_ext
    · rw [Category.assoc, lift_left_fst, lift_left_fst, push_left, hsq.1, Category.id_comp]
    · rw [Category.assoc, lift_left_snd, lift_left_snd, push_left, ep, Over.comp_left, Over.comp_left,
        Category.assoc, hyk, ← Category.assoc, hsq.2, Category.assoc]

theorem exists_birigid_kth_root : ∀ (Y : Scheme.{0}) (A D : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj D] (Q : LB (A ⊗ D).left) (h : A ⟶ D) (k : ℕ) (X : Scheme.{0}) (M : LB X) (c : (A ⊗ A).left ⟶ X), IsAbelianScheme A → IsAbelianScheme D → GlobalTheory.AbDual.IsDual A D Q → GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) → IsMonHom h → 0 < k → IsUnit (k : Γ(Y, ⊤)) → M.IsLB → LBIso (M.pull c) (Q.pull (lift (fst A A) (snd A A ≫ h)).left) → ∀ (U : Scheme.{0}) (t : U ⟶ Y) (AU : Over U) [GrpObj AU] [IsCommMonObj AU] (φ : AU.left ⟶ A.left) (φ₂ : (G2 AU).left ⟶ (G2 A).left), IsGrpPullback AU A t φ → IsSquare φ φ₂ → (∀ (T : Over Y) (s : T.left ⟶ U), s ≫ t = T.hom → ∀ a : T ⟶ A, a ^ k = 1 → a ≫ h = 1) → ∃ P : LB (G2 AU).left, P.IsLB ∧ (∃ t : (P.pull (lift (1 : AU ⟶ AU) (𝟙 AU)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (𝟙 AU) (1 : AU ⟶ AU)).left).Gen, t.IsGen) ∧ LBIso (M.pull (φ₂ ≫ c)) (lbPow P k) := by
  intro Y A D _ _ _ Q h k X M c hA hD hQ hadd hh hk hku hM hiso U t AU _ _ φ φ₂ hpb hsq hker
  obtain ⟨y, hy, hyk⟩ := exists_descent_mulN Y A D h k U t AU φ hA hh hk hpb hker
  exact exists_birigid_root_of_descent Y A D Q h k X M c hQ hadd hM hiso U t AU φ φ₂ hpb hsq y hy hyk

end GlobalTheory.KthRoot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirigidifiedKthRootPullbackBundleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

open scoped CategoryTheory.Obj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_birigidified_kth_root_pullback_bundle : ∀ (Y : Scheme.{0}) (A D : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj D] (Q : LB (A ⊗ D).left) (h : A ⟶ D) (k : ℕ) (X : Scheme.{0}) (M : LB X) (c : (A ⊗ A).left ⟶ X), IsAbelianScheme A → IsAbelianScheme D → GlobalTheory.AbDual.IsDual A D Q → GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) → IsMonHom h → 0 < k → IsUnit (k : Γ(Y, ⊤)) → M.IsLB → LBIso (M.pull c) (Q.pull (lift (fst A A) (snd A A ≫ h)).left) → ∀ (U : Scheme.{0}) (t : U ⟶ Y) (AU : Over U) [GrpObj AU] [IsCommMonObj AU] (φ : AU.left ⟶ A.left) (φ₂ : (G2 AU).left ⟶ (G2 A).left), IsGrpPullback AU A t φ → IsSquare φ φ₂ → (∀ (T : Over Y) (s : T.left ⟶ U), s ≫ t = T.hom → ∀ a : T ⟶ A, a ^ k = 1 → a ≫ h = 1) → ∃ P : LB (G2 AU).left, P.IsLB ∧ (∃ t : (P.pull (lift (1 : AU ⟶ AU) (𝟙 AU)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (𝟙 AU) (1 : AU ⟶ AU)).left).Gen, t.IsGen) ∧ LBIso (M.pull (φ₂ ≫ c)) (lbPow P k) := by
  first | (exact @GlobalTheory.KthRoot.exists_birigid_kth_root) | (exact GlobalTheory.KthRoot.exists_birigid_kth_root) | (intros; apply GlobalTheory.KthRoot.exists_birigid_kth_root <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackMapSemiAbelianNormalDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackMapSemiAbelianNormalDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.SemiAbDesc.exists_grpPullback_map : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] {X S : Scheme.{0}} (j : X ⟶ S) (A : Over X) [GrpObj A] (G : Over S) [GrpObj G] (e : A.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback A G j e → ∀ (G₁ : Over (Sp R)) [GrpObj G₁], IsSemiAbelian G₁ → ∀ (ξ : Sp R ⟶ S) (y : Sp (FractionRing R) ⟶ X), y ≫ j = jK R ≫ ξ → ∀ (B : Over (Sp (FractionRing R))) [GrpObj B] (a : B.left ⟶ G₁.left) (b : B.left ⟶ A.left), IsGrpPullback B G₁ (jK R) a → IsGrpPullback B A y b → ∃ πC : G₁.left ⟶ G.left, IsGrpPullback G₁ G ξ πC ∧ a ≫ πC = b ≫ e := by
  intro R _ _ _ _ X S j A _ G _ e hG hA G₁ _ hG₁ ξ y hyj B _ a b ha hb
  have hBG : IsGrpPullback B G (jK R ≫ ξ) (b ≫ e) := (hb.comp hA).congr hyj rfl
  have hG₂ : IsGrpPullback ((Over.pullback ξ).obj G) G ξ (pullback.fst G.hom ξ) := isGrpPullback_pullback G ξ
  have hsG₂ : IsSemiAbelian ((Over.pullback ξ).obj G) := IsSemiAbelian.pullback ξ G hG
  have hw : (b ≫ e) ≫ G.hom = (B.hom ≫ jK R) ≫ ξ := by rw [hBG.1.w, Category.assoc]
  let i₂ : B.left ⟶ ((Over.pullback ξ).obj G).left := pullback.lift (b ≫ e) (B.hom ≫ jK R) hw
  have hi₂ : i₂ ≫ pullback.fst G.hom ξ = b ≫ e := pullback.lift_fst _ _ _
  have hBG₂ : IsGrpPullback B ((Over.pullback ξ).obj G) (jK R) i₂ :=
    hG₂.cancel (hBG.congr rfl hi₂.symm) (pullback.lift_snd _ _ _)
  have hj : GlobalTheory.IsGenericPointHom (S := Sp R) (ReciprocityTheory.ChartRestriction.G.Out.jK R) := .fractionField R (FractionRing R)
  obtain ⟨_, _⟩ := hj.quasiCompact_and_dominant
  obtain ⟨_, -⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G₁ hG₁
  obtain ⟨-, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian _ hsG₂
  obtain ⟨E, ⟨hE, hEa⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.generic_existsUnique_iso_of_extensions
    (GlobalTheory.IsNormalScheme.pred _) hj hG₁ hsG₂ ha hBG₂
  haveI := hE
  refine ⟨E.hom.left ≫ pullback.fst G.hom ξ, ((isGrpPullback_of_iso E).comp hG₂).congr (Category.id_comp _) rfl, ?_⟩
  rw [← Category.assoc, hEa, hi₂]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackMapSemiAbelianNormalDomainStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_grpPullback_map_semiAbelian_normalDomain : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] {X S : Scheme.{0}} (j : X ⟶ S) (A : Over X) [GrpObj A] (G : Over S) [GrpObj G] (e : A.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback A G j e → ∀ (G₁ : Over (Sp R)) [GrpObj G₁], IsSemiAbelian G₁ → ∀ (ξ : Sp R ⟶ S) (y : Sp (FractionRing R) ⟶ X), y ≫ j = jK R ≫ ξ → ∀ (B : Over (Sp (FractionRing R))) [GrpObj B] (a : B.left ⟶ G₁.left) (b : B.left ⟶ A.left), IsGrpPullback B G₁ (jK R) a → IsGrpPullback B A y b → ∃ πC : G₁.left ⟶ G.left, IsGrpPullback G₁ G ξ πC ∧ a ≫ πC = b ≫ e := by
  first | exact @GlobalTheory.SemiAbDesc.exists_grpPullback_map | exact GlobalTheory.SemiAbDesc.exists_grpPullback_map | (intros; apply GlobalTheory.SemiAbDesc.exists_grpPullback_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFactorsThroughMulN
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB mulN)
open GlobalTheory.PDiv (SpAlg)
open GlobalTheory.DeRham (spOver)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MulNDiv

theorem hom_ext_of_spAlg {R : Type} [CommRing R] {T B : Over (Sp R)} (a b : T ⟶ B)
    (h : ∀ (S : Type) [CommRing S] [Algebra R S] (g : SpAlg R S ⟶ T), g ≫ a = g ≫ b) : a = b := by
  ext1
  apply T.left.affineOpenCover.openCover.hom_ext
  intro j
  let C : CommRingCat := T.left.affineOpenCover.X j
  let φ : CommRingCat.of R ⟶ C := Spec.preimage (T.left.affineOpenCover.f j ≫ T.hom)
  letI : Algebra R C := φ.hom.toAlgebra
  let g : SpAlg R C ⟶ T := Over.homMk (T.left.affineOpenCover.f j) (by
    show _ = Spec.map (CommRingCat.ofHom (algebraMap R C))
    rw [← Spec.map_preimage (T.left.affineOpenCover.f j ≫ T.hom)]
    rfl)
  have := congrArg CommaMorphism.left (h C g)
  simp only [g, Over.comp_left, Over.homMk_left] at this
  exact this

theorem exists_factor_mulN : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B], IsAbelianScheme A → IsAbelianScheme B → ∀ (n : ℕ), 0 < n → ∀ (F : A ⟶ B), IsMonHom F → (∀ (S : Type) [CommRing S] [Algebra R S] (z : SpAlg R S ⟶ A), z ^ n = 1 → z ≫ F = 1) → ∃ f : A ⟶ B, IsMonHom f ∧ F = mulN A n ≫ f := by
  intro R _ A B _ _ hA _ n hn F hF hker
  haveI := hA.comm
  obtain ⟨hfin, hflat, hsurj⟩ := GlobalTheory.T.abelianScheme_mulN_finite_flat_surjective R A hA n hn
  haveI : IsMonHom (mulN A n) := GlobalTheory.MulEtaleDvr.isMonHom_mulN A n
  have hqc : QuasiCompact (mulN A n).left := inferInstance
  have h : ∀ (T : Over (Sp R)) (x : T ⟶ A), x ≫ mulN A n = 1 → x ≫ F = 1 := by
    intro T x hx
    apply hom_ext_of_spAlg
    intro S _ _ g
    have hxn : x ^ n = 1 := by
      rw [← hx, GlobalTheory.MulEtaleDvr.mulN_eq_pow, MonObj.comp_pow, Category.comp_id]
    have hz : (g ≫ x) ^ n = 1 := by
      rw [← MonObj.comp_pow, hxn, MonObj.comp_one]
    rw [← Category.assoc, hker S (g ≫ x) hz, MonObj.comp_one]
  obtain ⟨⟨ψ, hψ, hc⟩, -⟩ := exists_monHom_factor_of_flat_surjective _ A A B (mulN A n) F inferInstance hF
    hflat hsurj hqc h
  exact ⟨ψ, hψ, hc.symm⟩

end GlobalTheory.MulNDiv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTRealise

variable {k : Type} [Field k]

def graphFil (A₀ : Over (Sp k)) [GrpObj A₀] (f : HdR A₀ →ₗ[k] HdR A₀) :
    Submodule (DualNumber k) (Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀) where
  carrier := {d | ∃ x ∈ Fil A₀, ∃ y ∈ Fil A₀, ∀ c : primDR A₀,
    d ((constMor A₀).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f x c + y c)}
  add_mem' := by
    rintro d d' ⟨x, hx, y, hy, e⟩ ⟨x', hx', y', hy', e'⟩
    refine ⟨x + x', add_mem hx hx', y + y', add_mem hy hy', fun c => ?_⟩
    rw [LinearMap.add_apply, e, e']
    ext <;> simp <;> ring
  zero_mem' := ⟨0, zero_mem _, 0, zero_mem _, fun c => by
    rw [LinearMap.zero_apply]
    ext <;> simp⟩
  smul_mem' := by
    rintro r d ⟨x, hx, y, hy, e⟩
    refine ⟨r.fst • x, Submodule.smul_mem _ _ hx, r.fst • y + r.snd • x,
      add_mem (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ hx), fun c => ?_⟩
    rw [LinearMap.smul_apply, e, smul_eq_mul]
    ext <;> simp <;> ring

variable {A₀ : Over (Sp k)} [GrpObj A₀]

theorem mem_graphFil {f : HdR A₀ →ₗ[k] HdR A₀} {d : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀} :
    d ∈ graphFil A₀ f ↔ ∃ x ∈ Fil A₀, ∃ y ∈ Fil A₀, ∀ c : primDR A₀,
      d ((constMor A₀).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f x c + y c) := Iff.rfl

theorem isBC_constMor (hA : IsAbelianScheme A₀) : (constMor A₀).IsBC :=
  GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k k A₀ hA (SqExt.dual k).sq (constMor A₀)

theorem exists_crys (hA : IsAbelianScheme A₀) (u v : HdR A₀) :
    ∃ d : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀, ∀ c : primDR A₀,
      d ((constMor A₀).pull c) = TrivSqZeroExt.inl (u c) + TrivSqZeroExt.inr (v c) := by
  obtain ⟨d₁, h₁⟩ := (isBC_constMor hA).exists u
  obtain ⟨d₂, h₂⟩ := (isBC_constMor hA).exists v
  refine ⟨d₁ + (TrivSqZeroExt.inr (1 : k) : DualNumber k) • d₂, fun c => ?_⟩
  rw [LinearMap.add_apply, LinearMap.smul_apply, h₁ c, h₂ c]
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]


set_option maxHeartbeats 1000000 in
theorem crys_ext (hA : IsAbelianScheme A₀) {d d' : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀}
    (h : ∀ c : primDR A₀, d ((constMor A₀).pull c) = d' ((constMor A₀).pull c)) : d = d' := by
  refine LinearMap.ext fun c' => ?_
  obtain ⟨z, rfl⟩ := (isBC_constMor hA).2 c'
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul x c => rw [liftSemi_tmul, map_smul, map_smul, h c]

def coordOf (g : DualNumber k →ₗ[k] k) (d : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀) : HdR A₀ where
  toFun c := g (d ((constMor A₀).pull c))
  map_add' a b := by rw [map_add (f := _), map_add (f := _), map_add (f := _)]
  map_smul' r a := by
    rw [map_smulₛₗ, map_smul, smul_eq_mul, ← Algebra.smul_def, map_smul]
    rfl

theorem exists_coords (d : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀) :
    ∃ u v : HdR A₀, ∀ c : primDR A₀,
      d ((constMor A₀).pull c) = TrivSqZeroExt.inl (u c) + TrivSqZeroExt.inr (v c) := by
  refine ⟨coordOf (TrivSqZeroExt.fstHom k k k).toLinearMap d, coordOf (TrivSqZeroExt.sndHom k k) d, fun c => ?_⟩
  ext <;> simp [coordOf]

end GlobalTheory.HTRealise
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeNsmulEndomorphismPreservesCompletio
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeNsmulEndomorphismPreservesCompletio
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LKGeo.DenEnd

variable {p : ℕ} [Fact p.Prime]

theorem inAf_mem (D : Datum p) (x : D.La) : inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, x, fun v => by rw [map_one]; exact one_mem _, rfl⟩

theorem smul_mem (D : Datum p) {a : AfP p} (ha : IsIntAf a) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) :
    a • v ∈ LaHat D := by
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, x, hc, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a * c, x, fun w => ?_, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hc w)
    · rw [TensorProduct.smul_tmul', smul_eq_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem exists_nsmul_mem (D : Datum p) (v : AfP p ⊗[ℚ] VQ D) : ∃ d : ℕ, 0 < d ∧ d • v ∈ LaHat D := by
  have hadd : ∀ u w : AfP p ⊗[ℚ] VQ D, (∃ d : ℕ, 0 < d ∧ d • u ∈ LaHat D) → (∃ d : ℕ, 0 < d ∧ d • w ∈ LaHat D) →
      ∃ d : ℕ, 0 < d ∧ d • (u + w) ∈ LaHat D := by
    rintro u w ⟨d, hd, hu⟩ ⟨e, he, hw⟩
    refine ⟨d * e, Nat.mul_pos hd he, ?_⟩
    have : (d * e) • (u + w) = e • (d • u) + d • (e • w) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm e d]
    rw [this]
    exact add_mem (nsmul_mem hu _) (nsmul_mem hw _)
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, by rw [smul_zero]; exact zero_mem _⟩
  | add u w hu hw => exact hadd u w hu hw
  | tmul a w =>
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨1, one_pos, by rw [TensorProduct.tmul_zero, smul_zero]; exact zero_mem _⟩
    | add u w hu hw => rw [TensorProduct.tmul_add]; exact hadd _ _ hu hw
    | tmul q x =>
      obtain ⟨d, hd, h⟩ := GlobalTheory.DenAway.exists_nat_adele (q • a)
      refine ⟨d, hd, AddSubgroup.subset_closure ⟨(d : AfP p) * (q • a), x, h, ?_⟩⟩
      have e : q ⊗ₜ[ℤ] x = q • ((1 : ℚ) ⊗ₜ[ℤ] x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [e, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul', nsmul_eq_mul]

theorem isIntAf_inv : IsIntAf (algebraMap ℚ (AfP p) (p : ℚ)⁻¹) := by
  intro v
  rw [AlgHom.commutes, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.1.valuation ℚ (algebraMap ℤ ℚ (p : ℤ)) = 1 := by
    refine le_antisymm (v.1.valuation_le_one _) (not_lt.1 fun h => v.2 ?_)
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem] at h
    have hm : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp Fact.out).irreducible
    exact (hm.eq_of_le v.1.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 h)).symm
  have h2 : Valued.v (algebraMap ℚ (v.1.adicCompletion ℚ) (p : ℚ)⁻¹) = v.1.valuation ℚ (p : ℚ)⁻¹ :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v.1 _
  rw [h2, map_inv₀]
  simp only [eq_intCast, Int.cast_natCast] at h1
  rw [h1, inv_one]

theorem exists_coprime_nsmul_mem (D : Datum p) (v : AfP p ⊗[ℚ] VQ D) :
    ∃ t : ℕ, 0 < t ∧ t.Coprime p ∧ t • v ∈ LaHat D := by
  obtain ⟨d, hd, h⟩ := exists_nsmul_mem D v
  obtain ⟨k, t, ht, hdt⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd.ne' p (Fact.out : p.Prime).ne_one
  have ht0 : 0 < t := Nat.pos_of_ne_zero fun h => ht (h ▸ dvd_zero p)
  refine ⟨t, ht0, ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 ht).symm, ?_⟩
  have hint : IsIntAf (algebraMap ℚ (AfP p) (p : ℚ)⁻¹ ^ k) := fun u => by
    rw [map_pow]; exact pow_mem (isIntAf_inv u) k
  have hm := smul_mem D hint h
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  convert hm using 1
  rw [hdt, ← map_pow, algebraMap_smul, ← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  congr 1
  push_cast
  rw [inv_pow, ← _root_.mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hp), _root_.one_mul]

theorem exists_coprime_nsmul_map_mem : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p)
    (A : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)), ∃ j : ℕ, 0 < j ∧ j.Coprime p ∧ ∀ v ∈ LaHat D, j • A v ∈ LaHat D := by
  intro p _ D A
  have := D.freeLa
  have := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  choose t ht0 htc ht using fun i => exists_coprime_nsmul_mem D (A (inAf D (b i)))
  refine ⟨∏ i, t i, Finset.prod_pos fun i _ => ht0 i, Nat.Coprime.prod_left fun i _ => htc i, ?_⟩
  have hbase : ∀ x : D.La, (∏ i, t i) • A (inAf D x) ∈ LaHat D := by
    intro x
    have hx : x ∈ Submodule.span ℤ (Set.range b) := by rw [b.span_eq]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem t (Finset.mem_univ i)
      rw [hk, mul_comm, mul_smul]
      exact nsmul_mem (ht i) k
    | zero =>
      have : inAf D 0 = 0 := by simp [inAf]
      rw [this, map_zero, smul_zero]; exact zero_mem _
    | add y z _ _ hy hz =>
      have : inAf D (y + z) = inAf D y + inAf D z := by simp only [inAf, TensorProduct.tmul_add]
      rw [this, map_add (f := _), smul_add]; exact add_mem hy hz
    | smul c y _ hy =>
      have : inAf D (c • y) = c • inAf D y := by
        simp only [inAf, TensorProduct.tmul_smul]
      rw [this, map_zsmul, smul_comm]; exact zsmul_mem hy c
  intro v hv
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, x, ha, rfl⟩ := hz
    have e : a ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x) = a • inAf D x := by
      rw [inAf, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [e, map_smul, smul_comm]
    exact smul_mem D ha (hbase x)
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _), smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg, smul_neg]; exact neg_mem hx

end GlobalTheory.LKGeo.DenEnd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeNsmulEndomorphismPreservesCompletioStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coprime_nsmul_endomorphism_preserves_completion : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (A : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)), ∃ j : ℕ, 0 < j ∧ j.Coprime p ∧ ∀ v ∈ LaHat D, j • A v ∈ LaHat D := by
  first | (exact @GlobalTheory.LKGeo.DenEnd.exists_coprime_nsmul_map_mem) | (exact GlobalTheory.LKGeo.DenEnd.exists_coprime_nsmul_map_mem) | (intros; apply GlobalTheory.LKGeo.DenEnd.exists_coprime_nsmul_map_mem  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleArchimedeanConstant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ReadMatch

theorem gbig_and {Q1 Q2 Q : GlobalTheory.SqTop.GP} (h1 : GlobalTheory.SqTop.GBig Q1) (h2 : GlobalTheory.SqTop.GBig Q2)
    (h : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q1 G μ₀ C x b → Q2 G μ₀ C x b → Q G μ₀ C x b) : GlobalTheory.SqTop.GBig Q := by
  obtain ⟨A1, h1⟩ := h1
  obtain ⟨A2, h2⟩ := h2
  refine ⟨max A1 A2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, h1⟩ := h1 ε CF (le_of_max_le_left hCF)
  obtain ⟨C2, x2, h2⟩ := h2 ε CF (le_of_max_le_right hCF)
  refine ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hR T Lc μ₀ hL G => h G μ₀ C _ _
    (h1 C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ₀ hL G)
    (h2 C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ₀ hL G)⟩

end GlobalTheory.ReadMatch
end
end
