module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PointEqIffIsometry
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqIffIsometry
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.UnifPoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}

def HomAlg : Prop :=
  ∀ (P P' : Out.PolAV (Sp ℂ)) (g : ℕ) (u : HolUnif P.A P.L g) (u' : HolUnif P'.A P'.L g)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), P.g = g → P'.g = g → (∀ z ∈ u.Λ, F z ∈ u'.Λ) →
    ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u'.ex (F z) = u.ex z ≫ f

def WeilDet : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (P P' : Out.PolAV (Sp k)) (α : P.A ⟶ P'.A) (p d : ℕ), IsMonHom α →
    p.Prime → CharZero k → (∀ (n : ℕ) (x y : 𝟙_ (Over (Sp k)) ⟶ P.A) (c : kˣ), 0 < n → n.Coprime p → x ^ n = 1 →
      y ^ n = 1 → Out.WeilIs P.A P.L n x y (unitOn c) → Out.WeilIs P'.A P'.L n (x ≫ α) (y ≫ α) (unitOn (c ^ d))) →
    LBIso (abelian₂ P.A (lbPow P.L d)) (abelian₂ P.A (P'.L.pull α.left))

theorem exists_hom (hT : ThetaUnifAV) (hA : HomAlg) (Q Q' : Out.PolAV (Sp ℂ)) (hg : Q'.g = Q.g)
    {e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ Q.A)} {e' : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ Q'.A)}
    (he : ∀ (g₀ : ℕ) (u : HolUnif Q.A Q.L g₀), ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e (h z) = u.ex z)
    (he' : ∀ (g₀ : ℕ) (u : HolUnif Q'.A Q'.L g₀), ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e' (h z) = u.ex z)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hF : ∀ z, e z = 1 → e' (F z) = 1) :
    ∃ α : Q.A ⟶ Q'.A, IsMonHom α ∧ ∀ z, e' (F z) = e z ≫ α := by
  obtain ⟨r, hr⟩ := Q.rigid
  obtain ⟨r', hr'⟩ := Q'.rigid
  obtain ⟨u, -⟩ := hT Q r hr
  obtain ⟨u₁, -⟩ := hT Q' r' hr'
  have u' : HolUnif Q'.A Q'.L Q.g := hg ▸ u₁
  obtain ⟨h, hh⟩ := he _ u
  obtain ⟨h', hh'⟩ := he' _ u'
  obtain ⟨α, hα, hu⟩ := hA Q Q' Q.g u u' (h'.symm.toLinearMap ∘ₗ F ∘ₗ h.toLinearMap) rfl hg fun z hz =>
    (u'.ker _).1 (by
      rw [← hh']
      show e' (h' (h'.symm (F (h z)))) = 1
      rw [h'.apply_symm_apply]
      exact hF _ ((hh z).trans ((u.ker z).2 hz)))
  refine ⟨α, hα, fun z => ?_⟩
  have k := hu (h.symm z)
  rw [← hh', ← hh, h.apply_symm_apply] at k
  rw [← k]
  show _ = e' (h' (h'.symm (F (h (h.symm z)))))
  rw [h'.apply_symm_apply, h.apply_symm_apply]

abbrev objPol {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}
    (o : Obj D l b s) {n : ℕ} (h : IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension n o.t.G.hom ∧
      Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) : Out.PolAV S :=
  { A := o.t.G, isAb := h.1, g := n, smoothDim := h.2.1, L := o.t.PP.L, isLB := o.t.PP.isLB, rigid := h.2.2.1,
    sym := h.2.2.2, ample := o.ample, ktriv := o.ktriv }

theorem exists_sabMap (hT : ThetaUnifAV) (hG : Out.GlobalFnsSt) (hA : HomAlg) (hD : WeilDet) {D D₁ D₂ : Datum H}
    {l : Level H} {b : Base l ℂ} {s : Sp ℂ ⟶ Sp ℂ} (o₁ o₂ : Obj D l b s) {n : ℕ}
    (p₁ : IsAbelianScheme o₁.t.G ∧ SmoothOfRelativeDimension n o₁.t.G.hom ∧
      Out.Rigidified o₁.t.G o₁.t.PP.L ∧ Out.Sym o₁.t.G o₁.t.PP.L)
    (p₂ : IsAbelianScheme o₂.t.G ∧ SmoothOfRelativeDimension n o₂.t.G.hom ∧
      Out.Rigidified o₂.t.G o₂.t.PP.L ∧ Out.Sym o₂.t.G o₂.t.PP.L)
    {ty : Fin g → (E →+* ℂ)} {P₁ : D₁.La →+ (Fin g → ℂ)} {P₂ : D₂.La →+ (Fin g → ℂ)} (hP₁ : IsPeriod D₁ ty P₁)
    (hP₂ : IsPeriod D₂ ty P₂) {e₁ : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ o₁.t.G)}
    {e₂ : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ o₂.t.G)} (a₁ : ∀ z w, e₁ (z + w) = e₁ z * e₁ w)
    (s₁ : Function.Surjective e₁) (s₂ : Function.Surjective e₂)
    (r₁ : ReadsPeriods o₁.t unitOn D₁ ty P₁ e₁) (r₂ : ReadsPeriods o₂.t unitOn D₂ ty P₂ e₂)
    (u₁ : ∀ (g₀ : ℕ) (u : HolUnif o₁.t.G o₁.t.PP.L g₀),
      ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e₁ (h z) = u.ex z)
    (u₂ : ∀ (g₀ : ℕ) (u : HolUnif o₂.t.G o₂.t.PP.L g₀),
      ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e₂ (h z) = u.ex z)
    (gam : D₁.La ≃ₗ[𝓞 E] D₂.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hEF : ∀ a b, D₂.EF (gam a) (gam b) = D₁.EF a b) (hh : ∀ a, P₂ (gam a) = h (P₁ a)) :
    ∃ m : SABMap o₁.t o₂.t (𝟙 _), ∀ z, (e₁ z).left ≫ m.φ = (e₂ (h z)).left := by
  obtain ⟨α, hα, hα'⟩ : ∃ α : o₁.t.G ⟶ o₂.t.G, IsMonHom α ∧ ∀ z, e₂ (h z) = e₁ z ≫ α :=
    exists_hom hT hA (objPol o₁ p₁) (objPol o₂ p₂) rfl u₁ u₂ h.toLinearMap fun z hz => by
      obtain ⟨a, rfl⟩ := (r₁.1 z).1 hz
      exact (r₂.1 _).2 ⟨gam a, hh a⟩
  obtain ⟨β, -, hβ'⟩ : ∃ β : o₂.t.G ⟶ o₁.t.G, IsMonHom β ∧ ∀ z, e₁ (h.symm z) = e₂ z ≫ β :=
    exists_hom hT hA (objPol o₂ p₂) (objPol o₁ p₁) rfl u₂ u₁ h.symm.toLinearMap fun z hz => by
      obtain ⟨a, rfl⟩ := (r₂.1 z).1 hz
      refine (r₁.1 _).2 ⟨gam.symm a, h.injective ?_⟩
      rw [← hh, gam.apply_symm_apply]
      exact (h.apply_symm_apply _).symm
  have := p₁.1.smooth
  have := p₂.1.smooth
  have := p₁.1.proper
  have := p₂.1.proper
  have : IsReduced o₁.t.G.left := isReduced_of_smooth_complex _ o₁.t.G.hom inferInstance
  have : IsReduced o₂.t.G.left := isReduced_of_smooth_complex _ o₂.t.G.hom inferInstance
  let ψ : o₁.t.G ≅ o₂.t.G :=
    { hom := α
      inv := β
      hom_inv_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := s₁ x
        rw [← Category.assoc, ← hα', ← hβ', h.symm_apply_apply, Category.comp_id]
      inv_hom_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := s₂ x
        rw [← Category.assoc, ← hβ', ← hα', h.apply_symm_apply, Category.comp_id] }
  have hcomm : ∀ (a : 𝓞 E) z, h (fun k => ty k (a : E) * z k) = fun k => ty k (a : E) * h z k := fun a z => by
    have k : (h.toLinearMap.restrictScalars ℝ) ∘ₗ LinearMap.mulLeft ℝ (fun k => ty k (a : E)) =
        LinearMap.mulLeft ℝ (fun k => ty k (a : E)) ∘ₗ (h.toLinearMap.restrictScalars ℝ) := by
      refine LinearMap.ext_on_range hP₁.2.2.2.1 fun x => ?_
      show h (fun k => ty k (a : E) * P₁ x k) = fun k => ty k (a : E) * h (P₁ x) k
      rw [← funext (hP₁.1 a x), ← hh, ← hh, map_smul]
      exact funext (hP₂.1 a _)
    exact DFunLike.congr_fun k z
  have hact : ∀ a, o₁.t.act.act a ≫ α = α ≫ o₂.t.act.act a := fun a =>
    ComplexPoints.over_hom_ext_of_complexPoints fun x => by
      obtain ⟨z, rfl⟩ := s₁ x
      rw [← Category.assoc, ← Category.assoc, ← r₁.2.1, ← hα', ← hα', ← r₂.2.1, hcomm]
  have hlam := hD ℂ (objPol o₁ p₁) (objPol o₂ p₂) α 2 1 hα Nat.prime_two inferInstance
    fun k x y c hk _ hx hy hw => by
      obtain ⟨a, rfl⟩ := exists_div_of_pow a₁ s₁ r₁.1 hk hx
      obtain ⟨a', rfl⟩ := exists_div_of_pow a₁ s₁ r₁.1 hk hy
      have w := r₁.2.2 k a a' (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
      obtain rfl := weilIs_unique_fieldPoint _ _ _ o₁.t.PP.isLB ℂ (𝟙 _) k _ _ _ _ hw w
      have w' := r₂.2.2 k (gam a) (gam a') (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
      rw [hh, hh, ← map_smul h, ← map_smul h, hα', hα', hEF] at w'
      rw [pow_one]
      exact w'
  have : IsMonHom ψ.hom := hα
  exact ⟨⟨CubeMap.ofHom α, isGrpPullback_of_iso ψ, rfl, fun a => congrArg (fun z => z.left) (hact a),
    HeckePoint.isPullCubical_of_iso hG p₁.1 α o₁.t.cub o₂.t.cub (HeckePoint.iso_of_lam o₁.t o₂.t α hact hlam)⟩,
    fun z => congrArg (fun q => q.left) (hα' z).symm⟩

theorem exists_objMap {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}}
    {s : S ⟶ Sp B} (o₁ o₂ : Obj D l b s) (m : SABMap o₁.t o₂.t (𝟙 S))
    (h₁ : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      (o₁.eta a).left ≫ m.φ = (o₂.eta a).left)
    (h₂ : ∀ a, (o₁.etaA a).left ≫ m.φ = (o₂.etaA a).left) : Nonempty (ObjMap o₁ o₂ (𝟙 S)) := by
  refine ⟨⟨m, fun a => ?_, fun a => (h₂ a).trans (Category.id_comp _).symm⟩⟩
  have ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) ⊔
      l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) := by
    rw [← Submodule.sup_smul, l.coprime, Submodule.top_smul]
    trivial
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 ha
  rw [o₁.eta_add, o₂.eta_add, o₁.eta_ker x hx, o₂.eta_ker x hx, _root_.one_mul, _root_.one_mul]
  exact (h₁ y hy).trans (Category.id_comp _).symm

def baseOfEmb {l : Level H} (σ : KA l →+* ℂ) : Base l ℂ where
  unit _ hn := IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn.ne')
  ρ := σ (baseKA l).ρ
  ρ_sq := by rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  ζ := σ (baseKA l).ζ
  ζ_prim := (baseKA l).ζ_prim.map_of_injective σ.injective

end GlobalTheory.UnifPoint
end
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.UnifPoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} {g : ℕ}

theorem exists_fibre_unif {t : SAB H S} {y : Sp ℂ ⟶ S} {t₁ : SAB H (Sp ℂ)} (m : SABMap t₁ t y)
    {D : Datum H} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P)
    {e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)} (he : IsExp e) (hr : ReadsPeriods t unitOn D ty P e) :
    ∃ e₁ : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ t₁.G), (∀ z, (e₁ z).left ≫ m.φ = (e z).left) ∧
      (∀ z w, e₁ (z + w) = e₁ z * e₁ w) ∧ Function.Surjective e₁ ∧ ReadsPeriods t₁ unitOn D ty P e₁ ∧
      ∀ (g₀ : ℕ) (u : HolUnif t₁.G t₁.PP.L g₀), ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e₁ (h z) = u.ex z := by
  obtain ⟨β, hβ⟩ := exists_pointEquiv m.cart
  have hiso : LBIso t₁.PP.L (t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  refine ⟨fun z => β.symm (e z), ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    have h1 := hβ (β.symm (e z))
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  · intro z w
    simp only [he.1 z w, map_mul]
  · intro x
    obtain ⟨z, hz⟩ := he.2.1 (β x)
    exact ⟨z, by simp [hz]⟩
  · refine ⟨fun z => ?_, fun a z => ?_, fun k a a₂ c hk hc => ?_⟩
    · rw [MulEquiv.map_eq_one_iff]
      exact hr.1 z
    · apply β.injective
      rw [MulEquiv.apply_symm_apply, hr.2.1 a z]
      apply Over.OverMorphism.ext
      rw [hβ, Over.comp_left, Over.comp_left, Category.assoc, m.act a, ← Category.assoc, ← hβ,
        MulEquiv.apply_symm_apply]
    · have H := hr.2.2 k a a₂ c hk hc
      have hL : t.PP.L.IsLB := t.PP.isLB
      have hL₁ : t₁.PP.L.IsLB := t₁.PP.isLB
      let T : Over (Sp ℂ) := 𝟙_ (Over (Sp ℂ))
      have hy : y = T.hom ≫ y := (Category.id_comp y).symm
      let lift : (Over.mk y ⟶ t.G) → (Over.mk (T.hom ≫ y) ⟶ t.G) := fun x =>
        Over.homMk x.left (by simp [T])
      rw [GlobalTheory.weilIs_grpPullback_of_comm S (Sp ℂ) t.G t₁.G y m.cm.F t.PP.L t₁.PP.L hL hL₁ m.cart hiso T (k : ℤ)
        _ _ (lift (e ((k : ℂ)⁻¹ • P a))) (lift (e ((k : ℂ)⁻¹ • P a₂))) (unitOn c)
        (by rw [← hβ, MulEquiv.apply_symm_apply]; rfl) (by rw [← hβ, MulEquiv.apply_symm_apply]; rfl)]
      exact weilIs_congr hy rfl rfl H
  · intro g₀ u
    have hc : {z | β (u.ex z) = 1}.Countable := by
      have := u.discrete
      have : Countable u.Λ := (TopologicalSpace.separableSpace_iff_countable).mp inferInstance
      have h2 : {z | β (u.ex z) = 1} = (u.Λ : Set (Fin g₀ → ℂ)) := by
        ext z
        simp only [Set.mem_ofPred_eq, MulEquiv.map_eq_one_iff, SetLike.mem_coe]
        exact u.ker z
      rw [h2]
      exact Set.countable_coe_iff.mp this
    have hhol : IsHolTo Set.univ (fun z => (β (u.ex z)).left) := by
      unfold IsHolTo
      intro U f
      have h1 := u.hol (m.cm.F ⁻¹ᵁ U) ((m.cm.F.app U).hom f)
      simp only [hβ, Set.mem_univ, true_and]
      exact h1
    obtain ⟨h, hh⟩ := exists_linearEquiv_of_period hP he hr.1 (e₀ := fun z => β (u.ex z))
      (fun z w => by simp only [u.ex_add, map_mul]) (β.surjective.comp u.ex_onto) hhol hc
    exact ⟨h, fun z => by rw [MulEquiv.symm_apply_eq]; exact hh z⟩

private theorem eq_of_left_comp_sabMap_phi_eq {S : Scheme.{0}} {t₁ : SAB H (Sp ℂ)} {t : SAB H S} {y : Sp ℂ ⟶ S}
    (m : SABMap t₁ t y) {x x' : 𝟙_ (Over (Sp ℂ)) ⟶ t₁.G} (h : x.left ≫ m.φ = x'.left ≫ m.φ) : x = x' := by
  obtain ⟨β, hβ⟩ := exists_pointEquiv m.cart
  apply β.injective
  apply Over.OverMorphism.ext
  rw [hβ, hβ]
  exact h

private theorem comp_left_eq_toUnit_comp_left {X : Scheme.{0}} (y : Sp ℂ ⟶ X) {G : Over X} (s : 𝟙_ (Over X) ⟶ G) :
    y ≫ s.left = (toUnit (Over.mk y) ≫ s).left := by
  rw [Over.comp_left]
  congr 1

theorem point_eq_iff_isometry : ThetaUnifAV → Out.Laws → (∀ (P P' : Out.PolAV (Sp ℂ)) (g : ℕ) (u
    : HolUnif P.A P.L g) (u' : HolUnif P'.A P'.L g) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g →
    ℂ)), P.g = g → P'.g = g → (∀ z ∈ u.Λ, F z ∈ u'.Λ) → ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u'.ex (F
    z) = u.ex z ≫ f) → (∀ (k : Type) [Field k] [IsAlgClosed k] (P P' : Out.PolAV (Sp k)) (α
    : P.A ⟶ P'.A) (p d : ℕ), IsMonHom α → p.Prime → CharZero k → (∀ (n : ℕ) (x y : 𝟙_ (Over (Sp
    k)) ⟶ P.A) (c
    : kˣ), 0 < n → n.Coprime p → x ^ n = 1 → y ^ n = 1 → Out.WeilIs P.A P.L n x y (unitOn
    c) → Out.WeilIs P'.A P'.L n (x ≫ α) (y ≫ α) (unitOn (c ^ d))) → LBIso (abelian₂ P.A (lbPow P.L
    d)) (abelian₂ P.A (P'.L.pull α.left))) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField
    E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b
    : Base l B) (b' : Base l B') (j : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s'
    : S' ⟶ Sp B') (f
    : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap
    o' o f)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l
    : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b'
    : Base l B') (b'' : Base l B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s''
    : S'' ⟶ Sp B'') (o : Obj D l b s) (o' : Obj D l b' s') (o''
    : Obj D l b'' s''), (∃ m : ObjMap o o (𝟙 S), m.toSABMap.φ = 𝟙 _) ∧ ∀ (f : S' ⟶ S) (f'
    : S'' ⟶ S') (m : ObjMap o' o f), (∀ m' : ObjMap o'' o' f', ∃ m'' : ObjMap o'' o (f' ≫
    f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) ∧ (∀ m'' : ObjMap o'' o (f' ≫
    f), ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ)) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B
    : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o
    : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p
    + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo
    : Moduli D l) (B : Type) [CommRing B] (b : Base l B) (j : KA l →+* B) (S : Scheme.{0}) (s
    : S ⟶ Sp B) (o : Obj D l b s), IsReduced S → j (baseKA l).ρ = b.ρ → j (baseKA
    l).ζ = b.ζ → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ f)) → ∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo
    : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA
    l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' D'' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (t'
    : D.La →ₗ[𝓞 E] D''.La) (P : D'.La →+ (Fin g → ℂ)) (P' : D''.La →+ (Fin g → ℂ)) (y y'
    : Sp ℂ ⟶ Xo.X) (e : (Fin g → ℂ) → (Over.mk y ⟶ Xo.univ.t.G)) (e' : (Fin g → ℂ) → (Over.mk y' ⟶
    Xo.univ.t.G)), (y ≫ Xo.s = spMap σ ∧ IsPeriod D' ty P ∧ ((∀ z w, e (z + w) = e z * e w) ∧
    Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧
    (∀ w, ∃! v : epsPt y ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
    (∀ v : epsPt y ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e
    0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) ∧ (∀ z, e z = 1 ↔ z ∈ (P).range) ∧
    (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂
    : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ)
    / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P
    a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = e ((l.M : ℂ)⁻¹ • P (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = e ((l.A : ℂ)⁻¹ • P (t a))) → (y' ≫ Xo.s = spMap σ ∧ IsPeriod
    D'' ty P' ∧ ((∀ z w, e' (z + w) = e' z * e' w) ∧ Function.Surjective e' ∧ IsHolTo Set.univ
    (fun z => (e' z).left) ∧ (∀ w, ∃! v : epsPt y' ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e'
    z).left) w v.left) ∧ (∀ v : epsPt y' ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ
    ℂ).toRingHom ≫ v.left = (e' 0).left → ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left)) ∧
    (∀ z, e' z = 1 ↔ z ∈ (P').range) ∧ (∀ (a : 𝓞 E) z, e' (fun k => ty k (a
    : E) * z k) = e' z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D''.La) (c : ℂˣ), 0 < k → (c
    : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D''.EF a a₂ : ℂ) /
    k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e' ((k : ℂ)⁻¹ • P' a)) (e' ((k : ℂ)⁻¹ • P'
    a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = e' ((l.M : ℂ)⁻¹ • P' (t' a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = e' ((l.A : ℂ)⁻¹ • P' (t' a))) → (y = y' ↔ ∃ (gam : D'.La ≃ₗ[𝓞
    E] D''.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ a b, D''.EF (gam a) (gam
    b) = D'.EF a b) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), ∃ x, gam (t a) = t' a + l.M • x) ∧ (∀ a, ∃ x, gam (t
    a) = t' a + l.A • x) ∧ ∀ a, P' (gam a) = h (P a)) := by
  intro hT hLaws hA hW hBC hComp hAb hMod E _ _ _ H D l Xo σ g ty hpq hρ hty D' D'' t t' P P' y y' e e' hy hy'
  obtain ⟨hys, hP, hexp, hker, hact, hweil, heta, hetaA⟩ := hy
  obtain ⟨hys', hP', hexp', hker', hact', hweil', heta', hetaA'⟩ := hy'
  have hx : IsExp e := hexp
  have hx' : IsExp e' := hexp'
  have hr : ReadsPeriods Xo.univ.t unitOn D' ty P e := ⟨hker, hact, hweil⟩
  have hr' : ReadsPeriods Xo.univ.t unitOn D'' ty P' e' := ⟨hker', hact', hweil'⟩
  have hM : 0 < l.M := by
    have := l.three_le
    omega
  constructor
  · rintro rfl
    obtain ⟨gam, h, hEF, hPh, heh⟩ := exists_isometry hP hP' hx hx' hr hr'
    refine ⟨gam, h, hEF, fun a ha => ?_, fun a => ?_, hPh⟩
    · rw [← div_eq_iff hP'.2.1 hx'.1 hker' hM, ← heta' a ha, heta a ha, ← heh, map_smul, hPh]
    · rw [← div_eq_iff hP'.2.1 hx'.1 hker' l.A_pos, ← hetaA' a, hetaA a, ← heh, map_smul, hPh]
  · rintro ⟨gam, h, hEF, hMl, hAl, hPh⟩
    let b : Base l ℂ := baseOfEmb σ
    obtain ⟨o₁, ⟨m₁⟩⟩ := hBC E H D l (KA l) ℂ (baseKA l) b σ Xo.X (Sp ℂ) Xo.s (𝟙 _) y rfl rfl
      (by simp [hys]) Xo.univ
    obtain ⟨o₂, ⟨m₂⟩⟩ := hBC E H D l (KA l) ℂ (baseKA l) b σ Xo.X (Sp ℂ) Xo.s (𝟙 _) y' rfl rfl
      (by simp [hys']) Xo.univ
    obtain ⟨e₁, he₁, ha₁, hs₁, hr₁, hu₁⟩ := exists_fibre_unif m₁.toSABMap hP hx hr
    obtain ⟨e₂, he₂, ha₂, hs₂, hr₂, hu₂⟩ := exists_fibre_unif m₂.toSABMap hP' hx' hr'
    have p₁ := hAb E H D l ℂ b (Sp ℂ) (𝟙 _) o₁
    have p₂ := hAb E H D l ℂ b (Sp ℂ) (𝟙 _) o₂
    obtain ⟨m, hm⟩ := exists_sabMap hT hLaws.globalFns hA hW o₁ o₂ p₁ p₂ hP hP' ha₁ hs₁ hs₂ hr₁ hr₂ hu₁ hu₂
      gam h hEF hPh
    have shift : ∀ (n : ℕ), 0 < n → ∀ (a : D.La) (x : D''.La), gam (t a) = t' a + n • x →
        e₂ (h ((n : ℂ)⁻¹ • P (t a))) = e₂ ((n : ℂ)⁻¹ • P' (t' a)) := by
      intro n hn a x hgx
      have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      have h1 : e₂ ((n : ℂ)⁻¹ • P' (n • x)) = 1 := by
        rw [hr₂.1, AddMonoidHom.mem_range]
        refine ⟨x, ?_⟩
        rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hn', one_smul]
      rw [map_smul, ← hPh, hgx, map_add (f := _), smul_add, ha₂, h1, _root_.mul_one]
    have eta₁ : ∀ a, o₁.eta a = e₁ ((l.M : ℂ)⁻¹ • P (t a)) ∨
        a ∉ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) := by
      intro a
      by_cases ha : a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La)
      · left
        refine eq_of_left_comp_sabMap_phi_eq m₁.toSABMap ?_
        exact ((m₁.eta a).trans ((comp_left_eq_toUnit_comp_left y _).trans
          (congrArg Over.Hom.left (heta a ha)))).trans (he₁ _).symm
      · exact Or.inr ha
    have eta₂ : ∀ a, o₂.eta a = e₂ ((l.M : ℂ)⁻¹ • P' (t' a)) ∨
        a ∉ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) := by
      intro a
      by_cases ha : a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La)
      · left
        refine eq_of_left_comp_sabMap_phi_eq m₂.toSABMap ?_
        exact ((m₂.eta a).trans ((comp_left_eq_toUnit_comp_left y' _).trans
          (congrArg Over.Hom.left (heta' a ha)))).trans (he₂ _).symm
      · exact Or.inr ha
    have etaA₁ : ∀ a, o₁.etaA a = e₁ ((l.A : ℂ)⁻¹ • P (t a)) := fun a =>
      eq_of_left_comp_sabMap_phi_eq m₁.toSABMap (((m₁.etaA a).trans ((comp_left_eq_toUnit_comp_left y _).trans
        (congrArg Over.Hom.left (hetaA a)))).trans (he₁ _).symm)
    have etaA₂ : ∀ a, o₂.etaA a = e₂ ((l.A : ℂ)⁻¹ • P' (t' a)) := fun a =>
      eq_of_left_comp_sabMap_phi_eq m₂.toSABMap (((m₂.etaA a).trans ((comp_left_eq_toUnit_comp_left y' _).trans
        (congrArg Over.Hom.left (hetaA' a)))).trans (he₂ _).symm)
    obtain ⟨mo⟩ := exists_objMap o₁ o₂ m
      (fun a ha => by
        obtain ⟨x, hgx⟩ := hMl a ha
        rw [(eta₁ a).resolve_right (not_not_intro ha), (eta₂ a).resolve_right (not_not_intro ha), hm,
          shift l.M hM a x hgx])
      (fun a => by
        obtain ⟨x, hgx⟩ := hAl a
        rw [etaA₁ a, etaA₂ a, hm, shift l.A l.A_pos a x hgx])
    obtain ⟨m₃, -⟩ := ((hComp E H D l (KA l) ℂ ℂ (baseKA l) b b Xo.X (Sp ℂ) (Sp ℂ) Xo.s (𝟙 _) (𝟙 _)
      Xo.univ o₂ o₁).2 y' (𝟙 _) m₂).1 mo
    obtain ⟨f₀, -, huniq⟩ := hMod E H D l Xo ℂ b σ (Sp ℂ) (𝟙 _) o₁ inferInstance rfl rfl
    have k₁ := huniq y ⟨by simp [hys], ⟨m₁⟩⟩
    have k₂ := huniq (𝟙 _ ≫ y') ⟨by simp [hys'], ⟨m₃⟩⟩
    rw [Category.id_comp] at k₂
    exact k₁.trans k₂.symm

end GlobalTheory.UnifPoint
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.UnifPoint

theorem point_eq_iff_isometry_closed :
    ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' D'' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (t' : D.La →ₗ[𝓞 E] D''.La) (P : D'.La →+ (Fin g → ℂ)) (P' : D''.La →+ (Fin g → ℂ)) (y y' : Sp ℂ ⟶ Xo.X) (e : (Fin g → ℂ) → (Over.mk y ⟶ Xo.univ.t.G)) (e' : (Fin g → ℂ) → (Over.mk y' ⟶ Xo.univ.t.G)), (y ≫ Xo.s = spMap σ ∧ IsPeriod D' ty P ∧ ((∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ (∀ w, ∃! v : epsPt y ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ (∀ v : epsPt y ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) ∧ (∀ z, e z = 1 ↔ z ∈ (P).range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ Xo.univ.eta a = e ((l.M : ℂ)⁻¹ • P (t a))) ∧ ∀ a, toUnit _ ≫ Xo.univ.etaA a = e ((l.A : ℂ)⁻¹ • P (t a))) → (y' ≫ Xo.s = spMap σ ∧ IsPeriod D'' ty P' ∧ ((∀ z w, e' (z + w) = e' z * e' w) ∧ Function.Surjective e' ∧ IsHolTo Set.univ (fun z => (e' z).left) ∧ (∀ w, ∃! v : epsPt y' ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e' z).left) w v.left) ∧ (∀ v : epsPt y' ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' 0).left → ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left)) ∧ (∀ z, e' z = 1 ↔ z ∈ (P').range) ∧ (∀ (a : 𝓞 E) z, e' (fun k => ty k (a : E) * z k) = e' z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D''.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D''.EF a a₂ : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e' ((k : ℂ)⁻¹ • P' a)) (e' ((k : ℂ)⁻¹ • P' a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ Xo.univ.eta a = e' ((l.M : ℂ)⁻¹ • P' (t' a))) ∧ ∀ a, toUnit _ ≫ Xo.univ.etaA a = e' ((l.A : ℂ)⁻¹ • P' (t' a))) → (y = y' ↔ ∃ (gam : D'.La ≃ₗ[𝓞 E] D''.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ a b, D''.EF (gam a) (gam b) = D'.EF a b) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ x, gam (t a) = t' a + l.M • x) ∧ (∀ a, ∃ x, gam (t a) = t' a + l.A • x) ∧ ∀ a, P' (gam a) = h (P a)) :=
  fun hT hL =>
    point_eq_iff_isometry hT hL (GlobalTheory.exists_isMonHom_of_map_lattice hT hL) (GlobalTheory.T.lambdaBundleIso_of_primeToP_weilPairings hL)
      GlobalTheory.obj_pull GlobalTheory.ObjMaps.id_comp_cancel GlobalTheory.obj_isAbelianScheme_dim_rigidified_sym
      (GlobalTheory.moduli_rep_of_base GlobalTheory.ObjMaps.id_comp_cancel)

end GlobalTheory.UnifPoint
