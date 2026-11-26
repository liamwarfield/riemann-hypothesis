module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProof
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFramedPointOfArcBaseChange
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TestPointValueEqConstMulReading
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartBase

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsObjMapOfCoprime
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.CoverExp

open GlobalTheory.UnifPoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}

theorem exists_sabMap_types {D D₁ D₂ : Datum H}
    {l : Level H} {b : Base l ℂ} {s : Sp ℂ ⟶ Sp ℂ} (o₁ o₂ : Obj D l b s)
    {ty₁ ty₂ : Fin g → (E →+* ℂ)} {P₁ : D₁.La →+ (Fin g → ℂ)} {P₂ : D₂.La →+ (Fin g → ℂ)} (hP₁ : IsPeriod D₁ ty₁ P₁)
    (hP₂ : IsPeriod D₂ ty₂ P₂) {e₁ : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ o₁.t.G)}
    {e₂ : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ o₂.t.G)} (a₁ : ∀ z w, e₁ (z + w) = e₁ z * e₁ w)
    (s₁ : Function.Surjective e₁) (s₂ : Function.Surjective e₂)
    (r₁ : ReadsPeriods o₁.t unitOn D₁ ty₁ P₁ e₁) (r₂ : ReadsPeriods o₂.t unitOn D₂ ty₂ P₂ e₂)
    (u₁ : ∀ (g₀ : ℕ) (u : HolUnif o₁.t.G o₁.t.PP.L g₀),
      ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e₁ (h z) = u.ex z)
    (u₂ : ∀ (g₀ : ℕ) (u : HolUnif o₂.t.G o₂.t.PP.L g₀),
      ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e₂ (h z) = u.ex z)
    (gam : D₁.La ≃ₗ[𝓞 E] D₂.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hEF : ∀ a b, D₂.EF (gam a) (gam b) = D₁.EF a b) (hh : ∀ a, P₂ (gam a) = h (P₁ a)) :
    ∃ m : SABMap o₁.t o₂.t (𝟙 _), ∀ z, (e₁ z).left ≫ m.φ = (e₂ (h z)).left := by
  have hT := GlobalTheory.ArcCM.known_holds.theta
  have hL := GlobalTheory.ArcCM.known_holds.laws
  have hG := hL.globalFns
  have hA : HomAlg := GlobalTheory.exists_isMonHom_of_map_lattice hT hL
  have hD : WeilDet := GlobalTheory.T.lambdaBundleIso_of_primeToP_weilPairings hL
  have p₁ := GlobalTheory.obj_isAbelianScheme_dim_rigidified_sym E H D l _ _ _ _ o₁
  have p₂ := GlobalTheory.obj_isAbelianScheme_dim_rigidified_sym E H D l _ _ _ _ o₂
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
  have hcomm : ∀ (a : 𝓞 E) z, h (fun k => ty₁ k (a : E) * z k) = fun k => ty₂ k (a : E) * h z k := fun a z => by
    have k : (h.toLinearMap.restrictScalars ℝ) ∘ₗ LinearMap.mulLeft ℝ (fun k => ty₁ k (a : E)) =
        LinearMap.mulLeft ℝ (fun k => ty₂ k (a : E)) ∘ₗ (h.toLinearMap.restrictScalars ℝ) := by
      refine LinearMap.ext_on_range hP₁.2.2.2.1 fun x => ?_
      show h (fun k => ty₁ k (a : E) * P₁ x k) = fun k => ty₂ k (a : E) * h (P₁ x) k
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

theorem exists_objMap_of_coprime {D : Datum H} {l : Level H} (hA : l.A = 1) {B : Type} [CommRing B] {b : Base l B}
    {S : Scheme.{0}} {s : S ⟶ Sp B} (o₁ o₂ : Obj D l b s) (m : SABMap o₁.t o₂.t (𝟙 S)) (J : Ideal (𝓞 E))
    (hJ : l.Mb ⊔ J = ⊤)
    (h₁ : ∀ a ∈ J • (⊤ : Submodule (𝓞 E) D.La), (o₁.eta a).left ≫ m.φ = (o₂.eta a).left)
    (h₂ : (1 : 𝟙_ (Over S) ⟶ o₁.t.G).left ≫ m.φ = (1 : 𝟙_ (Over S) ⟶ o₂.t.G).left) :
    ∃ n : ObjMap o₁ o₂ (𝟙 S), n.toSABMap.φ = m.φ := by
  refine ⟨⟨m, fun a => ?_, fun a => ?_⟩, rfl⟩
  · have ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) ⊔ J • (⊤ : Submodule (𝓞 E) D.La) := by
      rw [← Submodule.sup_smul, hJ, Submodule.top_smul]
      trivial
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 ha
    rw [o₁.eta_add, o₂.eta_add, o₁.eta_ker x hx, o₂.eta_ker x hx, _root_.one_mul, _root_.one_mul]
    exact (h₁ y hy).trans (Category.id_comp _).symm
  · have c₁ := o₁.etaA_ker a
    have c₂ := o₂.etaA_ker a
    rw [hA, one_smul] at c₁ c₂
    rw [c₁, c₂]
    exact h₂.trans (Category.id_comp _).symm

theorem phi_eq_of_point_eq {D : Datum H} {l : Level H} {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B}
    {b' : Base l B'} {S : Scheme.{0}} {s : S ⟶ Sp B} {s' : Sp ℂ ⟶ Sp B'}
    {o : Obj D l b s} {o₁ : Obj D l b' s'} {y y' : Sp ℂ ⟶ S} (h : y' = y) (m : ObjMap o₁ o y)
    (m' : ObjMap o₁ o y') : m'.toSABMap.φ = m.toSABMap.φ := by
  subst h
  exact objMap_unique_of_field GlobalTheory.ArcCM.known_holds.laws.serre m' m

theorem isExp_family {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {ty : Fin g → (E →+* ℂ)}
    (F : FamilyUnif Xo σ ty) (i : Fin F.n) {P : (F.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di i) ty P) :
    GlobalTheory.UnifPoint.IsExp (F.ex i P) :=
  ⟨F.ex_add i P hP, F.ex_onto i P hP, GlobalTheory.ArcCM.isHolTo_exp_of_isPeriod F i P hP, (F.ex_diff i P hP).1,
    (F.ex_diff i P hP).2⟩

theorem pow_of_add {V Q : Type} [AddCommGroup V] [Group Q] {e : V → Q} (he : ∀ z w, e (z + w) = e z * e w) (n : ℕ)
    (z : V) : e (n • z) = e z ^ n := by
  induction n with
  | zero =>
    have := he 0 0
    rw [add_zero] at this
    rw [zero_smul, pow_zero]
    exact left_eq_mul.1 this
  | succ n ih => rw [succ_nsmul, he, ih, pow_succ]

theorem ex_comp_eq {D : Datum H} {l l₂ : Level H} {Xo : Moduli D l} {Xo₂ : Moduli D l₂} {r : Xo₂.X ⟶ Xo.X}
    (m : SABMap Xo₂.univ.t Xo.univ.t r) (pd : ℕ) (hA : l.A = 1) (hM : l₂.M = l.M * pd) (hle : l₂.Mb ≤ l.Mb)
    (heta : ∀ a, (Xo₂.univ.eta a ^ pd).left ≫ m.φ = r ≫ (Xo.univ.eta a).left)
    {σ : KA l →+* ℂ} {σ₂ : KA l₂ →+* ℂ} {ty ty₂ : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty)
    (F₂ : FamilyUnif Xo₂ σ₂ ty₂) (k : Fin F.n) (k₂ : Fin F₂.n) {P : (F.Di k).La →+ (Fin g → ℂ)}
    {P₂ : (F₂.Di k₂).La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di k) ty P) (hP₂ : IsPeriod (F₂.Di k₂) ty₂ P₂)
    (hy : (F₂.u k₂ P₂ ≫ r) ≫ Xo.s = spMap σ)
    (gam : (F₂.Di k₂).La ≃ₗ[𝓞 E] (F.Di k).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hEF : ∀ a b, (F.Di k).EF (gam a) (gam b) = (F₂.Di k₂).EF a b)
    (gM : ∀ a ∈ l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      ∃ x, gam (F₂.t k₂ a) = F.t k a + l.M • x)
    (hh : ∀ a, P (gam a) = h (P₂ a)) :
    F₂.u k₂ P₂ ≫ r = F.u k P ∧ ∀ z, (F₂.ex k₂ P₂ z).left ≫ m.φ = (F.ex k P (h z)).left := by
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hp0 : pd ≠ 0 := fun h0 => by
    have := l₂.three_le
    rw [hM, h0] at this
    omega
  have hy' := F.over_σ k P hP
  obtain ⟨o₁, ⟨m₁⟩⟩ := GlobalTheory.obj_pull E H D l _ ℂ (baseKA l) (baseOfEmb σ) σ _ _ Xo.s (𝟙 _) (F₂.u k₂ P₂ ≫ r) rfl rfl
    (hy.trans (Category.id_comp _).symm) Xo.univ
  obtain ⟨o₂, ⟨m₂⟩⟩ := GlobalTheory.obj_pull E H D l _ ℂ (baseKA l) (baseOfEmb σ) σ _ _ Xo.s (𝟙 _) (F.u k P) rfl rfl
    (hy'.trans (Category.id_comp _).symm) Xo.univ
  obtain ⟨n, hn⟩ := (GlobalTheory.sabMap_cancel_and_comp_over E H _ _ _ _ _ _ r _ (F₂.u k₂ P₂) m m₁.toSABMap rfl).1
  obtain ⟨e₁, f₁, a₁, s₁, r₁, u₁⟩ := exists_fibre_unif n hP₂ (isExp_family F₂ k₂ hP₂)
    ⟨F₂.ex_ker k₂ P₂ hP₂, F₂.ex_lin k₂ P₂ hP₂, F₂.ex_weil k₂ P₂ hP₂⟩
  obtain ⟨e₂, f₂, a₂, s₂, r₂, u₂⟩ := exists_fibre_unif m₂.toSABMap hP (isExp_family F k hP)
    ⟨F.ex_ker k P hP, F.ex_lin k P hP, F.ex_weil k P hP⟩
  obtain ⟨w, hw⟩ := exists_sabMap_types o₁ o₂ hP₂ hP a₁ s₁ s₂ r₁ r₂ u₁ u₂ gam h hEF hh
  have hmap : l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.map_mono hle
  obtain ⟨q, hq⟩ := exists_objMap_of_coprime hA o₁ o₂ w (l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))
    (eq_top_iff.2 (l₂.coprime.symm.le.trans (sup_le_sup_right hle _)))
    (fun a ha => by
      have j₂ := F.ex_eta k P hP a (Submodule.smul_mono_left hmap ha)
      have j₁ : toUnit _ ≫ Xo₂.univ.eta a ^ pd = F₂.ex k₂ P₂ ((l.M : ℂ)⁻¹ • P₂ (F₂.t k₂ a)) := by
        rw [MonObj.comp_pow, F₂.ex_eta k₂ P₂ hP₂ a ha, ← pow_of_add (F₂.ex_add k₂ P₂ hP₂), hM,
          ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Nat.cast_mul, mul_inv, mul_left_comm,
          mul_inv_cancel₀ (Nat.cast_ne_zero.2 hp0), _root_.mul_one]
      have c₁ : (o₁.eta a).left = (e₁ ((l.M : ℂ)⁻¹ • P₂ (F₂.t k₂ a))).left := by
        refine m₁.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm)
        refine (m₁.eta a).trans (Eq.trans ?_ (congrArg (_ ≫ ·) hn))
        rw [← Category.assoc (e₁ _).left, f₁, ← j₁, Category.assoc, ← heta]
        exact (Category.assoc _ _ _).symm
      have c₂ : (o₂.eta a).left = (e₂ ((l.M : ℂ)⁻¹ • P (F.t k a))).left :=
        m₂.cart.1.hom_ext ((m₂.eta a).trans ((congrArg (fun q => q.left) j₂).trans (f₂ _).symm))
          ((Over.w _).trans (Over.w _).symm)
      rw [c₁, c₂, hw, map_smul h, ← hh, (div_eq_iff hP.2.1 a₂ r₂.1 hM0 _ _).2 (gM a ha)])
    (by
      have := hw 0
      rwa [map_zero, (r₁.1 0).2 (zero_mem _), (r₂.1 0).2 (zero_mem _)] at this)
  obtain ⟨q', hq'⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₂ o₁).2 (F.u k P)
    (𝟙 _) m₂).1 q
  have hyy : F₂.u k₂ P₂ ≫ r = 𝟙 _ ≫ F.u k P :=
    (GlobalTheory.moduli_rep_of_base GlobalTheory.ObjMaps.id_comp_cancel E H D l Xo ℂ (baseOfEmb σ) σ _ (𝟙 _) o₁ inferInstance rfl
      rfl).unique ⟨hy.trans (Category.id_comp _).symm, ⟨m₁⟩⟩
      ⟨by rw [Category.id_comp, hy', Category.id_comp], ⟨q'⟩⟩
  have hφ := phi_eq_of_point_eq hyy.symm m₁ q'
  refine ⟨hyy.trans (Category.id_comp _), fun z => ?_⟩
  rw [← f₁, ← f₂, ← hw, Category.assoc, Category.assoc, hn, ← hq, ← hq', hφ]

end GlobalTheory.CoverExp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverReadingEqPowMulMovedFrameReading
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.CoverFrameRead

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}


omit [IsCMField E] in
theorem exists_latEquiv (L₁ L₂ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E)
    (h : (L₁ : Set (Fin r → E)) = (γ : Matrix (Fin r) (Fin r) E).mulVec '' (L₂ : Set _)) :
    ∃ f : L₂ ≃ₗ[𝓞 E] L₁, ∀ a, (f a : Fin r → E) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ (a : Fin r → E) := by
  have hli : ∀ v, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  let f : L₂ →ₗ[𝓞 E] L₁ :=
    { toFun := fun a => ⟨(γ : Matrix (Fin r) (Fin r) E) *ᵥ (a : Fin r → E), by
        rw [← SetLike.mem_coe, h]
        exact ⟨a, a.2, rfl⟩⟩
      map_add' := fun a b => Subtype.ext (by simp [Matrix.mulVec_add])
      map_smul' := fun s a => Subtype.ext (by simp [Matrix.mulVec_smul]) }
  refine ⟨LinearEquiv.ofBijective f ⟨fun a b hab => Subtype.ext ?_, fun v => ?_⟩, fun _ => rfl⟩
  · rw [← hli a, ← hli b]
    exact congrArg _ (congrArg Subtype.val hab)
  · have hv : (v : Fin r → E) ∈ (L₁ : Set (Fin r → E)) := v.2
    rw [h] at hv
    obtain ⟨u, hu, e⟩ := hv
    exact ⟨⟨u, hu⟩, Subtype.ext e⟩

theorem perFr_move (X X' : Data E r) (hΨ : ∀ τ, τ ∈ X'.Ψ ↔ τ ∈ X.Ψ) (hp : X'.p0 = X.p0) (hG : X'.Gm = X.Gm)
    (γ : GL (Fin r) E)
    (hγ : ∀ u v, herm X'.Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      herm X.Gm u v) (x : Frame X.Ψ r) (x' : Frame X'.Ψ r)
    (hx : ∀ τ (h : τ ∈ X.Ψ) (h' : τ ∈ X'.Ψ), mat x' ⟨τ, h'⟩ = (γ : Matrix (Fin r) (Fin r) E).map τ * mat x ⟨τ, h⟩)
    (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    perFr X' x' ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i = perFr X x v τ i := by
  have hu : ∀ t : E →+* ℂ, IsUnit ((γ : Matrix (Fin r) (Fin r) E).map t).det := fun t =>
    (Matrix.isUnit_iff_isUnit_det _).1 (γ.isUnit.map t.mapMatrix)
  rw [hG] at hγ
  unfold perFr
  rw [hp, hG]
  by_cases h₁ : τ ∈ X.Ψ
  · rw [dif_pos h₁, dif_pos ((hΨ τ).2 h₁), hx τ h₁, GlobalTheory.PerMove.emb_mulVec, Matrix.mul_inv_rev, Matrix.mulVec_mulVec,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hu _), Matrix.mul_one]
  · rw [dite_eq_right h₁, dite_eq_right (mt (hΨ τ).1 h₁)]
    by_cases h₂ : conjEmb τ ∈ X.Ψ
    · rw [dif_pos h₂, dif_pos ((hΨ _).2 h₂), hx _ h₂]
      simp only [GlobalTheory.PerMove.emb_mulVec, GlobalTheory.PerMove.col_mul, GlobalTheory.PerMove.hermC_unitary _ _ _ hγ]
    · rw [dite_eq_right h₂, dite_eq_right (mt (hΨ _).1 h₂)]

end Lattice

theorem congr_one {G A : Type} [Group G] [CommRing A] {n : ℕ} (f : G →* GL (Fin n) A) (L : AddSubgroup (Fin n → A))
    (M : ℕ) (z : Fin n → A) : ∃ w ∈ L, (f 1).1 *ᵥ z = z + M • w :=
  ⟨0, zero_mem _, by rw [map_one, Units.val_one, Matrix.one_mulVec, smul_zero, add_zero]⟩

theorem congr_of_mul {A : Type} [AddCommGroup A] (L : AddSubgroup A) (M p : ℕ) {x : A}
    (h : ∃ w ∈ L, x = (M * p) • w) : ∃ w ∈ L, x = M • w := by
  obtain ⟨w, hw, e⟩ := h
  exact ⟨p • w, nsmul_mem hw p, e.trans (mul_smul M p w)⟩


set_option maxHeartbeats 1000000 in
theorem move_mark {D : D7} (V : HSp D) {r : ℕ} (hr : V.rank = r) (h γ₁ γ₂ : GA D V) (hγ₁ : γ₁ ∈ GQ V) (hγ₂ : γ₂ ∈ GQ V)
    (L₁ : Submodule (𝓞 D.host.E) (Fin r → D.host.E))
    (hL₁ : (L₁ : Set (Fin r → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ₁ * h) : Set _)) :
    ∃ δ : GL (Fin r) D.host.E,
      (∀ (τ : D.host.E →+* ℂ) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), Formalism.MainNotions.StandardLattice.IsInfEmb τ θ →
        ∀ x : Matrix (Fin r) (Fin r) ℂ,
          Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ (γ₁ * h)) * x =
            (δ : Matrix (Fin r) (Fin r) D.host.E).map τ *
              (Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ (γ₂ * h)) * x)) ∧
      ∀ (M p : ℕ), M ≠ 0 → ∀ (v₁ v₂ : Fin r → D.host.E) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E),
        (∃ w ∈ latGHat V (γ₁ * h), finVec V (v₁ ∘ Fin.cast hr) - (finHom V (γ₁ * h)).1.mulVec z = M • w) →
        (∃ w ∈ latGHat V (γ₂ * h), finVec V (v₂ ∘ Fin.cast hr) - (finHom V (γ₂ * h)).1.mulVec z = (M * p) • w) →
        ∃ u ∈ L₁, (δ : Matrix (Fin r) (Fin r) D.host.E) *ᵥ v₂ = v₁ + M • u := by
  subst hr
  have hre : ∀ m : Matrix (Fin V.rank) (Fin V.rank) ℂ,
      Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr rfl) m = m := fun m => by
    ext i j
    rfl
  obtain ⟨δ, -, hδf, hδa⟩ := GlobalTheory.MarkCoset.rational_matrix V _ (mul_mem hγ₁ (inv_mem hγ₂))
  have hmem : ∀ v, v ∈ L₁ ↔ finVec V v ∈ latGHat V (γ₁ * h) := fun v => by
    rw [← (GlobalTheory.MarkCoset.latG_spec D V _).1, ← SetLike.mem_coe, hL₁]
    exact Set.ext_iff.1 (Set.image_id _) v
  refine ⟨δ, fun τ θ hθ x => ?_, fun M p hM v₁ v₂ z h₁ h₂ => ?_⟩
  · have hmul : ∀ a b : GA D V, archM V θ (a * b) = archM V θ a * archM V θ b := by
      intro a b
      rw [archM, archM, archM, map_mul, Units.val_mul, Matrix.map_mul]
    have e : γ₁ * h = γ₁ * γ₂⁻¹ * (γ₂ * h) := by group
    rw [hre, hre, e, hmul, hδa _ _ hθ, Matrix.mul_assoc]
  · have hprod : γ₁ * γ₂⁻¹ * (γ₂ * h) * 1 = γ₁ * h := by group
    obtain ⟨-, ht⟩ := GlobalTheory.ShortMoveIso.transport (finHom V) (latGHat V)
      (fun g => (GlobalTheory.MarkCoset.latG_spec D V g).2) M (γ₁ * γ₂⁻¹) (γ₂ * h) 1 rfl
    rw [hprod] at ht
    obtain ⟨y, hy, e⟩ := ht (finVec V v₂) (finVec V v₁) z z (congr_one _ _ M z) (congr_of_mul _ M p h₂) h₁
    obtain ⟨w, hw, e'⟩ := GlobalTheory.MarkCoset.finVec_div V M hM (δ.1 *ᵥ v₂ - v₁) y (by
      rw [← e, hδf]
      funext i
      exact TensorProduct.tmul_sub _ _ _)
    exact ⟨w, (hmem w).2 (hw ▸ hy), sub_eq_iff_eq_add'.1 e'⟩

section Geo

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

theorem point_over (d : DeltaDat Xo c n) (hd : d.IsLev) (hpq : Dw.p ≠ Dw.q) (hA : l.A = 1) (hle : KA l ≤ KA d.l₂)
    {σ : KA l →+* ℂ} {σ₂ : KA d.l₂ →+* ℂ} (hσ : σ₂.comp (IntermediateField.inclusion hle).toRingHom = σ)
    {ι : Type} {g g₂ : ℕ} (e : Fin g ≃ ι) (e₂ : Fin g₂ ≃ ι) {ty : Fin g → (E →+* ℂ)} {ty₂ : Fin g₂ → (E →+* ℂ)}
    (F : FamilyUnif Xo σ ty) (F₂ : FamilyUnif d.Xo₂ σ₂ ty₂) (k : Fin F.n) (k₂ : Fin F₂.n)
    {P : (F.Di k).La →+ (Fin g → ℂ)} {P₂ : (F₂.Di k₂).La →+ (Fin g₂ → ℂ)} (hP : IsPeriod (F.Di k) ty P)
    (hP₂ : IsPeriod (F₂.Di k₂) ty₂ P₂) (gam : (F₂.Di k₂).La ≃ₗ[𝓞 E] (F.Di k).La)
    (hEF : ∀ a b, (F.Di k).EF (gam a) (gam b) = (F₂.Di k₂).EF a b)
    (gM : ∀ a ∈ d.l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
      ∃ x, gam (F₂.t k₂ a) = F.t k a + l.M • x)
    (hh : ∀ a j, P (gam a) j = P₂ a (e₂.symm (e j))) :
    F₂.u k₂ P₂ ≫ d.r = F.u k P ∧ ∀ (ℓ : ι) v v₂,
      IsDerivAt0 (fun z => (F.ex k P z).left) (Pi.single (e.symm ℓ) 1) v →
      IsDerivAt0 (fun z => (F₂.ex k₂ P₂ z).left) (Pi.single (e₂.symm ℓ) 1) v₂ → v₂ ≫ d.m.φ = v := by
  obtain rfl : g₂ = g := by simpa using Fintype.card_congr (e₂.trans e.symm)
  have hy : (F₂.u k₂ P₂ ≫ d.r) ≫ Xo.s = spMap σ := by
    rw [Category.assoc, GlobalTheory.ClsVal.Cmp.point_over_of_ne hpq hA d hle, ← Category.assoc, F₂.over_σ k₂ P₂ hP₂,
      GlobalTheory.ClsVal.Cmp.spMap_comp', hσ]
  let h : (Fin g₂ → ℂ) ≃ₗ[ℂ] (Fin g₂ → ℂ) := LinearEquiv.funCongrLeft ℂ ℂ (e.trans e₂.symm)
  obtain ⟨h₁, h₂⟩ := GlobalTheory.CoverExp.ex_comp_eq d.m d.pd hA hd.2.1 hd.1.2.1 hd.2.2.2.2.2.1.1 F F₂ k k₂ hP hP₂ hy gam h
    hEF gM fun a => funext (hh a)
  refine ⟨h₁, fun ℓ v v₂ hv hv₂ => ?_⟩
  have k₁ := GlobalTheory.FibreDeriv.isDerivAt0_comp hv₂ d.m.φ
  simp only [h₂] at k₁
  have k₂ := (GlobalTheory.ExpChain.isDerivAt0_comp_linear _ (GlobalTheory.ExpChain.isHolTo_ex F k P hP) h.toLinearMap _ _).1 k₁
  have k₃ : h.toLinearMap (Pi.single (e₂.symm ℓ) 1) = Pi.single (e.symm ℓ) 1 := by
    funext j
    change (Pi.single (e₂.symm ℓ) 1 : Fin g₂ → ℂ) (e₂.symm (e j)) = _
    rw [Pi.single_apply, Pi.single_apply]
    exact if_congr (e₂.symm.apply_eq_iff_eq.trans e.eq_symm_apply.symm) rfl rfl
  rw [k₃] at k₂
  exact GlobalTheory.VerticalDeriv.isDerivAt0_unique k₂ hv

theorem wchar_generator {S : Type} [CommRing S] (a : (E →+* ℂ) × ℕ → ℕ) (m : ℕ) (t : Sˣ) :
    wchar (ex Dw a m) (fun i => Option.elim i t (fun _ => 1)) = (t : S) ^ m := by
  simp [wchar, Fintype.prod_option, ex]

end Geo

section Read

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi

theorem read_of_over {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (C : Cover T j σ)
    (hσ : C.σ₂.comp C.inc = σ) (y : FrPt (T.Q.Xo j) T.Q.c (CAt σ)) (y₂ : FrPt C.d.Xo₂ C.d.c₂ (CAt C.σ₂))
    (hx : y₂.x ≫ C.d.r = y.x) (hu : ∀ τ i, y₂.u τ i ≫ C.d.m.φ = y.u τ i) :
    ∃ t : ℂ, t ≠ 0 ∧ ∀ (n : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j), ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n,
      C.IsPull f f₂ → toC (evR C.d.Xo₂ C.d.c₂ f₂ y₂) = t ^ n * toC (evR (T.Q.Xo j) T.Q.c f y) := by
  letI : Field (CAt C.σ₂) := inferInstanceAs (Field ℂ)
  letI : Algebra T.Q.c.F (CAt C.σ₂) := (show T.Q.c.F →+* CAt C.σ₂ from σ).toAlgebra
  letI : Algebra C.c'.F (CAt C.σ₂) :=
    (show C.c'.F →+* CAt C.σ₂ from C.σ₂.comp (C.d.eF : C.c'.F →+* C.d.c₂.F)).toAlgebra
  have hA : AlgOver T.Q.c C.c' C.hle (CAt C.σ₂) := fun a => RingHom.congr_fun hσ a
  have hc : ∀ x : C.c'.F, algebraMap C.d.c₂.F (CAt C.σ₂) (C.d.eF x) = algebraMap C.c'.F (CAt C.σ₂) x := fun _ => rfl
  let y₀ : FrPt (T.Q.Xo j) T.Q.c (CAt C.σ₂) := y
  obtain ⟨z, hz, ho⟩ := GlobalTheory.FrameLift.exists_frOver C.d hc (y₀.ext C.hle hA) y₂.x hx y₂.x_over
  have hzu : y₂.u = z.u := by
    funext τ i
    refine C.d.m.cart.1.hom_ext ((hu τ i).trans (ho.2.1 τ i).symm) ?_
    rw [(y₂.tan τ i).1, (z.tan τ i).1, hz]
  obtain ⟨t, ht⟩ := GlobalTheory.GeoLevel.exists_frBor_gen z y₂ hz.symm hzu
  refine ⟨toC (t : CAt C.σ₂), t.ne_zero, fun n a f f₂ hf₂ hp => ?_⟩
  have e₁ := GlobalTheory.NonDominant.evR_weight hf₂ ht
  rw [wchar_generator] at e₁
  have e₂ := hp (CAt C.σ₂) hA hc z (y₀.ext C.hle hA) ho
  exact e₁.trans (congrArg (fun s => (t : CAt C.σ₂) ^ n * s) e₂)

end Read


set_option maxHeartbeats 1000000 in
theorem rdU_cover_eq : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (h : GA D (T.V j σ)) (γ : GL (Fin D.R.r) D.host.E), (((T.U j σ).X (T.dict j σ h).1).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h).1).Λ : Set _) → (∀ v w, herm ((T.U j σ).X (T.dict j σ h).1).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h).1).Gm v w) → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat (T.dict j σ h).2 ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h).2 ⟨τ, h₂⟩) → ∀ (x : Frame (C.U₂.X (C.dict₂ h).1).Ψ D.R.r) (x' : Frame ((T.U j σ).X (T.dict j σ h).1).Ψ D.R.r), x ∈ (C.U₂.X (C.dict₂ h).1).dom → x' ∈ ((T.U j σ).X (T.dict j σ h).1).dom → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → ∃ t : ℂ, t ≠ 0 ∧ ∀ n : ℕ, ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → rdU C.U₂ f₂ (C.dict₂ h).1 x = t ^ n * rdU (T.U j σ) f (T.dict j σ h).1 x' := by
  intro D T hT j hj σ hσ C hC h γ hlat hiso hfr x x' hx hx' hxx
  obtain ⟨hr₁, g₁, e₁, F₁, ik₁, φ₁, th₁, -, -, hth₁, ⟨hEF₁, hper₁⟩, hd₁⟩ := hT.adPin j hj σ hσ
  obtain ⟨hlev, hA₂, hσ₂, hU₂, hdom, hr₂, g₂, e₂, F₂, ik₂, φ₂, th₂, hW₂, hth₂, ⟨hEF₂, hper₂⟩, hd₂⟩ := hC
  obtain ⟨hr₀, hW₁⟩ := hT.modelW j hj σ hσ
  have hU₁ := hT.unf j hj σ hσ
  have hA : T.Q.l.A = 1 := hT.pins.2.1.2
  obtain ⟨-, hpq, -, hq⟩ := GlobalTheory.Member.exists_iotaOK D T.Q hT.pins j hj
  obtain ⟨γ₁, hγ₁, hL₁, hm₁, hf₁⟩ := hd₁ h
  obtain ⟨γ₂, hγ₂, -, hm₂, hf₂⟩ := hd₂ h
  have hΨ : ∀ τ, τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ ↔ τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ := fun τ =>
    ((hU₁.2.1 _).2 τ).trans ((hU₂.2.1 _).2 τ).symm
  obtain ⟨δ, hδf, hδm⟩ := move_mark (T.V j σ) hr₁ h γ₁ γ₂ hγ₁ hγ₂ _ hL₁
  have hγδ : (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) = δ := by
    obtain ⟨τ, t₂⟩ : ∃ τ, τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ := by
      by_cases h0 : D.host.φ₀ ∈ (C.U₂.X (C.dict₂ h).1).Ψ
      · exact ⟨_, h0⟩
      · exact ⟨_, not_not.1 (mt ((C.U₂.X (C.dict₂ h).1).cmType _).2 h0)⟩
    have t₁ := (hΨ τ).2 t₂
    have a₂ := hf₂ ⟨τ, t₂⟩
    have a₁ := hf₁ ⟨τ, t₁⟩
    rw [GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (hth₂ _ ⟨τ, t₂⟩) (hth₁ _ ⟨τ, t₁⟩)] at a₂
    have a₃ := a₁.trans ((hδf τ _ (hth₁ _ ⟨τ, t₁⟩) _).trans (congrArg (_ * ·) a₂.symm))
    have a₄ := (hfr τ t₂ t₁).symm.trans a₃
    have hu : IsUnit (mat (C.dict₂ h).2 ⟨τ, t₂⟩) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit (hdom h ⟨τ, t₂⟩).1)
    exact Matrix.map_injective τ.injective (hu.mul_right_cancel a₄)
  obtain ⟨f, hf⟩ := exists_latEquiv _ _ γ hlat
  let gam := (φ₂ (C.dict₂ h).1).trans (f.trans (φ₁ (T.dict j σ h).1).symm)
  have hgam : ∀ a, (φ₁ (T.dict j σ h).1 (gam a) : Fin D.R.r → D.host.E) =
      (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ (φ₂ (C.dict₂ h).1 a : Fin D.R.r → D.host.E) := fun a =>
    (congrArg Subtype.val ((φ₁ (T.dict j σ h).1).apply_symm_apply _)).trans (hf _)
  obtain ⟨P₁, hP₁, hp₁, hu₁, hv₁⟩ := hper₁ _ ⟨x', hx'⟩
  obtain ⟨P₂, hP₂, hp₂, hu₂, hv₂⟩ := hper₂ _ ⟨x, hx⟩
  have hle : KA T.Q.l ≤ KA C.d.l₂ := by rw [KA, KA, hA, hA₂]
  have hrel : ∀ τ : D.host.E →+* ℂ, relab T.Q.c σ τ = relab C.d.c₂ C.σ₂ τ := fun τ => by
    ext a
    exact (RingHom.congr_fun hσ₂ _).symm.trans (congrArg C.σ₂ (Subtype.ext rfl))
  obtain ⟨k₁, k₂⟩ := point_over C.d hlev (by omega) hA hle
    (RingHom.ext fun a => (congrArg C.σ₂ (Subtype.ext rfl)).trans
      (RingHom.congr_fun hσ₂ ((IntermediateField.inclusion T.Q.c.le).toRingHom a)))
    e₁ e₂ F₁ F₂ _ _ hp₁ hp₂ gam
    (fun a b => by
      have := (hEF₁ _ (gam a) (gam b)).trans (Eq.trans (by rw [hgam, hgam, hiso, (hW₁ _).2, (hW₂ _).2])
        (hEF₂ _ a b).symm)
      exact_mod_cast this)
    (fun a ha => by
      have b₂ := hm₂ a ha
      rw [hlev.2.1] at b₂
      obtain ⟨u, hu, e⟩ := hδm T.Q.l.M C.d.pd (by have := T.Q.l.three_le; omega) _ _ _
        (hm₁ a (Submodule.smul_mono_left (Ideal.map_mono hlev.1.2.1) ha)) b₂
      refine ⟨(φ₁ _).symm ⟨u, hu⟩, (φ₁ (T.dict j σ h).1).injective (Subtype.ext ?_)⟩
      rw [hgam, hγδ, e, map_add (f := _), map_nsmul, LinearEquiv.apply_symm_apply]
      rfl)
    (fun a i => by
      rw [hP₁, hP₂, hgam, Equiv.apply_symm_apply, hrel]
      exact perFr_move _ _ hΨ ((hU₁.2.1 _).1.trans (hU₂.2.1 _).1.symm) ((hW₁ _).1.trans (hW₂ _).1.symm) γ hiso x x'
        hxx _ _ _)
  obtain ⟨t, ht, H⟩ := read_of_over C hσ₂ ((T.U j σ).un _ ⟨x', hx'⟩) (C.U₂.un _ ⟨x, hx⟩)
    (by rw [hu₁, hu₂]; exact k₁) fun τ i => k₂ ⟨τ, i⟩ _ _ (hv₁ τ i) (hv₂ τ i)
  refine ⟨t, ht, fun n a _ f _ f₂ hf₂ hp => ?_⟩
  have b₁ : rdU (T.U j σ) f (T.dict j σ h).1 x' = toC (evR (T.Q.Xo j) T.Q.c f ((T.U j σ).un _ ⟨x', hx'⟩)) := dif_pos hx'
  have b₂ : rdU C.U₂ f₂ (C.dict₂ h).1 x = toC (evR C.d.Xo₂ C.d.c₂ f₂ (C.U₂.un _ ⟨x, hx⟩)) := dif_pos hx
  rw [b₁, b₂]
  exact H n a f f₂ hf₂ hp

end GlobalTheory.CoverFrameRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverReadingEqPowMulMovedFrameReadingStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coverReading_eq_pow_mul_movedFrameReading : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (h : GA D (T.V j σ)) (γ : GL (Fin D.R.r) D.host.E), (((T.U j σ).X (T.dict j σ h).1).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h).1).Λ : Set _) → (∀ v w, herm ((T.U j σ).X (T.dict j σ h).1).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h).1).Gm v w) → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat (T.dict j σ h).2 ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h).2 ⟨τ, h₂⟩) → ∀ (x : Frame (C.U₂.X (C.dict₂ h).1).Ψ D.R.r) (x' : Frame ((T.U j σ).X (T.dict j σ h).1).Ψ D.R.r), x ∈ (C.U₂.X (C.dict₂ h).1).dom → x' ∈ ((T.U j σ).X (T.dict j σ h).1).dom → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → ∃ t : ℂ, t ≠ 0 ∧ ∀ n : ℕ, ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → rdU C.U₂ f₂ (C.dict₂ h).1 x = t ^ n * rdU (T.U j σ) f (T.dict j σ h).1 x' := by
  first | exact @GlobalTheory.CoverFrameRead.rdU_cover_eq | exact GlobalTheory.CoverFrameRead.rdU_cover_eq | (intros; apply GlobalTheory.CoverFrameRead.rdU_cover_eq <;> assumption)
end
