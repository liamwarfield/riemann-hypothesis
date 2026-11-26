module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLoc

@[expose] public section

section -- merged from ReciprocityTheory.AnalyticForms.RegularLocalRings.SecHomSurjective
namespace ReciprocityTheory.AnForm.R

open AlgebraicGeometry CategoryTheory MvPolynomial

noncomputable section

variable {W : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)}

theorem val_eval₂ {S : Scheme.{0}} (s : S ⟶ Spec (.of ℂ)) [LocallyOfFiniteType s] {U : S.Opens}
    {σ : Type} (u : σ → Γ(S, U)) (F : MvPolynomial σ ℂ) (x : S) (hx : x ∈ U)
    (hc : IsClosed ({x} : Set S)) :
    val s (eval₂ (constSec s U) u F) x hx = eval (fun t => val s (u t) x hx) F := by
  obtain ⟨φ, hφ⟩ := val_ringHom s U x hx hc
  rw [← hφ, eval₂_comp_left]
  have h1 : φ.comp (constSec s U) = RingHom.id ℂ := by
    ext c
    simp only [RingHom.comp_apply, hφ, RingHom.id_apply]
    exact val_const s U x hx hc c
  rw [h1]
  change eval₂ (RingHom.id ℂ) (φ ∘ u) F = eval₂ (RingHom.id ℂ) _ F
  congr 1
  funext t
  exact hφ (u t)

namespace AffPres


set_option backward.isDefEq.respectTransparency false in
theorem secHom_C (P : AffPres sW) (c : ℂ) : P.secHom (C c) = constSec sW P.V c := by
  have key : (Scheme.ΓSpecIso (.of ℂ)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin P.n) ℂ ⧸ P.K)))).appTop ≫
      P.iso.hom.appTop ≫ P.V.topIso.hom =
      (Scheme.ΓSpecIso (.of ℂ)).inv ≫ sW.appLE ⊤ P.V le_top := by
    rw [← Scheme.Hom.comp_appTop_assoc, P.hover, Scheme.Hom.comp_appTop, Category.assoc]
    simp only [Scheme.Hom.appTop, Scheme.Hom.appLE, Scheme.Opens.ι_appTop,
      Scheme.Opens.topIso_hom, ← W.presheaf.map_comp]
    rfl
  have e3 : P.secHom (C c) = ((CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin P.n) ℂ ⧸ P.K))) ≫
      (Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).inv ≫
      P.iso.hom.appTop ≫ P.V.topIso.hom) c := rfl
  rw [e3, Scheme.ΓSpecIso_inv_naturality_assoc, key]
  rfl

theorem secHom_surjective (P : AffPres sW) : Function.Surjective P.secHom := by
  intro a
  have h1 : Function.Surjective P.V.topIso.hom.hom :=
    (ConcreteCategory.bijective_of_isIso P.V.topIso.hom).2
  have h2 : Function.Surjective (P.iso.hom.app ⊤).hom :=
    (ConcreteCategory.bijective_of_isIso (P.iso.hom.app ⊤)).2
  have h3 : Function.Surjective (Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).2
  obtain ⟨a1, rfl⟩ := h1 a
  obtain ⟨a2, rfl⟩ := h2 a1
  obtain ⟨a3, rfl⟩ := h3 a2
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a3
  exact ⟨f, rfl⟩

theorem val_secHom [LocallyOfFiniteType sW] (P : AffPres sW) (y : W) (hy : y ∈ P.V)
    (hc : IsClosed ({y} : Set W)) (f : MvPolynomial (Fin P.n) ℂ) :
    val sW (P.secHom f) y hy = eval (P.coord y hy) f := by
  obtain ⟨φ, hφ⟩ := val_ringHom sW P.V y hy hc
  have hker : ∀ g ∈ ptIdeal (P.coord y hy), val sW (P.secHom g) y hy = 0 := by
    intro g hg
    rw [val_eq_zero_iff sW _ y hy hc, ← Scheme.germ_residue, CommRingCat.comp_apply]
    apply (IsLocalRing.residue_eq_zero_iff _).mpr
    have h2 : P.stalkEquiv y hy hc (W.presheaf.germ P.V y hy (P.secHom g)) ∈
        (IsLocalRing.maximalIdeal (W.presheaf.stalk y)).map (P.stalkEquiv y hy hc) := by
      rw [P.map_maximalIdeal_stalk y hy hc, P.stalkEquiv_germ]
      exact Ideal.mem_map_of_mem _ hg
    obtain ⟨w, hw, hwe⟩ := (Ideal.mem_map_of_equiv _ _).mp h2
    rw [(P.stalkEquiv y hy hc).injective hwe] at hw
    exact hw
  let ψ : MvPolynomial (Fin P.n) ℂ →+* ℂ := φ.comp P.secHom
  have hψ : ∀ g, ψ g = val sW (P.secHom g) y hy := fun g => hφ _
  have hC : ∀ c, ψ (C c) = c := fun c => by
    rw [hψ, secHom_C, val_const sW P.V y hy hc]
  have hX : ∀ j, ψ (MvPolynomial.X j) = P.coord y hy j := fun j => by
    have hm : X j - C (P.coord y hy j) ∈ ptIdeal (P.coord y hy) := by
      simp [ptIdeal, RingHom.mem_ker]
    have := hker _ hm
    rw [← hψ, map_sub, hC, sub_eq_zero] at this
    exact this
  have hext : ψ = MvPolynomial.eval (P.coord y hy) := by
    apply MvPolynomial.ringHom_ext
    · intro c; rw [hC, eval_C]
    · intro j; rw [hX, eval_X]
  rw [← hψ, hext]

end AffPres

theorem exists_ratio_core {S T : Scheme.{0}} (s : S ⟶ Spec (.of ℂ)) (t : T ⟶ Spec (.of ℂ))
    (g : S ⟶ T) (hg : g ≫ t = s) [LocallyOfFiniteType s] [LocallyOfFiniteType t]
    (V : T.Opens) (hV : IsAffineOpen V) {σ : Type} (u : σ → Γ(T, V))
    (hu : ∀ a : Γ(T, V), ∃ F : MvPolynomial σ ℂ, a = eval₂ (constSec t V) u F)
    {ι : Type} [Finite ι] (Ω : S.Opens) (e : ι → Γ(S, Ω)) (x : S) (hxΩ : x ∈ Ω)
    (hxV : g.base x ∈ V) (hc : IsClosed ({x} : Set S))
    (hsurj : Function.Surjective (g.stalkMap x)) :
    ∃ O : S.Opens, x ∈ O ∧ O ≤ Ω ⊓ g ⁻¹ᵁ V ∧
      ∃ (q : MvPolynomial σ ℂ) (F : ι → MvPolynomial σ ℂ),
        eval (fun a => val t (u a) (g.base x) hxV) q ≠ 0 ∧
        ∀ (y : S) (hyΩ : y ∈ Ω) (hyV : g.base y ∈ V), y ∈ O → IsClosed ({y} : Set S) →
          eval (fun a => val t (u a) (g.base y) hyV) q ≠ 0 ∧
          ∀ i, val s (e i) y hyΩ * eval (fun a => val t (u a) (g.base y) hyV) q =
            eval (fun a => val t (u a) (g.base y) hyV) (F i) := by
  classical
  cases nonempty_fintype ι
  let z : V := ⟨g.base x, hxV⟩
  let : Algebra Γ(T, V) (T.presheaf.stalk (g.base x)) :=
    TopCat.Presheaf.algebra_section_stalk T.presheaf z
  have : IsLocalization.AtPrime (T.presheaf.stalk (g.base x)) (hV.primeIdealOf z).asIdeal :=
    hV.isLocalization_stalk z
  have hw : ∀ i, ∃ w : T.presheaf.stalk (g.base x),
      g.stalkMap x w = S.presheaf.germ Ω x hxΩ (e i) := fun i => hsurj _
  choose w hw using hw
  obtain ⟨⟨b, hb⟩, hint⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (hV.primeIdealOf z).asIdeal.primeCompl w
  have hint' : ∀ i, ∃ a : Γ(T, V), algebraMap Γ(T, V) (T.presheaf.stalk (g.base x)) a = b • w i :=
    fun i => hint i
  choose a ha using hint'
  have halg : ∀ c : Γ(T, V), algebraMap Γ(T, V) (T.presheaf.stalk (g.base x)) c =
      T.presheaf.germ V (g.base x) hxV c := fun c => rfl
  have hunit : IsUnit (T.presheaf.germ V (g.base x) hxV b) := by
    rw [← halg]
    exact IsLocalization.map_units (T.presheaf.stalk (g.base x))
      (⟨b, hb⟩ : (hV.primeIdealOf z).asIdeal.primeCompl)
  let Ω' : S.Opens := Ω ⊓ g ⁻¹ᵁ V
  have hΩ'V : Ω' ≤ g ⁻¹ᵁ V := inf_le_right
  have hΩ'Ω : Ω' ≤ Ω := inf_le_left
  have hxΩ' : x ∈ Ω' := ⟨hxΩ, hxV⟩
  have hgerm : ∀ c : Γ(T, V), S.presheaf.germ Ω' x hxΩ' (g.appLE V Ω' hΩ'V c) =
      g.stalkMap x (T.presheaf.germ V (g.base x) hxV c) := by
    intro c
    rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE, CommRingCat.comp_apply,
      TopCat.Presheaf.germ_res_apply]
  have hEq : ∀ i, S.presheaf.germ Ω' x hxΩ'
      (g.appLE V Ω' hΩ'V b * S.presheaf.map (homOfLE hΩ'Ω).op (e i)) =
      S.presheaf.germ Ω' x hxΩ' (g.appLE V Ω' hΩ'V (a i)) := by
    intro i
    rw [map_mul, hgerm, hgerm, TopCat.Presheaf.germ_res_apply, ← hw i, ← map_mul]
    congr 1
    rw [← halg, ← halg, ha i, Algebra.smul_def]
  have hO := fun i => TopCat.Presheaf.germ_eq S.presheaf x hxΩ' hxΩ' _ _ (hEq i)
  choose Oi hxOi iU iV hOi using hO
  obtain ⟨q, hq⟩ := hu b
  choose F hF using fun i => hu (a i)
  let O : S.Opens := (g ⁻¹ᵁ T.basicOpen b) ⊓ Ω' ⊓ Finset.univ.inf Oi
  have hmemO : ∀ y, y ∈ O → y ∈ g ⁻¹ᵁ T.basicOpen b ∧ y ∈ Ω' ∧ ∀ i, y ∈ Oi i := by
    intro y hy
    refine ⟨hy.1.1, hy.1.2, fun i => ?_⟩
    have h2 := hy.2
    rw [TopologicalSpace.Opens.coe_finset_inf, Finset.inf_eq_iInf] at h2
    simp only [Set.iInf_eq_iInter, Set.mem_iInter] at h2
    exact h2 i (Finset.mem_univ i)

  have hne : ∀ (y : S) (hyV : g.base y ∈ V), IsClosed ({y} : Set S) →
      g.base y ∈ T.basicOpen b → eval (fun a => val t (u a) (g.base y) hyV) q ≠ 0 := by
    intro y hyV hcy hyb
    have hcy' := isClosed_image_of_closed s t g hg y hcy
    rw [← val_eval₂ t u q _ hyV hcy', ← hq]
    intro h0
    rw [val_eq_zero_iff t b _ hyV hcy', ← Scheme.germ_residue, CommRingCat.comp_apply] at h0
    have hu' := (T.mem_basicOpen b (g.base y) hyV).mp hyb
    exact (hu'.map (T.residue (g.base y)).hom).ne_zero h0
  refine ⟨O, ?_, fun y hy => (hmemO y hy).2.1, q, F, ?_, ?_⟩
  · refine ⟨⟨?_, hxΩ'⟩, ?_⟩
    · exact (T.mem_basicOpen b (g.base x) hxV).mpr hunit
    · show x ∈ ((Finset.univ.inf Oi : S.Opens) : Set S)
      rw [TopologicalSpace.Opens.coe_finset_inf, Finset.inf_eq_iInf]
      simp only [Set.iInf_eq_iInter, Set.mem_iInter]
      exact fun i _ => hxOi i
  · exact hne x hxV hc ((T.mem_basicOpen b (g.base x) hxV).mpr hunit)
  · intro y hyΩ hyV hyO hcy
    obtain ⟨hyb, hyΩ', hyOi⟩ := hmemO y hyO
    have hcy' := isClosed_image_of_closed s t g hg y hcy
    refine ⟨hne y hyV hcy hyb, fun i => ?_⟩
    obtain ⟨φ, hφ⟩ := val_ringHom s Ω' y hyΩ' hcy
    have h1 := congrArg (fun f => val s f y (hyOi i)) (hOi i)
    simp only at h1
    rw [show iU i = homOfLE (leOfHom (iU i)) from rfl, show iV i = homOfLE (leOfHom (iV i)) from rfl,
      val_restrict, val_restrict, ← hφ, map_mul, hφ, hφ, val_restrict] at h1
    rw [(val_comp s t g hg hΩ'V b y hyΩ' hcy).2, (val_comp s t g hg hΩ'V (a i) y hyΩ' hcy).2] at h1
    have e1 : val t b (g.base y) (hΩ'V hyΩ') = eval (fun a => val t (u a) (g.base y) hyV) q := by
      rw [hq]; exact val_eval₂ t u q _ hyV hcy'
    have e2 : val t (a i) (g.base y) (hΩ'V hyΩ') =
        eval (fun a => val t (u a) (g.base y) hyV) (F i) := by
      rw [hF i]; exact val_eval₂ t u (F i) _ hyV hcy'
    rw [e1, e2] at h1
    rw [mul_comm]
    exact h1

end

end ReciprocityTheory.AnForm.R
end

namespace ReciprocityTheory.AnForm.R

open AlgebraicGeometry CategoryTheory MvPolynomial

noncomputable section

variable {W X : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)} {sX : X ⟶ Spec (.of ℂ)}

theorem isClosed_of_isClosed_open [LocallyOfFiniteType sW] (V : W.Opens) (x : V)
    (hx : IsClosed ({x} : Set V)) : IsClosed ({x.1} : Set W) := by
  have : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace sW
  apply isClosed_singleton_of_isLocallyClosed_singleton
  obtain ⟨t, ht, hteq⟩ := isClosed_induced_iff.mp hx
  refine ⟨(V : Set W), t, V.isOpen, ht, ?_⟩
  ext z
  constructor
  · rintro rfl
    exact ⟨x.2, (Set.ext_iff.mp hteq x).mpr rfl⟩
  · rintro ⟨hzV, hzt⟩
    have e : (⟨z, hzV⟩ : V) = x := (Set.ext_iff.mp hteq ⟨z, hzV⟩).mp hzt
    show z = x.1
    exact congrArg Subtype.val e

theorem bijOn_closedPoints_of_isIso (π : W ⟶ X) (hπ : π ≫ sX = sW) [LocallyOfFiniteType sW]
    [LocallyOfFiniteType sX] (U : X.Opens) [IsIso (π ∣_ U)] :
    Set.BijOn π.base {x | IsClosed ({x} : Set W) ∧ π.base x ∈ U}
      {y | IsClosed ({y} : Set X) ∧ y ∈ U} := by
  let h := Scheme.homeoOfIso (asIso (π ∣_ U))
  have hb : ∀ z, (h z).1 = π.base z.1 := fun z => morphismRestrict_base_coe π U z
  refine ⟨fun x hx => ⟨isClosed_image_of_closed sW sX π hπ x hx.1, hx.2⟩, ?_, ?_⟩
  · intro x₁ hx₁ x₂ hx₂ he
    have e1 : h ⟨x₁, hx₁.2⟩ = h ⟨x₂, hx₂.2⟩ :=
      Subtype.ext ((hb ⟨x₁, hx₁.2⟩).trans (he.trans (hb ⟨x₂, hx₂.2⟩).symm))
    exact congrArg Subtype.val (h.injective e1)
  · intro y hy
    let w := h.symm ⟨y, hy.2⟩
    have hw : h w = ⟨y, hy.2⟩ := h.apply_symm_apply _
    have hcl : IsClosed ({h w} : Set _) := by
      refine isClosed_induced_iff.mpr ⟨{y}, hy.1, Set.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
      · exact Subtype.ext (hz.trans (congrArg Subtype.val hw).symm)
      · exact (congrArg Subtype.val hz).trans (congrArg Subtype.val hw)
    have hcw : IsClosed ({w} : Set _) := by
      have := hcl.preimage h.continuous
      rwa [← Set.image_singleton, h.injective.preimage_image] at this
    have hW : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace sW
    refine ⟨w.1, ⟨?_, w.2⟩, (hb w).symm.trans (congrArg Subtype.val hw)⟩
    apply isClosed_singleton_of_isLocallyClosed_singleton
    obtain ⟨t, ht, hteq⟩ := isClosed_induced_iff.mp hcw
    refine ⟨((π ⁻¹ᵁ U : W.Opens) : Set W), t, (π ⁻¹ᵁ U).isOpen, ht, ?_⟩
    ext z
    constructor
    · rintro rfl
      exact ⟨w.2, (Set.ext_iff.mp hteq w).mpr rfl⟩
    · rintro ⟨hzV, hzt⟩
      have e : (⟨z, hzV⟩ : ((π ⁻¹ᵁ U : W.Opens) : Set W)) = w := (Set.ext_iff.mp hteq ⟨z, hzV⟩).mp hzt
      show z = w.1
      exact congrArg Subtype.val e

theorem exists_coord_inv (π : W ⟶ X) (hπ : π ≫ sX = sW) [LocallyOfFiniteType sW]
    [LocallyOfFiniteType sX] (U : X.Opens) [IsIso (π ∣_ U)] (PW : AffPres sW) (V : X.Opens)
    (hV : IsAffineOpen V) {σ : Type} [Finite σ] (u : σ → Γ(X, V))
    (hu : ∀ t : Γ(X, V), ∃ F : MvPolynomial σ ℂ, t = eval₂ (constSec sX V) u F)
    (x : W) (hxW : x ∈ PW.V) (hxV : π.base x ∈ V) (hxU : π.base x ∈ U)
    (hc : IsClosed ({x} : Set W)) :
    ∃ O : W.Opens, x ∈ O ∧ O ≤ PW.V ⊓ π ⁻¹ᵁ (U ⊓ V) ∧
      ∃ (q : MvPolynomial σ ℂ) (F : Fin PW.n → MvPolynomial σ ℂ),
        eval (fun t => val sX (u t) (π.base x) hxV) q ≠ 0 ∧
        ∀ (y : W) (hyW : y ∈ PW.V) (hyV : π.base y ∈ V), y ∈ O → IsClosed ({y} : Set W) →
          eval (fun t => val sX (u t) (π.base y) hyV) q ≠ 0 ∧
          ∀ l, PW.coord y hyW l * eval (fun t => val sX (u t) (π.base y) hyV) q =
            eval (fun t => val sX (u t) (π.base y) hyV) (F l) := by
  have hiso : IsIso (π.stalkMap x) := by
    let x' : (π ⁻¹ᵁ U : W.Opens) := ⟨x, hxU⟩
    have h1 : IsIso ((π ∣_ U).stalkMap x') := by
      first
      | exact inferInstance
      | exact (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion (π ∣_ U))).2 x'
    have h2 : (MorphismProperty.isomorphisms CommRingCat) ((π ∣_ U).stalkMap x') := h1
    exact (MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
      (morphismRestrictStalkMap π U x') |>.mp h2
  obtain ⟨O, hxO, hO, q, F, hq, hF⟩ := exists_ratio_core sW sX π hπ V hV u hu PW.V
    (fun l => PW.secHom (MvPolynomial.X l)) x hxW hxV hc (ConcreteCategory.bijective_of_isIso (π.stalkMap x)).2
  refine ⟨O ⊓ π ⁻¹ᵁ U, ⟨hxO, hxU⟩, ?_, q, F, hq, ?_⟩
  · intro y hy
    exact ⟨(hO hy.1).1, hy.2, (hO hy.1).2⟩
  · intro y hyW hyV hyO hcy
    obtain ⟨h1, h2⟩ := hF y hyW hyV hyO.1 hcy
    refine ⟨h1, fun l => ?_⟩
    rw [← h2 l, PW.val_secHom y hyW hcy, eval_X]

theorem exists_coord_fwd (π : W ⟶ X) (hπ : π ≫ sX = sW) [LocallyOfFiniteType sW]
    [LocallyOfFiniteType sX] (PW : AffPres sW) (V : X.Opens) {σ : Type} [Finite σ]
    (u : σ → Γ(X, V)) (x : W) (hxW : x ∈ PW.V) (hxV : π.base x ∈ V)
    (hc : IsClosed ({x} : Set W)) :
    ∃ O : W.Opens, x ∈ O ∧ O ≤ PW.V ⊓ π ⁻¹ᵁ V ∧
      ∃ (q : MvPolynomial (Fin PW.n) ℂ) (F : σ → MvPolynomial (Fin PW.n) ℂ),
        eval (PW.coord x hxW) q ≠ 0 ∧
        ∀ (y : W) (hyW : y ∈ PW.V) (hyV : π.base y ∈ V), y ∈ O → IsClosed ({y} : Set W) →
          eval (PW.coord y hyW) q ≠ 0 ∧
          ∀ t, val sX (u t) (π.base y) hyV * eval (PW.coord y hyW) q =
            eval (PW.coord y hyW) (F t) := by
  have : IsAffine PW.V.toScheme := IsAffine.of_isIso PW.iso.hom
  have hV : IsAffineOpen PW.V := this
  let u' : Fin PW.n → Γ(W, PW.V) := fun j => PW.secHom (MvPolynomial.X j)
  have hu' : ∀ a : Γ(W, PW.V), ∃ F : MvPolynomial (Fin PW.n) ℂ,
      a = eval₂ (constSec sW PW.V) u' F := by
    intro a
    obtain ⟨f, rfl⟩ := PW.secHom_surjective a
    refine ⟨f, ?_⟩
    conv_lhs => rw [← MvPolynomial.eval₂_eta f]
    rw [eval₂_comp_left]
    congr 1
    ext c
    exact PW.secHom_C c
  have hxW' : (𝟙 W : W ⟶ W).base x ∈ PW.V := hxW
  obtain ⟨O, hxO, hO, q, F, hq, hF⟩ := exists_ratio_core sW sW (𝟙 W) (Category.id_comp _) PW.V hV
    u' hu' (PW.V ⊓ π ⁻¹ᵁ V) (fun t => π.appLE V (PW.V ⊓ π ⁻¹ᵁ V) inf_le_right (u t)) x
    ⟨hxW, hxV⟩ hxW' hc (by rw [Scheme.Hom.stalkMap_id]; exact fun z => ⟨z, rfl⟩)
  have hcoord : ∀ (y : W) (hyW : y ∈ PW.V) (h : (𝟙 W : W ⟶ W).base y ∈ PW.V),
      IsClosed ({y} : Set W) → (fun a => val sW (u' a) ((𝟙 W : W ⟶ W).base y) h) = PW.coord y hyW := by
    intro y hyW h hcy
    funext j
    change val sW (PW.secHom (MvPolynomial.X j)) y hyW = _
    rw [PW.val_secHom y hyW hcy, eval_X]
  refine ⟨O, hxO, fun y hy => (hO hy).1, q, F, ?_, ?_⟩
  · rw [← hcoord x hxW hxW' hc]
    exact hq
  · intro y hyW hyV hyO hcy
    have hyW' : (𝟙 W : W ⟶ W).base y ∈ PW.V := hyW
    obtain ⟨h1, h2⟩ := hF y ⟨hyW, hyV⟩ hyW' hyO hcy
    rw [hcoord y hyW hyW' hcy] at h1 h2
    refine ⟨h1, fun t => ?_⟩
    rw [← h2 t, (val_comp sW sX π hπ inf_le_right (u t) y ⟨hyW, hyV⟩ hcy).2]

end

end ReciprocityTheory.AnForm.R
