module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalNearBoundary
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodDecompositionNearBoundary

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.CentreIdent
section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.TorusExpEqOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section
namespace LevelTowerAlt.Val
open GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.PerSpan GlobalTheory.CompanionTheory.Ar.QuotLoc GlobalTheory.CompanionTheory.Ar.QuotLoc.Lat

theorem lie_equiv {S : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over (Sp ℂ)} [GrpObj G'] {z : Sp ℂ ⟶ S}
    {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G z φ) {V V' : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] (MV : LieModel G' (𝟙 (Sp ℂ)) V) (Mz : LieModel G z V') :
    ∃ Φ : V ≃ₗ[ℂ] V', ∀ x, (Mz.pt (Φ x)).left = (MV.pt x).left ≫ φ := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.AlphaPair.exists_ptEquiv hp (epsAt (𝟙 (Sp ℂ))).hom (epsAt z).hom (by simp)
  obtain ⟨ρ₀, hρ₀⟩ := GlobalTheory.AlphaPair.exists_ptEquiv hp (𝟙 (Sp ℂ)) z (Category.id_comp _).symm
  have h1 : (1 : Over.mk z ⟶ G).left = (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ G').left ≫ φ := by
    rw [← hρ₀, map_one]
  have tan : ∀ v : epsAt (𝟙 (Sp ℂ)) ⟶ G', IsTanAt G z (ρ v) ↔ IsTanAt G' (𝟙 _) v := by
    intro v
    unfold IsTanAt
    constructor
    · intro h
      refine hp.1.hom_ext ?_ ?_
      · rw [← h1, ← h, Category.assoc]
        exact congrArg _ (hρ v).symm
      · rw [Category.assoc, Over.w v, Over.w (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ G')]
        exact TorusModel.fst_eps (𝟙 (Sp ℂ))
    · intro h
      rw [h1, ← h, Category.assoc]
      exact congrArg _ (hρ v)
  choose f hf using fun x => Mz.onto _ ((tan _).2 (MV.tan x))
  have hl : ∀ x, (Mz.pt (f x)).left = (MV.pt x).left ≫ φ := fun x => by
    rw [hf]
    exact hρ _
  let F : V →ₗ[ℂ] V' :=
    { toFun := f
      map_add' := fun x y => Mz.inj (by
        rw [Mz.add, hf, hf, hf, MV.add]
        exact map_mul ρ _ _)
      map_smul' := fun c x => Mz.inj (Over.OverMorphism.ext (by
        rw [RingHom.id_apply, Mz.smul, hl, hl, MV.smul, Category.assoc])) }
  refine ⟨LinearEquiv.ofBijective F ⟨fun x y h => ?_, fun y => ?_⟩, hl⟩
  · have h' : f x = f y := h
    refine MV.inj (ρ.injective ?_)
    exact (hf x).symm.trans ((congrArg Mz.pt h').trans (hf y))
  · obtain ⟨x, hx⟩ := MV.onto (ρ.symm (Mz.pt y)) ((tan _).1 (by rw [ρ.apply_symm_apply]; exact Mz.tan y))
    refine ⟨x, Mz.inj ?_⟩
    show Mz.pt (f x) = _
    rw [hf, hx]
    exact ρ.apply_symm_apply _

theorem torus_deriv {X : Type} [AddCommGroup X] {d : ℕ} (β : Module.Basis (Fin d) ℤ X)
    (MT : LieModel (splitTorus (Sp ℂ) X) (𝟙 _) (X →+ ℂ)) (hMT : IsCocharLie MT) (δ : X →+ ℂ) :
    IsDerivAt0 (fun w => (torusExp β w).left) (fun a => δ (β a)) (MT.pt δ).left := by
  obtain ⟨v, H⟩ := GlobalTheory.VerticalDeriv.exists_isDerivAt0 (isHolTo_torusExp β) (fun a => δ (β a))
  have hv := GlobalTheory.VerticalDeriv.isDerivAt0_vertical (splitTorus (Sp ℂ) X).hom (𝟙 (Sp ℂ))
    (e := fun w => (torusExp β w).left) (fun w => Over.w (torusExp β w)) H
  let v' : epsAt (𝟙 (Sp ℂ)) ⟶ splitTorus (Sp ℂ) X := Over.homMk v hv
  have h0 : torusExp β (0 : Fin d → ℂ) = 1 := by
    have := torusExp_add β (0 : Fin d → ℂ) 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have ht : IsTanAt (splitTorus (Sp ℂ) X) (𝟙 _) v' := H.1.trans (congrArg (·.left) h0)
  obtain ⟨δ', hδ'⟩ := MT.onto v' ht
  have e : δ' = δ := by
    ext χ
    have H2 := GlobalTheory.FibreDeriv.isDerivAt0_comp H (pullback.fst (splitTorusAff ZU X).hom (toZ (Sp ℂ)))
    have h3 := H2.2 ⊤ le_top ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom (AddMonoidAlgebra.single χ 1))
    have h4 : (fun z => valAt' ((torusExp β z).left ≫ pullback.fst (splitTorusAff ZU X).hom (toZ (Sp ℂ))) ⊤
        ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom (AddMonoidAlgebra.single χ 1))) =
        fun z => Complex.exp (pairing β z χ) :=
      funext fun z => (valAt'_torusFst' _ _).trans (torusExp_hol_char β z χ)
    let Lc : (Fin d → ℂ) →L[ℂ] ℂ := ∑ a, ((β.repr χ a : ℤ) : ℂ) • ContinuousLinearMap.proj a
    have hLc : ∀ w, Lc w = pairing β w χ := fun w => by simp [Lc, pairing]
    have h5 : fderiv ℂ (fun z => Complex.exp (pairing β z χ)) 0 (fun a => δ (β a)) = δ χ := by
      have : HasFDerivAt (fun z => Complex.exp (Lc z)) (Complex.exp (Lc 0) • Lc) 0 := Lc.hasFDerivAt.cexp
      simp only [hLc] at this
      rw [this.fderiv, ContinuousLinearMap.smul_apply, hLc, ← hLc 0, map_zero, Complex.exp_zero, one_smul]
      set_option synthInstance.maxHeartbeats 100000 in
        conv_rhs => rw [← β.sum_repr χ, map_sum]
      simp only [pairing, map_zsmul, zsmul_eq_mul]
    have h6 := hMT δ' χ
    rw [hδ'] at h6
    have h7 : (charVal v' χ).snd = δ' χ := by rw [h6]; simp
    rw [← h7, ← h5, ← h4]
    refine Eq.trans ?_ h3
    congr 1
    unfold charVal
    set g : Sp (DualNumber ℂ) ⟶ Spec (torusRing ZU X) :=
      v'.left ≫ pullback.fst (splitTorusAff ZU X).hom (toZ (Sp ℂ)) with hg
    have h : (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ g.appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom = Spec.preimage g := by
      conv_lhs => rw [← Spec.map_preimage g]
      rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    have h8 : g.appTop = g.appLE ⊤ ⊤ le_top := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
    rw [← h, h8]
    rfl
  rw [← e, hδ', e]
  exact H

theorem torusExp_eq_one {X : Type} [AddCommGroup X] {d : ℕ} (β : Module.Basis (Fin d) ℤ X) (w : Fin d → ℂ) :
    torusExp β w = 1 ↔ ∃ δ : X →+ ℤ, w = fun a => (2 * Real.pi * Complex.I) * (δ (β a) : ℂ) := by
  have hT : ∀ χ : X, torusHom β w (Multiplicative.ofAdd χ) = expUnit (pairing β w χ) := fun χ => rfl
  have hE : torusExp β w =
      (GlobalTheory.splitTorusPointsEquiv (Sp ℂ) X (𝟙_ (Over (Sp ℂ)))).symm (torusHom β w) := rfl
  constructor
  · intro h1
    have hH : torusHom β w = 1 := by
      have h0 := congrArg (GlobalTheory.splitTorusPointsEquiv (Sp ℂ) X (𝟙_ (Over (Sp ℂ)))) h1
      rw [hE, MulEquiv.apply_symm_apply, map_one] at h0
      exact h0
    have hexp : ∀ a, Complex.exp (w a) = 1 := by
      intro a
      have h2 := congrArg (fun f => f (Multiplicative.ofAdd (β a))) hH
      simp only [hT, MonoidHom.one_apply, pairing_basis] at h2
      have h3 := gamma_expUnit (w a)
      rw [h2, Units.val_one, map_one] at h3
      exact h3.symm
    choose n hn using fun a => Complex.exp_eq_one_iff.1 (hexp a)
    refine ⟨(β.constr ℤ n).toAddMonoidHom, ?_⟩
    funext a
    rw [hn a]
    simp only [LinearMap.toAddMonoidHom_coe, Module.Basis.constr_basis]
    ring
  · rintro ⟨δ, rfl⟩
    have hH : torusHom β (fun a => (2 * Real.pi * Complex.I) * (δ (β a) : ℂ)) = 1 := by
      apply monoidHom_ext_basis β
      intro a
      rw [hT, pairing_basis, MonoidHom.one_apply]
      apply expUnit_eq_one
      show Complex.exp (2 * ↑Real.pi * Complex.I * (δ (β a) : ℂ)) = 1
      rw [mul_comm]
      exact Complex.exp_int_mul_two_pi_mul_I (δ (β a))
    rw [hE, hH, map_one]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R] {t : SAB H (Sp R)}
  {g n : ℕ} {M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}

theorem torus_lift (e : FamExp t.G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) (P : AbPart t (spMap (ψ b)))
    (Mz : LieModel t.G (spMap (ψ b)) (Fin g → ℂ))
    (hL : ∀ i, ((Mz.pt (Pi.single i 1)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (ψ b)) ≫ (M.pt (Pi.single i 1)).left)) :
    letI := P.τ.addCommGroup
    ∃ (d : ℕ) (β : Module.Basis (Fin d) ℤ P.τ.X) (h : (Fin d → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      (∀ (MT : LieModel (splitTorus (Sp ℂ) P.τ.X) (𝟙 _) (P.τ.X →+ ℂ)), IsCocharLie MT → ∀ δ : P.τ.X →+ ℂ,
        (Mz.pt (h fun a => δ (β a))).left = (MT.pt δ ≫ P.τ.i).left ≫ P.m.φ) ∧
      (∀ z, h z ∈ e.per b ↔ ∃ δ : P.τ.X →+ ℤ, z = fun a => (2 * Real.pi * Complex.I) * (δ (β a) : ℂ)) ∧
      ∀ (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ P.tB.G.left) (g' : ℕ) (u : HolUnif A (P.tB.PP.L.pull φ) g')
        (ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), IsGrpPullback A P.tB.G (𝟙 _) φ → IsAbLift e b P φ u ℓ →
        ∀ y, ℓ y = 0 ↔ ∃ z, y = h z := by
  letI := P.τ.grpB
  letI := P.τ.addCommGroup
  haveI := P.τ.free
  haveI := P.τ.finite
  haveI := P.τ.q_hom
  haveI := P.τ.i_hom
  haveI : IsMonHom P.e.hom := P.e_hom
  let β := Module.finBasis ℤ P.τ.X
  obtain ⟨ρ, hρ⟩ := GlobalTheory.AlphaPair.exists_ptEquiv P.m.cart (𝟙 (Sp ℂ)) (spMap (ψ b)) (Category.id_comp _).symm
  let v : (Fin (Module.finrank ℤ P.τ.X) → ℂ) → (Over.mk (spMap (ψ b)) ⟶ t.G) := fun z => ρ (torusExp β z ≫ P.τ.i)
  have vadd : ∀ z w, v (z + w) = v z * v w := fun z w => by
    show ρ (torusExp β (z + w) ≫ P.τ.i) = ρ (torusExp β z ≫ P.τ.i) * ρ (torusExp β w ≫ P.τ.i)
    rw [torusExp_add, MonObj.mul_comp]
    exact map_mul ρ _ _
  have vl : (fun z => (v z).left) = fun z => (torusExp β z).left ≫ P.τ.i.left ≫ P.m.φ := funext fun z => by
    rw [← Category.assoc]
    exact hρ _
  have vhol : IsHolTo Set.univ (fun z => (v z).left) := by
    rw [vl]
    exact ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp (isHolTo_torusExp β) _
  obtain ⟨h', -, hh⟩ := exists_linear_lift_of_additive_family R t.G g 0 M Set.univ (fun _ => ψ b)
    (famExpAtPoint e hb) _ Set.univ (fun _ z => v z) isOpen_univ subset_rfl (fun _ _ z w => vadd z w)
    (isHolTo_snd (V := Fin 0 → ℂ) (X := t.G.left) (c := fun z => (v z).left) vhol)
  obtain ⟨hex, -, hder⟩ := hh 0 trivial
  have hex' : ∀ z, e.ex b (h' 0 z) = v z := hex
  have hder' : ∀ z w, IsDerivAt0 (fun z => (v z).left) z w ↔ IsDerivAt0 (fun z => (e.ex b z).left) (h' 0 z) w := hder
  have hmono : Mono P.τ.i := by
    refine ⟨fun a a' haa => P.τ.isKernel.hom_ext haa (toUnit_unique _ _)⟩
  have hQ1 : ∀ z : 𝟙_ (Over (Sp ℂ)) ⟶ splitTorus (Sp ℂ) P.τ.X, (z ≫ P.τ.i) ≫ P.τ.q ≫ P.e.hom = 1 := by
    intro z
    have h1 : P.τ.i ≫ P.τ.q = toUnit _ ≫ η := P.τ.isKernel.w
    have h2 : z ≫ P.τ.i ≫ P.τ.q = 1 := by
      rw [h1, ← Category.assoc, Hom.one_def]
      congr 1
      exact toUnit_unique _ _
    calc (z ≫ P.τ.i) ≫ P.τ.q ≫ P.e.hom = (z ≫ P.τ.i ≫ P.τ.q) ≫ P.e.hom := by simp only [Category.assoc]
      _ = 1 := by rw [h2, MonObj.one_comp]
  refine ⟨_, β, h' 0, fun MT hMT δ => ?_, fun z => ?_, fun A _ φ g' u ℓ hA hl y => ?_⟩
  · have d1 := GlobalTheory.FibreDeriv.isDerivAt0_comp (torus_deriv β MT hMT δ) (P.τ.i.left ≫ P.m.φ)
    rw [← vl] at d1
    have d2 := (hder' _ _).1 d1
    rw [Over.comp_left, Category.assoc]
    exact GlobalTheory.VerticalDeriv.isDerivAt0_unique (DiffL.isDerivAt0_pt e hb Mz hL _) d2
  · rw [← torusExp_eq_one]
    show e.ex b (h' 0 z) = 1 ↔ _
    rw [hex']
    refine (map_eq_one_iff ρ ρ.injective).trans ⟨fun h1 => ?_, fun h1 => ?_⟩
    · rw [← cancel_mono P.τ.i, MonObj.one_comp]
      exact h1
    · show torusExp β z ≫ P.τ.i = 1
      rw [h1, MonObj.one_comp]
  · obtain ⟨ρ', hρ'⟩ := GlobalTheory.AlphaPair.exists_ptEquiv hA (𝟙 (Sp ℂ)) (𝟙 (Sp ℂ)) (Category.id_comp _).symm
    have hl' : ∀ y (s : 𝟙_ (Over (Sp ℂ)) ⟶ P.tK.G), ρ s = e.ex b y → ρ' (u.ex (ℓ y)) = s ≫ P.τ.q ≫ P.e.hom :=
      fun y s hs => Over.OverMorphism.ext ((hρ' _).trans (hl y s ((hρ s).symm.trans (congrArg (·.left) hs))))
    constructor
    · intro hy
      obtain ⟨Γ₀, hΓ, hd, -, -⟩ := GlobalTheory.T.period_lattice_discrete_free R t.G g n M B ψ e b hb
      have hcount : (e.per b).Countable := by
        rw [← hΓ]
        haveI := hd
        have : Countable Γ₀ := countable_of_Lindelof_of_discrete
        exact Set.countable_coe_iff.1 this
      have h0 : (LinearMap.range (h' 0)).mkQ y = 0 := by
        refine GlobalTheory.eq_zero_of_forall_smul_mem_countable (hcount.image (LinearMap.range (h' 0)).mkQ) fun c => ?_
        obtain ⟨s, hs⟩ := ρ.surjective (e.ex b (c • y))
        have h1 := hl' _ s hs
        rw [map_smul, hy, smul_zero, (u.ker 0).2 u.Λ.zero_mem] at h1
        have h2 : s ≫ P.τ.q ≫ P.e.hom = 1 := h1.symm.trans (map_one ρ')
        have h3 : s ≫ P.τ.q = 1 := by
          rw [← cancel_mono P.e.hom, MonObj.one_comp, Category.assoc]
          exact h2
        let τ₀ : 𝟙_ (Over (Sp ℂ)) ⟶ splitTorus (Sp ℂ) P.τ.X :=
          P.τ.isKernel.lift s (toUnit _) (by rw [h3, Hom.one_def]; rfl)
        have hτ : τ₀ ≫ P.τ.i = s := P.τ.isKernel.lift_fst _ _ _
        obtain ⟨w, hw⟩ := torusExp_surjective β τ₀
        have h4 : e.ex b (h' 0 w) = e.ex b (c • y) := by
          rw [hex', ← hs, ← hτ, ← hw]
        refine ⟨c • y - h' 0 w, ?_, ?_⟩
        · show e.ex b _ = 1
          have := e.add b hb (c • y - h' 0 w) (h' 0 w)
          rw [sub_add_cancel, h4] at this
          exact right_eq_mul.1 this
        · simp only [map_sub, map_smul, Submodule.mkQ_apply]
          rw [(Submodule.Quotient.mk_eq_zero (LinearMap.range (h' 0))).2 ⟨w, rfl⟩, sub_zero]
      have : y ∈ LinearMap.range (h' 0) := by simpa using h0
      obtain ⟨z, hz⟩ := this
      exact ⟨z, hz.symm⟩
    · rintro ⟨z, rfl⟩
      have hcount : (u.Λ : Set (Fin g' → ℂ)).Countable := by
        haveI := u.discrete
        have : Countable u.Λ := countable_of_Lindelof_of_discrete
        exact Set.countable_coe_iff.1 this
      refine GlobalTheory.eq_zero_of_forall_smul_mem_countable hcount fun c => ?_
      rw [← map_smul, ← map_smul]
      refine (u.ker _).1 (ρ'.injective ?_)
      exact ((hl' _ _ (hex' (c • z)).symm).trans (hQ1 _)).trans (map_one ρ').symm

end LevelTowerAlt.Val
end
end

section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.PhiTransport
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section
namespace LevelTowerAlt.Val

theorem phi_transport {E : Type} [Field E] [NumberField E] {V V' A : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [Fintype A] (ρ : 𝓞 E →+* Module.End ℂ V) (ρ' : 𝓞 E →+* Module.End ℂ V')
    (Ψ : V ≃ₗ[ℂ] V') (hρ : ∀ a x, ρ' a (Ψ x) = Ψ (ρ a x)) (hb : V → V → ℂ) (hb' : V' → V' → ℂ) (κ : ℝ)
    (hh : ∀ x x', hb x x' = κ * hb' (Ψ x) (Ψ x')) (I : AddSubgroup V) (I' : AddSubgroup V')
    (hI : I' = I.map Ψ.toLinearMap.toAddMonoidHom) (σ : A → (𝓞 E →+* ℂ)) {m : ℕ} (b : A → Fin m → V)
    (b' : A → Fin m → V') (c : ℂ) (hc : c ≠ 0) (hbb : ∀ τ j, Ψ (b τ j) = c • b' τ j) (ν : ℝ)
    (h : PhiNormSq ρ hb I κ σ b ν) :
    ∃ ν', PhiNormSq ρ' hb' I' 1 σ b' ν' ∧ ν = (κ * ‖c‖ ^ 2) ^ (m * Fintype.card A) * ν' := by
  subst hI
  have heig : ∀ (s₀ : 𝓞 E →+* ℂ) (x : V),
      Ψ (GlobalTheory.CompanionTheory.Ar.Cusp.eigComp ρ s₀ x) = GlobalTheory.CompanionTheory.Ar.Cusp.eigComp ρ' s₀ (Ψ x) := by
    intro s₀ x
    obtain ⟨c₀, hc₀⟩ := GlobalTheory.T.exists_eigenComponent_polynomial E s₀
    set_option synthInstance.maxHeartbeats 100000 in
      rw [(hc₀ V ρ).1 x, (hc₀ V' ρ').1 (Ψ x), map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, hρ]
  have hmem : ∀ (s₀ : 𝓞 E →+* ℂ) (x : V), x ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ s₀ →
      Ψ x ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ' s₀ := by
    intro s₀ x hx
    unfold GlobalTheory.CompanionTheory.Ar.eigSp at hx ⊢
    rw [Submodule.mem_iInf] at hx ⊢
    intro a
    have hx' := hx a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hx'
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hρ,
      ← map_smul Ψ, ← map_sub Ψ, hx', map_zero Ψ]
  have hspan : ∀ {r : ℕ} (v : Fin r → V), GlobalTheory.CompanionTheory.Ar.Cusp.oSpan ρ' (fun i => Ψ (v i)) =
      (GlobalTheory.CompanionTheory.Ar.Cusp.oSpan ρ v).map Ψ.toLinearMap.toAddMonoidHom := by
    intro r v
    unfold GlobalTheory.CompanionTheory.Ar.Cusp.oSpan
    rw [AddMonoidHom.map_closure]
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨a, i, rfl⟩
      exact ⟨ρ a (v i), ⟨a, i, rfl⟩, (hρ a (v i)).symm⟩
    · rintro ⟨y, ⟨a, i, rfl⟩, rfl⟩
      exact ⟨a, i, (hρ a (v i)).symm⟩
  obtain ⟨r, k, hrk, v, q, T, hint, hq, hT, hdet, hν⟩ := h
  refine ⟨_, ⟨r, k, hrk, fun i => Ψ (v i), fun τ j => Ψ (q τ j), fun τ => c • T τ, ?_, ?_, ?_, ?_,
    rfl⟩, ?_⟩
  · obtain ⟨hvI, hind, hidx⟩ := hint
    refine ⟨fun i => AddSubgroup.mem_map_of_mem _ (hvI i), fun a ha => hind a ?_, ?_⟩
    · apply Ψ.injective
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_zero]
      simp only [← hρ]
      exact ha
    · rw [hspan v, AddSubgroup.relIndex_map_map_of_injective (f := Ψ.toLinearMap.toAddMonoidHom)
        _ _ Ψ.injective]
      exact hidx
  · exact fun τ j => hmem _ _ (hq τ j)
  · intro τ i
    have h1 : Fin.append (fun a => GlobalTheory.CompanionTheory.Ar.Cusp.eigComp ρ' (σ τ) (Ψ (v a))) (fun j => Ψ (q τ j)) i =
        Ψ (Fin.append (fun a => GlobalTheory.CompanionTheory.Ar.Cusp.eigComp ρ (σ τ) (v a)) (q τ) i) := by
      refine Fin.addCases (fun l => ?_) (fun l => ?_) i
      · rw [Fin.append_left, Fin.append_left, heig]
      · rw [Fin.append_right, Fin.append_right]
    refine h1.trans ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hT τ i, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hbb, smul_smul]
    congr 1
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring
  · intro τ
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hc) (hdet τ)
  · have hcn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
    have hmat : ∀ τ, (Matrix.of fun i j => hb (q τ i) (q τ j)) =
        (κ : ℂ) • Matrix.of (fun i j => hb' (Ψ (q τ i)) (Ψ (q τ j))) := by
      intro τ
      ext i j
      rw [Matrix.smul_apply, Matrix.of_apply, Matrix.of_apply, hh, smul_eq_mul]
    rw [hν, hspan v, AddSubgroup.relIndex_map_map_of_injective
      (f := Ψ.toLinearMap.toAddMonoidHom) _ _ Ψ.injective, pow_mul, ← Finset.card_univ,
      ← Finset.prod_const, mul_left_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    have hY : ‖(T τ).det‖ ≠ 0 := norm_ne_zero_iff.mpr (hdet τ)
    rw [hmat τ]
    simp only [Matrix.det_smul, Fintype.card_fin]
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul, norm_mul, norm_pow]
    have hκ : κ ^ r * κ ^ k = κ ^ m := by rw [← pow_add, hrk]
    rw [← mul_assoc, hκ]
    field_simp
    ring

theorem herm_unique {g : ℕ} (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ) (h₁ : H₁.IsHermitian) (h₂ : H₂.IsHermitian)
    (S N : Set (Fin g → ℂ)) (hS : ∀ x ∈ S, ∀ y ∈ S, (x ⬝ᵥ H₁ *ᵥ star y).im = (x ⬝ᵥ H₂ *ᵥ star y).im)
    (n₁ : ∀ y ∈ N, H₁ *ᵥ star y = 0) (n₂ : ∀ y ∈ N, H₂ *ᵥ star y = 0)
    (hall : ∀ p, ∃ r ∈ Submodule.span ℝ S, p - r ∈ N) : H₁ = H₂ := by
  set D := H₁ - H₂ with hD
  have hDh : D.IsHermitian := h₁.sub h₂
  have hS' : ∀ x ∈ S, ∀ y ∈ S, (x ⬝ᵥ D *ᵥ star y).im = 0 := by
    intro x hx y hy
    rw [hD, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_im, hS x hx y hy, sub_self]
  have hN : ∀ y ∈ N, D *ᵥ star y = 0 := by
    intro y hy
    rw [hD, Matrix.sub_mulVec, n₁ y hy, n₂ y hy, sub_zero]
  have hNl : ∀ x ∈ N, ∀ q, x ⬝ᵥ D *ᵥ star q = 0 := by
    intro x hx q
    have hx0 : x ᵥ* D = 0 := by
      have h := congrArg star (hN x hx)
      rwa [Matrix.star_mulVec, star_star, hDh.eq, star_zero] at h
    rw [Matrix.dotProduct_mulVec, hx0, zero_dotProduct]
  have hspan : ∀ x ∈ Submodule.span ℝ S, ∀ y ∈ Submodule.span ℝ S,
      (x ⬝ᵥ D *ᵥ star y).im = 0 := by
    intro x hx y hy
    induction hy using Submodule.span_induction with
    | mem y hy' =>
      induction hx using Submodule.span_induction with
      | mem x hx' => exact hS' x hx' y hy'
      | zero => simp
      | add x x' _ _ h h' => rw [add_dotProduct, Complex.add_im, h, h', add_zero]
      | smul a x _ h => rw [smul_dotProduct, Complex.smul_im, h, smul_zero]
    | zero => simp
    | add y y' _ _ h h' =>
      rw [star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im, h, h', add_zero]
    | smul a y _ h =>
      rw [star_smul, star_trivial, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im, h,
        smul_zero]
  have hall' : ∀ p q : Fin g → ℂ, (p ⬝ᵥ D *ᵥ star q).im = 0 := by
    intro p q
    obtain ⟨r, hr, hpr⟩ := hall p
    obtain ⟨r', hr', hqr⟩ := hall q
    rw [show p = r + (p - r) by abel, add_dotProduct, hNl _ hpr, add_zero,
      show q = r' + (q - r') by abel, star_add, Matrix.mulVec_add, hN _ hqr, add_zero]
    exact hspan r hr r' hr'
  have hzero : ∀ p q : Fin g → ℂ, p ⬝ᵥ D *ᵥ star q = 0 := by
    intro p q
    have h1 := hall' p q
    have h2 := hall' (Complex.I • p) q
    rw [smul_dotProduct, smul_eq_mul, Complex.mul_im, Complex.I_re, Complex.I_im] at h2
    apply Complex.ext
    · simpa using h2
    · simpa using h1
  have hD0 : D = 0 := by
    ext i j
    have h0 := hzero (Pi.single i 1) (Pi.single j 1)
    rw [← Pi.single_star, star_one, single_dotProduct, one_mul] at h0
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h0
  rw [hD] at hD0
  exact sub_eq_zero.mp hD0

end LevelTowerAlt.Val
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section
namespace LevelTowerAlt.Val
open GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.QuotLoc GlobalTheory.UU GlobalTheory.CompanionTheory.Ar.Cusp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R] {t : SAB H (Sp R)}
  {g n : ℕ} {M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}

theorem centre_ident (e : FamExp t.G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) (P : AbPart t (spMap (ψ b)))
    (hP : IsPrincipal P.tB) (Mz : LieModel t.G (spMap (ψ b)) (Fin g → ℂ))
    (hL : ∀ i, ((Mz.pt (Pi.single i 1)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (ψ b)) ≫ (M.pt (Pi.single i 1)).left))
    {V : Type} [AddCommGroup V] [Module ℂ V] (MV : LieModel P.tK.G (𝟙 (Sp ℂ)) V)
    (ρ : 𝓞 E →+* Module.End ℂ V) (I : AddSubgroup V) (hf : V → V → ℂ) (hact : MV.IsActOf P.tK.act.act ρ)
    (hI : P.IsCochars MV I)
    (hh : ∀ x x', HodgeIP P.tB.G P.tB.PP.L (𝟙 _) (MV.pt x ≫ P.τ.q ≫ P.e.hom) (MV.pt x' ≫ P.τ.q ≫ P.e.hom) (hf x x'))
    (Bb : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (hB : ∀ c x, e.ex b (Bb c x) = e.ex b x ≫ t.act.act c)
    (Hb : Matrix (Fin g) (Fin g) ℂ) (hH : Hb.IsHermitian)
    (hW : ∀ y ∈ e.per b, ∀ y' ∈ e.per b, ∃ k : ℤ, (y ⬝ᵥ Hb *ᵥ star y').im = k ∧ ∀ (N : ℕ) (ζ : ℂˣ), 0 < N →
      (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (k : ℂ) / N) →
      CubWeil t.cub N (e.ex b ((N : ℂ)⁻¹ • y)) (e.ex b ((N : ℂ)⁻¹ • y')) (unitOn ζ))
    (I' : Set (Fin g → ℂ)) (hI' : ∀ p, p ∈ I' ↔ p ∈ e.per b ∧ ∀ y ∈ e.per b, (p ⬝ᵥ Hb *ᵥ star y).im = 0)
    (hrad : ∀ p ∈ I', Hb *ᵥ star p = 0) :
    ∃ Φ : V ≃ₗ[ℂ] (Fin g → ℂ), (∀ x, (Mz.pt (Φ x)).left = (MV.pt x).left ≫ P.m.φ) ∧
      (∀ a x, Bb a (Φ x) = Φ (ρ a x)) ∧ (∀ x x', hf x x' = Real.pi * (Φ x' ⬝ᵥ Hb *ᵥ star (Φ x))) ∧
      ∀ p, p ∈ I' ↔ ∃ x ∈ I, p = (2 * Real.pi * Complex.I : ℂ) • Φ x := by
  letI := P.τ.addCommGroup
  obtain ⟨Φ, hΦ⟩ := lie_equiv P.m.cart MV Mz
  obtain ⟨d, β, h, t1, t2, t3⟩ := torus_lift e hb P Mz hL
  have key : ∀ (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ P.tB.G.left) (g' : ℕ) (u : HolUnif A (P.tB.PP.L.pull φ) g')
      (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)),
      IsGrpPullback A P.tB.G (𝟙 _) φ → u.IsAH Hm χ → IsAbLift e b P φ u ℓ →
      (∀ p, p ∈ I' ↔ p ∈ e.per b ∧ ℓ p = 0) ∧ ∀ p q, ℓ p ⬝ᵥ Hm *ᵥ star (ℓ q) = p ⬝ᵥ Hb *ᵥ star q := by
    intro A iA φ g' u Hm χ ℓ hφ hAH hℓ
    obtain ⟨hin, honto⟩ := GlobalTheory.T.hol_unif_period_matrix_right E H R t g n M _ ψ e _ P A iA φ g' u Hm χ ℓ hb hφ hAH hP hℓ
    obtain ⟨H', hH1, hH2, hH3⟩ := exists_pull_form ℓ Hm hAH.1
    have hE : ∀ y ∈ e.per b, ∀ y' ∈ e.per b, (y ⬝ᵥ Hb *ᵥ star y').im = (ℓ y ⬝ᵥ Hm *ᵥ star (ℓ y')).im := by
      intro y hy y' hy'
      obtain ⟨k, hk, hc⟩ := hW y hy y' hy'
      rw [hk]
      refine eq_of_forall_exp fun N hN => ?_
      have := GlobalTheory.T.hol_unif_period_matrix_middle E H R t g n M _ ψ e _ P A iA φ g' u Hm χ ℓ hb hφ hAH hP hℓ N _ y y' hN hy hy'
        (hc N (Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (k : ℂ) / N))) hN rfl)
      rw [Units.val_mk0] at this
      have c : ((k : ℝ) : ℂ) = (k : ℂ) := by push_cast; rfl
      rw [c]
      exact this
    have k1 : ∀ p, p ∈ I' ↔ p ∈ e.per b ∧ ℓ p = 0 := fun p => by
      rw [hI']
      refine and_congr_right fun hp => ⟨fun h0 => ?_, fun h0 y hy => ?_⟩
      · refine eq_zero_of_im_lattice Hm u.Λ u.full hAH.2.1 _ fun q hq => ?_
        obtain ⟨y, hy, rfl⟩ := honto q hq
        rw [← hE p hp y hy, h0 y hy]
      · rw [hE p hp y hy, h0]
        simp
    refine ⟨k1, fun p q => ?_⟩
    rw [← hH2]
    congr 2
    refine herm_unique H' Hb hH1 hH (e.per b) {y | ℓ y = 0} (fun x hx y hy => by rw [hH2, hE x hx y hy]) hH3
      (fun y hy => ?_) (fun p => ?_)
    · obtain ⟨z, rfl⟩ := (t3 A φ g' u ℓ hφ hℓ y).1 hy
      have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
      have e1 : z = ∑ a, (z a / (2 * Real.pi * Complex.I)) • (Pi.single a (2 * Real.pi * Complex.I) : Fin d → ℂ) := by
        ext c
        simp [Finset.sum_apply, Pi.single_apply, h2]
      have e2 : ∀ a, Hb *ᵥ star (h (Pi.single a (2 * Real.pi * Complex.I))) = 0 := fun a => by
        refine hrad _ ((k1 _).2 ⟨(t2 _).2 ⟨(β.coord a).toAddMonoidHom, funext fun c => ?_⟩,
          (t3 A φ g' u ℓ hφ hℓ _).2 ⟨_, rfl⟩⟩)
        by_cases hc : c = a
        · subst hc; simp
        · simp [hc, Finsupp.single_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [e1, map_sum, star_sum, Matrix.mulVec_sum]
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [map_smul, star_smul, Matrix.mulVec_smul, e2, smul_zero]
    · have hp : ℓ p ∈ Submodule.span ℝ (u.Λ : Set (Fin g' → ℂ)) := by rw [u.full]; trivial
      have : ∀ w ∈ Submodule.span ℝ (u.Λ : Set (Fin g' → ℂ)), ∃ r ∈ Submodule.span ℝ (e.per b), ℓ r = w := by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨y, hy, rfl⟩ := honto x hx
          exact ⟨y, Submodule.subset_span hy, rfl⟩
        | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
        | add x y _ _ hx hy =>
          obtain ⟨r, hr, rfl⟩ := hx
          obtain ⟨r', hr', rfl⟩ := hy
          exact ⟨r + r', Submodule.add_mem _ hr hr', map_add _ _ _⟩
        | smul c x _ hx =>
          obtain ⟨r, hr, rfl⟩ := hx
          exact ⟨c • r, Submodule.smul_mem _ _ hr, ℓ.map_smul_of_tower c r⟩
      obtain ⟨r, hr, hrp⟩ := this _ hp
      exact ⟨r, hr, by show ℓ (p - r) = 0; rw [map_sub, hrp, sub_self]⟩
  refine ⟨Φ, hΦ, fun a x => ?_, fun x x' => ?_, fun p => ?_⟩
  · have d1 := GlobalTheory.FibreDeriv.isDerivAt0_comp (DiffL.isDerivAt0_pt e hb Mz hL (Φ x)) (t.act.act a).left
    have d2 := PerGram.isDerivAt0_comp_linMap (PerSpan.isHolTo_ex_slice e hb) (Bb a)
      (DiffL.isDerivAt0_pt e hb Mz hL (Bb a (Φ x)))
    have e1 : (fun z => (e.ex b (Bb a z)).left) = fun z => (e.ex b z).left ≫ (t.act.act a).left :=
      funext fun z => by rw [hB, Over.comp_left]
    rw [e1] at d2
    refine Mz.inj (Over.OverMorphism.ext ?_)
    rw [GlobalTheory.VerticalDeriv.isDerivAt0_unique d2 d1, hΦ, hΦ, hact a x, Over.comp_left, Category.assoc, Category.assoc,
      P.m.act]
  · obtain ⟨-, -, -, A, iA, φ, g', u, Hm, χ, v', w', a', b', hφ, hAH, hv', hw', ha', hb', hc⟩ := hh x x'
    obtain ⟨ℓ, hℓ⟩ := GlobalTheory.T.hol_unif_period_matrix_left E H R t g n M _ ψ e _ P A iA φ g' u Hm χ hb hφ hAH hP
    have e1 : a' = ℓ (Φ x) := DiffL.isDiff_eq_lift E H R t g n M _ ψ e _ P A iA φ g' u Hm χ ℓ hb hφ hAH hP hℓ Mz hL _ _
      v' a' (hΦ x).symm hv' ha'
    have e2 : b' = ℓ (Φ x') := DiffL.isDiff_eq_lift E H R t g n M _ ψ e _ P A iA φ g' u Hm χ ℓ hb hφ hAH hP hℓ Mz hL _ _
      w' b' (hΦ x').symm hw' hb'
    rw [hc, e1, e2, ← (key A φ g' u Hm χ ℓ hφ hAH hℓ).2]
  · obtain ⟨-, -, -, A, iA, φ, g', u, Hm, χ, v', w', a', b', hφ, hAH, -⟩ := hh 0 0
    obtain ⟨ℓ, hℓ⟩ := GlobalTheory.T.hol_unif_period_matrix_left E H R t g n M _ ψ e _ P A iA φ g' u Hm χ hb hφ hAH hP
    obtain ⟨MT, hMT, hI⟩ := hI
    have k2 : ∀ x (δ : P.τ.X →+ ℤ), MV.pt x = MT.pt ((Int.castAddHom ℂ).comp δ) ≫ P.τ.i ↔
        Φ x = h fun a => (δ (β a) : ℂ) := fun x δ => by
      have a1 := t1 MT hMT ((Int.castAddHom ℂ).comp δ)
      constructor
      · intro hx
        refine Mz.inj (Over.OverMorphism.ext ?_)
        rw [hΦ, hx]
        exact a1.symm
      · intro hx
        refine Over.OverMorphism.ext (P.m.cart.1.hom_ext ?_ ?_)
        · rw [← hΦ, hx]
          exact a1
        · rw [Over.w (MV.pt x), Over.w (MT.pt ((Int.castAddHom ℂ).comp δ) ≫ P.τ.i)]
    have k3 : ∀ δ : P.τ.X →+ ℤ, h (fun a => (2 * Real.pi * Complex.I) * (δ (β a) : ℂ)) =
        (2 * Real.pi * Complex.I : ℂ) • h fun a => (δ (β a) : ℂ) := fun δ => by
      rw [← map_smul]
      rfl
    rw [(key A φ g' u Hm χ ℓ hφ hAH hℓ).1, t3 A φ g' u ℓ hφ hℓ]
    constructor
    · rintro ⟨hp, z, rfl⟩
      obtain ⟨δ, rfl⟩ := (t2 z).1 hp
      refine ⟨Φ.symm (h fun a => (δ (β a) : ℂ)), (hI _).2 ⟨δ, (k2 _ δ).2 (Φ.apply_symm_apply _)⟩, ?_⟩
      rw [Φ.apply_symm_apply, k3]
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨δ, hδ⟩ := (hI x).1 hx
      rw [(k2 x δ).1 hδ, ← k3]
      exact ⟨(t2 _).2 ⟨δ, rfl⟩, _, rfl⟩

theorem per_small (e : FamExp t.G M B ψ) {b₀ : Fin n → ℂ} (hb : b₀ ∈ B) (hB : B ∈ 𝓝 b₀) :
    ∀ᶠ bz : (Fin n → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), bz.2 ∈ e.per bz.1 → bz.2 = 0 := by
  obtain ⟨V, N, f, L, -, -, hL, -⟩ := e.log b₀ hb
  have hB' : ∀ᶠ bz : (Fin n → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), bz.1 ∈ B :=
    (continuous_fst.tendsto (b₀, (0 : Fin g → ℂ))).eventually_mem hB
  have hc : Continuous fun bz : (Fin n → ℂ) × (Fin g → ℂ) => (bz.1, (0 : Fin g → ℂ)) := by fun_prop
  have hL0 := (hc.tendsto (b₀, 0)).eventually hL
  filter_upwards [hL, hL0, hB'] with bz h1 h2 h3 hper
  have h0 : e.ex bz.1 0 = 1 := by
    have h4 := e.add bz.1 h3 0 0
    rw [add_zero] at h4
    simpa using h4.symm
  have hx : e.ex bz.1 bz.2 = e.ex bz.1 0 := by
    rw [h0]
    exact hper
  rw [← h1, hx]
  exact h2

end LevelTowerAlt.Val
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section
namespace LevelTowerAlt.Val
open GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.QuotLoc GlobalTheory.UU GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree
open GroundTheory.Heights₂.Heights.Regular (logCover expCover)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {σ₀ : KA l →+* ℂ} {n a : ℕ}

theorem abPart_principal (C : Flat.BdryChart Xo σ₀ n a) {z : Fin n → ℂ} (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1)
    (P : AbPart C.t (spMap (C.ψ z))) : IsPrincipal P.tB := by
  obtain ⟨V, _, _, _, f, r, tV, mV, hV, hr, hker, hrf, hpol⟩ := GlobalTheory.T.exists_dvr_through_disc_point E H D l Xo σ₀ n a C z hz
  have key : ∀ (z₀ : Sp ℂ ⟶ Sp C.R), z₀ = spMap r ≫ spMap f → ∀ P : AbPart C.t z₀, IsPrincipal P.tB := by
    rintro _ rfl P
    obtain ⟨m', -⟩ := GlobalTheory.T.abelian_part_factors_through E H _ _ tV C.t _ mV ℂ (spMap r) P
    exact GlobalTheory.T.polarized_abelian_part_principal E H V r tV hV hr hker hpol ⟨P.tK, m', P.τ, P.tB, P.e, P.e_hom, P.act, P.pp⟩
  refine key _ ?_ P
  rw [← hrf]
  show Spec.map (CommRingCat.ofHom (r.comp f)) = _
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem exists_seq_cover (h : a ≤ n) : ∃ ws : ℕ → Fin n → ℂ, (∀ k, ws k ∈ logCover h) ∧
    Tendsto (fun k => expCover a (ws k)) atTop (𝓝 0) := by
  refine ⟨fun m i => if (i : ℕ) < a then -((m : ℂ) + 1) else 0, fun m => ⟨fun i => ?_, fun i hi => ?_⟩, ?_⟩
  · have hi : ((Fin.castLE h i : Fin n) : ℕ) < a := by simp
    simp only [hi, ↓reduceIte, Complex.neg_re, Complex.add_re, Complex.natCast_re, Complex.one_re]
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  · have hi' : ¬ ((i : ℕ) < a) := by omega
    simp [hi']
  · rw [tendsto_pi_nhds]
    intro i
    by_cases hi : (i : ℕ) < a
    · simp only [expCover, hi, ↓reduceIte, Pi.zero_apply]
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [Complex.norm_exp, Complex.neg_re, Complex.add_re, Complex.natCast_re, Complex.one_re]
      exact Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop))
    · simp only [expCover, hi, ↓reduceIte, Pi.zero_apply]
      exact tendsto_const_nhds

theorem periods_inj {g : ℕ} {Λ : Type} [AddCommGroup Λ] (L₀ : Flat.LogPeriods n a g Λ) {w : Fin n → ℂ}
    (hw : w ∈ logCover L₀.a_le) : Function.Injective (L₀.P w) := by
  intro x x' hxx
  have h0 : L₀.P w (x - x') = 0 := by rw [map_sub, hxx, sub_self]
  have hE : L₀.E (x - x') = 0 := by
    refine LinearMap.ext fun y => ?_
    have him := L₀.im w hw (x - x') y
    rw [h0] at him
    have h2 : ((L₀.E (x - x') y : ℤ) : ℝ) = 0 := by
      rw [← him]
      simp
    rw [LinearMap.zero_apply]
    exact_mod_cast h2
  exact sub_eq_zero.1 (L₀.unimod.1 (hE.trans (map_zero L₀.E).symm))

theorem centre_phi (C : Flat.BdryChart Xo σ₀ n a) {X : Scheme.{0}} {tt : SAB H X} {jj : Sp C.R ⟶ X}
    (m : SABMap C.t tt jj) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (e : Flat.FamExp C.t.G C.M (Metric.ball 0 ρ) C.ψ)
    {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (L : ActPeriods E n a C.g Λ)
    (hlink : ∀ w ∈ logCover L.a_le, (∀ p, p ∈ e.per ((ρ : ℂ) • expCover a w) ↔ ∃ x, L.P w x = p) ∧
      ∀ (N : ℕ) (ζ : ℂˣ) (x x' : Λ), 0 < N → CubWeil C.t.cub N (e.ex ((ρ : ℂ) • expCover a w) ((N : ℂ)⁻¹ • L.P w x))
        (e.ex ((ρ : ℂ) • expCover a w) ((N : ℂ)⁻¹ • L.P w x')) (unitOn ζ) →
        (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((L.toLogPeriods.E x x' : ℤ) : ℂ) / N))
    (hB : ∀ c x, e.ex ((ρ : ℂ) • 0) (L.B 0 c x) = e.ex ((ρ : ℂ) • 0) x ≫ C.t.act.act c)
    {A : Type} [Fintype A] {k : ℕ} (σ : A → (𝓞 E →+* ℂ)) (b : A → Fin k → (Fin n → ℂ) → Fin C.g → ℂ)
    (sc : A → Fin k → Fin C.g → C.R) (hb0 : ∀ τ i, b τ i 0 = fun j => C.ψ ((ρ : ℂ) • 0) (sc τ i j))
    (hσ : IsCMFam σ) (hb : IsEigFrames (Metric.ball 0 1) L.B σ b)
    (P : AbPart tt (spMap (C.ψ ((ρ : ℂ) • 0)) ≫ jj))
    {V : Type} [AddCommGroup V] [Module ℂ V] (MV : LieModel P.tK.G (𝟙 (Sp ℂ)) V)
    (ρV : 𝓞 E →+* Module.End ℂ V) (I₀ : AddSubgroup V) (hf : V → V → ℂ) (hact : MV.IsActOf P.tK.act.act ρV)
    (hI₀ : P.IsCochars MV I₀)
    (hh : ∀ x x', HodgeIP P.tB.G P.tB.PP.L (𝟙 _) (MV.pt x ≫ P.τ.q ≫ P.e.hom) (MV.pt x' ≫ P.τ.q ≫ P.e.hom) (hf x x'))
    (bz : A → Fin k → V) (hbz : ∀ τ i, (MV.pt (bz τ i)).left ≫ P.m.φ =
      spMap (dualMap (C.ψ ((ρ : ℂ) • 0))) ≫ (C.M.pt (sc τ i)).left ≫ m.φ)
    {ν : ℝ} (hν : PhiNormSq ρV hf I₀ (4 * Real.pi)⁻¹ σ bz ν) :
    ∃ I : Submodule (𝓞 E) Λ, IsSaturated I ∧ IsIsoSub L.toLogPeriods.E I ∧ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ w (hw : w ∈ logCover L.a_le), ‖expCover a w‖ < δ →
        Real.log ν - ε ≤ (Fintype.card A : ℝ) * ((k : ℝ) * Real.log Real.pi) +
          (L.riem w hw).logDet (fun τ i => b τ i (expCover a w)) - Real.log ((L.riem w hw).nz σ I) := by
  obtain ⟨W, I, per, s, Hb, hI, hsat, -, hs, hlim, -, hH, hIm, hrad, hlimν⟩ := GlobalTheory.T.period_decomposition_near_boundary E n a C.g Λ A L σ k b hσ hb
  have h00 : (ρ : ℂ) • (0 : Fin n → ℂ) = 0 := smul_zero _
  have hbρ : (ρ : ℂ) • (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) ρ := by
    rw [h00]; exact Metric.mem_ball_self hρ0
  have hol : Flat.IsHolPts (Metric.ball 0 ρ) C.ψ :=
    ⟨Metric.isOpen_ball, fun r => (C.hol.2 r).mono (Metric.ball_subset_ball hρ1)⟩
  obtain ⟨ws, hws, hw0⟩ := exists_seq_cover L.a_le
  have hper : ∀ x : W, Tendsto (fun j => L.P (ws j) x) atTop (𝓝 (per x)) := fun x => by
    obtain ⟨h1, h2, h3⟩ := hs x
    have := h1.tendsto.comp hw0
    rw [h2] at this
    exact this.congr fun j => h3 _ (hws j)
  have hfour : ∀ (x : ℕ → Λ) (p : Fin C.g → ℂ), Tendsto (fun j => L.P (ws j) (x j)) atTop (𝓝 p) →
      ∃ x₀ : W, p = per x₀ ∧ ∀ᶠ j in atTop, x j = x₀ := by
    intro x p hx
    obtain ⟨x₀, rfl⟩ := hlim ws x p hws hw0 hx
    refine ⟨x₀, rfl, ?_⟩
    have h1 : Tendsto (fun j => ((ρ : ℂ) • expCover a (ws j), L.P (ws j) (x j - x₀))) atTop (𝓝 ((ρ : ℂ) • 0, 0)) := by
      refine (hw0.const_smul _).prodMk_nhds ?_
      have := hx.sub (hper x₀)
      rw [sub_self] at this
      simpa only [map_sub] using this
    filter_upwards [h1.eventually (per_small e hbρ (Metric.isOpen_ball.mem_nhds hbρ))] with j hj
    have h2 := hj (((hlink _ (hws j)).1 _).2 ⟨_, rfl⟩)
    exact sub_eq_zero.1 (periods_inj L.toLogPeriods (hws j) (h2.trans (map_zero _).symm))
  obtain ⟨hA, hBp, hC⟩ := GlobalTheory.T.family_exp_log_cover_bound E H C.R C.t C.g n a C.M C.ψ ρ e Λ L.toLogPeriods hρ0 hρ1 hol hlink 0
    (Metric.mem_ball_self one_pos) ws (W.restrictScalars ℤ) per hws hw0 hper hfour
  replace hA : ∀ x : W, per x ∈ e.per ((ρ : ℂ) • 0) := hA
  replace hBp : ∀ p ∈ e.per ((ρ : ℂ) • 0), ∃ x : W, per x = p := hBp
  obtain ⟨m', hm'⟩ := GlobalTheory.T.abelian_part_factors_through E H _ _ C.t tt jj m ℂ _ P
  let P' : AbPart C.t (spMap (C.ψ ((ρ : ℂ) • 0))) := ⟨P.tK, m', P.τ, P.tB, P.e, P.e_hom, P.act, P.pp⟩
  have hP := abPart_principal C (Metric.ball_subset_ball hρ1 hbρ) P'
  obtain ⟨Mz, hMz⟩ := GlobalTheory.T.boundary_chart_lie_model_exists E H D l Xo σ₀ n a C ((ρ : ℂ) • 0)
  have hL : ∀ i, ((Mz.pt (Pi.single i 1)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ ((ρ : ℂ) • 0))) ≫ (C.M.pt (Pi.single i 1)).left) := fun i => by
    have h1 := hMz (Pi.single i 1)
    have h2 : (fun j => C.ψ ((ρ : ℂ) • 0) ((Pi.single i 1 : Fin C.g → C.R) j)) = (Pi.single i 1 : Fin C.g → ℂ) := by
      funext j
      by_cases h : j = i
      · subst h; simp
      · simp [Pi.single_apply, h]
    rwa [h2] at h1
  obtain ⟨Φ, f1, f2, f3, f4⟩ := centre_ident e hbρ P' hP Mz hL MV ρV I₀ hf hact hI₀ hh (L.B 0) hB Hb hH
    (fun y hy y' hy' => by
      obtain ⟨x, rfl⟩ := hBp y hy
      obtain ⟨x', rfl⟩ := hBp y' hy'
      exact ⟨_, hIm x x', fun N ζ hN hζ => hC N ζ x x' hN hζ⟩)
    {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x}
    (fun p => ⟨by
      rintro ⟨x, hx, rfl⟩
      refine ⟨hA x, fun y hy => ?_⟩
      obtain ⟨x', rfl⟩ := hBp y hy
      rw [hIm x x', ((hI _).1 hx).2 _ x'.2, Int.cast_zero], by
      rintro ⟨hp, h0⟩
      obtain ⟨x, rfl⟩ := hBp p hp
      refine ⟨x, (hI _).2 ⟨x.2, fun y hy => ?_⟩, rfl⟩
      have := h0 _ (hA ⟨y, hy⟩)
      rw [hIm x ⟨y, hy⟩] at this
      exact_mod_cast this⟩)
    (by
      rintro _ ⟨x, hx, rfl⟩
      exact hrad x hx)
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  let Ψ : V ≃ₗ[ℂ] (Fin C.g → ℂ) := Φ.trans (LinearEquiv.smulOfNeZero ℂ _ _ hc)
  have hΨ : ∀ x, Ψ x = (2 * Real.pi * Complex.I : ℂ) • Φ x := fun x => rfl
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  obtain ⟨ν', hν', hνe⟩ := phi_transport ρV (L.B 0) Ψ (fun c x => by rw [hΨ, hΨ, map_smul, f2]) hf
    (fun x y => y ⬝ᵥ Hb *ᵥ star x) (4 * Real.pi)⁻¹
    (fun x x' => by
      rw [f3, hΨ, hΨ, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
      simp only [smul_eq_mul, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
      push_cast
      field_simp
      linear_combination (4 * (Φ x' ⬝ᵥ Hb *ᵥ star (Φ x))) * Complex.I_mul_I)
    I₀ (AddSubgroup.closure {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x})
    (by
      rw [← AddSubgroup.closure_eq (I₀.map Ψ.toLinearMap.toAddMonoidHom)]
      congr 1
      ext p
      rw [f4]
      exact ⟨fun ⟨x, hx, h⟩ => ⟨x, hx, h.symm⟩, fun ⟨x, hx, h⟩ => ⟨x, hx, h.symm⟩⟩)
    σ bz (fun τ i => b τ i 0) _ hc
    (fun τ i => by
      rw [hΨ, hb0]
      congr 1
      refine Mz.inj (Over.OverMorphism.ext (m.cart.1.hom_ext ?_ ?_))
      · have h1 := hMz (sc τ i)
        change _ ≫ _ = _ ≫ _ at h1
        rw [Category.comp_id] at h1
        rw [f1, h1, Category.assoc, Category.assoc]
        exact (congrArg _ hm').trans (hbz τ i)
      · rw [Over.w (Mz.pt _), Over.w (Mz.pt _)])
    ν hν
  obtain ⟨hpos, hlim'⟩ := hlimν ν' hν'
  have e1 : (4 * Real.pi)⁻¹ * ‖(2 * Real.pi * Complex.I : ℂ)‖ ^ 2 = Real.pi := by
    have := Real.pi_pos
    simp only [norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_ofNat, Real.norm_of_nonneg this.le]
    field_simp
    ring
  have e2 : Real.log ν = (Fintype.card A : ℝ) * ((k : ℝ) * Real.log Real.pi) + Real.log ν' := by
    rw [hνe, e1, Real.log_mul (pow_ne_zero _ Real.pi_ne_zero) hpos.ne', Real.log_pow]
    push_cast
    ring
  refine ⟨I, hsat, fun v hv w hw => ((hI _).1 hv).2 _ ((hI _).1 hw).1, fun ε hε => ?_⟩
  obtain ⟨δ, hδ, h⟩ := hlim' ε hε
  refine ⟨δ, hδ, fun w hw h1 => ?_⟩
  have := (abs_lt.1 (h w hw h1)).1
  linarith

end LevelTowerAlt.Val
