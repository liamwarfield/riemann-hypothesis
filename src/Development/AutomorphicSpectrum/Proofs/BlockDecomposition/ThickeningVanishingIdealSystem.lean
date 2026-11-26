module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsFormOfEqRatioPowMul
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningVanishingIdealSystem
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
open GlobalTheory.ProjSpace

namespace GlobalTheory.CompanionTheory.GE.Family

variable {R : Type} [CommRing R] {N : ℕ}

instance isClosedImmersion_thickι (I : Ideal R) (e : ℕ) : IsClosedImmersion (thickι R I N e) := by
  have : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  unfold thickι
  infer_instance

theorem thickMap_comp_thickι (I : Ideal R) (e : ℕ) :
    thickMap R I e (PO R N) ≫ thickι R I N (e + 1) = thickι R I N e := by
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

instance isClosedImmersion_thickMap (I : Ideal R) (e : ℕ) :
    IsClosedImmersion (thickMap R I e (PO R N)) := by
  have : IsClosedImmersion (thickMap R I e (PO R N) ≫ thickι R I N (e + 1)) := by
    rw [thickMap_comp_thickι]; infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (thickι R I N (e + 1))

theorem formOn_X_pow_mul (k : Fin (N + 1)) {m n : ℕ} {f : MvPolynomial (Fin (N + 1)) R}
    (hf : f.IsHomogeneous n) (h : (X k ^ m * f : MvPolynomial (Fin (N + 1)) R).IsHomogeneous (m + n)) :
    formOn (chart R N k) k le_rfl (m + n) (X k ^ m * f) h = formOn (chart R N k) k le_rfl n f hf := by
  simp only [formOn_eq_aeval, map_mul, map_pow, aeval_X, ratioOn_self, one_pow, one_mul]

theorem killsForm_of_X_pow_mul {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N) {n : ℕ}
    {f : MvPolynomial (Fin (N + 1)) R} (hf : f.IsHomogeneous n)
    (h : ∀ k, ∃ m : ℕ, X k ^ m * f ∈ vanIdeal φ) : KillsForm φ n f hf := by
  intro k
  obtain ⟨m, hm⟩ := h k
  have hh : (X k ^ m * f : MvPolynomial (Fin (N + 1)) R).IsHomogeneous (m + n) :=
    (isHomogeneous_X_pow k m).mul hf
  have := (GlobalTheory.CompanionTheory.GE.mem_vanIdeal_iff_killsForm φ (m + n) _ hh).1 hm k
  rwa [formOn_X_pow_mul k hf hh] at this


attribute [local instance] MvPolynomial.gradedAlgebra in
theorem homogeneousComponent_X_pow_mul (k : Fin (N + 1)) (m d : ℕ)
    (f : MvPolynomial (Fin (N + 1)) R) :
    homogeneousComponent (m + d) (X k ^ m * f) = X k ^ m * homogeneousComponent d f := by
  have := DirectSum.coe_decompose_mul_add_of_left_mem (homogeneousSubmodule (Fin (N + 1)) R)
    (a := X k ^ m) (b := f) (i := m) (j := d) (isHomogeneous_X_pow k m)
  have h2 : ∀ (g : MvPolynomial (Fin (N + 1)) R) (d : ℕ),
      ((DirectSum.decompose (homogeneousSubmodule (Fin (N + 1)) R) g) d :
        MvPolynomial (Fin (N + 1)) R) = homogeneousComponent d g :=
    fun g d => decomposition.decompose'_apply g d
  rwa [h2, h2] at this

theorem mem_vanIdeal_of_X_pow_mul {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N)
    (f : MvPolynomial (Fin (N + 1)) R) (h : ∀ k, ∃ m : ℕ, X k ^ m * f ∈ vanIdeal φ) :
    f ∈ vanIdeal φ := by
  rw [← sum_homogeneousComponent f]
  refine Ideal.sum_mem _ fun d _ => ?_
  refine (GlobalTheory.CompanionTheory.GE.mem_vanIdeal_iff_killsForm φ d _ (homogeneousComponent_isHomogeneous d f)).2
    (killsForm_of_X_pow_mul φ _ fun k => ?_)
  obtain ⟨m, hm⟩ := h k
  exact ⟨m, homogeneousComponent_X_pow_mul k m d f ▸ vanIdeal_homog φ (m + d) _ hm⟩

theorem killsForm_comp {Y Z : Scheme.{0}} (g : Z ⟶ Y) (φ : Y ⟶ PSpace R N) {n : ℕ}
    {f : MvPolynomial (Fin (N + 1)) R} {hf : f.IsHomogeneous n} (h : KillsForm φ n f hf) :
    KillsForm (g ≫ φ) n f hf := by
  intro k
  have := h k
  rw [Scheme.Hom.comp_app]
  change (g.app _).hom ((φ.app _).hom _) = 0
  rw [this, map_zero]

theorem vanIdeal_le_comp {Y Z : Scheme.{0}} (g : Z ⟶ Y) (φ : Y ⟶ PSpace R N) :
    vanIdeal φ ≤ vanIdeal (g ≫ φ) :=
  Ideal.span_mono fun _ ⟨n, hf, h⟩ => ⟨n, hf, killsForm_comp g φ h⟩

theorem map_pow_le_vanIdeal {Y : Scheme.{0}} (I : Ideal R) (e : ℕ)
    (a : Y ⟶ (thickObj R I e (PO R N)).left) :
    (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ≤ vanIdeal (a ≫ thickι R I N e) := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  refine (GlobalTheory.CompanionTheory.GE.mem_vanIdeal_iff_killsForm _ 0 (C r) (isHomogeneous_C _ r)).2 (killsForm_comp a _ fun k => ?_)
  have h := (GlobalTheory.CompanionTheory.GE.ker_thickι_chart I N e k).2 0 (C r) (isHomogeneous_C _ r) (Ideal.mem_map_of_mem _ hr)
  rw [Scheme.Hom.ker_apply] at h
  exact h

theorem exists_X_pow_mul_mem {Y Z : Scheme.{0}} (φ : Y ⟶ PSpace R N) [QuasiCompact φ]
    (ψ : Z ⟶ PSpace R N) [QuasiCompact ψ] (I : Ideal R) (e : ℕ)
    (hker : Scheme.Hom.ker ψ = Scheme.Hom.ker φ ⊔ Scheme.Hom.ker (thickι R I N e))
    {n : ℕ} {f : MvPolynomial (Fin (N + 1)) R} {hf : f.IsHomogeneous n}
    (hK : KillsForm ψ n f hf) (k : Fin (N + 1)) :
    ∃ m : ℕ, X k ^ m * f ∈ vanIdeal φ ⊔
      (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  have h1 : formOn (chart R N k) k le_rfl n f hf ∈
      (Scheme.Hom.ker ψ).ideal ⟨chart R N k, isAffineOpen_chart R N k⟩ := by
    rw [Scheme.Hom.ker_apply]
    exact hK k
  rw [hker, Scheme.IdealSheafData.ideal_sup] at h1
  obtain ⟨s, hs, s', hs', hss⟩ := Submodule.mem_sup.1 h1
  obtain ⟨c, t, ht, htm, rfl⟩ := (GlobalTheory.CompanionTheory.GE.ker_thickι_chart I N e k).1 s' hs'
  obtain ⟨a, b, hb, rfl⟩ := GlobalTheory.ProjSpace.Model.exists_formOn k s
  rw [Scheme.Hom.ker_apply] at hs
  obtain ⟨m, hm, hkill⟩ := GlobalTheory.CompanionTheory.GE.exists_killsForm_X_pow_mul φ a b hb k hs
  have hmem : X k ^ m * b ∈ vanIdeal φ := (GlobalTheory.CompanionTheory.GE.mem_vanIdeal_iff_killsForm φ _ _ hm).2 hkill
  have key : X k ^ (a + c) * f = X k ^ (n + c) * b + X k ^ (n + a) * t := by
    have hL : (X k ^ (a + c) * f : MvPolynomial (Fin (N + 1)) R).IsHomogeneous (a + c + n) :=
      (isHomogeneous_X_pow k _).mul hf
    have hR : (X k ^ (n + c) * b + X k ^ (n + a) * t :
        MvPolynomial (Fin (N + 1)) R).IsHomogeneous (a + c + n) := by
      refine IsHomogeneous.add ?_ ?_
      · have := (isHomogeneous_X_pow (R := R) k (n + c)).mul hb
        rwa [show n + c + a = a + c + n by ring] at this
      · have := (isHomogeneous_X_pow (R := R) k (n + a)).mul ht
        rwa [show n + a + c = a + c + n by ring] at this
    refine (formOn_chart_inj R N k hL hR).1 ?_
    simp only [formOn_eq_aeval, map_add (f := _), map_mul, map_pow, aeval_X, ratioOn_self, one_pow,
      one_mul] at hss ⊢
    exact hss.symm
  refine ⟨m + a + c, ?_⟩
  have e1 : X k ^ (m + a + c) * f =
      X k ^ (n + c) * (X k ^ m * b) + X k ^ (m + n + a) * t := by
    have : X k ^ (m + a + c) * f = X k ^ m * (X k ^ (a + c) * f) := by ring
    rw [this, key]; ring
  rw [e1]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mem_sup_left hmem))
    (Ideal.mul_mem_left _ _ (Ideal.mem_sup_right htm))

theorem vanIdeal_family : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (N : ℕ)
    (Cs : ℕ → Scheme.{0}) (i : ∀ e, Cs e ⟶ (thickObj R I e (PO R N)).left)
    (β : ∀ e, Cs e ⟶ Cs (e + 1)),
    (∀ e, IsClosedImmersion (i e)) →
    (∀ e, IsPullback (β e) (i e) (i (e + 1)) (thickMap R I e (PO R N))) →
    (∀ e, (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ≤
        vanIdeal (i e ≫ thickι R I N e)) ∧
    (∀ e f, (∀ k, ∃ m : ℕ, X k ^ m * f ∈ vanIdeal (i e ≫ thickι R I N e)) →
        f ∈ vanIdeal (i e ≫ thickι R I N e)) ∧
    (∀ e, vanIdeal (i (e + 1) ≫ thickι R I N (e + 1)) ≤ vanIdeal (i e ≫ thickι R I N e)) ∧
    (∀ e, ∀ f ∈ vanIdeal (i e ≫ thickι R I N e), ∀ k, ∃ m : ℕ, X k ^ m * f ∈
        vanIdeal (i (e + 1) ≫ thickι R I N (e + 1)) ⊔
          (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) := by
  intro R _ _ I N Cs i β hi hβ
  have hcomp : ∀ e, i e ≫ thickι R I N e =
      β e ≫ i (e + 1) ≫ thickι R I N (e + 1) := fun e => by
    rw [← thickMap_comp_thickι I e, ← Category.assoc, ← Category.assoc, (hβ e).w]
  refine ⟨fun e => map_pow_le_vanIdeal I e (i e), fun e f h => mem_vanIdeal_of_X_pow_mul _ f h,
    fun e => ?_, fun e f hf k => ?_⟩
  · rw [hcomp e]
    exact vanIdeal_le_comp _ _
  · have hker : Scheme.Hom.ker (i e ≫ thickι R I N e) =
        Scheme.Hom.ker (i (e + 1) ≫ thickι R I N (e + 1)) ⊔ Scheme.Hom.ker (thickι R I N e) := by
      have := GlobalTheory.CompanionTheory.GE.ker_inter_eq_sup (thickι R I N (e + 1)) (i (e + 1)) (thickMap R I e (PO R N))
        (β e) (i e) (hβ e)
      rwa [thickMap_comp_thickι, Category.assoc, ← hcomp e] at this
    refine Submodule.span_induction (p := fun f _ => ∃ m : ℕ, X k ^ m * f ∈
        vanIdeal (i (e + 1) ≫ thickι R I N (e + 1)) ⊔
          (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) ?_ ?_ ?_ ?_ hf
    · rintro x ⟨n, hx, hK⟩
      exact exists_X_pow_mul_mem _ _ I e hker hK k
    · exact ⟨0, by simp⟩
    · rintro x y _ _ ⟨a, ha⟩ ⟨b, hb⟩
      refine ⟨a + b, ?_⟩
      have e1 : X k ^ (a + b) * (x + y) = X k ^ b * (X k ^ a * x) + X k ^ a * (X k ^ b * y) := by
        ring
      rw [e1]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)
    · rintro a x _ ⟨m, hm⟩
      refine ⟨m, ?_⟩
      rw [smul_eq_mul, mul_left_comm]
      exact Ideal.mul_mem_left _ _ hm

end GlobalTheory.CompanionTheory.GE.Family
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalLiftVeryAmpleSections
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalLiftVeryAmpleSections
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem inv_of_mul_eq {A : Type} [CommRing A] {a a' b b' g g' : A} (h : a = g * b) (ha : a * a' = 1)
    (hb : b * b' = 1) (hg : g * g' = 1) : a' = g' * b' := by
  linear_combination (-(g' * b' * a')) * h + (g' * b') * ha + (-a') * hb + (-(a' * b * b')) * hg

variable {X X' : Scheme.{0}}

theorem exists_inv_of_isUnit_coord {N : LB X} {a : ℤ} {V : X.Opens} (x : SecOn (pw N a) V)
    (hx : ∀ k : N.ι, IsUnit (GlobalTheory.LB.coord x k)) :
    ∃ y : SecOn (pw N (-a)) V, secMulOn rfl x y = oneOn N (add_neg_cancel a) V := by
  have hy : (fun k : N.ι => (((hx k).unit⁻¹ : Γ(X, V ⊓ N.U k)ˣ) : Γ(X, V ⊓ N.U k))) ∈
      Geo.Tor.secOn (pw N (-a)) V := by
    intro i j
    have h := GlobalTheory.LB.coord_rel x i j (W := V ⊓ N.U i ⊓ N.U j) inf_le_left
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
    refine inv_of_mul_eq h ?_ ?_ ?_
    · exact (map_mul _ _ _).symm.trans ((congrArg _ (IsUnit.mul_val_inv (hx i))).trans (map_one _))
    · exact (map_mul _ _ _).symm.trans ((congrArg _ (IsUnit.mul_val_inv (hx j))).trans (map_one _))
    · refine (map_mul _ _ _).symm.trans ?_
      have e : ((N.g i j ^ a : Γ(X, N.U i ⊓ N.U j)ˣ) : Γ(X, N.U i ⊓ N.U j)) *
          ((N.g i j ^ (-a) : Γ(X, N.U i ⊓ N.U j)ˣ) : Γ(X, N.U i ⊓ N.U j)) = 1 := by
        rw [← Units.val_mul, zpow_neg, mul_inv_cancel, Units.val_one]
      exact (congrArg _ e).trans (map_one _)
  refine ⟨GlobalTheory.LB.mkSec _ hy, GlobalTheory.LB.sec_ext fun k => ?_⟩
  exact IsUnit.mul_val_inv (hx k)

theorem isUnit_coord_of_congr (π : X' ⟶ X) (hπ : Function.Surjective π) {M : LB X} {L : LB X'}
    (hL : L.IsLB) (hM : M.IsLB) (w : LB.Iso L (M.pull π)) (hw : w.IsGen) {V : X.Opens}
    {V' : X'.Opens} (e : π ⁻¹ᵁ V = V') (x : SecOn M V) (t : SecOn L V')
    (h : SecOn.congr hL (LB.isLB_pull hM π) w hw V' t = SecOn.pullLE M π V V' e.ge x)
    (ht : ∀ q, IsUnit (GlobalTheory.LB.coord t q)) (k : M.ι) : IsUnit (GlobalTheory.LB.coord x k) := by
  have hb : V ⊓ M.U k ≤ X.basicOpen (GlobalTheory.LB.coord x k) := by
    intro z hz
    obtain ⟨z', rfl⟩ := hπ z
    let j : (M.pull π).ι := fun _ => k
    have hz₁ : z' ∈ V' := e.le hz.1
    have hz₂ : z' ∈ (M.pull π).U j := by rw [pull_U]; exact hz.2
    obtain ⟨q, hq⟩ := TopologicalSpace.Opens.mem_iSup.1
      (hL.cover.ge (TopologicalSpace.Opens.mem_top z'))
    let O : X'.Opens := V' ⊓ (M.pull π).U j ⊓ L.U q
    have hp : O ≤ V' ⊓ (M.pull π).U j := inf_le_left
    have hq' : O ≤ V' ⊓ L.U q := inf_le_inf_right _ inf_le_left
    have hpq : O ≤ (M.pull π).U j ⊓ L.U q := inf_le_inf_right _ inf_le_right
    have c := SecOn.coord_congr hL (LB.isLB_pull hM π) w hw t j q hp hq' hpq
    rw [h] at c
    have hu : IsUnit (rs X' hp (GlobalTheory.LB.coord (SecOn.pullLE M π V V' e.ge x) j)) := by
      rw [c]
      exact (Units.isUnit _).map (rs X' hpq) |>.mul ((ht q).map (rs X' hq'))
    have hz' : z' ∈ X'.basicOpen (rs X' hp (GlobalTheory.LB.coord (SecOn.pullLE M π V V' e.ge x) j)) := by
      rw [X'.basicOpen_of_isUnit hu]
      exact ⟨⟨hz₁, hz₂⟩, hq⟩
    erw [Scheme.basicOpen_res] at hz'
    have hz'' := hz'.2
    rw [SecOn.coord_pullLE, Scheme.basicOpen_appLE] at hz''
    exact hz''.2
  have hu : IsUnit (rs X (X.basicOpen_le _) (GlobalTheory.LB.coord x k)) :=
    X.toRingedSpace.isUnit_res_basicOpen (GlobalTheory.LB.coord x k)
  simpa only [rs_rs, rs_self] using hu.map (rs X hb)

variable {R : Type} [CommRing R] (I : Ideal R)

theorem ker_factor_le_nilradical (e : ℕ) (h : I ^ (e + 1 + 1) ≤ I ^ (e + 1)) :
    RingHom.ker (Ideal.Quotient.factor h) ≤ nilradical (R ⧸ I ^ (e + 1 + 1)) := by
  intro x hx
  rw [RingHom.mem_ker] at hx
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
  rw [mem_nilradical]
  refine ⟨2, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  have hy2 : y ^ 2 ∈ I ^ (e + 1) * I ^ (e + 1) := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hx hx
  rw [← pow_add] at hy2
  exact Ideal.pow_le_pow_right (by omega) hy2

theorem surjective_thickTrans (e : ℕ) : Surjective (thickTrans R I e) := by
  delta ReciprocityTheory.ChartRestriction.G.Out.thickTrans
  have key : ∀ (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B), Function.Surjective φ →
      RingHom.ker φ ≤ nilradical A → Surjective (Spec.map (CommRingCat.ofHom φ)) := by
    intro A B _ _ φ hφ hker
    constructor
    intro p
    haveI := p.isPrime
    have hk : RingHom.ker φ ≤ p.asIdeal := le_trans hker (nilradical_le_prime p.asIdeal)
    refine ⟨⟨p.asIdeal.map φ, Ideal.map_isPrime_of_surjective hφ hk⟩, ?_⟩
    show PrimeSpectrum.comap φ ⟨p.asIdeal.map φ, Ideal.map_isPrime_of_surjective hφ hk⟩ = p
    ext1
    show Ideal.comap φ (Ideal.map φ p.asIdeal) = p.asIdeal
    rw [Ideal.comap_map_of_surjective' φ hφ, sup_eq_left.mpr hk]
  exact key _ _ _ (Ideal.Quotient.factor_surjective _) (ker_factor_le_nilradical I e _)

variable (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
  (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
  (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))


include hβ in
theorem surjective_tower (e : ℕ) : Function.Surjective (β e) := by
  exact (MorphismProperty.of_isPullback (P := @Surjective) (hβ e).flip (surjective_thickTrans I e)).surj

theorem isUnit_coord_of_redL (L : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e)))
    (hL : ∀ e, (L e).IsLB ∧ (w e).IsGen) (e : ℕ) {V : (Y (e + 1)).left.Opens}
    {V' : (Y e).left.Opens} (h : β e ⁻¹ᵁ V = V') (x : SecOnR (toR I Y (e + 1)) (L (e + 1)) V)
    (ht : ∀ q, IsUnit (SecOnR.coord (redL I Y β hβ L w hL e V V' h.ge x) q)) (k : (L (e + 1)).ι) :
    IsUnit (SecOnR.coord x k) :=
  isUnit_coord_of_congr (β e) (surjective_tower I Y β hβ e) (hL e).1 (hL (e + 1)).1 (w e) (hL e).2 h
    x (redL I Y β hβ L w hL e V V' h.ge x)
    ((SecOnR.linEquiv (toR I Y e) (SecOn.congr (hL e).1 (LB.isLB_pull (hL (e + 1)).1 (β e)) (w e)
      (hL e).2 V')).apply_symm_apply _) ht k

theorem exists_lifts_tower : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℕ) (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))) (hs : VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s) (D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens) (hD0 : ∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) (hDβ : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) (hDm : ∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) (hDi : ∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) (hDc : ∀ e, ⨆ i, D e {i} = ⊤) (hDa : ∀ e S, S.Nonempty → IsAffineOpen (D e S)), ∃ sh : ∀ e (j : Fin (m + 1)) (S : Finset (Fin (m + 1))), SecOn (pw (N e) (d : ℤ)) (D e S), (∀ j S, S.Nonempty → sh 0 j S = GlobalTheory.LB.ofSec (s j) (D 0 S)) ∧ (∀ e j S, S.Nonempty → red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) (d : ℤ) e S (SecOnR.of _ _ _ (sh (e + 1) j S)) = SecOnR.of _ _ _ (sh e j S)) ∧ (∀ e i S, i ∈ S → ∃ y : SecOn (pw (N e) (-(d : ℤ))) (D e S), secMulOn rfl (sh e i S) y = oneOn (N e) (add_neg_cancel (d : ℤ)) (D e S)) := by
  intro R _ I Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa
  have hge : ∀ e (S : Finset (Fin (m + 1))), D e S ≤ β e ⁻¹ᵁ D (e + 1) S := fun e S => (hDβ e S).ge
  have hsurj : ∀ e (S : Finset (Fin (m + 1))), S.Nonempty →
      Function.Surjective (red I Y N D β hβ v hN hge (d : ℤ) e S) := fun e S hS =>
    (redL_surjective_ker R I Y β hβ (fun e => pw (N e) (d : ℤ)) (fun e => pullPow (v e) (d : ℤ))
      (fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩) e (D (e + 1) S) (D e S)
      (hDβ e S) (hDa (e + 1) S hS)).1
  have hl : ∀ e (S : Finset (Fin (m + 1))) (t : SecOn (pw (N e) (d : ℤ)) (D e S)),
      ∃ x : SecOn (pw (N (e + 1)) (d : ℤ)) (D (e + 1) S), S.Nonempty →
        red I Y N D β hβ v hN hge (d : ℤ) e S (SecOnR.of _ _ _ x) = SecOnR.of _ _ _ t := by
    intro e S t
    by_cases hS : S.Nonempty
    · obtain ⟨x, hx⟩ := hsurj e S hS (SecOnR.of _ _ _ t)
      exact ⟨(SecOnR.of _ _ _).symm x, fun _ => hx⟩
    · exact ⟨0, fun h => absurd h hS⟩
  choose lf hlf using hl
  let sh : ∀ e (j : Fin (m + 1)) (S : Finset (Fin (m + 1))), SecOn (pw (N e) (d : ℤ)) (D e S) :=
    fun e j S => Nat.rec (motive := fun e => SecOn (pw (N e) (d : ℤ)) (D e S))
      (GlobalTheory.LB.ofSec (s j) (D 0 S)) (fun e t => lf e S t) e
  refine ⟨sh, fun j S _ => rfl, fun e j S hS => hlf e S _ hS, fun e i S hi =>
    exists_inv_of_isUnit_coord _ ?_⟩
  induction e with
  | zero =>
    intro k
    have hle : D 0 S ≤ nonzeroLocus (s i) := by
      rw [hD0]
      exact iInf₂_le i hi
    exact SecOn.isUnit_rs_of_le_nonzeroLocus (s i) k (inf_le_right : D 0 S ⊓ (N 0).U k ≤ (N 0).U k)
      (inf_le_left.trans hle)
  | succ e ih =>
    intro k
    refine isUnit_coord_of_redL I Y β hβ (fun e => pw (N e) (d : ℤ))
      (fun e => pullPow (v e) (d : ℤ))
      (fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩) e (hDβ e S)
      (SecOnR.of _ _ _ (sh (e + 1) i S)) (fun q => ?_) k
    have hr : red I Y N D β hβ v hN hge (d : ℤ) e S (SecOnR.of _ _ _ (sh (e + 1) i S)) =
        SecOnR.of _ _ _ (sh e i S) := hlf e S (sh e i S) ⟨i, hi⟩
    change IsUnit (SecOnR.coord (red I Y N D β hβ v hN hge (d : ℤ) e S
      (SecOnR.of _ _ _ (sh (e + 1) i S))) q)
    rw [hr]
    exact ih q

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalLiftVeryAmpleSectionsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_lift_very_ample_sections : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℕ) (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))) (hs : VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s) (D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens) (hD0 : ∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) (hDβ : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) (hDm : ∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) (hDi : ∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) (hDc : ∀ e, ⨆ i, D e {i} = ⊤) (hDa : ∀ e S, S.Nonempty → IsAffineOpen (D e S)), ∃ sh : ∀ e (j : Fin (m + 1)) (S : Finset (Fin (m + 1))), SecOn (pw (N e) (d : ℤ)) (D e S), (∀ j S, S.Nonempty → sh 0 j S = GlobalTheory.LB.ofSec (s j) (D 0 S)) ∧ (∀ e j S, S.Nonempty → red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) (d : ℤ) e S (SecOnR.of _ _ _ (sh (e + 1) j S)) = SecOnR.of _ _ _ (sh e j S)) ∧ (∀ e i S, i ∈ S → ∃ y : SecOn (pw (N e) (-(d : ℤ))) (D e S), secMulOn rfl (sh e i S) y = oneOn (N e) (add_neg_cancel (d : ℤ)) (D e S)) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_lifts_tower | exact GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_lifts_tower | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_lifts_tower <;> assumption)
end
end
