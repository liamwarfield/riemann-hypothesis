module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliPrimePowerFullLevel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverTargetOfIsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianTripleDescentGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTwistOfLowers

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeNonemptyAtEveryLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyCmModuliOfDeeperLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyLevelQuot
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyLevelQuot
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.LevelTower

theorem zeta_eq_pow {n m : ℕ} (hm : 0 < m) (h : n ∣ m) : zeta n = zeta m ^ (m / n) := by
  obtain ⟨c, rfl⟩ := h
  have hn : 0 < n := Nat.pos_of_mul_pos_right hm
  have hc : 0 < c := Nat.pos_of_mul_pos_left hm
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
  rw [Nat.mul_div_cancel_left c hn, zeta, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem KA_le {l l₂ : Level H} (h : l.A ∣ l₂.A) : KA l ≤ KA l₂ := by
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro x (rfl | rfl)
  · exact (baseKA l₂).ρ.2
  · rw [zeta_eq_pow l₂.A_pos h]
    exact pow_mem (baseKA l₂).ζ.2 _

theorem base_rho (l : Level H) : (((baseKA l).ρ : KA l) : ℂ) = H.rt0 := rfl

theorem base_zeta (l : Level H) : (((baseKA l).ζ : KA l) : ℂ) = zeta l.A := rfl

theorem exists_inclusion' {F F' : IntermediateField ℚ ℂ} (h : F ≤ F') :
    ∃ j : F →+* F', ∀ x, ((j x : F') : ℂ) = ((x : F) : ℂ) :=
  ⟨(IntermediateField.inclusion h).toRingHom, fun x => IntermediateField.coe_inclusion h x⟩

theorem exists_inclusion {l l₂ : Level H} (h : l.A ∣ l₂.A) :
    ∃ j : KA l →+* KA l₂, (∀ x, ((j x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ j (baseKA l).ρ = (baseKA l₂).ρ ∧
      j (baseKA l).ζ = (baseKA l₂).ζ ^ (l₂.A / l.A) := by
  obtain ⟨j, hj⟩ := exists_inclusion' (KA_le h)
  refine ⟨j, hj, Subtype.ext ?_, Subtype.ext ?_⟩
  · rw [hj, base_rho, base_rho]
  · rw [hj, IntermediateField.coe_pow, base_zeta, base_zeta]
    exact zeta_eq_pow l₂.A_pos h

theorem finiteDimensional_KA (l : Level H) : FiniteDimensional ℚ (KA l) := by
  refine IntermediateField.finiteDimensional_adjoin ?_
  rintro x (rfl | rfl)
  · refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [H.sqrt_neg_disc_sq]
    exact (isIntegral_natCast H.d).neg
  · refine IsIntegral.of_pow l.A_pos ?_
    rw [show zeta l.A ^ l.A = 1 from (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one]
    exact isIntegral_one

theorem finite_of_numberField {K K' : Type} [Field K] [Field K'] [CharZero K] [CharZero K']
    [FiniteDimensional ℚ K'] (j : K →+* K') : j.Finite := by
  letI := j.toAlgebra
  exact Module.Finite.of_restrictScalars_finite ℚ K K'

theorem etale_of_numberField {K K' : Type} [Field K] [Field K'] [CharZero K] [CharZero K']
    [FiniteDimensional ℚ K'] (j : K →+* K') : Etale (spMap j) := by
  letI := j.toAlgebra
  haveI : Module.Finite K K' := finite_of_numberField j
  haveI : Algebra.FormallyEtale K K' := Algebra.FormallyEtale.of_isSeparable K K'
  haveI : Algebra.FinitePresentation K K' := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.Etale K K' := ⟨inferInstance, inferInstance⟩
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr this

end GlobalTheory.LevelTower

namespace GlobalTheory

open LevelTower

theorem nonempty_levelQuot : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → Nonempty (LevelQuot l Xo₂) := by
  intro hL hL2 hTh E _ _ _ H D l l₂ Xo₂ hpq hdvd
  have hA : l.A ∣ l₂.A := hdvd.2.2
  obtain ⟨jK, hj, hjρ, hjζ⟩ := exists_inclusion hA
  haveI := finiteDimensional_KA l₂
  obtain ⟨Ga, _, _, ρ, ν, h1, hmul, hν1, hνmul, hover, hlow, hfree, htrans⟩ :=
    GlobalTheory.LevelGroup.exists_group_action hL hL2 E H D l l₂ Xo₂ jK hpq hdvd hj
  have hq : IsQProjOver (Xo₂.s ≫ spMap jK) :=
    (isQProjOver_baseChange_and_finite_restrict _ _ jK Xo₂.X (Xo₂.s ≫ spMap jK)).2 Xo₂.s
      (finite_of_numberField jK) Xo₂.qproj
  obtain ⟨Y, π, sY, hπ, hG, hsep, hft, -⟩ :=
    exists_isGaloisCover_of_isQProjOver (KA l) Xo₂.X (Xo₂.s ≫ spMap jK) Ga ρ hq h1 hmul hover hfree
  have hqY : IsQProjOver sY := GlobalTheory.T.isQProjOver_target_of_isGaloisCover (KA l) _ Y π sY Ga ρ hG hsep hft (by rw [hπ]; exact hq)
  have hsm : SmoothOfRelativeDimension D.dim (π ≫ sY) := by
    rw [hπ]
    haveI := Xo₂.smooth
    haveI : Etale (spMap jK) := etale_of_numberField jK
    haveI : SmoothOfRelativeDimension 0 (spMap jK) := inferInstance
    have := smoothOfRelativeDimension_comp D.dim 0 Xo₂.s (spMap jK)
    rwa [Nat.add_zero] at this
  have hsY : SmoothOfRelativeDimension D.dim sY := GlobalTheory.T.smoothOfRelativeDimension_descends_etale_cover (KA l) _ Y π sY _ hG.etale hG.onto hft hsm
  obtain ⟨t', m, hνm, hp, ha, hk⟩ := GlobalTheory.T.exists_abelianTriple_descent_galoisCover hL hL2 hTh E H (KA l) _ Y π sY Ga ρ Xo₂.univ.t _ ν hG hqY
    Xo₂.univ.proper (obj_isAbelianScheme_dim_rigidified_sym E H D l₂ _ _ _ _ Xo₂.univ).2.1
    Xo₂.univ.ample Xo₂.univ.ktriv hν1 hνmul
  obtain ⟨ob, m', hη, hηA⟩ := obj_descend_lower_level hL hL2 E H D l l₂ _ _ (baseKA l) (baseKA l₂) jK _ Y π sY
    Xo₂.s Ga ρ Xo₂.univ (fun a => (ν a).φ) t' m hdvd hjρ hjζ
    hπ hG hνm hlow hp ha hk
  refine ⟨⟨Y, sY, hqY, hsY, ob, π, jK, hj, hπ, hG.fin, hG.etale, hG.onto, m', hη, hηA, ?_⟩⟩
  intro K _ _ y y' t mu mu' eM eA h₀ h₁ h₂
  obtain ⟨a, rfl⟩ := htrans K y y' t mu mu' eM eA h₀ h₁ h₂
  rw [Category.assoc, hG.inv]

end GlobalTheory

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyLevelQuotStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_levelQuot_of_level_dvd : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → Nonempty (LevelQuot l Xo₂) := by
  first | exact @GlobalTheory.nonempty_levelQuot | exact GlobalTheory.nonempty_levelQuot | (intros; apply GlobalTheory.nonempty_levelQuot <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelQuotientUnramifiedDualNumberPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelQuotientUnramifiedDualNumberPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.LevelQuotUnram

open GlobalTheory.TangentCrit (dualPt dualBase dualPt_dualBase dualPt_dualBase_assoc)

lemma subsingleton_sp_dual (k : Type) [Field k] : Subsingleton (Sp (DualNumber k)) := by
  refine ⟨fun a b => ?_⟩
  have key : ∀ a : PrimeSpectrum (DualNumber k), a.asIdeal = RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom := by
    intro a
    ext d
    constructor
    · intro hd
      by_contra h
      exact a.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hd
        (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (IsUnit.mk0 _ h)))
    · intro hd
      have h : d.fst = 0 := hd
      refine a.isPrime.mem_of_pow_mem 2 ?_
      have : d ^ 2 = 0 := by ext1 <;> simp [pow_two, h]
      rw [this]; exact a.asIdeal.zero_mem
  exact PrimeSpectrum.ext ((key a).trans (key b).symm)

lemma dualMap_cancel {k K : Type} [Field k] [Field K] (f : k →+* K) {X : Scheme.{0}}
    {g g' : Sp (DualNumber k) ⟶ X} (h : spMap (Chart.dualMapR f) ≫ g = spMap (Chart.dualMapR f) ≫ g') : g = g' := by
  have := subsingleton_sp_dual k
  refine TangentCrit.hom_ext_of_ker_inf (CommRingCat.ofHom (Chart.dualMapR f)) (CommRingCat.ofHom (Chart.dualMapR f))
    (fun z => ⟨IsLocalRing.closedPoint (DualNumber K), Subsingleton.elim _ _⟩) (fun d hd _ => ?_) h h
  have h₁ : f d.fst = 0 := by simpa [Chart.dualMapR] using congrArg TrivSqZeroExt.fst hd
  have h₂ : f d.snd = 0 := by simpa [Chart.dualMapR] using congrArg TrivSqZeroExt.snd hd
  exact TrivSqZeroExt.ext (f.injective (by simpa using h₁)) (f.injective (by simpa using h₂))

lemma constPt_dualMap {k K : Type} [Field k] [Field K] (f : k →+* K) {X : Scheme.{0}} (x : Sp (DualNumber k) ⟶ X) :
    constPt (spMap (Chart.dualMapR f) ≫ x) = spMap (Chart.dualMapR f) ≫ constPt x := by
  simp only [constPt, ← Category.assoc]
  congr 1
  simp only [← Spec.map_comp]
  congr 1
  ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

lemma exists_dual_lift {X Y : Scheme.{0}} (π : X ⟶ Y) [Smooth π] [IsAffineHom π] {k : Type} [Field k]
    (x : Sp (DualNumber k) ⟶ Y) (y : Sp k ⟶ X) (h : y ≫ π = dualPt k ≫ x) :
    ∃ x₂ : Sp (DualNumber k) ⟶ X, dualPt k ≫ x₂ = y ∧ x₂ ≫ π = x := by
  have := subsingleton_sp_dual k
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (x (IsLocalRing.closedPoint (DualNumber k)))) isOpen_univ
  have hx : Set.range x ⊆ U := by
    rintro _ ⟨z, rfl⟩
    rwa [Subsingleton.elim z (IsLocalRing.closedPoint (DualNumber k))]
  refine exists_lift_of_smooth_of_isAffineOpen π hU (hU.preimage π) le_rfl _ x y h hx ?_ ?_
  · rintro _ ⟨z, rfl⟩
    change π (y z) ∈ U
    rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
    exact hx ⟨_, rfl⟩
  · intro R A _ _ _ _ _ _ ρ hρ φ
    refine SmoothNilLift.exists_lift_of_nil ρ (fun c => ⟨TrivSqZeroExt.inl c, hρ _⟩) (fun d hd => ?_) φ
    have h : TrivSqZeroExt.fst d = 0 := (hρ d).symm.trans hd
    exact ⟨2, by ext1 <;> simp [pow_two, h]⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

lemma sab_cast {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f g : S' ⟶ S} (m : SABMap t' t f) (h : f = g) :
    ∃ n : SABMap t' t g, n.φ = m.φ := by
  subst h; exact ⟨m, rfl⟩

lemma torsion_rigid {X : Scheme.{0}} {k : Type} [Field k] (t : SAB H (Sp (DualNumber k))) (t₂ : SAB H X)
    (y : Sp k ⟶ X) (ν : SABMap t t₂ (dualBase k ≫ y)) {n : ℕ} (hn : IsUnit (n : Γ(X, ⊤)))
    (σ : 𝟙_ (Over (Sp (DualNumber k))) ⟶ t.G) (τ : 𝟙_ (Over X) ⟶ t₂.G) (hσ : σ ^ n = 1) (hτ : τ ^ n = 1)
    (h : dualPt k ≫ σ.left ≫ ν.φ = y ≫ τ.left) : σ.left ≫ ν.φ = (dualBase k ≫ y) ≫ τ.left := by
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback ν.cart (𝟙 _) (dualBase k ≫ y) (Category.id_comp _).symm
  have h₁ : (e σ).left = σ.left ≫ ν.φ := he σ
  have h₂ : (toUnit (Over.mk (dualBase k ≫ y)) ≫ τ).left = (dualBase k ≫ y) ≫ τ.left := by simp
  rw [← h₁, ← h₂]
  congr 1
  refine GrpTangent.eq_of_tangentMap_injective y (mulN t₂.G n)
    (GrpTangent.tangentMap_pullback_mulN_bijective t₂.G hn y).1 _ _ (Over.OverMorphism.ext ?_) ?_
  · change dualPt k ≫ Over.Hom.left (e σ) = dualPt k ≫ Over.Hom.left (toUnit (Over.mk (dualBase k ≫ y)) ≫ τ)
    rw [h₁, h₂, h, Category.assoc, dualPt_dualBase_assoc]
  · rw [GrpTangent.comp_mulN, GrpTangent.comp_mulN, ← comp_pow, hτ, comp_one, ← map_pow]
    exact (congrArg e hσ).trans (map_one e)

variable {D : Datum H}

section
variable {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s)

lemma pow_eq_of_add {L Γ : Type} [AddCommGroup L] [Group Γ] (f : L → Γ) (hf : ∀ a c, f (a + c) = f a * f c)
    (n : ℕ) (a : L) : f a ^ n = f (n • a) := by
  induction n with
  | zero =>
    have := hf 0 0
    rw [add_zero] at this
    rw [pow_zero, zero_smul]
    exact (mul_left_cancel (a := f 0) (by rw [← this, _root_.mul_one])).symm
  | succ n ih => rw [pow_succ, ih, add_smul, one_smul, hf]

lemma natCast_mem_Mb (l : Level H) : (l.M : 𝓞 E) ∈ l.Mb := by
  have h := Ideal.mem_span_singleton_self (l.M : 𝓞 E)
  rw [← l.prod] at h
  exact Ideal.mul_le_left h

lemma nsmul_mem_Mb (l : Level H) (a : D.La) : l.M • a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul (natCast_mem_Mb l) Submodule.mem_top

lemma eta_pow (a : D.La) : o.eta a ^ l.M = 1 := by
  rw [pow_eq_of_add o.eta o.eta_add, o.eta_ker _ (nsmul_mem_Mb l a)]

lemma etaA_pow (a : D.La) : o.etaA a ^ l.A = 1 := by
  rw [pow_eq_of_add o.etaA o.etaA_add, o.etaA_ker]

include b s in
lemma isUnit_nat {n : ℕ} (hn : 0 < n) : IsUnit (n : Γ(S, ⊤)) := by
  simpa using (b.unit n hn).map ((Scheme.ΓSpecIso (.of B)).inv ≫ s.appTop).hom

end

theorem unram_of_isAlgClosed (hL : Out.Laws) {l l₂ : Level H} (Xo₂ : Moduli D l₂) (Q : LevelQuot l Xo₂)
    (k : Type) [Field k] [IsAlgClosed k] (x : Sp (DualNumber k) ⟶ Q.X) (ob : Obj D l (baseKA l) (x ≫ Q.s))
    (m₁ : ObjMap ob Q.univ x) (m₂ : ObjMap ob Q.univ (constPt x)) : x = constPt x := by
  have := Q.fin
  have := Q.etale
  have := Q.onto
  obtain ⟨y, hy⟩ := GeomSurj.exists_lift_of_surjective Q.π (dualPt k ≫ x)
  obtain ⟨x₂, hx₂, hx⟩ := exists_dual_lift Q.π x y hy.symm
  have hc : constPt x₂ = dualBase k ≫ y := by rw [← hx₂]; rfl
  have hcπ : (dualBase k ≫ y) ≫ Q.π = constPt x := by rw [Category.assoc, ← hy]; rfl

  obtain ⟨o₀, ⟨r⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ (x ≫ Q.s)
    (dualPt k ≫ x ≫ Q.s) (dualPt k) rfl rfl (by simp [spMap]) ob
  have hr : r.toSABMap.φ ≫ m₁.toSABMap.φ = r.toSABMap.φ ≫ m₂.toSABMap.φ := by
    obtain ⟨n₁, hn₁⟩ := ObjMaps.exists_sab_comp m₁.toSABMap r.toSABMap
    obtain ⟨n₂, hn₂⟩ := ObjMaps.exists_sab_comp m₂.toSABMap r.toSABMap
    have e : dualPt k ≫ constPt x = dualPt k ≫ x := dualPt_dualBase_assoc k _
    obtain ⟨n₃, hn₃⟩ := sab_cast n₂ e
    rw [← hn₁, ← hn₂, ← hn₃]
    refine obj_rigid_closed hL E H D l _ _ _ _ _ _ _ _ Q.univ o₀ _ (Or.inl inferInstance) n₁ n₃
      fun a => ⟨_, rfl, ?_⟩
    rw [hn₃, hn₂, hn₁, reassoc_of% (r.eta a), reassoc_of% (r.eta a), m₁.eta, m₂.eta, reassoc_of% e]
  have hr' : ∀ {Z : Scheme.{0}} (z : Z ⟶ ob.t.G.left) (w : Z ⟶ Sp k), z ≫ ob.t.G.hom = w ≫ dualPt k →
      z ≫ m₁.toSABMap.φ = z ≫ m₂.toSABMap.φ := by
    intro Z z w hz
    rw [← r.cart.1.lift_fst z w hz, Category.assoc, Category.assoc]
    exact congrArg _ hr

  obtain ⟨o₁, ⟨n₁⟩⟩ := obj_pull E H D l₂ _ _ (baseKA l₂) (baseKA l₂) (RingHom.id _) _ _ Xo₂.s
    (x₂ ≫ Xo₂.s) x₂ rfl rfl (by simp [spMap]) Xo₂.univ
  obtain ⟨a₁, ha₁⟩ := ObjMaps.exists_sab_comp Q.m n₁.toSABMap
  obtain ⟨a₂, ha₂⟩ := sab_cast a₁ (hx.trans (Category.id_comp x).symm)
  obtain ⟨u, hu⟩ := ObjMaps.exists_sab_cancel m₁.toSABMap a₂
  obtain ⟨a₃, ha₃⟩ := ObjMaps.exists_sab_comp m₂.toSABMap u
  obtain ⟨a₄, ha₄⟩ := sab_cast a₃ ((Category.id_comp _).trans hcπ.symm)
  obtain ⟨n₂, hn₂⟩ := ObjMaps.exists_sab_cancel Q.m a₄
  have e₁ : n₁.toSABMap.φ ≫ Q.m.φ = u.φ ≫ m₁.toSABMap.φ := by rw [← ha₁, ← ha₂, hu]
  have e₂ : n₂.φ ≫ Q.m.φ = u.φ ≫ m₂.toSABMap.φ := by rw [← hn₂, ha₄, ha₃]
  have key : ∀ σ : 𝟙_ (Over (Sp (DualNumber k))) ⟶ o₁.t.G,
      dualPt k ≫ σ.left ≫ n₂.φ = dualPt k ≫ σ.left ≫ n₁.toSABMap.φ := by
    intro σ
    have hσ : σ.left ≫ o₁.t.G.hom = 𝟙 _ := Over.w σ
    refine Q.m.cart.1.hom_ext ?_ ?_
    · have := hr' (dualPt k ≫ σ.left ≫ u.φ) (𝟙 _) (by
        have w := u.cart.1.w
        simp only [Category.assoc, Category.id_comp, Category.comp_id] at w ⊢
        rw [w, hσ]
        exact Category.comp_id _)
      simp only [Category.assoc] at this ⊢
      rw [e₁, e₂, this]
    · have w₁ := n₁.cart.1.w
      have w₂ := n₂.cart.1.w
      simp only [Category.assoc]
      rw [w₁, w₂, reassoc_of% hσ, reassoc_of% hσ, dualPt_dualBase_assoc, hx₂]
  obtain ⟨n₃, hn₃⟩ := sab_cast n₂ hc.symm
  have h₂ : x₂ = constPt x₂ := by
    refine Xo₂.unram k x₂ o₁ ⟨n₁⟩ ⟨{ toSABMap := n₃, eta := fun a => ?_, etaA := fun a => ?_ }⟩
    · change _ ≫ n₃.φ = _
      rw [hn₃, hc]
      refine torsion_rigid _ _ y n₂ (isUnit_nat (b := baseKA l₂) (s := Xo₂.s) (by have := l₂.three_le; omega))
        _ _ (eta_pow o₁ a) (eta_pow Xo₂.univ a) ?_
      rw [key, n₁.eta, reassoc_of% hx₂]
    · change _ ≫ n₃.φ = _
      rw [hn₃, hc]
      refine torsion_rigid _ _ y n₂ (isUnit_nat (b := baseKA l₂) (s := Xo₂.s) l₂.A_pos)
        _ _ (etaA_pow o₁ a) (etaA_pow Xo₂.univ a) ?_
      rw [key, n₁.etaA, reassoc_of% hx₂]
  rw [← hcπ, ← hc, ← h₂, hx]

end GlobalTheory.LevelQuotUnram

namespace GlobalTheory

theorem levelQuot_unram : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo₂ : Moduli D l₂) (Q : LevelQuot l Xo₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (k : Type) [Field k] (x : Sp (DualNumber k) ⟶ Q.X) (ob : Obj D l (baseKA l) (x ≫ Q.s)), Nonempty (ObjMap ob Q.univ x) → Nonempty (ObjMap ob Q.univ (constPt x)) → x = constPt x := by
  rintro hL - E _ _ _ H D l l₂ Xo₂ Q - - k _ x ob ⟨m₁⟩ ⟨m₂⟩
  let f : k →+* AlgebraicClosure k := algebraMap _ _
  refine LevelQuotUnram.dualMap_cancel f ?_
  rw [← LevelQuotUnram.constPt_dualMap]
  obtain ⟨o', ⟨r⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ (x ≫ Q.s)
    ((spMap (Chart.dualMapR f) ≫ x) ≫ Q.s) (spMap (Chart.dualMapR f)) rfl rfl (by simp [spMap]) ob
  obtain ⟨n₁, -⟩ := ObjComp.objMap_comp m₁ r
  obtain ⟨n₂, -⟩ := ObjComp.objMap_comp m₂ r
  exact LevelQuotUnram.unram_of_isAlgClosed hL Xo₂ Q _ _ o' n₁ (LevelQuotUnram.constPt_dualMap f x ▸ n₂)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelQuotientUnramifiedDualNumberPointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelQuotient_unramified_dualNumberPoints : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo₂ : Moduli D l₂) (Q : LevelQuot l Xo₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (k : Type) [Field k] (x : Sp (DualNumber k) ⟶ Q.X) (ob : Obj D l (baseKA l) (x ≫ Q.s)), Nonempty (ObjMap ob Q.univ x) → Nonempty (ObjMap ob Q.univ (constPt x)) → x = constPt x := by
  first | exact @GlobalTheory.levelQuot_unram | exact GlobalTheory.levelQuot_unram | (intros; apply GlobalTheory.levelQuot_unram <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyCmModuliOfDeeperLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
namespace GlobalTheory.ZM

theorem moduli_of_deeper_level : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H), 1 ≤ D.p + D.q → l.Dvd l₂ → Nonempty (Moduli D l₂) → Nonempty (Moduli D l) := by
  intro L L2 hT E _ _ _ H D l l₂ hD hl ⟨Xo₂⟩
  obtain ⟨Q⟩ := GlobalTheory.T.nonempty_levelQuot_of_level_dvd L L2 hT E H D l l₂ Xo₂ hD hl
  exact ⟨{ X := Q.X, s := Q.s, qproj := Q.qproj, smooth := Q.smooth, univ := Q.univ,
           rep := GlobalTheory.T.levelQuotient_represents_reduced L L2 E H D l l₂ Xo₂ Q hD hl,
           unram := GlobalTheory.T.levelQuotient_unramified_dualNumberPoints L L2 E H D l l₂ Xo₂ Q hD hl }⟩
end GlobalTheory.ZM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyCmModuliOfDeeperLevelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_cmModuli_of_deeper_level : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H), 1 ≤ D.p + D.q → l.Dvd l₂ → Nonempty (Moduli D l₂) → Nonempty (Moduli D l) := by
  first | exact @GlobalTheory.ZM.moduli_of_deeper_level | exact GlobalTheory.ZM.moduli_of_deeper_level | (intros; apply GlobalTheory.ZM.moduli_of_deeper_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelWithOddPrimeFirstNumber
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelWithOddPrimeFirstNumber
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem exists_prime_level :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H), ∃ n : ℕ, n.Prime ∧ Odd n ∧
      ∀ A₀ : ℕ, 0 < A₀ → ∃ l₀ l₂ : Level H, l₀.M = n ∧ l₀.A = A₀ ∧ l₀.Dvd l₂ ∧ l.Dvd l₂ := by
  intro E _ _ _ H l
  have hM1 : l.M ≠ 1 := by have := l.three_le; omega
  obtain ⟨n, hn, hnM⟩ := Nat.exists_prime_and_dvd hM1
  have hodd : Odd n := Odd.of_dvd_nat l.odd hnM
  have h3 : 3 ≤ n := by
    have h2 := hn.two_le
    rcases hodd with ⟨k, hk⟩
    omega
  refine ⟨n, hn, hodd, fun A₀ hA₀ => ?_⟩
  have hmap : (l.Mb ⊔ Ideal.span {(n : 𝓞 E)}).map (H.bar : 𝓞 E →+* 𝓞 E) =
      l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ⊔ Ideal.span {(n : 𝓞 E)} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast]
  have hMn : Ideal.span {(l.M : 𝓞 E)} ≤ Ideal.span {(n : 𝓞 E)} :=
    Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast hnM)
  refine ⟨⟨n, h3, hodd, l.Mb ⊔ Ideal.span {(n : 𝓞 E)}, ?_, ?_, ?_, A₀, hA₀⟩,
    ⟨l.M, l.three_le, l.odd, l.Mb, l.fromK, l.prod, l.coprime, Nat.lcm l.A A₀, Nat.lcm_pos l.A_pos hA₀⟩,
    rfl, rfl, ⟨hnM, le_sup_left, Nat.dvd_lcm_right _ _⟩, ⟨dvd_rfl, le_rfl, Nat.dvd_lcm_left _ _⟩⟩
  · apply le_antisymm
    · apply sup_le
      · refine l.fromK.le.trans (Ideal.span_mono ?_)
        intro a ha
        exact ⟨Ideal.mem_sup_left ha.1, ha.2⟩
      · refine Ideal.span_mono ?_
        intro a ha
        rw [Set.mem_singleton_iff] at ha
        subst ha
        exact ⟨Ideal.mem_sup_right (Ideal.mem_span_singleton_self _), natCast_mem _ _⟩
    · exact Ideal.span_le.2 fun a ha => ha.1
  · rw [hmap, Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup, l.prod]
    set N : Ideal (𝓞 E) := Ideal.span {(n : 𝓞 E)}
    apply le_antisymm
    · refine sup_le (sup_le hMn ?_) (sup_le ?_ ?_) <;>
        first | exact Ideal.mul_le_left | exact Ideal.mul_le_right
    · calc N = N * (l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) := by rw [l.coprime, Ideal.mul_top]
        _ = l.Mb * N ⊔ N * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by rw [Ideal.mul_sup, mul_comm N l.Mb]
        _ ≤ _ := sup_le (le_sup_right.trans le_sup_left) (le_sup_left.trans le_sup_right)
  · rw [hmap, eq_top_iff, ← l.coprime]
    exact sup_le_sup le_sup_left le_sup_left

end GlobalTheory.ZM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelWithOddPrimeFirstNumberStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.exists_level_with_odd_prime_first_number : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H), ∃ n : ℕ, n.Prime ∧ Odd n ∧ ∀ A₀ : ℕ, 0 < A₀ → ∃ l₀ l₂ : Level H, l₀.M = n ∧ l₀.A = A₀ ∧ l₀.Dvd l₂ ∧ l.Dvd l₂ := by
  first | exact @GlobalTheory.ZM.exists_prime_level | exact GlobalTheory.ZM.exists_prime_level | (intros; apply GlobalTheory.ZM.exists_prime_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeNonemptyAtEveryLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem moduli_nonempty_all_levels : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → N1ab := by
  intro h1 h2 h3 h4 E _ _ _ H D l hD
  obtain ⟨n, hn, hodd, hl⟩ := GlobalTheory.T.exists_level_with_odd_prime_first_number E H l
  obtain ⟨j, hj⟩ := GlobalTheory.T.exists_moduli_prime_power_fullLevel h1 h2 h3 h4 E H D n hD hn hodd
  obtain ⟨l₀, l₂, hM, hA, h02, h2'⟩ := hl ((n ^ j) ^ 2) (pow_pos (pow_pos hn.pos j) 2)
  exact GlobalTheory.T.nonempty_cmModuli_of_deeper_level h1 h2 h3 E H D l l₂ hD h2'
    (GlobalTheory.T.nonempty_moduli_of_level_dvd h1 h2 E H D l₀ l₂ hD h02 (hj l₀ hM hA))

end GlobalTheory.ZM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeNonemptyAtEveryLevelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduliScheme_nonempty_at_every_level : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → N1ab := by
  first | exact @GlobalTheory.ZM.moduli_nonempty_all_levels | exact GlobalTheory.ZM.moduli_nonempty_all_levels | (intros; apply GlobalTheory.ZM.moduli_nonempty_all_levels <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.Moduli

theorem moduli_scheme_exists : N1ab :=
  GlobalTheory.T.moduliScheme_nonempty_at_every_level GlobalTheory.T.all_six_abelian_scheme_laws_hold.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.1 GlobalTheory.T.theorem_of_cube_polAbelianScheme GlobalTheory.T.theta_uniformisation_complex_abelian_varieties

end GlobalTheory.Moduli
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevelStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_moduli_scheme_polarized_abelian_level : N1ab := by
  first | exact @GlobalTheory.Moduli.moduli_scheme_exists | exact GlobalTheory.Moduli.moduli_scheme_exists | (intros; apply GlobalTheory.Moduli.moduli_scheme_exists <;> assumption)
end
