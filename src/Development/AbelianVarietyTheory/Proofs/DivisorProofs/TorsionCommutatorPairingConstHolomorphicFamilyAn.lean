module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetWittFrameDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulEqOfLogDerivationExtendEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopBijectiveAndSurjectiveNormalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMultiplierIntegralImaginary
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCommutatorPairingConstHolomorphicFamilyAn
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCommutatorPairingConstHolomorphicFamilyAn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HolTorsionAny

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left}

theorem triv_step (hA : IsAbelianScheme G) (hL : L.IsLB) {T : Over S} (a c : T ⟶ G) (n : ℕ) :
    GlobalTheory.AbLaw.Triv (LB.LinComb L (K := Fin 6)
      ![(a ^ n * c).left, c.left, (a ^ n).left, (1 : T ⟶ G).left, (a * c).left, a.left]
      ![1, (n : ℤ) - 1, -1, 1 - (n : ℤ), -(n : ℤ), (n : ℤ)]) := by
  induction n with
  | zero =>
    have h := GlobalTheory.CubeTop.cubeTheorem S G hA L hL T 1 1 c
    simp only [_root_.one_mul] at h
    obtain ⟨t, ht⟩ := h
    obtain ⟨u, hu, -⟩ := exists_gen hL (φ' := ![((a ^ 0) * c).left, c.left, (a ^ 0).left, (1 : T ⟶ G).left,
      (a * c).left, a.left]) (ε' := ![1, ((0 : ℕ) : ℤ) - 1, -1, 1 - ((0 : ℕ) : ℤ), -((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ)])
      (fun U _ h => by
        simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
          pow_zero, _root_.one_mul]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_zpow, ofMul_one]
        push_cast
        module) t ht
    exact ⟨u, hu⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    have h := GlobalTheory.CubeTop.cubeTheorem S G hA L hL T a (a ^ n) c
    rw [← pow_succ'] at h
    obtain ⟨q, hq⟩ := h
    obtain ⟨u, hu, -⟩ := exists_gen hL (φ' := ![(a ^ (n + 1) * c).left, c.left, (a ^ (n + 1)).left,
      (1 : T ⟶ G).left, (a * c).left, a.left])
      (ε' := ![1, ((n + 1 : ℕ) : ℤ) - 1, -1, 1 - ((n + 1 : ℕ) : ℤ), -((n + 1 : ℕ) : ℤ), ((n + 1 : ℕ) : ℤ)])
      (fun U _ h => by
        rw [Fintype.prod_sum_type]
        simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
          Sum.elim_inl, Sum.elim_inr, Matrix.cons_val]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_zpow, ofMul_one]
        push_cast
        module) (LB.mulGen L _ _ _ _ t q) (DVR.mulGen_isGen _ _ _ _ _ _ _ ht hq)
    exact ⟨u, hu⟩

theorem exists_theta_local (hA : IsAbelianScheme G) (hL : L.IsLB) {k : ℕ} {T : Over S} (x : T ⟶ G) (hx : x ^ k = 1)
    (p : T.left) : ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : Out.ThetaGrp G L (k : ℤ) (Out.overRes V), θ.pt = Out.overResι V ≫ x := by
  obtain ⟨V, hV, w, hw⟩ := exists_local_gen hL (Y := T.left) ![(1 : T ⟶ G).left, x.left] ![(k : ℤ), -(k : ℤ)] p
  refine ⟨V, hV, ?_⟩
  let xV : Out.overRes V ⟶ G := Out.overResι V ≫ x
  let a : Out.overRes V ⊗ G ⟶ G := fst (Out.overRes V) G ≫ xV
  let c : Out.overRes V ⊗ G ⟶ G := snd (Out.overRes V) G
  have ha : a ^ k = 1 := by
    show (fst (Out.overRes V) G ≫ Out.overResι V ≫ x) ^ k = 1
    rw [← MonObj.comp_pow, ← MonObj.comp_pow, hx, MonObj.comp_one, MonObj.comp_one]
  have hP := triv_step hA hL a c k
  rw [ha, _root_.one_mul] at hP
  obtain ⟨t, ht⟩ := hP
  have e₁ : (fst (Out.overRes V) G).left ≫ V.ι ≫ (1 : T ⟶ G).left = (1 : Out.overRes V ⊗ G ⟶ G).left := by
    have : (fst (Out.overRes V) G ≫ Out.overResι V ≫ (1 : T ⟶ G)) = 1 := by
      rw [MonObj.comp_one, MonObj.comp_one]
    rw [← this]
    rfl
  have e₂ : (fst (Out.overRes V) G).left ≫ V.ι ≫ x.left = a.left := rfl
  obtain ⟨u, hu, -⟩ := exists_gen hL (φ' := ![(snd (Out.overRes V) G).left, (Out.translPt G xV).left])
    (ε' := ![(k : ℤ), -(k : ℤ)])
    (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Sum.elim_inl, Sum.elim_inr, Matrix.cons_val, e₁, e₂]
      rw [translPt_eq]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_one]
      module)
    (LB.mulGen L _ _ _ _ t (LB.pullGen L _ _ w (fst (Out.overRes V) G).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.pullGen_isGen _ _ _ _ hw _))
  exact ⟨⟨xV, u, hu⟩, rfl⟩

theorem exists_weilIs_pow_eq_one (hA : IsAbelianScheme G) (hL : L.IsLB) {k : ℕ} {T : Over S} {x y : T ⟶ G}
    (hx : x ^ k = 1) (hy : y ^ k = 1) : ∃ e : Γ(T.left, ⊤)ˣ, e ^ k = 1 ∧ Out.WeilIs G L (k : ℤ) x y e := by
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  obtain ⟨e, he⟩ := GlobalTheory.CommutatorPairing.exists_weilIs (k := (k : ℤ)) hG hA hL
    (fun p => exists_theta_local hA hL x hx p) (fun p => exists_theta_local hA hL y hy p)
  have pw : ∀ m : ℕ, Out.WeilIs G L (k : ℤ) (x ^ (m + 1)) y (e ^ (m + 1)) := fun m => by
    induction m with
    | zero => simpa only [zero_add, pow_one] using he
    | succ m ih =>
      rw [pow_succ x (m + 1), pow_succ e (m + 1)]
      exact GlobalTheory.DiagPairing.weilIs_mul_left hG hA hL ih he
  have hk := pw k
  rw [pow_succ x k, hx, _root_.one_mul] at hk
  have := GlobalTheory.CommutatorPairing.weilIs_unique hG hA hL hk he
  rw [pow_succ, mul_eq_right] at this
  exact ⟨e, this, he⟩

end GlobalTheory.HolTorsionAny

namespace GlobalTheory


open HolTorsion HolTorsionAny in
theorem torsion_eq_and_weilIs_of_isHolTo_anyLB : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (G : Over X) [GrpObj G] [IsCommMonObj G] (L : LB G.left), LocallyOfFiniteType s → IsAbelianScheme G → L.IsLB → ∀ (m k : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (x x' : ∀ b, Over.mk (y b) ⟶ G) (c : ℂˣ) (b₀ : Fin m → ℂ), 0 < k → IsOpen B → IsPreconnected B → b₀ ∈ B → (∀ b ∈ B, y b ≫ s = spMap (RingHom.id ℂ)) → IsHolTo B (fun b => (x b).left) → IsHolTo B (fun b => (x' b).left) → (∀ b ∈ B, x b ^ k = 1 ∧ x' b ^ k = 1) → ((x b₀ = x' b₀ → ∀ b ∈ B, x b = x' b) ∧ (Out.WeilIs G L k (x b₀) (x' b₀) (unitOn c) → ∀ b ∈ B, Out.WeilIs G L k (x b) (x' b) (unitOn c))) := by
  intro X s G _ _ L _ hA hLB m k B y x x' c b₀ hk _ hB hb₀ _ hx hx' htor
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds

  have hku : IsUnit (k : Γ(X, ⊤)) := by
    have h₁ : IsUnit ((k : ℂ)) := isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hk.ne')
    have h₂ := (h₁.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom).map s.appTop.hom
    simpa only [map_natCast] using h₂
  haveI : FormallyUnramified (Out.mulA G k).left := GlobalTheory.formallyUnramified_mulA X G k hku
  haveI : Smooth G.hom := hA.smooth
  haveI : IsProper G.hom := hA.proper
  haveI : LocallyOfFiniteType ((Out.mulA G k).left ≫ G.hom) := by rw [Over.w]; infer_instance
  haveI : LocallyOfFiniteType (Out.mulA G k).left := locallyOfFiniteType_of_comp _ G.hom
  haveI : IsSeparated ((Out.mulA G k).left ≫ G.hom) := by rw [Over.w]; infer_instance
  haveI : IsSeparated (Out.mulA G k).left := IsSeparated.of_comp _ G.hom
  let o : X ⟶ G.left := (η[G] : 𝟙_ (Over X) ⟶ G).left
  have ho : o ≫ G.hom = 𝟙 X := Over.w (η[G] : 𝟙_ (Over X) ⟶ G)
  have hkill : ∀ (T : Over X) (u : T ⟶ G), u ^ k = 1 ↔ u.left ≫ (Out.mulA G k).left = T.hom ≫ o := by
    intro T u
    have e₁ : u.left ≫ (Out.mulA G k).left = (u ^ k).left := by
      rw [← Over.comp_left, Out.mulA, MonObj.comp_pow, Category.comp_id]
    have e₂ : T.hom ≫ o = (1 : T ⟶ G).left := by
      rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    rw [e₁, e₂]
    exact ⟨fun h => by rw [h], fun h => Over.OverMorphism.ext h⟩
  let p := pullback.fst (Out.mulA G k).left o
  let q := pullback.snd (Out.mulA G k).left o
  have H : IsPullback p q (Out.mulA G k).left o := IsPullback.of_hasPullback _ _
  haveI : FormallyUnramified q := MorphismProperty.of_isPullback (P := @FormallyUnramified) H ‹_›
  haveI : LocallyOfFiniteType q := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) H ‹_›
  haveI : IsSeparated q := MorphismProperty.of_isPullback (P := @IsSeparated) H ‹_›
  have hpq : p ≫ G.hom = q := by
    rw [← Over.w (Out.mulA G k), ← Category.assoc, H.w, Category.assoc, ho, Category.comp_id]
  have hy : IsHolTo B y := isHolTo_congr (isHolTo_comp hx G.hom) fun b _ => (Over.w (x b)).symm
  obtain ⟨a, ha, hab⟩ := exists_isHolTo_lift H hx hy (fun b hb => (hkill _ _).1 (htor b hb).1) hb₀
  obtain ⟨a', ha', hab'⟩ := exists_isHolTo_lift H hx' hy (fun b hb => (hkill _ _).1 (htor b hb).2) hb₀
  obtain ⟨z, hz, hzb⟩ := exists_isHolTo_lift (IsPullback.of_hasPullback q q) ha ha'
    (fun b hb => (hab b hb).2.trans (hab' b hb).2.symm) hb₀
  refine ⟨fun h₀ b hb => ?_, fun h₀ b hb => ?_⟩
  · have e₀ : a b₀ = a' b₀ := H.hom_ext (by rw [(hab b₀ hb₀).1, (hab' b₀ hb₀).1, h₀])
      (by rw [(hab b₀ hb₀).2, (hab' b₀ hb₀).2])
    have e := comp_eq_of_unramified q hz hB hb₀ hb (by rw [(hzb b₀ hb₀).1, (hzb b₀ hb₀).2, e₀])
    rw [(hzb b hb).1, (hzb b hb).2] at e
    apply Over.OverMorphism.ext
    rw [← (hab b hb).1, ← (hab' b hb).1, e]
  · let T : Over X := Over.mk (pullback.fst q q ≫ q)
    let u : T ⟶ G := Over.homMk (pullback.fst q q ≫ p) (by
      show (pullback.fst q q ≫ p) ≫ G.hom = pullback.fst q q ≫ q
      rw [Category.assoc, hpq])
    let v : T ⟶ G := Over.homMk (pullback.snd q q ≫ p) (by
      show (pullback.snd q q ≫ p) ≫ G.hom = pullback.fst q q ≫ q
      rw [Category.assoc, hpq, pullback.condition])
    have hu : u ^ k = 1 := (hkill T u).2 (by
      show (pullback.fst q q ≫ p) ≫ _ = (pullback.fst q q ≫ q) ≫ o
      rw [Category.assoc, H.w, Category.assoc])
    have hv : v ^ k = 1 := (hkill T v).2 (by
      show (pullback.snd q q ≫ p) ≫ _ = (pullback.fst q q ≫ q) ≫ o
      rw [Category.assoc, H.w, pullback.condition, Category.assoc])
    obtain ⟨e, hek', he⟩ := exists_weilIs_pow_eq_one hA hLB hu hv
    have hek : e.val ^ k = 1 := congrArg Units.val hek'
    have hpull : ∀ w ∈ B, Out.WeilIs G L k (x w) (x' w) (Units.map (z w).appTop.hom.toMonoidHom e) := by
      intro w hw
      let h : Over.mk (y w) ⟶ T := Over.homMk (z w) (by
        show z w ≫ pullback.fst q q ≫ q = y w
        rw [← Category.assoc, (hzb w hw).1, (hab w hw).2])
      have e₁ : h ≫ u = x w := Over.OverMorphism.ext (by
        show z w ≫ pullback.fst q q ≫ p = _
        rw [← Category.assoc, (hzb w hw).1, (hab w hw).1])
      have e₂ : h ≫ v = x' w := Over.OverMorphism.ext (by
        show z w ≫ pullback.snd q q ≫ p = _
        rw [← Category.assoc, (hzb w hw).2, (hab' w hw).1])
      have := GlobalTheory.CommPairing.weilIs_pull hG hA hLB h he
      rw [e₁, e₂] at this
      exact this
    have e₀ : Units.map (z b₀).appTop.hom.toMonoidHom e = unitOn c :=
      GlobalTheory.CommutatorPairing.weilIs_unique hG hA hLB (hpull b₀ hb₀) h₀
    have e₁ : Units.map (z b).appTop.hom.toMonoidHom e = Units.map (z b₀).appTop.hom.toMonoidHom e :=
      Units.ext ((val_map_appTop (z b) e.val).trans
        ((congrArg _ (valAt'_eq_of_pow_eq_one hz hB hk hek hb₀ hb)).trans (val_map_appTop (z b₀) e.val).symm))
    have := hpull b hb
    rw [e₁, e₀] at this
    exact this

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCommutatorPairingConstHolomorphicFamilyAnStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_commutatorPairing_const_holomorphicFamily_anyLineBundle : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (G : Over X) [GrpObj G] [IsCommMonObj G] (L : LB G.left), LocallyOfFiniteType s → IsAbelianScheme G → L.IsLB → ∀ (m k : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (x x' : ∀ b, Over.mk (y b) ⟶ G) (c : ℂˣ) (b₀ : Fin m → ℂ), 0 < k → IsOpen B → IsPreconnected B → b₀ ∈ B → (∀ b ∈ B, y b ≫ s = spMap (RingHom.id ℂ)) → IsHolTo B (fun b => (x b).left) → IsHolTo B (fun b => (x' b).left) → (∀ b ∈ B, x b ^ k = 1 ∧ x' b ^ k = 1) → ((x b₀ = x' b₀ → ∀ b ∈ B, x b = x' b) ∧ (Out.WeilIs G L k (x b₀) (x' b₀) (unitOn c) → ∀ b ∈ B, Out.WeilIs G L k (x b) (x' b) (unitOn c))) := by
  first | exact @GlobalTheory.torsion_eq_and_weilIs_of_isHolTo_anyLB | exact GlobalTheory.torsion_eq_and_weilIs_of_isHolTo_anyLB | (intros; apply GlobalTheory.torsion_eq_and_weilIs_of_isHolTo_anyLB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernel
noncomputable section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThKWeil

theorem cone_zero (F : Type) [Field F] [NumberField F] (n d : ℕ) (c : ℝ) :
    ∫⁻ t in GlobalTheory.SiegelSet.cone 0 c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * d)) *
      ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) < ⊤ := by
  have e : ∀ t : Fin 0 → ℝ, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * d)) *
      ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) = 1 := fun t => by
    simp [GlobalTheory.SiegelSet.modulus]
  simp only [e, setLIntegral_const, one_mul]
  refine (measure_mono (Set.subset_univ _)).trans_lt ?_
  rw [MeasureTheory.volume_pi, Measure.pi_univ]
  simp

theorem mul_le_max_mul {C H₁ H P : ℝ} (h0 : 0 ≤ H₁) (h1 : H₁ ≤ H) (hP : 0 ≤ P) : C * H₁ * P ≤ max C 0 * H * P := by
  refine mul_le_mul_of_nonneg_right ?_ hP
  calc C * H₁ ≤ max C 0 * H₁ := mul_le_mul_of_nonneg_right (le_max_left _ _) h0
    _ ≤ max C 0 * H := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in
theorem one_le_ht {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (h : UA σ J) : (1 : ℝ) ≤ ht h := by
  have := GlobalTheory.AdelicU.one_le_heightGL (F := F) h.1
  exact_mod_cast this


open scoped Classical in
theorem weilConv (hKP : KP) : WeilConv := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP hdim
  have hb := GlobalTheory.T.theta_basic_properties hKP.base F E σ B n d X W M χX χW om r s r' s' hP
  have hcm := hP.base.cm
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hcm
  have hJ' : IsHermND σ ((1 : E) • X.J.map σ) := by
    rw [one_smul]; exact GlobalTheory.UnitaryVol.isHermND_map hσ hP.herm
  let e : UA σ X.J ≃* GAd σ ((1 : E) • X.J.map σ) :=
    MulEquiv.subgroupCongr (GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := X.J) hσ (one_ne_zero : (1 : E) ≠ 0))
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  have he' : Continuous e.symm := continuous_subtype_val.subtype_mk _
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI : ContinuousMul (UA σ X.J) := ⟨by
    have h3 : (fun p : UA σ X.J × UA σ X.J => p.1 * p.2) = fun p => e.symm (e p.1 * e p.2) :=
      funext fun p => by rw [← map_mul, MulEquiv.symm_apply_apply]
    rw [h3]
    exact he'.comp ((he.comp continuous_fst).mul (he.comp continuous_snd))⟩
  haveI := hP.good.haar
  haveI := GlobalTheory.UnitaryVol.countable_ratU σ X.J
  haveI : MeasurableMul (UA σ X.J) :=
    ⟨fun g => (continuous_const.mul continuous_id).measurable, fun g => (continuous_id.mul continuous_const).measurable⟩
  have hH : (M.μ.map e).IsHaarMeasure := MulEquiv.isHaarMeasure_map M.μ e he he'
  obtain ⟨r₀, Xf, Yf, hW⟩ := GlobalTheory.SiegelSet.exists_isWittFrame hcm hJ'
  obtain ⟨hr₀, hs₀⟩ := GlobalTheory.T.witt_rank_le_hermitian_signature F E σ B n X r s hP.base hP.herm r₀ Xf Yf hW
  obtain ⟨K, Ω, c, hK, hΩ, -, hc, -, hcl, hcov, ⟨C₀, hC₀, hconj⟩, hmeas, -, -⟩ :=
    hKP.siegelSetUnitary F E σ hcm n ((1 : E) • X.J.map σ) hJ' r₀ Xf Yf hW
  obtain ⟨-, C₁, hC₁⟩ := hmeas _ hH
  have hSm : MeasurableSet (GlobalTheory.SiegelSet.siegelSet σ ((1 : E) • X.J.map σ) Xf Yf Ω c K) := hcl.measurableSet
  have hS' : MeasurableSet (e ⁻¹' GlobalTheory.SiegelSet.siegelSet σ ((1 : E) • X.J.map σ) Xf Yf Ω c K) :=
    hSm.preimage he.measurable
  have hScov : ∀ g : UA σ X.J, ∃ γ ∈ ratU σ X.J,
      γ * g ∈ e ⁻¹' GlobalTheory.SiegelSet.siegelSet σ ((1 : E) • X.J.map σ) Xf Yf Ω c K := fun g => by
    obtain ⟨γ, hγ, s', hs', hgs⟩ := hcov (e g)
    obtain ⟨u, -, hu⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
    have hr : e.symm γ ∈ ratU σ X.J := Subgroup.mem_subgroupOf.2 ⟨u, hu⟩
    refine ⟨(e.symm γ)⁻¹, inv_mem hr, ?_⟩
    show e ((e.symm γ)⁻¹ * g) ∈ GlobalTheory.SiegelSet.siegelSet σ ((1 : E) • X.J.map σ) Xf Yf Ω c K
    rw [map_mul, map_inv, MulEquiv.apply_symm_apply, hgs, inv_mul_cancel_left]
    exact hs'
  have hI : ∫⁻ t in GlobalTheory.SiegelSet.cone r₀ c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * d)) *
      ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) < ⊤ := by
    rcases Nat.eq_zero_or_pos r₀ with h0 | h0
    · subst h0
      exact cone_zero F n d c
    · exact GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top F n r₀ d hc (by omega)
  set I := ∫⁻ t in GlobalTheory.SiegelSet.cone r₀ c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * d)) *
      ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) with hIdef
  have key : ∀ (θ0 : UA σ X.J → ℂ) (A : ℝ), Continuous θ0 → (∀ γ ∈ ratU σ X.J, ∀ g, θ0 (γ * g) = θ0 g) →
      (∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a →
        ∀ k ∈ K, ‖θ0 (e.symm (p * a * k))‖ ≤ A * ∏ i, t i ^ (Module.finrank ℚ F * d)) →
      IntegrableOn θ0 M.dom M.μ ∧ ∫ g in M.dom, ‖θ0 g‖ ∂M.μ ≤ (C₁ : ℝ) * max A 0 * I.toReal := by
    intro θ0 A hθc hθi hθb
    have hA : 0 ≤ max A 0 := le_max_right _ _
    have hle : ∫⁻ g in M.dom, ‖θ0 g‖ₑ ∂M.μ ≤ C₁ * (ENNReal.ofReal (max A 0) * I) := by
      calc ∫⁻ g in M.dom, ‖θ0 g‖ₑ ∂M.μ
          ≤ ∫⁻ g in e ⁻¹' GlobalTheory.SiegelSet.siegelSet σ ((1 : E) • X.J.map σ) Xf Yf Ω c K, ‖θ0 g‖ₑ ∂M.μ :=
            GlobalTheory.lintegral_fundamentalDomain_le_of_meets_orbits (ratU σ X.J) M.μ hP.good.dom hS' hScov
              hθc.enorm.measurable (fun γ hγ g => by rw [hθi γ hγ g])
        _ = ∫⁻ x in GlobalTheory.SiegelSet.siegelSet σ ((1 : E) • X.J.map σ) Xf Yf Ω c K, ‖θ0 (e.symm x)‖ₑ ∂(M.μ.map e) := by
            rw [setLIntegral_map (f := fun x => ‖θ0 (e.symm x)‖ₑ) hSm (hθc.comp he').enorm.measurable he.measurable]
            simp only [MulEquiv.symm_apply_apply]
        _ ≤ C₁ * ∫⁻ t in GlobalTheory.SiegelSet.cone r₀ c, ENNReal.ofReal (max A 0 * ∏ i, t i ^ (Module.finrank ℚ F * d)) *
              ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) := by
            refine hC₁ (fun x => ‖θ0 (e.symm x)‖ₑ) _ (by fun_prop) fun q hq t ht a ha k hk => ?_
            have ht0 : ∀ i, 0 < t i := ht.1
            have hP0 : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ F * d) :=
              Finset.prod_nonneg fun i _ => pow_nonneg (ht0 i).le _
            rw [← ofReal_norm_eq_enorm]
            exact ENNReal.ofReal_le_ofReal
              ((hθb q hq t ht a ha k hk).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hP0))
        _ = C₁ * (ENNReal.ofReal (max A 0) * I) := by
            rw [hIdef, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            congr 1
            exact lintegral_congr fun t => by rw [ENNReal.ofReal_mul hA, mul_assoc]
    refine ⟨⟨hθc.aestronglyMeasurable, hle.trans_lt (by finiteness)⟩, ?_⟩
    rw [integral_norm_eq_lintegral_enorm hθc.aestronglyMeasurable]
    refine (ENNReal.toReal_mono (by finiteness) hle).trans (le_of_eq ?_)
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hA, ENNReal.coe_toReal]
    ring

  have pres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d) := fun x Φ hΦ =>
    (IsUWeilPair.isUSplitting hP.weil).pres x Φ hΦ
  have thAdd : ∀ Φ ∈ schA F (Fin n × Fin d), ∀ Ψ ∈ schA F (Fin n × Fin d), ∀ g h,
      theta om (Φ + Ψ) g h = theta om Φ g h + theta om Ψ g h := fun Φ hΦ Ψ hΨ g h => by
    simp only [theta, map_add (f := _)]
    exact thetaSum_add F (pres _ Φ hΦ) (pres _ Ψ hΨ)
  have thSmul : ∀ (a : ℂ) Φ g h, theta om (a • Φ) g h = a * theta om Φ g h := fun a Φ g h => by
    simp only [theta, map_smul]
    exact thetaSum_smul F a _
  have contθ : ∀ Φ ∈ schA F (Fin n × Fin d), ∀ h, Continuous fun g => theta om Φ g h := fun Φ hΦ h =>
    (hb.1 Φ hΦ).1.comp (continuous_id.prodMk continuous_const)
  have invθ : ∀ Φ ∈ schA F (Fin n × Fin d), ∀ h, ∀ γ ∈ ratU σ X.J, ∀ g, theta om Φ (γ * g) h = theta om Φ g h :=
    fun Φ hΦ h γ hγ g => by
      have := (hb.1 Φ hΦ).2.1 γ hγ 1 (one_mem _) g h
      rwa [one_mul] at this
  have hPr : ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, 0 ≤ ∏ i, t i ^ (Module.finrank ℚ F * d) := fun t ht =>
    Finset.prod_nonneg fun i _ => pow_nonneg (ht.1 i).le _
  have boundA : ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (N : ℕ) (C : ℝ), ∀ h, ∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a,
      GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a → ∀ k ∈ K,
      ‖theta om Φ (e.symm (p * a * k)) h‖ ≤ C * (ht h : ℝ) ^ N * ∏ i, t i ^ (Module.finrank ℚ F * d) := by
    intro Φ hΦ
    induction hΦ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, g, hg, rfl⟩ := hx
      obtain ⟨N, C, T, hT⟩ :=
        GlobalTheory.T.siegel_set_witt_frame_domain F E σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hW Ω C₀ K c hΩ hC₀ hK hc hconj g hg
      exact ⟨N, C * (T.sup (schwartzSeminormFamily ℂ _ ℂ)) f, fun h p hp t htc a ha k hk => hT f h _ p hp t htc a ha k hk rfl⟩
    | zero => exact ⟨0, 0, fun h p _ t _ a _ k _ => by simp [theta, thetaSum]⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨N₁, C₁', h₁⟩ := ihx
      obtain ⟨N₂, C₂', h₂⟩ := ihy
      refine ⟨max N₁ N₂, max C₁' 0 + max C₂' 0, fun h p hp t htc a ha k hk => ?_⟩
      have e1 : (1 : ℝ) ≤ ht h := one_le_ht h
      have a1 : (ht h : ℝ) ^ N₁ ≤ (ht h : ℝ) ^ max N₁ N₂ := pow_le_pow_right₀ e1 (le_max_left _ _)
      have a2 : (ht h : ℝ) ^ N₂ ≤ (ht h : ℝ) ^ max N₁ N₂ := pow_le_pow_right₀ e1 (le_max_right _ _)
      have b1 := mul_le_max_mul (C := C₁') (by positivity) a1 (hPr t htc)
      have b2 := mul_le_max_mul (C := C₂') (by positivity) a2 (hPr t htc)
      rw [thAdd x hx y hy]
      calc _ ≤ ‖theta om x (e.symm (p * a * k)) h‖ + ‖theta om y (e.symm (p * a * k)) h‖ := norm_add_le _ _
        _ ≤ _ := add_le_add ((h₁ h p hp t htc a ha k hk).trans b1) ((h₂ h p hp t htc a ha k hk).trans b2)
        _ = _ := by ring
    | smul z x hx ih =>
      obtain ⟨N, C, h₁⟩ := ih
      refine ⟨N, ‖z‖ * C, fun h p hp t htc a ha k hk => ?_⟩
      rw [thSmul, norm_mul]
      calc ‖z‖ * ‖theta om x (e.symm (p * a * k)) h‖
          ≤ ‖z‖ * (C * (ht h : ℝ) ^ N * ∏ i, t i ^ (Module.finrank ℚ F * d)) :=
            mul_le_mul_of_nonneg_left (h₁ h p hp t htc a ha k hk) (norm_nonneg _)
        _ = _ := by ring
  have hIr : 0 ≤ I.toReal := ENNReal.toReal_nonneg
  refine ⟨fun Φ hΦ => ?_, fun φ hφ h => ?_⟩
  · obtain ⟨N, C, hC⟩ := boundA Φ hΦ
    have hk := fun h => key (fun g => theta om Φ g h) (C * (ht h : ℝ) ^ N) (contθ Φ hΦ h) (invθ Φ hΦ h)
      (fun p hp t htc a ha k hk => hC h p hp t htc a ha k hk)
    refine ⟨fun h => (hk h).1, (C₁ : ℝ) * max C 0 * I.toReal, N, fun h => (hk h).2.trans (le_of_eq ?_)⟩
    have hH : (0 : ℝ) ≤ (ht h : ℝ) ^ N := by positivity
    rw [← zero_mul ((ht h : ℝ) ^ N), ← max_mul_of_nonneg _ _ hH]
    ring_nf
  · obtain ⟨N, C, T, hT⟩ :=
      GlobalTheory.T.siegel_set_witt_frame_domain F E σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hW Ω C₀ K c hΩ hC₀ hK hc hconj φ hφ
    have memA : ∀ f : SInf F (Fin n × Fin d), pureA F f φ ∈ schA F (Fin n × Fin d) := fun f =>
      Submodule.subset_span ⟨f, φ, hφ, rfl⟩
    have hint := fun f : SInf F (Fin n × Fin d) => key (fun g => theta om (pureA F f φ) g h)
      (C * (T.sup (schwartzSeminormFamily ℂ _ ℂ)) f * (ht h : ℝ) ^ N) (contθ _ (memA f) h) (invθ _ (memA f) h)
      (fun p hp t htc a ha k hk => hT f h _ p hp t htc a ha k hk rfl)
    have pAdd : ∀ f₁ f₂ : SInf F (Fin n × Fin d), pureA F (⇑(f₁ + f₂)) φ = pureA F f₁ φ + pureA F f₂ φ :=
      fun f₁ f₂ => funext fun x => by simp [pureA, add_mul]
    have pSmul : ∀ (z : ℂ) (f₁ : SInf F (Fin n × Fin d)), pureA F (⇑(z • f₁)) φ = z • pureA F f₁ φ :=
      fun z f₁ => funext fun x => by simp [pureA, mul_assoc]
    let L : SInf F (Fin n × Fin d) →ₗ[ℂ] ℂ :=
      { toFun := fun f => M.I om (pureA F f φ) h
        map_add' := fun f₁ f₂ => by
          simp only [Model.I, pAdd, thAdd _ (memA f₁) _ (memA f₂)]
          exact integral_add (hint f₁).1 (hint f₂).1
        map_smul' := fun z f₁ => by
          simp only [Model.I, pSmul, thSmul, RingHom.id_apply, smul_eq_mul]
          exact integral_const_mul z _ }
    show Continuous L
    have hH : (0 : ℝ) ≤ (ht h : ℝ) ^ N := by positivity
    refine WithSeminorms.continuous_normedSpace_rng ℂ (schwartz_withSeminorms ℂ _ ℂ) L
      ⟨T, ⟨(C₁ : ℝ) * max C 0 * (ht h : ℝ) ^ N * I.toReal, by positivity⟩, fun f => ?_⟩
    have hq : 0 ≤ (T.sup (schwartzSeminormFamily ℂ _ ℂ)) f := apply_nonneg _ _
    show ‖M.I om (pureA F f φ) h‖ ≤ _
    refine (norm_integral_le_integral_norm _).trans ((hint f).2.trans (le_of_eq ?_))
    show _ = ((C₁ : ℝ) * max C 0 * (ht h : ℝ) ^ N * I.toReal) * (T.sup (schwartzSeminormFamily ℂ _ ℂ)) f
    rw [show C * (T.sup (schwartzSeminormFamily ℂ _ ℂ)) f * (ht h : ℝ) ^ N =
      C * ((T.sup (schwartzSeminormFamily ℂ _ ℂ)) f * (ht h : ℝ) ^ N) by ring,
      ← zero_mul ((T.sup (schwartzSeminormFamily ℂ _ ℂ)) f * (ht h : ℝ) ^ N),
      ← max_mul_of_nonneg _ _ (mul_nonneg hq hH)]
    ring_nf

end GlobalTheory.ThKWeil

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedAbelianVarietyPullbackAffineOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraTail
noncomputable section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FactorAndSection

theorem exists_factor {R K A : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing A] (φ : R →+* A) (hφ : φ.IsIntegral) (ψ : A →+* K)
    (h : ψ.comp φ = algebraMap R K) : ∃ χ : A →+* R, (algebraMap R K).comp χ = ψ ∧ χ.comp φ = RingHom.id R := by
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hmem : ∀ a : A, ψ a ∈ (algebraMap R K).range := by
    intro a
    have h1 : (ψ.comp φ).IsIntegralElem (ψ a) := (hφ a).map ψ
    rw [h] at h1
    exact (IsIntegrallyClosed.isIntegral_iff (R := R) (K := K)).1 h1
  let e : R ≃+* (algebraMap R K).range := RingEquiv.ofBijective (algebraMap R K).rangeRestrict
    ⟨fun a b hab => hinj (congrArg Subtype.val hab), (algebraMap R K).rangeRestrict_surjective⟩
  have he : ∀ z : (algebraMap R K).range, algebraMap R K (e.symm z) = z.1 := fun z =>
    congrArg Subtype.val (e.apply_symm_apply z)
  have h1 : (algebraMap R K).comp (e.symm.toRingHom.comp (ψ.codRestrict _ hmem)) = ψ := by
    ext a
    exact he _
  refine ⟨e.symm.toRingHom.comp (ψ.codRestrict _ hmem), h1, ?_⟩
  ext r
  apply hinj
  have h2 := congrArg (fun f : A →+* K => f (φ r)) h1
  have h3 := congrArg (fun f : R →+* K => f r) h
  exact h2.trans h3

theorem exists_section {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] {Z : Scheme.{0}} (p : Z ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) [IsFinite p]
    (y : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K ⟶ Z) (hy : y ≫ p = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K)) :
    ∃ x : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Z,
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K) ≫ x = y ∧ x ≫ p = 𝟙 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) := by
  haveI : IsAffine Z := isAffine_of_isAffineHom p
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Z.isoSpec.inv ≫ p)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (y ≫ Z.isoSpec.hom)
  have hfin : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hint : φ.hom.IsIntegral := ((IsFinite.SpecMap_iff φ).1 hfin).to_isIntegral
  have hc : φ ≫ ψ = CommRingCat.ofHom (algebraMap R K) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hψ, Category.assoc, Iso.hom_inv_id_assoc, hy]
  obtain ⟨χ, h1, h2⟩ := exists_factor (R := R) (K := K) φ.hom hint ψ.hom (congrArg CommRingCat.Hom.hom hc)
  have h1' : CommRingCat.ofHom χ ≫ CommRingCat.ofHom (algebraMap R K) = ψ := CommRingCat.hom_ext h1
  have h2' : φ ≫ CommRingCat.ofHom χ = 𝟙 _ := CommRingCat.hom_ext h2
  refine ⟨Spec.map (CommRingCat.ofHom χ) ≫ Z.isoSpec.inv, ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, h1', hψ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · rw [Category.assoc, ← hφ, ← Spec.map_comp, h2', Spec.map_id]

end GlobalTheory.FactorAndSection
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedAbelianVarietyPullbackAffineOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.TorsExtend

theorem exists_section_of_isFinite {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K]
    [Algebra R K] [IsFractionRing R K] {Z : Scheme.{0}} (p : Z ⟶ Sp R) [IsFinite p] (y : Sp K ⟶ Z)
    (h : y ≫ p = spMap (algebraMap R K)) : ∃ x : Sp R ⟶ Z, spMap (algebraMap R K) ≫ x = y ∧ x ≫ p = 𝟙 _ := by
  first
  | exact @_root_.GlobalTheory.FactorAndSection.exists_section
  | exact _root_.GlobalTheory.FactorAndSection.exists_section
  | (apply _root_.GlobalTheory.FactorAndSection.exists_section <;> assumption)
  | (intros; apply _root_.GlobalTheory.FactorAndSection.exists_section <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FactorAndSection.exists_section <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FactorAndSection.exists_section ..)

theorem pow_eq_one_iff {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) {T : Over S} (z : T ⟶ G) :
    z ^ n = 1 ↔ z.left ≫ (mulA G n).left = T.hom ≫ (η[G]).left := by
  have e : (1 : T ⟶ G).left = T.hom ≫ (η[G]).left := by
    rw [Hom.one_def]; simp
  rw [← Over.comp_left, mulA, MonObj.comp_pow, Category.comp_id, ← e]
  exact ⟨fun h => by rw [h], fun h => Over.OverMorphism.ext h⟩

theorem exists_torsion_section (hL : Laws) {R K : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] (P : PolAV (Sp R)) {n : ℕ} (hn : 1 ≤ n)
    {s : Sp K ⟶ Sp R} (hs : s = spMap (algebraMap R K)) (y : Over.mk s ⟶ P.A) (hy : y ^ n = 1) :
    ∃ x : baseOver (Sp R) ⟶ P.A, x ^ n = 1 ∧ spMap (algebraMap R K) ≫ x.left = y.left := by
  subst hs
  haveI := (hL.mulN _ P n hn).1
  let e : Sp R ⟶ P.A.left := (η[P.A]).left
  have he : e ≫ P.A.hom = 𝟙 _ := Over.w η[P.A]
  obtain ⟨x, h₁, h₂⟩ := exists_section_of_isFinite (pullback.snd (mulA P.A n).left e)
    (pullback.lift y.left (spMap (algebraMap R K)) ((pow_eq_one_iff _ _ _).1 hy)) (pullback.lift_snd _ _ _)
  have h₃ : (x ≫ pullback.fst (mulA P.A n).left e) ≫ (mulA P.A n).left = e := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, h₂, Category.id_comp]
  refine ⟨Over.homMk (x ≫ pullback.fst _ _) ?_, (pow_eq_one_iff _ _ _).2 (h₃.trans (Category.id_comp _).symm), ?_⟩
  · rw [← Over.w (mulA P.A n), ← Category.assoc, h₃]
    exact he
  · show _ ≫ x ≫ pullback.fst _ _ = _
    rw [← Category.assoc, h₁, pullback.lift_fst]

theorem torsion_section_eq (hL : Laws) {R K : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K]
    (P : PolAV (Sp R)) {n : ℕ} (hn : 1 ≤ n) (hu : IsUnit (n : R)) {x y : baseOver (Sp R) ⟶ P.A} (hx : x ^ n = 1)
    (hy : y ^ n = 1) (s : Sp K ⟶ Sp R) (h : s ≫ x.left = s ≫ y.left) : x = y := by
  haveI := (hL.mulN _ P n hn).1
  haveI := (hL.mulN _ P n hn).2.2.2.1 (by simpa using hu.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
  haveI : PreconnectedSpace (Sp R) := inferInstanceAs (PreconnectedSpace (PrimeSpectrum R))
  exact Over.OverMorphism.ext (eq_of_preconnected_of_unramified (T := Sp R) (mulA P.A n).left
    (((pow_eq_one_iff _ _ _).1 hx).trans ((pow_eq_one_iff _ _ _).1 hy).symm) s h)

theorem exists_labelled (hL : Laws) {R R₀ Ω : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Field Ω] [Algebra R Ω] [IsFractionRing R Ω] [CommRing R₀] (j₀ : R₀ →+* Ω)
    (P : PolAV (Sp R₀)) (P' : PolAV (Sp R)) (P₀ : PolAV (Sp Ω)) (a : P₀.A.left ⟶ P.A.left) (a' : P₀.A.left ⟶ P'.A.left)
    (ha : IsGrpPullback P₀.A P.A (spMap j₀) a) (ha' : IsGrpPullback P₀.A P'.A (spMap (algebraMap R Ω)) a')
    (hl : LBIso P₀.L (P.L.pull a)) (hl' : LBIso P₀.L (P'.L.pull a')) {n : ℕ} (hn : 1 ≤ n) (hu : IsUnit (n : R))
    {M : Type} [AddCommGroup M] (hM : ∀ x : M, n • x = 0) (pt : M → (baseOver (Sp R₀) ⟶ P.A))
    (add : ∀ x y, pt (x + y) = pt x * pt y)
    (bij : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R₀) (z : Over.mk x ⟶ P.A), z ^ n = 1 →
      ∃! c, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp R₀)) ≫ pt c = z) :
    ∃ pt' : M → (baseOver (Sp R) ⟶ P'.A), (∀ x y, pt' (x + y) = pt' x * pt' y) ∧
      (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (z : Over.mk x ⟶ P'.A), z ^ n = 1 →
        ∃! c, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp R)) ≫ pt' c = z) ∧
      (∀ x y (c₀ : R₀ˣ) (c : Rˣ), j₀ c₀ = algebraMap R Ω c → WeilIs P.A P.L n (pt x) (pt y) (unitOn c₀) →
        WeilIs P'.A P'.L n (pt' x) (pt' y) (unitOn c)) ∧
      ∀ x, ∃ w0 : Sp Ω ⟶ P₀.A.left, w0 ≫ a = spMap j₀ ≫ (pt x).left ∧
        w0 ≫ a' = spMap (algebraMap R Ω) ≫ (pt' x).left := by
  haveI := P₀.isAb.comm
  haveI := P'.isAb.proper
  have hi := IsFractionRing.injective R Ω
  have hb := GenericKTriv.pushHom_bijective ha (baseOver (Sp Ω))
  have hb' := GenericKTriv.pushHom_bijective ha' (baseOver (Sp Ω))
  let h₀ : Over.mk ((baseOver (Sp Ω)).hom ≫ spMap j₀) ⟶ baseOver (Sp R₀) := Over.homMk (spMap j₀) (by simp)
  let h : Over.mk ((baseOver (Sp Ω)).hom ≫ spMap (algebraMap R Ω)) ⟶ baseOver (Sp R) :=
    Over.homMk (spMap (algebraMap R Ω)) (by simp)
  have zero : pt 0 = 1 := by
    have := add 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have smul : ∀ (k : ℕ) x, pt (k • x) = pt x ^ k := fun k x => by
    induction k with
    | zero => rw [zero_smul, zero, pow_zero]
    | succ k ih => rw [succ_nsmul, add, ih, pow_succ]
  have tor : ∀ x, pt x ^ n = 1 := fun x => by rw [← smul, hM, zero]
  choose w hw using fun x => hb.2 (h₀ ≫ pt x)
  have torw : ∀ x, w x ^ n = 1 := fun x => hb.1 (by
    rw [map_pow, hw, map_one, ← MonObj.comp_pow, tor, MonObj.comp_one])
  have addw : ∀ x y, w (x + y) = w x * w y := fun x y => hb.1 (by
    rw [map_mul, hw, hw, hw, add, MonObj.comp_mul])
  choose pt' tor' hpt' using fun x => exists_torsion_section hL P' hn (Category.id_comp _)
    (pushHom ha' (baseOver (Sp Ω)) (w x)) (by rw [← map_pow, torw, map_one])
  have hpt : ∀ x, h ≫ pt' x = pushHom ha' (baseOver (Sp Ω)) (w x) := fun x => Over.OverMorphism.ext (hpt' x)
  have e₀ : ∀ x, (w x).left ≫ a = spMap j₀ ≫ (pt x).left := fun x => congrArg (fun q => q.left) (hw x)
  have e₁ : ∀ x, (w x).left ≫ a' = spMap (algebraMap R Ω) ≫ (pt' x).left := fun x => (hpt' x).symm
  let F := AlgebraicClosure Ω
  let t : Sp F ⟶ Sp Ω := spMap (algebraMap Ω F)
  let g : Over.mk (t ≫ spMap j₀) ⟶ baseOver (Sp R₀) := Over.homMk (t ≫ spMap j₀) (by simp)
  have torg : ∀ x, (g ≫ pt x) ^ n = 1 := fun x => by rw [← MonObj.comp_pow, tor, MonObj.comp_one]
  have inj : Function.Injective pt' := fun x y e => by
    have e₂ : w x = w y := hb'.1 (by rw [← hpt, ← hpt, e])
    refine (bij F (t ≫ spMap j₀) (g ≫ pt y) (torg y)).unique (Over.OverMorphism.ext ?_) rfl
    show (t ≫ spMap j₀) ≫ (pt x).left = (t ≫ spMap j₀) ≫ (pt y).left
    rw [Category.assoc, Category.assoc, ← e₀, ← e₀, e₂]
  have ne : ∀ (K : Type) [Field K] (s : Sp K ⟶ Sp R), (n : K) ≠ 0 := fun K _ s => by
    have := hu.map (Spec.preimage s).hom
    rw [map_natCast] at this
    exact this.ne_zero
  have card : Nat.card M = n ^ (2 * P'.g) := by
    rw [← (hL.mulN _ P' n hn).2.2.2.2 F (t ≫ spMap (algebraMap R Ω)) (ne F (t ≫ spMap (algebraMap R Ω))),
      GenericKTriv.card_torsion ha' t rfl, ← GenericKTriv.card_torsion ha t rfl]
    refine Nat.card_eq_of_bijective (fun x => ⟨g ≫ pt x, torg x⟩) ⟨fun x y e => ?_, fun z => ?_⟩
    · exact (bij F (t ≫ spMap j₀) (g ≫ pt y) (torg y)).unique (congrArg Subtype.val e) rfl
    · obtain ⟨c, hc, -⟩ := bij F (t ≫ spMap j₀) z.1 z.2
      exact ⟨c, Subtype.ext hc⟩
  refine ⟨pt', fun x y => ?_, fun K _ _ s z hz => ?_, fun x y c₀ c hc H => ?_, fun x => ⟨(w x).left, e₀ x, e₁ x⟩⟩
  · have e : h ≫ pt' (x + y) = h ≫ (pt' x * pt' y) := by
      rw [MonObj.comp_mul, hpt, hpt, hpt, addw, map_mul]
    exact over_points_ext_of_injective _ P'.A R Ω _ hi _ _ _ (congrArg (fun q => q.left) e)
  · have hc := (hL.mulN _ P' n hn).2.2.2.2 K s (ne K s)
    let Φ : M → {x : Over.mk s ⟶ P'.A // x ^ n = 1} := fun c =>
      ⟨(Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ pt' c, by
        rw [← MonObj.comp_pow, tor', MonObj.comp_one]⟩
    have hΦ : Function.Injective Φ := fun c c' e =>
      inj (torsion_section_eq hL P' hn hu (tor' c) (tor' c') s (congrArg (fun q => q.1.left) e))
    have : Finite {x : Over.mk s ⟶ P'.A // x ^ n = 1} :=
      Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
    obtain ⟨c, e⟩ := (hΦ.bijective_of_nat_card_le (by rw [hc, card])).2 ⟨z, hz⟩
    exact ⟨c, congrArg Subtype.val e, fun c' e' => hΦ ((Subtype.ext e').trans e.symm)⟩
  · refine MumPair.weilIs_of_spread Ω R _ hi P₀ P' a' ha' hl' n (w x) (w y) _ _ c hn (e₁ x) (e₁ y) (tor' x) (tor' y) ?_
    have H₁ := CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB h₀ H
    have H₂ := (weilIs_grpPullback_of_comm' (Sp R₀) (Sp Ω) P.A P₀.A (spMap j₀) a P.L P₀.L P.isLB P₀.isLB ha hl
      (baseOver (Sp Ω)) n (w x) (w y) (h₀ ≫ pt x) (h₀ ≫ pt y) _ (e₀ x).symm (e₀ y).symm).2 H₁
    have e := SpreadLevel.appTop_unitOn j₀ c₀ (Units.map (algebraMap R Ω).toMonoidHom c) hc
    exact e ▸ H₂

theorem isIntegrallyClosed_ringOn {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (hM : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z) {U : M.Z.Opens} (hU : IsAffineOpen U) (hne : (U : Set M.Z).Nonempty) :
    IsIntegrallyClosed (M.ringOn U) := by
  haveI := RatModel.isFractionRing_ringOn hU hne
  refine (isIntegrallyClosed_iff Ω).2 fun {x} hx => ⟨⟨x, RatModel.mem_ringOn.2 fun z hz => ?_⟩, rfl⟩
  have := RatModel.isIntegrallyClosed_O hM z
  letI : Algebra (M.ringOn U) (M.O z) := (Subalgebra.inclusion (RatModel.ringOn_le_O hz)).toRingHom.toAlgebra
  haveI : IsScalarTower (M.ringOn U) (M.O z) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hx.tower_top (A := M.O z))
  exact hy ▸ y.2

theorem exists_labelled_on_chart : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (U : X₁.M.Z.Opens) (P' : PolAV (Sp (X₁.M.ringOn U))) (P₀ : PolAV (Sp X₁.Ω₁)) (a : P₀.A.left ⟶ X₁.ρ.P.A.left) (a' : P₀.A.left ⟶ P'.A.left), IsAffineOpen U → (U : Set X₁.M.Z).Nonempty → IsGrpPullback P₀.A X₁.ρ.P.A (spMap X₁.S.R.val.toRingHom) a → IsGrpPullback P₀.A P'.A (spMap (X₁.M.ringOn U).val.toRingHom) a' → LBIso P₀.L (X₁.ρ.P.L.pull a) → LBIso P₀.L (P'.L.pull a') → ∃ pt' : X₁.S.Gam → (baseOver (Sp (X₁.M.ringOn U)) ⟶ P'.A), (∀ x y, pt' (x + y) = pt' x * pt' y) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp (X₁.M.ringOn U)) (z : Over.mk x ⟶ P'.A), z ^ (X₁.S.r * X₁.S.N) = 1 → ∃! c, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp (X₁.M.ringOn U))) ≫ pt' c = z) ∧ (∀ x y (c : (X₁.M.ringOn U)ˣ), (c : (X₁.M.ringOn U)) = algebraMap X₁.o₁ (X₁.M.ringOn U) (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (eStd X₁.S.g _ x y).val)) → WeilIs P'.A P'.L (X₁.S.r * X₁.S.N : ℕ) (pt' x) (pt' y) (unitOn c)) ∧ (∀ x, ∃ w0 : Sp X₁.Ω₁ ⟶ P₀.A.left, w0 ≫ a = spMap X₁.S.R.val.toRingHom ≫ (X₁.ρ.pt x).left ∧ w0 ≫ a' = spMap (X₁.M.ringOn U).val.toRingHom ≫ (pt' x).left) := by
  intro g n F W Z i X₁ U P' P₀ a a' hU hne ha ha' hl hl'
  have hL : Out.Laws := GlobalTheory.lawsAndExpansions.1.1
  haveI := RatModel.isFractionRing_ringOn hU hne
  haveI := isIntegrallyClosed_ringOn X₁.M ((isNormalScheme_iff_pred _).1 X₁.normal) hU hne
  haveI := ArithBase.ded (o := X₁.o₁) (Ω := X₁.Ω₁)
  haveI : IsNoetherianRing (X₁.M.ringOn U) := isNoetherianRing_of_fg (fg_ringOn_of_isAffineOpen _ _ X₁.M U hU hne)
  have hn : 1 ≤ X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (le_trans one_le_two X₁.S.N_ge)
  have hu : IsUnit ((X₁.S.r * X₁.S.N : ℕ) : X₁.M.ringOn U) := by
    have := X₁.S.unit.map (algebraMap X₁.o₁ (X₁.M.ringOn U))
    rwa [map_natCast] at this
  obtain ⟨pt', h₁, h₂, h₃, h₄⟩ := exists_labelled hL X₁.S.R.val.toRingHom X₁.ρ.P P' P₀ a a' ha ha' hl hl' hn hu
    (M := X₁.S.Gam) (fun x => by ext k; simp [nsmul_eq_mul, -Nat.cast_mul]) X₁.ρ.pt X₁.ρ.pt_add X₁.ρ.pt_bij
  refine ⟨pt', h₁, h₂, fun x y c hc => ?_, h₄⟩
  obtain ⟨c₀, hc₀⟩ := ((X₁.S.prim.isUnit (by positivity)).pow (X₁.S.r * X₁.S.N * (eStd X₁.S.g _ x y).val)).map
    (algebraMap X₁.o₁ X₁.S.R)
  refine h₃ x y c₀ c ?_ (X₁.ρ.weil x y c₀ hc₀)
  rw [hc₀, hc]
  rfl

end GlobalTheory.Poinc.TorsExtend
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedAbelianVarietyPullbackAffineOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarized_abelian_variety_pullback_affine_open : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (U : X₁.M.Z.Opens) (P' : PolAV (Sp (X₁.M.ringOn U))) (P₀ : PolAV (Sp X₁.Ω₁)) (a : P₀.A.left ⟶ X₁.ρ.P.A.left) (a' : P₀.A.left ⟶ P'.A.left), IsAffineOpen U → (U : Set X₁.M.Z).Nonempty → IsGrpPullback P₀.A X₁.ρ.P.A (spMap X₁.S.R.val.toRingHom) a → IsGrpPullback P₀.A P'.A (spMap (X₁.M.ringOn U).val.toRingHom) a' → LBIso P₀.L (X₁.ρ.P.L.pull a) → LBIso P₀.L (P'.L.pull a') → ∃ pt' : X₁.S.Gam → (baseOver (Sp (X₁.M.ringOn U)) ⟶ P'.A), (∀ x y, pt' (x + y) = pt' x * pt' y) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp (X₁.M.ringOn U)) (z : Over.mk x ⟶ P'.A), z ^ (X₁.S.r * X₁.S.N) = 1 → ∃! c, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp (X₁.M.ringOn U))) ≫ pt' c = z) ∧ (∀ x y (c : (X₁.M.ringOn U)ˣ), (c : (X₁.M.ringOn U)) = algebraMap X₁.o₁ (X₁.M.ringOn U) (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (eStd X₁.S.g _ x y).val)) → WeilIs P'.A P'.L (X₁.S.r * X₁.S.N : ℕ) (pt' x) (pt' y) (unitOn c)) ∧ (∀ x, ∃ w0 : Sp X₁.Ω₁ ⟶ P₀.A.left, w0 ≫ a = spMap X₁.S.R.val.toRingHom ≫ (X₁.ρ.pt x).left ∧ w0 ≫ a' = spMap (X₁.M.ringOn U).val.toRingHom ≫ (pt' x).left) := by
  first | exact @GlobalTheory.Poinc.TorsExtend.exists_labelled_on_chart | exact GlobalTheory.Poinc.TorsExtend.exists_labelled_on_chart | (intros; apply GlobalTheory.Poinc.TorsExtend.exists_labelled_on_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMapEqSelfOfInjectiveFiniteHopf
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMapEqSelfOfInjectiveFiniteHopf
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra

namespace GlobalTheory.PDiv

theorem faithfullyFlat_range_of_hopf_finite (k A B : Type) [Field k] [CommRing A] [CommRing B]
    [HopfAlgebra k A] [HopfAlgebra k B] [Module.Finite k A] (f : B →ₐc[k] A) :
    Module.FaithfullyFlat (AlgHom.range (f : B →ₐ[k] A)) A := by
  obtain ⟨e⟩ := GlobalTheory.HopfShear.shear k A B f
  haveI : Module.Finite k (AlgHom.range (f : B →ₐ[k] A)) :=
    Module.Finite.of_injective (AlgHom.range (f : B →ₐ[k] A)).val.toLinearMap
      Subtype.val_injective
  haveI : Module.Finite (AlgHom.range (f : B →ₐ[k] A)) A :=
    Module.Finite.of_restrictScalars_finite k _ A
  haveI : IsArtinianRing (AlgHom.range (f : B →ₐ[k] A)) := IsArtinianRing.of_finite k _
  obtain ⟨b⟩ := GlobalTheory.nonempty_basis_of_basis_baseChange (B := AlgHom.range (f : B →ₐ[k] A))
    (A := A) (M := A) Subtype.val_injective (((Module.finBasis k _).baseChange A).map e.symm)
  haveI := Module.Free.of_basis b
  haveI : Nontrivial A := (counitAlgHom k A).domain_nontrivial
  infer_instance

theorem comap_map_eq_self_of_hopf_injective : ∀ (k A B : Type) [Field k] [CommRing A] [CommRing B] [HopfAlgebra k A] [HopfAlgebra k B] [Module.Finite k A] (f : B →ₐc[k] A), Function.Injective f → ∀ J : Ideal B, Ideal.comap (f : B →ₐ[k] A) (Ideal.map (f : B →ₐ[k] A) J) = J := by
  intro k A B _ _ _ _ _ _ f hf J
  haveI := faithfullyFlat_range_of_hopf_finite k A B f
  let g : B →+* AlgHom.range (f : B →ₐ[k] A) := (f : B →ₐ[k] A).rangeRestrict.toRingHom
  have hg : Function.Bijective g :=
    ⟨fun x y h => hf (congrArg Subtype.val h), (f : B →ₐ[k] A).rangeRestrict_surjective⟩
  have h := Ideal.comap_map_eq_self_of_faithfullyFlat (B := A) (Ideal.map g J)
  rw [Ideal.map_map] at h
  have h2 := congrArg (Ideal.comap g) h
  rw [Ideal.comap_comap, Ideal.comap_map_of_bijective g hg] at h2
  exact h2

end GlobalTheory.PDiv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMapEqSelfOfInjectiveFiniteHopfStatement
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comap_map_eq_self_of_injective_finiteHopf : ∀ (k A B : Type) [Field k] [CommRing A] [CommRing B] [HopfAlgebra k A] [HopfAlgebra k B] [Module.Finite k A] (f : B →ₐc[k] A), Function.Injective f → ∀ J : Ideal B, Ideal.comap (f : B →ₐ[k] A) (Ideal.map (f : B →ₐ[k] A) J) = J := by
  first | exact @GlobalTheory.PDiv.comap_map_eq_self_of_hopf_injective | exact GlobalTheory.PDiv.comap_map_eq_self_of_hopf_injective | (intros; apply GlobalTheory.PDiv.comap_map_eq_self_of_hopf_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalFiniteDominantRefinement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open CategoryTheory.Limits TopologicalSpace

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mean4O.CommonGen

theorem exists_common (F : Type) [Field F] [NumberField F] (Y : Var F) (V₁ V₂ : Mean4O.Cover Y) :
    ∃ (G : Scheme.{0}) (_ : IsIntegral G) (_ : GlobalTheory.IsNormalScheme G) (g : G ⟶ V₁.G) (k : G ⟶ V₂.G),
      IsFinite g ∧ IsDominant g ∧ k ≫ V₂.π = g ≫ V₁.π := by
  have : IsProper V₁.p := CommonModel.isProper_of_isProjOver V₁.ar.isProjOver
  have : IsProper (V₁.π ≫ Y.str) := MorphismProperty.of_isPullback V₁.pb ‹IsProper V₁.p›
  let Q : Scheme.{0} := pullback V₁.π V₂.π
  let a : Q ⟶ V₁.G := pullback.fst V₁.π V₂.π
  let b : Q ⟶ V₂.G := pullback.snd V₁.π V₂.π
  have : IsFinite a := inferInstanceAs (IsFinite (pullback.fst V₁.π V₂.π))
  have hs : Surjective a := inferInstanceAs (Surjective (pullback.fst V₁.π V₂.π))
  obtain ⟨η, hη⟩ := hs.surj (genericPoint V₁.G)
  let s : Q ⟶ Spec (.of F) := a ≫ V₁.π ≫ Y.str
  have : IsProper s := inferInstanceAs (IsProper (a ≫ V₁.π ≫ Y.str))
  have : CharZero (Q.residueField η) := charZero_of_injective_ringHom
    ((Scheme.ΓSpecIso (.of F)).inv ≫ s.appTop ≫ Q.Γevaluation η).hom.injective
  let u : Spec (.of (Q.residueField η)) ⟶ Q := Spec.map (Q.residue η) ≫ Q.fromSpecStalk η
  have hfin : IsFinite u.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_SpecMap_fromSpecStalk s η (L := Q.residueField η) (Q.residue η)
      (RingHom.FiniteType.of_surjective _ (Q.residue_surjective η)).essFiniteType
  have hu : u (IsLocalRing.closedPoint (Q.residueField η)) = η :=
    Scheme.fromSpecResidueField_apply η _
  have : IsDominant (u ≫ a) := ⟨(dense_iff_closure_eq.2 (genericPoint_spec V₁.G)).mono
    (Set.singleton_subset_iff.2 ⟨IsLocalRing.closedPoint (Q.residueField η), by
      change a (u _) = _
      rw [hu, hη]⟩)⟩
  have hd : IsDominant (u.fromNormalization ≫ a) := by
    have : IsDominant (u.toNormalization ≫ u.fromNormalization ≫ a) := by
      rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization]; infer_instance
    exact IsDominant.of_comp u.toNormalization _
  refine ⟨u.normalization, inferInstance, GlobalTheory.IsNormalScheme.normalization_of_isIntegral u,
    u.fromNormalization ≫ a, u.fromNormalization ≫ b, inferInstance, hd, ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition]

end GlobalTheory.Mean4O.CommonGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivCmTypeRealEmbeddings
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivCmTypeRealEmbeddings
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.CMVal (OF Af lattice IsCMType)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum IsEisValue polydisc)

namespace GlobalTheory.CMTypeEmb

theorem card_eq_finrank {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : IsCMType φ) : Fintype.card I = Module.finrank ℚ (FR E) := by
  have hc : Fintype.card I = Fintype.card (InfinitePlace E) :=
    Fintype.card_of_bijective (GlobalTheory.CMTypeCard.bijective_mk_of_isCMType hφ)
  have hE : Fintype.card (InfinitePlace E) = Fintype.card (InfinitePlace (FR E)) :=
    Fintype.card_congr (IsCMField.equivInfinitePlace E)
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank (FR E)
  have hr : InfinitePlace.nrComplexPlaces (FR E) = 0 := IsTotallyReal.nrComplexPlaces_eq_zero (FR E)
  have h3 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := FR E)
  omega

theorem exists_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∃ e : I ≃ Emb (FR E), ∀ i (x : FR E), φ i (x : E) = ((e i x : ℝ) : ℂ) := by
  intro E _ _ _ I _ φ hφ
  have hcard : Fintype.card I = Module.finrank ℚ (FR E) := card_eq_finrank hφ
  let e₀ : Fin (Module.finrank ℚ (FR E)) ≃ I := (Fintype.equivFinOfCardEq hcard).symm
  obtain ⟨e, he⟩ := GlobalTheory.CMTypeRestrict.exists_equiv_realEmbeddings E I φ hφ e₀
  refine ⟨e₀.symm.trans e, fun i x ↦ ?_⟩
  have := he (e₀.symm i) x
  simp only [Equiv.apply_symm_apply] at this
  simp only [Equiv.trans_apply]
  exact this.symm

end GlobalTheory.CMTypeEmb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivCmTypeRealEmbeddingsStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.CMVal (OF Af lattice IsCMType)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum IsEisValue polydisc)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_cmType_realEmbeddings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∃ e : I ≃ Emb (FR E), ∀ i (x : FR E), φ i (x : E) = ((e i x : ℝ) : ℂ) := by
  first | exact @GlobalTheory.CMTypeEmb.exists_equiv | exact GlobalTheory.CMTypeEmb.exists_equiv | (intros; apply GlobalTheory.CMTypeEmb.exists_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnTrivialThickeningsAdditiveLiStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.PtExt.fv_linear (R : Type) [CommRing R] (X : Over (Sp R)) :
    (∀ (f f' : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))), fv (f + f') = (fv f).add (fv f')) ∧
    (∀ (r : R) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _)))
      (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
      (φ : D →ₐ[R] D') (x : Pt X D),
      fv (r • f) D D' φ x = algebraMap R D' r * fv f D D' φ x) ∧
    (∀ g : C0 (O (dp0 R) (X.hom ≫ 𝟙 _)),
      ∃ k : Fn0 X, IsCob (whole X) (fv ⟨d0 _ g, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ g⟩) k) := by
  refine ⟨fun f f' ↦ rfl, ?_, fun g ↦ ⟨fun D _ _ x ↦ g (trivAt x), ?_⟩⟩
  · intro r f D _ _ D' _ _ φ x
    exact Algebra.smul_def r (ev f (trivMap φ x))
  · intro D _ _ D' _ _ φ x _
    rfl

alias GlobalTheory.T.crystallineCocycleOnTrivialThickenings_additive_linear := GlobalTheory.PtExt.fv_linear
end
