module

public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ChartValJ
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DeterminantBlockProductRenameTorusPolynomial
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicValueGermsIndependentOfChart

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NormalisedPullbackCommutesSymmetricTranslations
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NormalisedPullbackCommutesSymmetricTranslations
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (endT)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PullMove

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem translT_mul {T : Over S} (x y : T ⟶ A) : translT A x ≫ translT A y = translT A (y * x) := by
  rw [translT, lift_transl, translPt_eq, translT, translPt_eq, MonObj.comp_mul, _root_.mul_assoc]

theorem translT_one {T : Over S} : translT A (1 : T ⟶ A) = 𝟙 _ := by
  rw [translT, translPt_eq, MonObj.comp_one, _root_.one_mul, lift_fst_snd]

theorem translT_endT (φ : A ⟶ A) [IsMonHom φ] {T : Over S} (x : T ⟶ A) :
    translT A x ≫ endT A T φ = endT A T φ ≫ translT A (x ≫ φ) := by
  rw [lift_transl, translT, comp_lift, lift_fst, lift_snd_assoc, translPt_eq, MonObj.mul_comp, Category.assoc]

theorem negT_endT (φ : A ⟶ A) [IsMonHom φ] (T : Over S) : negT A T ≫ endT A T φ = endT A T φ ≫ negT A T := by
  rw [negT, comp_lift, comp_lift, lift_fst, lift_fst, lift_snd_assoc, lift_snd_assoc]
  exact congrArg _ (GrpObj.inv_comp (snd T A) φ)

theorem negT_translT [IsCommMonObj A] {T : Over S} (x : T ⟶ A) :
    negT A T ≫ translT A x = translT A x⁻¹ ≫ negT A T := by
  rw [negT, lift_transl, translT, comp_lift, lift_fst, lift_snd_assoc, translPt_eq, GrpObj.comp_inv]
  refine congrArg _ ?_
  show fst T A ≫ x * (snd T A)⁻¹ = ((fst T A ≫ x)⁻¹ * snd T A)⁻¹
  rw [mul_inv, inv_inv]


omit [GrpObj A] in
theorem exists_conj {L : LB A.left} (hL : L.IsLB) (φ : A ⟶ A) (a b : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b])) (hα : α.IsGen) {T : Over S}
    (m' m : T ⊗ A ⟶ A) (e : m' ≫ φ = endT A T φ ≫ m)
    (u : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![b, -b])) (hu : u.IsGen) :
    ∃ u' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m'.left] ![a, -a]), u'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
        val u' r z J = val α (r ≫ (snd T A).left) z J * val u (r ≫ (endT A T φ).left) z J *
          (val α (r ≫ m'.left) z J)⁻¹ := by
  have e₁ : (endT A T φ).left ≫ (snd T A).left = (snd T A).left ≫ φ.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have e₂ : (endT A T φ).left ≫ m.left = m'.left ≫ φ.left := by
    rw [← Over.comp_left, ← e, Over.comp_left]
  obtain ⟨u', hu', hv⟩ := exists_gen hL (φ' := ![(snd T A).left, m'.left]) (ε' := ![a, -a])
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, e₁, e₂, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L _ _ _ _ (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ α (snd T A).left)
      (LB.pullGen L _ _ u (endT A T φ).left)) (LB.invGen L _ _ (LB.pullGen L _ _ α m'.left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _)
      (DVR.pullGen_isGen _ _ _ _ hu _)) (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _)))
  refine ⟨u', hu', fun Z r z J hJ => ?_⟩
  rw [hv _ _ z J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, val_pull hJ]

theorem prod_conj {U : Type} [CommGroup U] (f g : ℕ → U) (n N : ℕ)
    (hg : ∀ i, ∏ j ∈ Finset.range n, g (n * i + j) = 1) (hf : f (n * N) = f 0) :
    ∏ j ∈ Finset.range (n * N), (f j * g j * (f (j + 1))⁻¹) = 1 := by
  have t : ∀ k, ∏ j ∈ Finset.range k, (f j * g j * (f (j + 1))⁻¹) =
      f 0 * (∏ j ∈ Finset.range k, g j) * (f k)⁻¹ := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, ih]
      group
  have p : ∀ M, ∏ j ∈ Finset.range (n * M), g j = 1 := fun M => by
    induction M with
    | zero => simp
    | succ M ih => rw [Nat.mul_succ, Finset.prod_range_add, ih, hg, _root_.mul_one]
  rw [t, p, hf, _root_.mul_one, mul_inv_cancel]

theorem exists_symLift_conj [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB) (φ : A ⟶ A) [IsMonHom φ] (a b : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b])) (hα : α.IsGen) {T : Over S}
    (n N : ℕ) (x : T ⟶ A) (hx : x ^ (n * N) = 1) (U : ThetaGrp A L b T) (H : SymLift A L b n (x ≫ φ) U) :
    ∃ u : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (translPt A x).left] ![a, -a]), ∃ hu : u.IsGen,
      SymLift A L a (n * N) x ⟨x, u, hu⟩ ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
        val u r z J = val α (r ≫ (snd T A).left) z J *
          val (L := L) (φ := ![(snd T A).left, (translPt A U.pt).left]) (ε := ![b, -b]) U.φ
            (r ≫ (endT A T φ).left) z J * (val α (r ≫ (translPt A x).left) z J)⁻¹ := by
  have hp := H.pt_eq
  have ts : ∀ y : T ⟶ A, translT A y ≫ snd T A = translPt A y := fun y => lift_snd _ _
  have ns : negT A T ≫ snd T A = snd T A ≫ (GrpObj.inv : A ⟶ A) := lift_snd _ _
  obtain ⟨u, hu, vu⟩ := exists_conj hL φ a b α hα (translPt A x) (translPt A U.pt) (by
    rw [hp, ← ts (x ≫ φ), ← Category.assoc, ← translT_endT, Category.assoc, lift_snd, ← Category.assoc, ts])
    U.φ U.isGen
  obtain ⟨ν, hν, hs⟩ := H.sym
  obtain ⟨ν', hν', vν⟩ := exists_conj hL φ a b α hα (snd T A ≫ (GrpObj.inv : A ⟶ A))
    (snd T A ≫ (GrpObj.inv : A ⟶ A)) (by
      rw [lift_snd_assoc]
      exact GrpObj.inv_comp (snd T A) φ) ν hν
  refine ⟨u, hu, ⟨rfl, corr_of_val hL fun y J hJ => ?_, ν', hν', corr_of_val hL fun y J hJ => ?_⟩, vu⟩
  · refine (ThetaPullback.val_powGen ⟨x, u, hu⟩ (n * N) _ hJ).trans (Eq.trans ?_ (val_one _).symm)
    refine Eq.trans (Finset.prod_congr rfl fun j _ => ?_) ((Fin.prod_univ_eq_prod_range _ _).trans (prod_conj
      (fun j => val α (translPt A (x ^ j)).left y J)
      (fun j => val (L := L) (φ := ![(snd T A).left, (translPt A U.pt).left]) (ε := ![b, -b]) U.φ
        (endT A T φ ≫ translT A (U.pt ^ j)).left y J) n N (fun i => ?_) (by rw [hx, pow_zero])))
    · refine (vu _ _ y J hJ).trans ?_
      simp only [Category.id_comp, ← Over.comp_left]
      rw [ts, translT_endT, MonObj.pow_comp, ← hp, ← ts x, ← Category.assoc, translT_mul, ts, pow_succ']
    · have e := (ThetaPullback.val_powGen U n (endT A T φ ≫ translT A (U.pt ^ (n * i))).left hJ).symm.trans
        ((val_corr hJ H.pow_eq _).trans (val_one _))
      refine Eq.trans ?_ e
      rw [← Fin.prod_univ_eq_prod_range (fun j => val (L := L) (φ := ![(snd T A).left, (translPt A U.pt).left])
        (ε := ![b, -b]) U.φ (endT A T φ ≫ translT A (U.pt ^ (n * i + j))).left y J)]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [← Over.comp_left, Category.assoc, translT_mul, ← pow_add, add_comm]
  · have e := (ThetaPullback.val_symGen U ν (endT A T φ).left hJ).symm.trans ((val_corr hJ hs _).trans (val_one _))
    refine (ThetaPullback.val_symGen ⟨x, u, hu⟩ ν' _ hJ).trans (Eq.trans ?_ (e.trans (val_one _).symm))
    refine (congrArg₂ (· * ·) (congrArg₂ (· * ·) (vu _ _ y J hJ) (vν _ _ y J hJ))
      (congrArg₂ (· * ·) (vu _ _ y J hJ) (congrArg (·⁻¹) (vν _ _ y J hJ)))).trans ?_
    simp only [Category.id_comp, ← Over.comp_left]
    have e₁ : translT A x⁻¹ ≫ translPt A x = snd T A := by
      rw [← ts x, ← Category.assoc, translT_mul, mul_inv_cancel, translT_one, Category.id_comp]
    have e₂ : negT A T ≫ translPt A x = translT A x⁻¹ ≫ snd T A ≫ (GrpObj.inv : A ⟶ A) := by
      rw [← ts x, ← Category.assoc, negT_translT, Category.assoc, ns]
    rw [e₁, e₂, ns, negT_endT, translT_endT, GrpObj.inv_comp, ← hp]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem isSymAct_of_isNormPull [IsCommMonObj A] (hA : IsAbelianScheme A) (L : RigLB A) (φ : A ⟶ A) [IsMonHom φ]
    (k N : ℕ) {T : Over S} (x : T ⟶ A) (hx : x ^ (k * N) = 1) {F G : LB.Sec (LPow A L.L (k : ℤ) T)}
    {F' G' : LB.Sec (LPow A L.L ((k * N : ℕ) : ℤ) T)} (h : IsSymAct A L k (x ≫ φ) F G)
    (hF : IsNormPull A L φ ((k * N : ℕ) : ℤ) (k : ℤ) F F') (hG : IsNormPull A L φ ((k * N : ℕ) : ℤ) (k : ℤ) G G') :
    IsSymAct A L (k * N) x F' G' := by
  have hL := L.isLB
  obtain ⟨-, U, H, ac⟩ := h
  obtain ⟨α₀, α, g₀, n₀, c, tw⟩ := hF
  obtain ⟨α₀', α', g₀', n₀', c', tw'⟩ := hG
  obtain ⟨u, hu, H', vu⟩ := exists_symLift_conj hL φ _ _ α₀ g₀ k N x hx U H
  refine ⟨hx, ⟨x, u, hu⟩, H', VVRank.isTwistPull_of_sv A hL hu fun y J hJ => ?_⟩
  have bb := fun r : (T ⊗ A).left ⟶ A.left =>
    gen_unique hL A.hom (eSec A) (Over.w η[A]) (SemiRigid.globalFns _ _ hA).2 g₀' g₀ (fun w I hI => by
      have a := val_corr hI n₀' (𝟙 _)
      have b := val_corr hI n₀ (𝟙 _)
      rw [val_pull hI, Category.id_comp] at a b
      exact a.trans b.symm) _ r y J hJ
  rw [VVRank.sv_of_isTwistPull A tw' _ y hJ, VVRank.sv_of_isTwistPull A tw _ y hJ,
    VVRank.sv_of_isTwistPull A ac _ y hJ, vu _ _ y J hJ, val_corr hJ c, val_corr hJ c', val_pull hJ, val_pull hJ, bb]
  simp only [Category.id_comp, ← Over.comp_left]
  rw [translT_endT, ← H.pt_eq, show translT A x ≫ snd T A = translPt A x from lift_snd _ _,
    ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul,
    ← Units.val_mul, inv_mul_cancel_right]

end GlobalTheory.PullMove

namespace GlobalTheory.PlaceInt

theorem moves_of_pulls : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (β : 𝓞 E) (N k k' : ℕ), β * H.bar β = (N : 𝓞 E) → k' = k * N → Odd k' → ∀ (b b' : (ptO Xo x ⟶ Xo.univ.t.G)), b' ≫ Xo.univ.t.act.act β = b → b' ^ k' = 1 → ∀ (F G : SecN Xo x k) (F' G' : SecN Xo x k'), Moves Xo b F G → Pulls Xo β F F' → Pulls Xo β G G' → Moves Xo b' F' G' := by
  intro E _ _ _ H Dw l Xo S _ x β N k k' _ hk _ b b' hb hb' F G F' G' h hF hG
  subst hk hb
  have := Xo.univ.t.act.hom β
  exact PullMove.isSymAct_of_isNormPull
    ⟨inferInstance, Xo.univ.t.semi.smooth, Xo.univ.proper, Xo.univ.t.semi.geomConnected⟩ _ _ k N b' hb' h hF hG

end GlobalTheory.PlaceInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NormalisedPullbackCommutesSymmetricTranslationsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedPullback_commutes_symmetric_translations : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (β : 𝓞 E) (N k k' : ℕ), β * H.bar β = (N : 𝓞 E) → k' = k * N → Odd k' → ∀ (b b' : (ptO Xo x ⟶ Xo.univ.t.G)), b' ≫ Xo.univ.t.act.act β = b → b' ^ k' = 1 → ∀ (F G : SecN Xo x k) (F' G' : SecN Xo x k'), Moves Xo b F G → Pulls Xo β F F' → Pulls Xo β G G' → Moves Xo b' F' G' := by
  first | exact @GlobalTheory.PlaceInt.moves_of_pulls | exact GlobalTheory.PlaceInt.moves_of_pulls | (intros; apply GlobalTheory.PlaceInt.moves_of_pulls <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsPrincipalIdealRingLoc
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PlaceInt.LocBasis
open NumberField Module
open scoped nonZeroDivisors

theorem exists_basis_up_to {O A E : Type} [CommRing O] [CommRing A] [IsDomain A] [Field E] [Algebra O A] [Algebra A E]
    [Algebra O E] [IsScalarTower O A E] (S : Submonoid O) [IsLocalization S A] [IsFractionRing A E]
    [IsPrincipalIdealRing A] {n : ℕ} (L : Submodule O (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ (s : S) (b : Fin n → Fin n → E), LinearIndependent E b ∧ (∀ i, b i ∈ L) ∧
      ∀ w ∈ L, (s : O) • w ∈ Submodule.span O (Set.range b) := by
  classical
  set M : Submodule A (Fin n → E) := Submodule.span A (L : Set (Fin n → E)) with hM
  have : Submodule.IsFullLattice E M :=
    { toIsLattice := Submodule.IsLattice.of_fg E <| by
        obtain ⟨s, hs⟩ := hfg
        refine ⟨s, ?_⟩
        rw [hM, ← hs, Submodule.span_span_of_tower]
      span_eq_top := by rw [hM, Submodule.span_span_of_tower, hsp] }
  have hrk : Module.finrank A M = n := by
    simpa using ((Submodule.IsFullLattice.finrank_eq E M).trans (Module.finrank_fintype_fun_eq_card E))
  haveI : Module.Finite A M := Submodule.IsLattice.finite E M
  let c : Basis (Fin n) A M := Module.finBasisOfFinrankEq A M hrk
  have hc : ∀ i, ∃ t : S, (t : O) • (c i : Fin n → E) ∈ L := fun i => by
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span S A (L : Set (Fin n → E)) _ (c i).2
    rw [Submodule.span_eq] at ht
    exact ⟨t, ht⟩
  choose t ht using hc
  let u : Fin n → Aˣ := fun i => (IsLocalization.map_units A (t i)).unit
  let c' : Basis (Fin n) A M := c.unitsSMul u
  have hc' : ∀ i, (c' i : Fin n → E) = (t i : O) • (c i : Fin n → E) := fun i => by
    simp only [c', Basis.unitsSMul_apply, u, Units.smul_def, IsUnit.unit_spec, algebraMap_smul,
      Submodule.coe_smul_of_tower]
  let b : Fin n → Fin n → E := fun i => (c' i : Fin n → E)
  have hli : LinearIndependent E b := by
    have h : b = c'.extendOfIsFullLattice E := funext fun i => by simp [b]
    rw [h]
    exact (c'.extendOfIsFullLattice E).linearIndependent
  have hspanA : Submodule.span A (Set.range b) = M := by
    have : Set.range b = M.subtype '' Set.range c' := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, c'.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hw : ∀ w ∈ L, ∃ r : S, (r : O) • w ∈ Submodule.span O (Set.range b) := fun w hw => by
    obtain ⟨r, hr⟩ := multiple_mem_span_of_mem_localization_span S A (Set.range b) w
      (hspanA ▸ Submodule.subset_span hw)
    exact ⟨r, hr⟩
  obtain ⟨G, hG⟩ := hfg
  choose! r hr using hw
  refine ⟨∏ x ∈ G, r x, b, hli, fun i => by simpa only [b, hc'] using ht i, fun w hw => ?_⟩
  rw [← hG] at hw
  induction hw using Submodule.span_induction with
  | mem y hy =>
    have hy' : y ∈ G := hy
    rw [← Finset.prod_erase_mul G r hy', Submonoid.coe_mul, mul_smul]
    exact Submodule.smul_mem _ _ (hr y (hG ▸ Submodule.subset_span hy))
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ _ hy

def primeTo (R : Type) [CommRing R] (m : ℕ) : Submonoid R where
  carrier := {x | ∃ k : ℕ, k ≠ 0 ∧ Nat.Coprime k m ∧ x = (k : R)}
  one_mem' := ⟨1, one_ne_zero, Nat.coprime_one_left m, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha0, ha, rfl⟩ ⟨b, hb0, hb, rfl⟩
    exact ⟨a * b, mul_ne_zero ha0 hb0, Nat.Coprime.mul_left ha hb, by simp⟩

theorem exists_prime_mem {R : Type} [CommRing R] (Q : Ideal R) (hQ : Q.IsPrime) (a : ℕ) (ha : a ≠ 0)
    (h : (a : R) ∈ Q) : ∃ p : ℕ, p.Prime ∧ (p : R) ∈ Q := by
  induction a using induction_on_primes with
  | zero => exact absurd rfl ha
  | one => exact absurd ((Ideal.eq_top_iff_one Q).2 (by simpa using h)) hQ.ne_top
  | prime_mul p a hp ih =>
    rw [Nat.cast_mul] at h
    rcases hQ.mem_or_mem h with h | h
    · exact ⟨p, hp, h⟩
    · exact ih (by rintro rfl; simp at ha) h

theorem isPrincipalIdealRing_loc (E : Type) [Field E] [NumberField E] (m : ℕ) (hm : 0 < m)
    (hS : primeTo (𝓞 E) m ≤ (𝓞 E)⁰) (A : Type) [CommRing A] [IsDomain A] [Algebra (𝓞 E) A]
    [IsLocalization (primeTo (𝓞 E) m) A] : IsPrincipalIdealRing A := by
  have : IsDedekindDomain A := IsLocalization.isDedekindDomain (𝓞 E) hS A
  have hinj : Function.Injective (algebraMap (𝓞 E) A) := IsLocalization.injective A hS
  have hm0 : (m : A) ≠ 0 := by
    rw [← map_natCast (algebraMap (𝓞 E) A), map_ne_zero_iff _ hinj]
    exact_mod_cast hm.ne'
  have hI : (Ideal.span {(m : A)}) ≠ 0 := by simpa using hm0
  apply IsPrincipalIdealRing.of_finite_primes
  apply (((Ideal.finite_factors hI).image (fun v => v.asIdeal)).insert ⊥).subset
  intro P hP
  have hP' : P.IsPrime := hP
  by_cases hb : P = ⊥
  · exact Or.inl hb
  refine Or.inr ⟨⟨P, hP', hb⟩, ?_, rfl⟩
  set Q := P.comap (algebraMap (𝓞 E) A) with hQ
  have hQb : Q ≠ ⊥ := by
    intro h
    apply hb
    rw [← IsLocalization.map_under (primeTo (𝓞 E) m) A P]
    change Q.map _ = ⊥
    rw [h, Ideal.map_bot]
  have h1 : ((Ideal.absNorm Q : ℕ) : A) ∈ P := by
    have := Ideal.absNorm_mem Q
    rw [hQ, Ideal.mem_comap, map_natCast] at this
    exact this
  obtain ⟨p, hp, hpP⟩ := exists_prime_mem P hP' _ (by rwa [Ne, Ideal.absNorm_eq_zero_iff]) h1
  have hpm : p ∣ m := by
    by_contra hn
    have hu := IsLocalization.map_units A (⟨(p : 𝓞 E), p, hp.ne_zero, (Nat.Prime.coprime_iff_not_dvd hp).2 hn,
      rfl⟩ : primeTo (𝓞 E) m)
    simp only [map_natCast] at hu
    exact hP'.ne_top (Ideal.eq_top_of_isUnit_mem _ hpP hu)
  obtain ⟨c, rfl⟩ := hpm
  simp only [Set.mem_setOf_eq, Ideal.dvd_span_singleton, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hpP

end GlobalTheory.PlaceInt.LocBasis

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlaceInt.LocBasis

theorem exists_matrix_primeTo : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (N : ℕ), 0 < N → L ≤ stdLat E n → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ L → ∀ m : ℕ, 0 < m → ∃ (k₁ : ℕ) (g : Matrix (Fin n) (Fin n) (𝓞 E)), Nat.Coprime k₁ m ∧ g.det ≠ 0 ∧ (∀ v ∈ stdLat E n, (g.map (algebraMap (𝓞 E) E)).mulVec v ∈ L) ∧ ∀ w ∈ L, ∃ v ∈ stdLat E n, (k₁ : E) • w = (g.map (algebraMap (𝓞 E) E)).mulVec v := by
  intro E _ _ n L N hN hle hNL m hm
  classical
  have hmem : ∀ v : Fin n → E, v ∈ stdLat E n ↔ ∃ u : Fin n → 𝓞 E, v = fun i => algebraMap (𝓞 E) E (u i) := fun v => by
    simp only [stdLat, Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]
    constructor
    · intro h
      choose u hu using h
      exact ⟨u, funext fun i => (hu i).symm⟩
    · rintro ⟨u, rfl⟩ i
      exact ⟨u i, rfl⟩
  have hS : primeTo (𝓞 E) m ≤ nonZeroDivisors (𝓞 E) := by
    rintro _ ⟨k, hk, -, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hk)
  let A := Localization.subalgebra E (primeTo (𝓞 E) m) hS
  have : IsPrincipalIdealRing A := isPrincipalIdealRing_loc E m hm hS A
  have hstd : (stdLat E n).FG := Submodule.fg_pi fun _ => by
    rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  have hfg : L.FG := hstd.of_le hle
  have hN0 : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h1 : (Pi.basisFun E (Fin n) i) ∈ stdLat E n :=
      (hmem _).2 ⟨Pi.single i 1, funext fun j => by by_cases h : j = i <;> simp [h, Pi.single_apply]⟩
    have h2 := hNL (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (N : 𝓞 E)) h1)
    have h3 := Submodule.smul_mem (Submodule.span E (L : Set (Fin n → E))) (N : E)⁻¹ (Submodule.subset_span h2)
    rwa [← algebraMap_smul E (N : 𝓞 E), smul_smul, map_natCast, inv_mul_cancel₀ hN0, one_smul] at h3
  obtain ⟨⟨_, k, hk0, hk, rfl⟩, b, hli, hb, hw⟩ := exists_basis_up_to (A := A) (primeTo (𝓞 E) m) L hfg hsp
  choose u hu using fun j => (hmem (b j)).1 (hle (hb j))
  let g : Matrix (Fin n) (Fin n) (𝓞 E) := Matrix.of fun i j => u j i
  have hg : ∀ a : Fin n → 𝓞 E, (g.map (algebraMap (𝓞 E) E)).mulVec (fun i => algebraMap (𝓞 E) E (a i)) =
      ∑ j, a j • b j := fun a => by
    funext i
    simp only [Matrix.mulVec, dotProduct, g, Matrix.map_apply, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hu j, Algebra.smul_def, mul_comm]
  refine ⟨k, g, hk, ?_, ?_, ?_⟩
  · have hcol : (g.map (algebraMap (𝓞 E) E)).col = b := by
      funext j i
      rw [hu j]; rfl
    have hunit : IsUnit (g.map (algebraMap (𝓞 E) E)) :=
      Matrix.linearIndependent_cols_iff_isUnit.1 (hcol ▸ hli)
    intro h0
    have := ((Matrix.isUnit_iff_isUnit_det _).1 hunit).ne_zero
    apply this
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  · intro v hv
    obtain ⟨a, rfl⟩ := (hmem v).1 hv
    rw [hg]
    exact Submodule.sum_mem _ fun j _ => L.smul_mem _ (hb j)
  · intro w hwL
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hw w hwL)
    refine ⟨_, (hmem _).2 ⟨a, rfl⟩, ?_⟩
    rw [hg, ha]
    change _ = (k : 𝓞 E) • w
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
end GlobalTheory.PlaceInt.LocBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SumSupportCMul
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt


open GlobalTheory.NabLinear in
theorem nab_smul_secN {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab)
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k : ℕ) (F F' : SecN Xo y.x k) (r : S)
    (hF : ∀ j, F'.f j = liftFun Xo.univ.t.G _ (T := ptO Xo y.x) (toΓ S r) * F.f j) :
    ∀ α, nab y (k : ℤ) F' α = r * nab y (k : ℤ) F α := by
  intro α
  let _ : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
  obtain ⟨C, hex, hval⟩ := hnab.2 S y
  obtain ⟨f, hf⟩ := hex k F
  have hf' : IsGerm y C.d C.x C.B.A.act C.e C.wP k F' (MvPowerSeries.C r * f) := by
    unfold IsGerm at hf ⊢
    intro m
    obtain ⟨F₁, τ, h1, hc, hv⟩ := hf m
    obtain ⟨F₂, h2⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ)
      (jBase y C.d m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F'
    refine ⟨F₂, τ, h2, hc, ?_⟩
    have hs := GlobalTheory.NabLinear.isValueAt_scale Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (jBase y C.d m 1) hF h1 h2 hv
    convert hs using 1
    have hj : (jBase y C.d m 1).left = spMap (algebraMap S (Jet S (Fin 1 × Fin C.d) m)) := rfl
    rw [hj, GlobalTheory.NabLinear.appTop_toΓ, ← map_mul, ← GlobalTheory.NabLinear.psJet_C]
    congr 1
    clear hval hex hs h1 h2 hv hc hF hnab hj F₁ F₂ hf
    unfold psJet
    rw [← map_mul]
    congr 1
    unfold psTrunc
    have h0 : (0 : Fin 1 × Fin C.d →₀ ℕ) ∈ degLE m := by
      unfold degLE
      simp
      exact ⟨fun _ => 0, by ext; simp⟩
    have hC : ∑ e ∈ degLE m, MvPolynomial.monomial e
        (MvPowerSeries.coeff e (MvPowerSeries.C r : MvPowerSeries (Fin 1 × Fin C.d) S)) =
        MvPolynomial.monomial 0 r := by
      rw [Finset.sum_eq_single_of_mem 0 h0 (fun e _ he => by rw [MvPowerSeries.coeff_C, if_neg he, map_zero]),
        MvPowerSeries.coeff_C, if_pos rfl]
    rw [hC, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [MvPowerSeries.coeff_C_mul, MvPolynomial.monomial_mul, zero_add]
  exact (hval k F' _ hf' α).trans ((GlobalTheory.NabLinear.nabVal_C_mul C.B C.h H.w0 k r f C.uvec _).trans
    (congrArg (r * ·) (hval k F f hf α).symm))

theorem sum_support_C_mul {σ K S : Type} [CommRing K] [CommRing S] [Algebra K S] (P : MvPolynomial σ K) (s : K)
    (g : (σ →₀ ℕ) → S) :
    ∑ m ∈ (MvPolynomial.C s * P).support, algebraMap K S ((MvPolynomial.C s * P).coeff m) * g m =
      algebraMap K S s * ∑ m ∈ P.support, algebraMap K S (P.coeff m) * g m := by
  classical
  have hsub : (MvPolynomial.C s * P).support ⊆ P.support := by
    rw [MvPolynomial.C_mul']
    exact MvPolynomial.support_smul
  calc ∑ m ∈ (MvPolynomial.C s * P).support, algebraMap K S ((MvPolynomial.C s * P).coeff m) * g m
      = ∑ m ∈ P.support, algebraMap K S ((MvPolynomial.C s * P).coeff m) * g m := by
        apply Finset.sum_subset hsub
        intro m _ hm
        rw [MvPolynomial.mem_support_iff, not_not] at hm
        rw [hm, map_zero, zero_mul]
    _ = algebraMap K S s * ∑ m ∈ P.support, algebraMap K S (P.coeff m) * g m := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [MvPolynomial.coeff_C_mul, map_mul, _root_.mul_assoc]

theorem hv_linear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F), (∀ (k : ℕ) (F F' : Fin n → SecN Xo y.x k) (r : Fin n → S), (∀ b j, (F' b).f j = liftFun Xo.univ.t.G _ (T := ptO Xo y.x) (toΓ S (r b)) * (F b).f j) → hv Xo c nab y k F' P = (∏ b, r b) * hv Xo c nab y k F P) ∧ (∀ (k : ℕ) (F : Fin n → SecN Xo y.x k) (s : c.F), hv Xo c nab y k F (MvPolynomial.C s * P) = algebraMap c.F S s * hv Xo c nab y k F P) ∧ ∀ (N : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))), ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F b) (colOf m b) = hv Xo c nab y (N ^ 2) (fun b => sqN Xo N (F b)) P := by
  intro E _ _ _ H Dw l Xo c _ _ nab hnab S _ _ y n P
  refine ⟨?_, ?_, ?_⟩
  · intro k F F' r hF
    unfold hv
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have key : ∀ b, nab y (k : ℤ) (F' b) (colOf m b) = r b * nab y (k : ℤ) (F b) (colOf m b) :=
      fun b => nab_smul_secN Xo c nab hnab y k (F b) (F' b) (r b) (hF b) _
    simp only [key, Finset.prod_mul_distrib]
    ring
  · intro k F s
    unfold hv
    exact sum_support_C_mul P s _
  · intro N F
    unfold hv sqN
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1

end GlobalTheory.PlaceInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsotropicGroupPrimaryDecomposition
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsotropicGroupPrimaryDecomposition
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory

namespace IsotropicPrimary

theorem exists_primary_complement (Z : Type) [CommGroup Z] [Finite Z] (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ∃ P Q : Subgroup Z, (∀ u, u ∈ P ↔ ∃ j : ℕ, u ^ (ℓ ^ j) = 1) ∧ Nat.Coprime (Nat.card Q) ℓ ∧
      (Function.Bijective fun y : P × Q => (y.1 : Z) * (y.2 : Z)) ∧
      Nat.card P = ℓ ^ (Nat.card Z).factorization ℓ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨S⟩ : Nonempty (Sylow ℓ Z) := inferInstance
  haveI : (S : Subgroup Z).Normal := Subgroup.normal_of_isMulCommutative _
  obtain ⟨Q, hQ⟩ := Subgroup.exists_right_complement'_of_coprime (N := (S : Subgroup Z)) S.card_coprime_index
  refine ⟨S, Q, fun u => ⟨fun hu => ?_, fun hu => ?_⟩, ?_, hQ, S.card_eq_multiplicity⟩
  · obtain ⟨k, hk⟩ := S.isPGroup' ⟨u, hu⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  · obtain ⟨j, hj⟩ := hu
    have hp : IsPGroup ℓ (Subgroup.zpowers u) :=
      IsPGroup.of_card_dvd_pow (n := j) (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hj)
    obtain ⟨T, hT⟩ := hp.exists_le_sylow
    letI := Sylow.unique_of_normal S ‹_›
    have hTS : T = S := Subsingleton.elim _ _
    subst hTS
    exact hT (Subgroup.mem_zpowers u)
  · rw [← hQ.symm.index_eq_card]
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ).2 S.not_dvd_index)

theorem epi_spMap_of_fields {K k : Type} [Field K] [Field k] (β : K →+* k) : Epi (spMap β) := by
  letI : Algebra K k := β.toAlgebra
  have hff : (CommRingCat.ofHom β).hom.FaithfullyFlat := by
    change Module.FaithfullyFlat K k
    infer_instance
  obtain ⟨h1, h2⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom β)).2 hff
  exact Flat.epi_of_flat_of_surjective _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def zhSubgroup (Xo : Moduli Dw l) {n : ℕ} (Λ : GenLat E n) (N : ℕ) (hN : 0 < N) (T : Over Xo.X) :
    Subgroup (Fin n → (T ⟶ Xo.univ.t.G)) :=
  have hone : InZh Xo Λ N (1 : Fin n → (T ⟶ Xo.univ.t.G)) := by
    refine ⟨fun b => one_pow _, fun mu _ cm _ i => List.prod_eq_one fun x hx => ?_⟩
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
    have := Xo.univ.t.act.hom (cm i j)
    exact MonObj.one_comp _
  have hpow : ∀ (a : Fin n → (T ⟶ Xo.univ.t.G)), InZh Xo Λ N a → ∀ k : ℕ, InZh Xo Λ N (a ^ k) := by
    intro a ha k
    induction k with
    | zero => rw [pow_zero]; exact hone
    | succ k ih => rw [pow_succ]; exact ZhStable.inZh_mul Xo Λ N _ _ ih ha
  { carrier := {a | InZh Xo Λ N a}
    one_mem' := hone
    mul_mem' := fun {a a'} ha ha' => ZhStable.inZh_mul Xo Λ N a a' ha ha'
    inv_mem' := fun {a} ha => by
      have h1 : a ^ (N ^ 2) = 1 := funext ha.1
      have h2 : a⁻¹ = a ^ (N ^ 2 - 1) := by
        refine inv_eq_of_mul_eq_one_left ?_
        rw [← pow_succ, Nat.sub_add_cancel (pow_pos hN 2), h1]
      change InZh Xo Λ N a⁻¹
      rw [h2]
      exact hpow a ha _ }

theorem enumeration_bijective (Xo : Moduli Dw l) {K : Type} [Field K] (x : Sp K ⟶ Xo.X)
    {n : ℕ} (Λ : GenLat E n) {N : ℕ} (hΛ : Λ.Unimod) (hN : 0 < N)
    (hle : Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La)
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x ⟶ Xo.univ.t.G)) (hz : ∀ i, InZh Xo Λ N (z i))
    (hinj : GeoInj Xo x z) : Function.Injective z ∧ ∀ a, InZh Xo Λ N a → ∃ i, z i = a := by
  refine ⟨fun i j hij => ?_, fun a ha => ?_⟩
  · let g : ptO Xo (spMap (RingHom.id K) ≫ x) ⟶ ptO Xo x := Over.homMk (spMap (RingHom.id K)) rfl
    refine hinj K (RingHom.id K) g rfl ?_
    show (fun b => g ≫ z i b) = fun b => g ≫ z j b
    rw [hij]
  · let ψ : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
    let g : ptO Xo (spMap ψ ≫ x) ⟶ ptO Xo x := Over.homMk (spMap ψ) rfl
    have hw : ∀ i, InZh Xo Λ N (fun b => g ≫ z i b) := fun i => ZhStable.inZh_comp Xo Λ N g (z i) (hz i)
    obtain ⟨i, hi⟩ := IsotropicEnum.exists_eq_of_isAlgClosed Xo (spMap ψ ≫ x) Λ hΛ hN hle
      (fun i b => g ≫ z i b) hw (hinj (AlgebraicClosure K) ψ g rfl) (fun b => g ≫ a b)
      (ZhStable.inZh_comp Xo Λ N g a ha)
    refine ⟨i, funext fun b => ?_⟩
    haveI := epi_spMap_of_fields ψ
    have hb := congrArg CommaMorphism.left (congrFun hi b)
    simp only [Over.comp_left] at hb
    exact Over.OverMorphism.ext ((cancel_epi (spMap ψ)).1 hb)

end IsotropicPrimary


open IsotropicPrimary in
theorem isotropic_primary_decomposition :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X) (n : ℕ) (Λ : GenLat E n) (N M ℓ : ℕ), Λ.Unimod → Λ.LevOK N M → ℓ.Prime → ∀ z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x ⟶ Xo.univ.t.G), (∀ i, InZh Xo Λ N (z i)) → GeoInj Xo x z → ∃ (J J' : Type) (_ : Fintype J) (_ : Fintype J') (a : J → Fin n → (ptO Xo x ⟶ Xo.univ.t.G)) (a' : J' → Fin n → (ptO Xo x ⟶ Xo.univ.t.G)) (σ : J × J' ≃ Fin (Λ.zCard N (Dw.p + Dw.q))), Function.Injective a ∧ (∀ u, (∃ i, a i = u) ↔ (InZh Xo Λ N u ∧ ∀ b, ∃ j : ℕ, u b ^ (ℓ ^ j) = 1)) ∧ (∃ m : ℕ, Nat.Coprime m ℓ ∧ ∀ i b, a' i b ^ m = 1 ∧ a' i b ^ (N ^ 2) = 1) ∧ (∀ i i' b, z (σ (i, i')) b = a i b * a' i' b) ∧ Fintype.card J = ℓ ^ (Λ.zCard N (Dw.p + Dw.q)).factorization ℓ := by
  intro E _ _ _ H Dw l Xo K _ x n Λ N M ℓ hΛ hlev hℓ z hz hinj
  have hN : 0 < N := hlev.1.pos
  have hle : Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La := hlev.2.2.trans inf_le_left
  obtain ⟨hzinj, hzon⟩ := enumeration_bijective Xo x Λ hΛ hN hle z hz hinj
  let e : Fin (Λ.zCard N (Dw.p + Dw.q)) → zhSubgroup Xo Λ N hN (ptO Xo x) := fun i => ⟨z i, hz i⟩
  have he : Function.Bijective e :=
    ⟨fun i j h => hzinj (congrArg Subtype.val h), fun u => by
      obtain ⟨i, hi⟩ := hzon u.1 u.2
      exact ⟨i, Subtype.ext hi⟩⟩
  haveI : Finite (zhSubgroup Xo Λ N hN (ptO Xo x)) := Finite.of_surjective e he.2
  obtain ⟨P, Q, hP, hQ, hPQ, hcard⟩ := exists_primary_complement (zhSubgroup Xo Λ N hN (ptO Xo x)) ℓ hℓ
  refine ⟨P, Q, Fintype.ofFinite _, Fintype.ofFinite _, fun p => ((p : zhSubgroup Xo Λ N hN (ptO Xo x)) : Fin n → _),
    fun q => ((q : zhSubgroup Xo Λ N hN (ptO Xo x)) : Fin n → _),
    (Equiv.ofBijective _ hPQ).trans (Equiv.ofBijective e he).symm, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun p p' h => Subtype.ext (Subtype.ext h)
  · intro u
    constructor
    · rintro ⟨p, rfl⟩
      refine ⟨(p : zhSubgroup Xo Λ N hN (ptO Xo x)).2, fun b => ?_⟩
      obtain ⟨j, hj⟩ := (hP _).1 p.2
      refine ⟨j, ?_⟩
      have := congrArg (fun w : zhSubgroup Xo Λ N hN (ptO Xo x) => w.1 b) hj
      simpa using this
    · rintro ⟨hu, hpow⟩
      choose j hj using hpow
      refine ⟨⟨⟨u, hu⟩, (hP _).2 ⟨∑ b, j b, Subtype.ext (funext fun b => ?_)⟩⟩, rfl⟩
      obtain ⟨c, hc⟩ : ℓ ^ j b ∣ ℓ ^ (∑ b, j b) :=
        pow_dvd_pow ℓ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ b))
      simp only [Subgroup.coe_pow, Pi.pow_apply, Subgroup.coe_one, Pi.one_apply]
      rw [hc, pow_mul, hj b, one_pow]
  · refine ⟨Nat.card Q, hQ, fun i b => ⟨?_, ((i : zhSubgroup Xo Λ N hN (ptO Xo x)).2 : InZh Xo Λ N _).1 b⟩⟩
    have := congrArg (fun w : Q => (w : zhSubgroup Xo Λ N hN (ptO Xo x)).1 b) (pow_card_eq_one' (G := Q) (x := i))
    simp only [Subgroup.coe_pow, Pi.pow_apply, Subgroup.coe_one, Pi.one_apply] at this
    exact this
  · intro i i' b
    have h1 : e ((Equiv.ofBijective e he).symm ((i : zhSubgroup Xo Λ N hN (ptO Xo x)) * (i' : zhSubgroup Xo Λ N hN (ptO Xo x)))) =
        (i : zhSubgroup Xo Λ N hN (ptO Xo x)) * (i' : zhSubgroup Xo Λ N hN (ptO Xo x)) :=
      Equiv.ofBijective_apply_symm_apply e he _
    simp only [Equiv.trans_apply, Equiv.ofBijective_apply]
    exact congrFun (congrArg Subtype.val h1) b
  · rw [@Fintype.card_eq_nat_card P (Fintype.ofFinite P), hcard, ← Nat.card_eq_of_bijective e he, Nat.card_fin]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsotropicGroupPrimaryDecompositionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_group_primary_decomposition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X) (n : ℕ) (Λ : GenLat E n) (N M ℓ : ℕ), Λ.Unimod → Λ.LevOK N M → ℓ.Prime → ∀ z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x ⟶ Xo.univ.t.G), (∀ i, InZh Xo Λ N (z i)) → GeoInj Xo x z → ∃ (J J' : Type) (_ : Fintype J) (_ : Fintype J') (a : J → Fin n → (ptO Xo x ⟶ Xo.univ.t.G)) (a' : J' → Fin n → (ptO Xo x ⟶ Xo.univ.t.G)) (σ : J × J' ≃ Fin (Λ.zCard N (Dw.p + Dw.q))), Function.Injective a ∧ (∀ u, (∃ i, a i = u) ↔ (InZh Xo Λ N u ∧ ∀ b, ∃ j : ℕ, u b ^ (ℓ ^ j) = 1)) ∧ (∃ m : ℕ, Nat.Coprime m ℓ ∧ ∀ i b, a' i b ^ m = 1 ∧ a' i b ^ (N ^ 2) = 1) ∧ (∀ i i' b, z (σ (i, i')) b = a i b * a' i' b) ∧ Fintype.card J = ℓ ^ (Λ.zCard N (Dw.p + Dw.q)).factorization ℓ := by
  first | exact @GlobalTheory.isotropic_primary_decomposition | exact GlobalTheory.isotropic_primary_decomposition | (intros; apply GlobalTheory.isotropic_primary_decomposition <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DvdOfCastDvd
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.TorsFac

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem act_nat {S : Scheme.{0}} (t : SAB H S) {T : Over S} (x : T ⟶ t.G) (n : ℕ) :
    x ≫ t.act.act (n : 𝓞 E) = x ^ n := by
  have h0 : t.act.act 0 = 1 := by
    have h := t.act.add 0 0
    rw [add_zero] at h
    have h2 := congrArg (fun f => (t.act.act 0)⁻¹ * f) h
    simp only [inv_mul_cancel, inv_mul_cancel_left] at h2
    exact h2.symm
  induction n with
  | zero => rw [Nat.cast_zero, pow_zero, h0, MonObj.comp_one]
  | succ n ih => rw [Nat.cast_succ, t.act.add, MonObj.comp_mul, ih, t.act.one, Category.comp_id, pow_succ]

theorem act_pow {S : Scheme.{0}} (t : SAB H S) {T : Over S} (x : T ⟶ t.G) (b : 𝓞 E) (n : ℕ) :
    (x ≫ t.act.act b) ^ n = x ≫ t.act.act (b * n) := by
  rw [t.act.mul, ← Category.assoc, act_nat]

theorem bar_bar (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

theorem M_mem (l : Level H) : (l.M : 𝓞 E) ∈ l.Mb := by
  have h : (l.M : 𝓞 E) ∈ Ideal.span {(l.M : 𝓞 E)} := Ideal.mem_span_singleton_self _
  rw [← l.prod] at h
  exact (Ideal.mul_le_left : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb) h

theorem kill {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {T : Over Xo.X} (t : T ⟶ Xo.univ.t.G) (N : ℕ)
    (h : KilledBy Xo l.Mb (t ^ N)) (a : 𝓞 E) (ha : a ∈ l.Mb) : t ≫ Xo.univ.t.act.act (N * a) = 1 := by
  rw [Xo.univ.t.act.mul, ← Category.assoc, act_nat]
  exact h a ha

omit [IsCMField E] in
theorem dvd_of_cast_dvd {p m : ℕ} (hp : p.Prime) (h : (p : 𝓞 E) ∣ (m : 𝓞 E)) : p ∣ m := by
  have h2 := map_dvd (Algebra.norm ℤ) h
  have e1 : (p : 𝓞 E) = algebraMap ℤ (𝓞 E) (p : ℤ) := by simp
  have e2 : (m : 𝓞 E) = algebraMap ℤ (𝓞 E) (m : ℤ) := by simp
  rw [e1, e2, Algebra.norm_algebraMap, Algebra.norm_algebraMap] at h2
  have hr : Module.finrank ℤ (𝓞 E) ≠ 0 := Module.finrank_pos.ne'
  rw [IsIntegrallyClosed.pow_dvd_pow_iff hr] at h2
  exact Int.natCast_dvd_natCast.mp h2

theorem split_once {M ℓ e n' : ℕ} (hp : ℓ.Prime) (h1 : ℓ ∣ M) (h2 : ¬ ℓ ^ 2 ∣ M) (h : M ∣ ℓ ^ e * n') :
    ∃ m k, M = ℓ * m ∧ n' = m * k := by
  obtain ⟨m, rfl⟩ := h1
  have hm : ¬ ℓ ∣ m := fun ⟨c, hc⟩ => h2 ⟨c, by rw [hc]; ring⟩
  have hcop : Nat.Coprime m (ℓ ^ e) :=
    Nat.Coprime.pow_right e ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm
  obtain ⟨k, hk⟩ := hcop.dvd_of_dvd_mul_left ((Dvd.intro_left ℓ rfl).trans h)
  exact ⟨m, k, rfl, hk⟩

private theorem sq_lemma' {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {T : Over Xo.X} (t : T ⟶ Xo.univ.t.G)
    {N : ℕ} (hMN : l.M ∣ N) (hk : KilledBy Xo l.Mb (t ^ N)) : t ^ (N ^ 2) = 1 := by
  have hN : (N : 𝓞 E) ∈ l.Mb := by
    obtain ⟨q, rfl⟩ := hMN
    push_cast
    exact Ideal.mul_mem_right _ _ (M_mem l)
  rw [sq, pow_mul, ← act_nat Xo.univ.t (t ^ N) N]
  exact hk _ hN

private theorem natCast_mem_level_of_dvd {l : Level H} {k : ℕ} (h : l.M ∣ k) : (k : 𝓞 E) ∈ l.Mb := by
  obtain ⟨q, rfl⟩ := h
  push_cast
  exact Ideal.mul_mem_right _ _ (M_mem l)

private theorem dvd_lemma_3 {M ℓ e n' : ℕ} (hp : ℓ.Prime) (h2 : ¬ ℓ ^ 2 ∣ M) (h : M ∣ ℓ ^ e * n') :
    M ∣ ℓ * n' := by
  by_cases h1 : ℓ ∣ M
  · obtain ⟨m, k, rfl, rfl⟩ := split_once hp h1 h2 h
    exact ⟨k, by ring⟩
  · have hc : Nat.Coprime M (ℓ ^ e) :=
      Nat.Coprime.pow_right e ((Nat.Prime.coprime_iff_not_dvd hp).2 h1).symm
    exact Dvd.dvd.mul_left (hc.dvd_of_dvd_mul_left h) ℓ

theorem factorisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N ℓ : ℕ), Odd N → l.M ∣ N → ℓ.Prime → (¬ ℓ ∣ l.M → ∃ (n' j : ℕ), Nat.Coprime n' ℓ ∧ N = ℓ ^ j * n' ∧ ∀ (T : Over Xo.X) (t : T ⟶ Xo.univ.t.G), KilledBy Xo l.Mb (t ^ N) → (∃ i : ℕ, KilledBy Xo (l.Mb ^ i) t) → t ^ (N ^ 2) = 1 ∧ (t ≫ Xo.univ.t.act.act ((ℓ : 𝓞 E) ^ j)) ^ (n' ^ 2 * 1) = 1 ∧ ∃ i : ℕ, t ^ (l.M ^ i) = 1) ∧ ∀ (α : 𝓞 E) (A : ℕ), α * H.bar α = (A : 𝓞 E) → ¬ ℓ ^ 2 ∣ l.M → ((A = ℓ ∧ l.Mb ≤ Ideal.span {H.bar α}) ∨ (α = (ℓ : 𝓞 E) ∧ ℓ ∣ l.M)) → ∃ (n' Bn j : ℕ) (β : 𝓞 E), Nat.Coprime n' ℓ ∧ (N : 𝓞 E) = β * α * n' ∧ β * H.bar β = (Bn : 𝓞 E) ∧ A * Bn = ℓ ^ j ∧ ∀ (T : Over Xo.X) (t : T ⟶ Xo.univ.t.G), KilledBy Xo l.Mb (t ^ N) → (∃ i : ℕ, KilledBy Xo (l.Mb ^ i) t) → t ^ (N ^ 2) = 1 ∧ (t ≫ Xo.univ.t.act.act β) ^ (n' ^ 2 * A) = 1 := by
  intro E _ _ _ H Dw l Xo N ℓ hN hMN hp
  have hN0 : N ≠ 0 := hN.pos.ne'
  refine ⟨fun hℓM => ?_, fun α A hA h2 hc => ?_⟩
  · obtain ⟨j, n', hn', hNe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 ℓ hp.one_lt.ne'
    have hcop : Nat.Coprime n' ℓ := ((Nat.Prime.coprime_iff_not_dvd hp).2 hn').symm
    have hMn : l.M ∣ n' := by
      have hc : Nat.Coprime l.M (ℓ ^ j) :=
        Nat.Coprime.pow_right j ((Nat.Prime.coprime_iff_not_dvd hp).2 hℓM).symm
      exact hc.dvd_of_dvd_mul_left (hNe ▸ hMN)
    refine ⟨n', j, hcop, hNe, fun T t hk hi => ⟨sq_lemma' Xo t hMN hk, ?_, ?_⟩⟩
    · rw [act_pow]
      have he : (ℓ : 𝓞 E) ^ j * ((n' ^ 2 * 1 : ℕ) : 𝓞 E) = (N : 𝓞 E) * (n' : 𝓞 E) := by
        rw [hNe]; push_cast; ring
      rw [he]
      exact kill Xo t N hk _ (natCast_mem_level_of_dvd hMn)
    · obtain ⟨i, hi⟩ := hi
      refine ⟨i, ?_⟩
      rw [← act_nat Xo.univ.t t, Nat.cast_pow]
      exact hi _ (Ideal.pow_mem_pow (M_mem l) i)
  · have hℓN : ℓ ∣ N := by
      rcases hc with ⟨hA', hle⟩ | ⟨_, hℓM⟩
      · have hbM : H.bar α ∣ (l.M : 𝓞 E) := Ideal.mem_span_singleton.mp (hle (M_mem l))
        have haM : α ∣ (l.M : 𝓞 E) := by
          have h3 := map_dvd H.bar hbM
          rwa [bar_bar, map_natCast] at h3
        have hl : (ℓ : 𝓞 E) = α * H.bar α := by rw [hA, hA']
        have h4 : (ℓ : 𝓞 E) ∣ ((N ^ 2 : ℕ) : 𝓞 E) := by
          obtain ⟨q, rfl⟩ := hMN
          rw [hl]
          exact (mul_dvd_mul haM hbM).trans ⟨(q : 𝓞 E) ^ 2, by push_cast; ring⟩
        exact hp.dvd_of_dvd_pow (dvd_of_cast_dvd hp h4)
      · exact hℓM.trans hMN
    obtain ⟨N', hN'⟩ := hℓN
    have hN'0 : N' ≠ 0 := right_ne_zero_of_mul (hN' ▸ hN0)
    obtain ⟨e, n', hn', hN'e⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN'0 ℓ hp.one_lt.ne'
    have hNe : N = ℓ ^ (e + 1) * n' := by rw [hN', hN'e]; ring
    have hcop : Nat.Coprime n' ℓ := ((Nat.Prime.coprime_iff_not_dvd hp).2 hn').symm
    have hMl : l.M ∣ ℓ * n' := dvd_lemma_3 hp h2 (by rw [← hNe]; exact hMN)
    have hmem : ((ℓ * n' : ℕ) : 𝓞 E) ∈ l.Mb := natCast_mem_level_of_dvd hMl
    rcases hc with ⟨hA', hle⟩ | ⟨hα, _⟩
    · have hl : (ℓ : 𝓞 E) = α * H.bar α := by rw [hA, hA']
      refine ⟨n', ℓ ^ (2 * e + 1), 2 * e + 2, (ℓ : 𝓞 E) ^ e * H.bar α, hcop, ?_, ?_, ?_,
        fun T t hk _ => ⟨sq_lemma' Xo t hMN hk, ?_⟩⟩
      · rw [hNe]; push_cast; rw [hl]; ring
      · rw [map_mul, map_pow, map_natCast, bar_bar]; push_cast; rw [hl]; ring
      · rw [hA']; ring
      · have htop : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
          rw [l.coprime]; exact Submodule.mem_top
        obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp htop
        have hy' : y ∈ Ideal.span {α} := by
          have h5 := Ideal.map_mono (f := (H.bar : 𝓞 E →+* 𝓞 E)) hle hy
          simpa [Ideal.map_span, bar_bar] using h5
        obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hy'
        have hb : (n' : 𝓞 E) * H.bar α ∈ l.Mb := by
          have h6 : (n' : 𝓞 E) * H.bar α = x * ((n' : 𝓞 E) * H.bar α) + z * ((ℓ * n' : ℕ) : 𝓞 E) := by
            push_cast
            linear_combination (-((n' : 𝓞 E) * H.bar α)) * hxy + (-((n' : 𝓞 E) * H.bar α)) * hz +
              (-(z * (n' : 𝓞 E))) * hl
          rw [h6]
          exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hx) (Ideal.mul_mem_left _ z hmem)
        rw [act_pow]
        have he : (ℓ : 𝓞 E) ^ e * H.bar α * ((n' ^ 2 * A : ℕ) : 𝓞 E) =
            (N : 𝓞 E) * ((n' : 𝓞 E) * H.bar α) := by
          rw [hNe, hA']; push_cast; ring
        rw [he]
        exact kill Xo t N hk _ hb
    · have hA2 : A = ℓ ^ 2 := by
        have h7 : ((A : ℕ) : 𝓞 E) = ((ℓ ^ 2 : ℕ) : 𝓞 E) := by
          rw [← hA, hα, map_natCast]; push_cast; ring
        exact Nat.cast_injective h7
      refine ⟨n', ℓ ^ (2 * e), 2 * e + 2, (ℓ : 𝓞 E) ^ e, hcop, ?_, ?_, ?_,
        fun T t hk _ => ⟨sq_lemma' Xo t hMN hk, ?_⟩⟩
      · rw [hNe, hα]; push_cast; ring
      · rw [map_pow, map_natCast]; push_cast; ring
      · rw [hA2]; ring
      · rw [act_pow, hA2]
        have he : (ℓ : 𝓞 E) ^ e * ((n' ^ 2 * ℓ ^ 2 : ℕ) : 𝓞 E) = (N : 𝓞 E) * ((ℓ * n' : ℕ) : 𝓞 E) := by
          rw [hNe]; push_cast; ring
        rw [he]
        exact kill Xo t N hk _ hmem

end GlobalTheory.TorsFac
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueEqChartValue
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueEqChartValue
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

theorem hv_eq_chartVal :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (S : Type) [Field S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y) (k n : ℕ) (F : Fin n → SecN Xo y.x k) (f : Fin n → PS S 1 C.d), (∀ b, IsGerm y C.d C.x C.B.A.act C.e C.wP k (F b) (f b)) → ∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HH c w n → hv Xo c nab y k F P = chartVal C k f P := by
  intro E _ _ _ H Dw l Xo c _ hst nab hnab S _ _ _ y C k n F f hf w P hP
  obtain ⟨C₀, hex, hpin⟩ := hnab.2 S y
  choose f₀ hf₀ using fun b => hex k (F b)
  have e₀ : ∀ m, ∏ b, nab y k (F b) (colOf m b) =
      ∏ b, C₀.B.nabVal S C₀.h H.w0 k (f₀ b) C₀.uvec (MvPolynomial.monomial (colOf m b) 1) := fun m =>
    Finset.prod_congr rfl fun b _ => hpin k (F b) (f₀ b) (hf₀ b) (colOf m b)
  obtain ⟨N, hN, hA, hs⟩ := GlobalTheory.exists_natCast_smul_mem_harmA E H Dw l c w n P hP
  have h := GlobalTheory.T.harmonicValue_germs_independent_of_chart E H Dw l Xo c hst S y C₀ C k n F f₀ f hf₀ hf w _ hA
  have hu : IsUnit (algebraMap c.F S (N : c.F)) :=
    (IsUnit.mk0 (N : c.F) (Nat.cast_ne_zero.2 hN.ne')).map _
  simp only [chartVal, hs, MvPolynomial.coeff_smul, smul_eq_mul, map_mul, _root_.mul_assoc, ← Finset.mul_sum] at h
  simp only [hv, chartVal, e₀]
  exact hu.mul_left_cancel h

end GlobalTheory.PlaceInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueEqChartValueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonicValue_eq_chart_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (S : Type) [Field S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y) (k n : ℕ) (F : Fin n → SecN Xo y.x k) (f : Fin n → PS S 1 C.d), (∀ b, IsGerm y C.d C.x C.B.A.act C.e C.wP k (F b) (f b)) → ∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HH c w n → hv Xo c nab y k F P = chartVal C k f P := by
  first | exact @GlobalTheory.PlaceInt.hv_eq_chartVal | exact GlobalTheory.PlaceInt.hv_eq_chartVal | (intros; apply GlobalTheory.PlaceInt.hv_eq_chartVal <;> assumption)
end
end
