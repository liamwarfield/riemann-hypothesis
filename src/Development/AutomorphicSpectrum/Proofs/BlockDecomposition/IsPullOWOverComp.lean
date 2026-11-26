module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechTripleRestrictCompositeInjectiveSecond
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationComapSpanPow
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalGramFiberRankOneSetFormula

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullOWOverComp
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullOWOverComp
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Axis.PullO

theorem restrict_pull1_bijective_of_basis {R' : Type} [CommRing R'] {X' : Scheme.{0}} (s' : X' ⟶ Sp R')
    {C' : Type} [Category.{0} C'] [Quiver.IsThin C'] (G : C' ⥤ AffOp X')
    (hcov : ∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (OAff s').obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S),
        IsUnit (mp (OAff s') u (b i)) →
          ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u)
    (hdir : ∀ (t₁ t₂ : C') (S : AffOp X'), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) →
      ∃ (n : ℕ) (b : Fin n → (OAff s').obj S), Ideal.span (Set.range b) = ⊤ ∧
        ∀ (i : Fin n) (S' : AffOp X') (u : S ⟶ S'), IsUnit (mp (OAff s') u (b i)) →
          ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) :
    Function.Bijective (CoefMap.restrict (OAff s') G).pull1 := by
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s'
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s') G H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s') G H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s') G H hcov hdir
  exact ⟨_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg,
    _root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hs hg hv⟩

section Triple

variable {R'' : Type} [CommRing R''] {X X' X'' : Scheme.{0}}
variable (ψ : X'' ⟶ X') (φ : X' ⟶ X)

theorem triple_restriction_pair_restriction (s'' : X'' ⟶ Sp R'') (c : HO1 s'') :
    (cechTripleRestrictComposite ψ φ s'').pull1 ((pairRes (ψ ≫ φ) s'').pull1 c) =
      (CoefMap.restrict (OAff s'') (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ))).pull1 c := by
  rw [← GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_comp]
  refine GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app := fun _ => 𝟙 _, naturality := fun _ _ _ => Quiver.Hom.unop_inj (Subsingleton.elim _ _) } ?_ c
  intro T b
  rw [GlobalTheory.CatCoh.mp_id]

theorem triple_restriction_injective (s'' : X'' ⟶ Sp R'') : Function.Injective (cechTripleRestrictComposite ψ φ s'').pull1 := by
  intro x y hxy
  obtain ⟨x', rfl⟩ := (pairRes_bijective (ψ ≫ φ) s'').1.2 x
  obtain ⟨y', rfl⟩ := (pairRes_bijective (ψ ≫ φ) s'').1.2 y
  rw [triple_restriction_pair_restriction, triple_restriction_pair_restriction] at hxy
  rw [(restrict_pull1_bijective_of_basis s'' (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ))
    (triple_cover_affine ψ φ s'') (exists_triple_below_two ψ φ s'')).1 hxy]

end Triple

section Comp

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {τ : R' →+* R''}
  {φ : X' ⟶ X} {ψ : X'' ⟶ X'}

theorem tri_pull_pull (h : φ ≫ s = s' ≫ spMap σ) (h' : ψ ≫ s' = s'' ≫ spMap τ)
    (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (τ.comp σ)) (a : HO1 s) :
    (cechTripleRestrictComposite ψ φ s'').pull1 ((pairPull h'').pull1 a) =
      (cechTriplePullbackSecond h').pull1 ((pairPull h).pull1 a) := by
  rw [← GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_comp, ← GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_comp]
  refine GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_eq_of_natTrans ((pairPull h'').comp (cechTripleRestrictComposite ψ φ s''))
    ((pairPull h).comp (cechTriplePullbackSecond h')) { app := fun _ => 𝟙 _, naturality := fun _ _ _ => Quiver.Hom.unop_inj (Subsingleton.elim _ _) } ?_ a
  intro T b
  erw [GlobalTheory.CatCoh.mp_id]
  show (CommRingCat.Hom.hom (Scheme.Hom.appLE φ _ _ _ ≫ Scheme.Hom.appLE ψ _ _ _)) b =
    CommRingCat.Hom.hom (Scheme.Hom.appLE (ψ ≫ φ) _ _ _) b
  exact congrArg (fun k => CommRingCat.Hom.hom k b) (Scheme.Hom.appLE_comp_appLE ψ φ _ _ _ _ _)

theorem tri_res_pull (h' : ψ ≫ s' = s'' ≫ spMap τ) (a : HO1 s') :
    (cechTriplePullbackSecond (φ := φ) h').pull1 ((pairRes φ s').pull1 a) =
      (cechTripleRestrictFirst ψ φ s'').pull1 ((pairPull h').pull1 a) := by
  rw [← GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_comp, ← GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_comp]
  refine GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app := fun _ => 𝟙 _, naturality := fun _ _ _ => Quiver.Hom.unop_inj (Subsingleton.elim _ _) } ?_ a
  intro T b
  rw [GlobalTheory.CatCoh.mp_id]

theorem tri_res_res (a : HO1 s'') :
    (cechTripleRestrictFirst ψ φ s'').pull1 ((pairRes ψ s'').pull1 a) =
      (cechTripleRestrictComposite ψ φ s'').pull1 ((pairRes (ψ ≫ φ) s'').pull1 a) := by
  rw [← GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_comp, ← GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_comp]
  refine GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app := fun _ => 𝟙 _, naturality := fun _ _ _ => Quiver.Hom.unop_inj (Subsingleton.elim _ _) } ?_ a
  intro T b
  rw [GlobalTheory.CatCoh.mp_id]

theorem isPullO_comp (h : φ ≫ s = s' ≫ spMap σ) (h' : ψ ≫ s' = s'' ≫ spMap τ)
    (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (τ.comp σ)) (a : HO1 s) (b : HO1 s') (c : HO1 s'') :
    IsPullO h a b → IsPullO h' b c → IsPullO h'' a c := by
  intro hab hbc
  apply triple_restriction_injective ψ φ s''
  unfold IsPullO at hab hbc
  rw [tri_pull_pull h h' h'' a, hab, tri_res_pull h' b, hbc, tri_res_res (φ := φ) c]

end Comp

theorem isPullO_wOver_comp : ∀ (R : Type) [CommRing R] (X Y Z : Over (Sp R)) (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : HO1 Z.hom) (b : HO1 Y.hom) (c : HO1 X.hom), IsPullO (wOver g) a b → IsPullO (wOver f) b c →
    IsPullO (wOver (f ≫ g)) a c := by
  intro R _ X Y Z f g a b c hab hbc
  exact isPullO_comp (wOver g) (wOver f) (wOver (f ≫ g)) a b c hab hbc

end GlobalTheory.CompanionTheory.Axis.PullO
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullOWOverCompStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullO_comp_block_decomposition : ∀ (R : Type) [CommRing R] (X Y Z : Over (Sp R)) (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : HO1 Z.hom) (b : HO1 Y.hom) (c : HO1 X.hom), IsPullO (wOver g) a b → IsPullO (wOver f) b c →
    IsPullO (wOver (f ≫ g)) a c := by
  first | exact @GlobalTheory.CompanionTheory.Axis.PullO.isPullO_wOver_comp | exact GlobalTheory.CompanionTheory.Axis.PullO.isPullO_wOver_comp | (intros; apply GlobalTheory.CompanionTheory.Axis.PullO.isPullO_wOver_comp <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingComparisonOfBase
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingComparisonOfBase
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

noncomputable section

namespace GlobalTheory.CompanionTheory.BaseAcris

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

def invS (h : IsBase l A) : A.A →+* Ob l := (RingEquiv.ofBijective A.s h).symm.toRingHom

theorem invS_comp (h : IsBase l A) : (invS A h).comp A.s = RingHom.id _ :=
  RingHom.ext fun x => (RingEquiv.ofBijective A.s h).symm_apply_apply x

theorem comp_invS (h : IsBase l A) : A.s.comp (invS A h) = RingHom.id _ :=
  RingHom.ext fun x => (RingEquiv.ofBijective A.s h).apply_symm_apply x

theorem map_xi_invS (h : IsBase l A) : WittVector.map (invS A h) A.xi = xi0 l := by
  rw [xi, sW, ← wmap_comp, invS_comp, wmap_id]

theorem awayW_left (h : IsBase l A) (y : WL l (Ob l)) : awayW (invS A h) (awayW A.s y) = y := by
  rw [← RingHom.comp_apply, ← awayW_comp, invS_comp, awayW_id]; rfl

theorem awayW_right (h : IsBase l A) (y : WL l A.A) : awayW A.s (awayW (invS A h) y) = y := by
  rw [← RingHom.comp_apply, ← awayW_comp, comp_invS, awayW_id]; rfl

theorem awayW_inv_mem (h : IsBase l A) {y : WL l A.A} (hy : y ∈ A.Acr0) :
    awayW (invS A h) y ∈ ACris.ACrisZero ℂ_[l] l := by
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    have e := awayW_dpw (invS A h) k (A.isUnit_natCast k.factorial_ne_zero) A.xi
    rw [map_xi_invS] at e
    exact Set.mem_of_eq_of_mem e (ACris.dpow_mem xi0_mem k)
  | algebraMap x => rw [awayW_algebraMap]; exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem acrisZero_bijective_of_isBase (h : IsBase l A) : Function.Bijective A.cris0 := by
  constructor
  · intro x y hxy
    have e : awayW A.s x.1 = awayW A.s y.1 := congrArg Subtype.val hxy
    have e' := congrArg (awayW (invS A h)) e
    rw [awayW_left, awayW_left] at e'
    exact Subtype.ext e'
  · intro y
    exact ⟨⟨awayW (invS A h) y.1, awayW_inv_mem A h y.2⟩, Subtype.ext (awayW_right A h y.1)⟩

theorem sW_bijective (h : IsBase l A) : Function.Bijective A.sW :=
  Function.bijective_iff_has_inverse.2 ⟨WittVector.map (invS A h),
    fun x => by
      change WittVector.map (invS A h) (WittVector.map A.s x) = x
      rw [← wmap_comp, invS_comp, wmap_id],
    fun x => by
      change WittVector.map A.s (WittVector.map (invS A h) x) = x
      rw [← wmap_comp, comp_invS, wmap_id]⟩

theorem oC_bijective (h : IsBase l A) : Function.Bijective A.oC := by
  have hs := sW_bijective A h
  have hth := IsPerfectoidField.surjective_fontaineTheta (K := ℂ_[l]) l
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨x, rfl⟩ := hth y
    rw [oC_theta0] at hy
    have hm : A.sW x ∈ Ideal.span {A.xi} := Ideal.Quotient.eq_zero_iff_mem.1 hy
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hm
    obtain ⟨c', rfl⟩ := hs.2 c
    have e : x = c' * xi0 l := hs.1 (by rw [map_mul, ← hc]; rfl)
    have : x ∈ RingHom.ker (theta0 l) := by
      rw [e]; exact Ideal.mul_mem_left _ _ xi0_mem
    exact this
  · intro u
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨x, rfl⟩ := hs.2 w
    exact ⟨theta0 l x, A.oC_theta0 x⟩

theorem mem_map_of_evalₐ_eq_zero (B : Type) [CommRing B] (π : B) (n : ℕ)
    (a : AdicCompletion (Ideal.span {π}) B) (h : AdicCompletion.evalₐ (Ideal.span {π}) n a = 0) :
    a ∈ (Ideal.span {π} ^ n).map (algebraMap B (AdicCompletion (Ideal.span {π}) B)) := by
  rw [← Submodule.restrictScalars_mem B, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _), LinearMap.mem_ker,
    ← AdicCompletion.factor_evalₐ_eq_eval _ a (by simp), h, map_zero]

theorem cris_surjective (h : IsBase l A) (n : ℕ) : Function.Surjective (A.cris n) := by
  intro u
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective u
  obtain ⟨y, rfl⟩ := (acrisZero_bijective_of_isBase A h).2 w
  exact ⟨AdicCompletion.of _ _ y, A.cris_of n y⟩

theorem cris_natCast_pow (n : ℕ) : A.cris n ((l : Acris l) ^ n) = 0 := by
  rw [map_pow, map_natCast, pow_l_acr]

theorem ker_cris (h : IsBase l A) (n : ℕ) :
    RingHom.ker (A.cris n) = Ideal.span {(l : Acris l) ^ n} := by
  apply le_antisymm
  · intro a ha
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (Ideal.span {(l : Acris0 l)}) n a)
    have e : A.cris n a = A.mkAcr n (A.cris0 y) := by
      simp only [cris, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← hy,
        Ideal.Quotient.lift_mk]
    rw [RingHom.mem_ker, e] at ha
    have hm : A.cris0 y ∈ Ideal.span {(l : A.Acr0) ^ n} := Ideal.Quotient.eq_zero_iff_mem.1 ha
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hm
    obtain ⟨c', rfl⟩ := (acrisZero_bijective_of_isBase A h).2 c
    have e2 : y = c' * (l : Acris0 l) ^ n := (acrisZero_bijective_of_isBase A h).1 (by
      rw [map_mul, map_pow, map_natCast, hc])
    have hz : Ideal.Quotient.mk (Ideal.span {(l : Acris0 l)} ^ n) y = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (by
        rw [e2, Ideal.span_singleton_pow]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
    rw [hz] at hy
    have hk : a ∈ (Ideal.span {(l : Acris0 l)} ^ n).map (algebraMap (Acris0 l) (Acris l)) := by
      exact mem_map_of_evalₐ_eq_zero _ _ n a hy.symm
    rw [ACris.map_span_p_pow, Ideal.span_singleton_pow] at hk
    exact hk
  · rw [Ideal.span_singleton_le_iff_mem]
    exact cris_natCast_pow A n

theorem main : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), IsBase l A →
    (Function.Bijective A.cris0 ∧ Function.Bijective A.oC) ∧
      ∀ n, Function.Surjective (A.cris n) ∧ RingHom.ker (A.cris n) = Ideal.span {(l : Acris l) ^ n} :=
  fun A h => ⟨⟨acrisZero_bijective_of_isBase A h, oC_bijective A h⟩, fun n => ⟨cris_surjective A h n, ker_cris A h n⟩⟩

end GlobalTheory.CompanionTheory.BaseAcris
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingComparisonOfBaseStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_ring_comparison_of_base : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), IsBase l A → (Function.Bijective A.cris0 ∧ Function.Bijective A.oC) ∧ ∀ n, Function.Surjective (A.cris n) ∧ RingHom.ker (A.cris n) = Ideal.span {(l : Acris l) ^ n} := by
  first | exact @GlobalTheory.CompanionTheory.BaseAcris.main | exact GlobalTheory.CompanionTheory.BaseAcris.main | (intros; apply GlobalTheory.CompanionTheory.BaseAcris.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationFg
open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatFG

section
variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

theorem dpE_eq (i : ℕ) : Lat.dpE f ξ l M i =
    (((i.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ i) • f ξ ^ i := by
  simp only [Lat.dpE, Lat.η, smul_pow, mul_smul]

theorem dpE_mem {k i : ℕ} (h : k ≤ i) : Lat.dpE f ξ l M i ∈ Ideal.span {f ξ ^ k} := by
  rw [dpE_eq, Ideal.mem_span_singleton']
  refine ⟨(((i.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ i) • f ξ ^ (i - k), ?_⟩
  rw [smul_mul_assoc, ← pow_add, Nat.sub_add_cancel h]

variable {f ξ} in
theorem dpE_eq_zero {m : ℕ} (hn : f ξ ^ m = 0) {i : ℕ} (h : m ≤ i) : Lat.dpE f ξ l M i = 0 := by
  rw [dpE_eq, pow_eq_zero_of_le h hn, smul_zero]

theorem mul_dpE {l : ℕ} (hl : l ≠ 0) (j : ℕ) :
    f ξ * Lat.dpE f ξ l M j = ((l ^ M * (j + 1) : ℕ) : B) * Lat.dpE f ξ l M (j + 1) := by
  have hl' : ((l : ℚ) ^ M) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl)
  have h : f ξ = ((l : ℚ) ^ M) • Lat.η f ξ l M := by
    simp only [Lat.η, smul_smul, mul_inv_cancel₀ hl', one_smul]
  have hnat : ((l ^ M * (j + 1) : ℕ) : B) = ((l : ℚ) ^ M * ((j : ℚ) + 1)) • (1 : B) := by
    rw [Algebra.smul_def, mul_one, ← map_natCast (algebraMap ℚ B)]; push_cast; rfl
  simp only [Lat.dpE]
  generalize Lat.η f ξ l M = e at h
  rw [h, hnat]
  simp only [smul_mul_assoc, mul_smul_comm, one_mul, smul_smul, pow_succ']
  congr 1
  rw [Nat.factorial_succ]
  have h1 : ((j : ℚ) + 1) ≠ 0 := by positivity
  have h2 : ((j.factorial : ℚ)) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  push_cast
  field_simp

variable {f ξ l M} in
theorem sum_single {m : ℕ} (hn : f ξ ^ m = 0) (k : ℕ) (a : W) :
    ∑ i ∈ Finset.range m, f ((Pi.single k a : ℕ → W) i) * Lat.dpE f ξ l M i = f a * Lat.dpE f ξ l M k := by
  by_cases hk : k < m
  · rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro h
      exact absurd (Finset.mem_range.2 hk) h
  · rw [dpE_eq_zero l M hn (not_lt.1 hk), mul_zero]
    refine Finset.sum_eq_zero fun i hi => ?_
    have : i ≠ k := by
      have := Finset.mem_range.1 hi
      omega
    simp [Pi.single_eq_of_ne this]

variable {f ξ l} in
theorem l_ne {m : ℕ} (h : Lat.Hyp f ξ l m) : l ≠ 0 := by
  rintro rfl
  exact h.l0 (by simp)


variable {f ξ l} in
theorem dvd_of_mem {m : ℕ} (h : Lat.Hyp f ξ l m) {j : ℕ} (hj : j < m) {a : W}
    (hmem : f a * Lat.dpE f ξ l M j ∈ Ideal.span {f ξ ^ (j + 1)}) : ξ ∣ a := by
  have hl' : ((l : ℚ) ^ M)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (l_ne h)))
  have h2 : ((j.factorial : ℚ))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast j.factorial_ne_zero)
  have hu : (((j.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ j) ≠ 0 := mul_ne_zero h2 (pow_ne_zero _ hl')
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hmem
  rw [dpE_eq] at hb
  generalize (((j.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ j) = u at hb hu
  refine h.gr j hj a (u⁻¹ • b) ?_
  rw [mul_smul_comm, mul_comm (f ξ ^ (j + 1)), hb, mul_smul_comm, smul_smul, inv_mul_cancel₀ hu, one_smul]


variable {f ξ l} in
theorem exists_coeff {m : ℕ} (h : Lat.Hyp f ξ l m) {x : B} (hx : x ∈ Lat.sub f ξ l M) {r : ℕ}
    (hr : x ∈ Ideal.span {f ξ ^ r}) (j : ℕ) (hj : j ≤ r) :
    ∃ c : ℕ → W, (∀ i < j, c i = 0) ∧ x = ∑ i ∈ Finset.range m, f (c i) * Lat.dpE f ξ l M i := by
  induction j with
  | zero =>
    obtain ⟨n, c, hc⟩ := (GlobalTheory.T.mem_lattice_sub_iff_sum f ξ l M x).1 hx
    refine ⟨fun i => if hi : i < n then c ⟨i, hi⟩ else 0, fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩
    set g : ℕ → B := fun i => f (if hi : i < n then c ⟨i, hi⟩ else 0) * Lat.dpE f ξ l M i with hg
    have h1 : x = ∑ i ∈ Finset.range n, g i := by
      rw [hc, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [hg]
    have h2 : ∑ i ∈ Finset.range n, g i = ∑ i ∈ Finset.range (max n m), g i :=
      Finset.sum_subset (Finset.range_mono (le_max_left _ _)) fun i _ hi => by
        have : ¬ i < n := by simpa using hi
        simp [hg, this]
    have h3 : ∑ i ∈ Finset.range m, g i = ∑ i ∈ Finset.range (max n m), g i :=
      Finset.sum_subset (Finset.range_mono (le_max_right _ _)) fun i _ hi => by
        have : m ≤ i := by simpa using hi
        simp [hg, dpE_eq_zero l M h.nil this]
    rw [h1, h2, ← h3]
  | succ j ih =>
    obtain ⟨c, hc, hxc⟩ := ih (by omega)
    set c' : ℕ → W := c - Pi.single j (c j) with hc'
    have hsum : ∑ i ∈ Finset.range m, f (c' i) * Lat.dpE f ξ l M i =
        x - f (c j) * Lat.dpE f ξ l M j := by
      rw [← sum_single h.nil j (c j), hxc, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hc', Pi.sub_apply, map_sub, sub_mul]
    have hz : ∀ i ≤ j, c' i = 0 := by
      intro i hi
      rcases hi.lt_or_eq with hi | rfl
      · rw [hc', Pi.sub_apply, hc i hi, Pi.single_eq_of_ne hi.ne, sub_zero]
      · rw [hc', Pi.sub_apply, Pi.single_eq_same, sub_self]
    have hrest : ∑ i ∈ Finset.range m, f (c' i) * Lat.dpE f ξ l M i ∈ Ideal.span {f ξ ^ (j + 1)} := by
      refine Ideal.sum_mem _ fun i _ => ?_
      by_cases hi : i ≤ j
      · rw [hz i hi, map_zero, zero_mul]
        exact Ideal.zero_mem _
      · exact Ideal.mul_mem_left _ _ (dpE_mem f ξ l M (by omega))
    have hx1 : x ∈ Ideal.span {f ξ ^ (j + 1)} :=
      (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ hj)) hr
    have hterm : f (c j) * Lat.dpE f ξ l M j ∈ Ideal.span {f ξ ^ (j + 1)} := by
      have := Ideal.sub_mem _ hx1 hrest
      rwa [hsum, sub_sub_cancel] at this
    obtain ⟨e, he⟩ : ∃ e : W, f (c j) * Lat.dpE f ξ l M j = f e * Lat.dpE f ξ l M (j + 1) := by
      by_cases hjm : j < m
      · obtain ⟨d, hd⟩ := dvd_of_mem M h hjm hterm
        refine ⟨d * ((l ^ M * (j + 1) : ℕ) : W), ?_⟩
        rw [hd, map_mul, map_mul, map_natCast, mul_comm (f ξ), mul_assoc, mul_dpE f ξ M (l_ne h), mul_assoc]
      · refine ⟨0, ?_⟩
        rw [dpE_eq_zero l M h.nil (not_lt.1 hjm), map_zero, zero_mul, mul_zero]
    refine ⟨c' + Pi.single (j + 1) e, fun i hi => ?_, ?_⟩
    · rw [Pi.add_apply, hz i (by omega), Pi.single_eq_of_ne (by omega), add_zero]
    · simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]
      rw [hsum, sum_single h.nil, ← he, sub_add_cancel]

end

theorem dividedPowerFiltration_fg : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ),
    Lat.Hyp f ξ l m → ∀ hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ), ∀ r : ℕ,
      (pdP (Lat.γ f ξ l M hc) r).FG := by
  intro W B _ _ _ f ξ l M m h hc r
  have key : pdP (Lat.γ f ξ l M hc) r =
      Ideal.span (Lat.dpA f ξ l M '' (↑(Finset.Ico r m) : Set ℕ)) := by
    rw [GlobalTheory.T.lattice_filtration_comap_span_pow f ξ l M m h hc r]
    apply le_antisymm
    · intro x hx
      have hxs : Lat.ι f ξ l M x ∈ Lat.sub f ξ l M := x.2
      obtain ⟨c, hc0, hxc⟩ := exists_coeff M h hxs (Ideal.mem_comap.1 hx) r le_rfl
      have hx' : x = ∑ i ∈ Finset.range m, Lat.ofW f ξ l M (c i) * Lat.dpA f ξ l M i := by
        apply Lat.ι_injective f ξ l M
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hxc, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, Lat.ι_ofW, Lat.ι_dpA]
      rw [hx']
      refine Ideal.sum_mem _ fun i hi => ?_
      by_cases hir : i < r
      · rw [hc0 i hir, map_zero, zero_mul]
        exact Ideal.zero_mem _
      · refine Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, ?_, rfl⟩)
        simp only [Finset.coe_Ico, Set.mem_Ico]
        exact ⟨not_lt.1 hir, Finset.mem_range.1 hi⟩
    · refine Ideal.span_le.2 ?_
      rintro _ ⟨i, hi, rfl⟩
      simp only [Finset.coe_Ico, Set.mem_Ico] at hi
      exact Ideal.mem_comap.2 (dpE_mem f ξ l M hi.1)
  rw [key]
  exact Submodule.fg_span ((Finset.finite_toSet _).image _)

end GlobalTheory.CompanionTheory.LatFG
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBinaryGramIntegral
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBinaryGramIntegral
open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.FibreCpt

open GlobalTheory.CompanionTheory.SW.FibreRatio

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem masses_field (R : Type) [Field R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
    [BorelSpace R] (hloc : IsLocR R) (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) (hlam : lam.IsAddHaarMeasure)
    (m : HermR R σ 1 → Measure (Fin 1 → Fin M → R ⊗[F] E))
    (hfib : IsGramFib R σ J 1 (coordW R b lam 1 M) (coordHerm R σ b lam 1) m)
    (A : Set (Fin 1 → Fin M → R ⊗[F] E)) (hAc : IsCompact A) (hAo : IsOpen A)
    (hAU : A ⊆ {X | IsUnit (gramR R σ J X).det}) :
    Continuous (fun s : R => (m (hermScal R σ s) A).toReal) ∧
    HasCompactSupport (fun s : R => (m (hermScal R σ s) A).toReal) ∧
    ENNReal.ofReal (∫ s, (m (hermScal R σ s) A).toReal ∂lam) = coordW R b lam 1 M A := by
  obtain ⟨h1, h2, h3, h4, -⟩ := id hloc
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  obtain ⟨-, -, -, hT2, -, htr, -, hBor, -, hgr⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ h R
  haveI := hT2
  haveI := hBor 1 M
  haveI : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  have hHaar := GlobalTheory.T.coordinate_haar_measure F E σ h R d b lam hlam
  have hμ := hHaar.2.1 1 M
  have hν := hHaar.2.2 1
  have hAm : MeasurableSet A := hAo.measurableSet
  set φ : (Fin 1 → Fin M → R ⊗[F] E) → ℂ := A.indicator fun _ => 1 with hφ
  have hAclopen : IsClopen A := ⟨hAc.isClosed, hAo⟩
  have hφc : Continuous φ :=
    continuous_indicator (by simp [hAclopen.frontier_eq]) continuousOn_const
  have hφs : HasCompactSupport φ :=
    HasCompactSupport.intro hAc fun x hx => Set.indicator_of_notMem hx _
  obtain ⟨⟨hg, -⟩, -⟩ := GlobalTheory.T.gram_fiber_integral_isContDensityOn F E σ h M J hJ R hloc 1 _ _ m hμ hν hfib φ hφc hφs
  have hfin : ∀ S, m S A < ⊤ := fun S => by
    haveI := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ h M J hJ R hloc 1 _ _ m hμ hν hfib S).1
    exact hAc.measure_lt_top
  have hint : ∀ S, ∫ X, φ X ∂(m S) = (((m S A).toReal : ℝ) : ℂ) := fun S => by
    rw [hφ, integral_indicator_const _ hAm]
    simp [Measure.real]
  have hcs : Continuous (hermScal R σ (F := F) (E := E)) := continuous_hermScal R

  have hqc : Continuous fun X : Fin 1 → Fin M → R ⊗[F] E =>
      algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) :=
    continuous_const.mul (htr.comp ((hgr 1 M J).matrix_elem 0 0))
  set K : Set R := (fun X : Fin 1 → Fin M → R ⊗[F] E =>
      algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0)) '' A with hKdef
  have hKc : IsCompact K := hAc.image hqc
  haveI : Nontrivial (R ⊗[F] E) := ⟨1, 0, fun e => by
    have h3 := GlobalTheory.CompanionTheory.SW.FibreRatio.half_trace_tmul (F := F) (E := E) R h (1 : R)
    rw [← Algebra.TensorProduct.one_def, e, map_zero, mul_zero] at h3
    exact zero_ne_one h3⟩
  have hK0 : (0 : R) ∉ K := by
    rintro ⟨X, hX, h0⟩
    have hu : IsUnit (gramR R σ J X).det := hAU hX
    rw [Matrix.det_fin_one, gram_entry R h hJ X] at hu
    simp only at h0
    rw [h0, TensorProduct.zero_tmul] at hu
    exact not_isUnit_zero hu
  have hzero : ∀ s, s ∉ K → m (hermScal R σ s) A = 0 := by
    intro s hs
    refine measure_mono_null ?_ (hfib.1 (hermScal R σ s))
    intro X hX hXG
    apply hs
    refine ⟨X, hX, ?_⟩
    have e : gramR R σ J X = (hermScal R σ s : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) := hXG.1
    show algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) = s
    rw [e]
    exact qS_hermScal R h s
  have hcont : Continuous (fun s : R => (m (hermScal R σ s) A).toReal) := by
    rw [continuous_iff_continuousAt]
    intro s
    by_cases hs : s = 0
    · subst hs
      have hev : (fun _ : R => (0 : ℝ)) =ᶠ[𝓝 0] fun t : R => (m (hermScal R σ t) A).toReal := by
        filter_upwards [hKc.isClosed.isOpen_compl.mem_nhds hK0] with t ht
        simp [hzero t ht]
      exact continuousAt_const.congr hev
    · have hunit : hermScal R σ s ∈
          {S : HermR R σ 1 | IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det} := by
        show IsUnit (Matrix.det _)
        rw [Matrix.det_fin_one]
        exact isUnit_tmul R hs
      have hne : ∀ᶠ t in 𝓝 s, t ≠ 0 := isOpen_ne.mem_nhds hs
      have htend : Filter.Tendsto (hermScal R σ) (𝓝 s)
          (𝓝[{S : HermR R σ 1 | IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det}]
            (hermScal R σ s)) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨hcs.tendsto s, hne.mono fun t ht => ?_⟩
        show IsUnit (Matrix.det _)
        rw [Matrix.det_fin_one]
        exact isUnit_tmul R ht
      have := (Complex.continuous_re.tendsto _).comp ((hg _ hunit).tendsto.comp htend)
      simpa [ContinuousAt, Function.comp_def, hint] using this
  have hsupp : HasCompactSupport (fun s : R => (m (hermScal R σ s) A).toReal) :=
    HasCompactSupport.intro hKc fun s hs => by simp [hzero s hs]
  refine ⟨hcont, hsupp, ?_⟩
  have hνeq : coordHerm R σ b lam 1 = Measure.map (hermScal R σ) lam := by
    ext T hT
    rw [Measure.map_apply hcs.measurable hT,
      ← coordHerm_qS R h htr b lam (hcs.measurable hT : MeasurableSet (hermScal R σ ⁻¹' T))]
    congr 1
    ext S
    simp [hermScal_qS R h S]
  have hgS : ∀ S, m S A = ENNReal.ofReal ((m (hermScal R σ (qS R σ S)) A).toReal) := fun S => by
    rw [hermScal_qS R h S, ENNReal.ofReal_toReal (hfin S).ne]
  have hgm : Measurable fun S : HermR R σ 1 => m S A := by
    have e : (fun S : HermR R σ 1 => m S A) =
        fun S => ENNReal.ofReal ((m (hermScal R σ (qS R σ S)) A).toReal) := funext hgS
    rw [e]
    exact ENNReal.measurable_ofReal.comp (hcont.comp (continuous_qS R htr)).measurable
  have hV : MeasurableSet ({0}ᶜ : Set R) := (measurableSet_singleton 0).compl
  have hP : MeasurableSet {S : HermR R σ 1 | qS R σ S ∈ ({0}ᶜ : Set R)} :=
    (continuous_qS R htr).measurable hV
  have hQ : MeasurableSet {X : Fin 1 → Fin M → R ⊗[F] E |
      algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) ∈ ({0}ᶜ : Set R)} :=
    hqc.measurable hV
  have heq := mass_eq_lintegral R h hJ hfib hAm (V := {0}ᶜ) (by simp) hQ hP
  have hAQ : A ∩ {X : Fin 1 → Fin M → R ⊗[F] E |
      algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) ∈ ({0}ᶜ : Set R)} = A := by
    refine Set.inter_eq_left.mpr fun X hX e => hK0 ⟨X, hX, e⟩
  rw [hAQ, ← lintegral_indicator hP] at heq
  have hind : {S : HermR R σ 1 | qS R σ S ∈ ({0}ᶜ : Set R)}.indicator (fun S => m S A) =
      fun S => m S A := by
    funext S
    by_cases hS : S ∈ {S : HermR R σ 1 | qS R σ S ∈ ({0}ᶜ : Set R)}
    · exact Set.indicator_of_mem hS _
    · rw [Set.indicator_of_notMem hS]
      have h0 : qS R σ S = 0 := by simpa using hS
      have e : S = hermScal R σ 0 := by rw [← h0, hermScal_qS R h S]
      rw [e, hzero 0 hK0]
  rw [hind, hνeq, lintegral_map hgm hcs.measurable] at heq
  rw [ofReal_integral_eq_lintegral_ofReal (hcont.integrable_of_hasCompactSupport hsupp)
    (ae_of_all _ fun _ => ENNReal.toReal_nonneg), heq]
  exact lintegral_congr fun s => ENNReal.ofReal_toReal (hfin _).ne

theorem fibre_masses : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (J : Matrix (Fin 2) (Fin 2) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
  (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin 2 → Fv F v ⊗[F] E)),
  IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 2) (coordHerm (Fv F v) σ b lam 1) m →
  ∀ A : Set (Fin 1 → Fin 2 → Fv F v ⊗[F] E), IsCompact A → IsOpen A → A ⊆ {X | IsUnit (gramR (Fv F v) σ J X).det} →
  Continuous (fun s : Fv F v => (m (hermScal (Fv F v) σ s) A).toReal) ∧
  HasCompactSupport (fun s : Fv F v => (m (hermScal (Fv F v) σ s) A).toReal) ∧
  ENNReal.ofReal (∫ s, (m (hermScal (Fv F v) σ s) A).toReal ∂lam) = coordW (Fv F v) b lam 1 2 A := by
  intro F E _ _ _ _ _ σ hσ J hJ d b v lam hlam m hfib A hAc hAo hAU
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  exact masses_field (Fv F v) (GlobalTheory.T.completion_is_local_ring F v) hσ hJ b lam hlam.1 m hfib A hAc hAo hAU

end GlobalTheory.CompanionTheory.SW.FibreCpt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBinaryGramIntegralStatement
open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_binary_gram_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (J : Matrix (Fin 2) (Fin 2) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
  (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin 2 → Fv F v ⊗[F] E)),
  IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 2) (coordHerm (Fv F v) σ b lam 1) m →
  ∀ A : Set (Fin 1 → Fin 2 → Fv F v ⊗[F] E), IsCompact A → IsOpen A → A ⊆ {X | IsUnit (gramR (Fv F v) σ J X).det} →
  Continuous (fun s : Fv F v => (m (hermScal (Fv F v) σ s) A).toReal) ∧
  HasCompactSupport (fun s : Fv F v => (m (hermScal (Fv F v) σ s) A).toReal) ∧
  ENNReal.ofReal (∫ s, (m (hermScal (Fv F v) σ s) A).toReal ∂lam) = coordW (Fv F v) b lam 1 2 A := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibreCpt.fibre_masses | exact GlobalTheory.CompanionTheory.SW.FibreCpt.fibre_masses | (intros; apply GlobalTheory.CompanionTheory.SW.FibreCpt.fibre_masses <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistFrobeniusFiltrationCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistFrobeniusFiltrationCompat
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.TwFil

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem dpw_mul {R : Type} [CommRing R] (k : ℕ) (c x : WittVector l R) :
    dpw k (c * x) = algebraMap _ (WL l R) c ^ k * dpw k x := by
  simp only [dpw, map_mul, mul_pow]; ring

theorem exists_gal_xi (σ : Gal(PadicAlgCl l/K)) : ∃ c : Ainf l, σ • xi0 l = c * xi0 l := by
  have h : σ • xi0 l ∈ RingHom.ker (theta0 l) := ACris.gal_smul_mem_ker σ xi0_mem
  rw [ker_theta0] at h
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
  exact ⟨c, hc.symm⟩

theorem exists_twId_xi (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) :
    ∃ c : A.W, WittVector.map (twId σ A) (tw σ A).xi = c * A.xi := by
  obtain ⟨c, hc⟩ := exists_gal_xi σ
  refine ⟨A.sW c, ?_⟩
  have e : WittVector.map (twId σ A) (tw σ A).xi = A.sW (WittVector.map (galOb σ) (xi0 l)) := by
    rw [xi, sW, sW, ← wmap_comp, galois_twist_identity_section, wmap_comp]
  have hc' : WittVector.map (galOb σ) (xi0 l) = c * xi0 l := hc
  rw [e, hc', map_mul]; rfl

def twBack (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) : A.A →+* (tw σ A).A := RingHom.id A.A

theorem exists_twBack_xi (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) :
    ∃ c : (tw σ A).W, WittVector.map (twBack σ A) A.xi = c * (tw σ A).xi := by
  obtain ⟨c, hc⟩ := exists_gal_xi σ⁻¹
  refine ⟨(tw σ A).sW c, ?_⟩
  have e : WittVector.map (twBack σ A) A.xi = (tw σ A).sW (σ⁻¹ • xi0 l) := by
    have h : WittVector.map (galOb σ) (σ⁻¹ • xi0 l) = xi0 l := smul_inv_smul σ (xi0 l)
    have e2 : (A.xi : WittVector l A.A) = (tw σ A).sW (σ⁻¹ • xi0 l) :=
      (congrArg (WittVector.map A.s) h.symm).trans (wmap_comp _ _ _).symm
    exact (wmap_id A.xi).trans e2
  rw [e, hc, map_mul]; rfl

theorem pdOk_twBack (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) : PdOk (twBack σ A) := fun k => by
  obtain ⟨c, hc⟩ := exists_twBack_xi σ A
  rw [hc, dpw_mul]
  exact mul_mem (pow_mem (Subalgebra.algebraMap_mem _ c) k) ((tw σ A).dpw_xi_mem k)

theorem acrisZero_map_dividedXi {A B : PAlg l} {f : A.A →+* B.A} (h : PdOk f) {c : B.W}
    (hc : WittVector.map f A.xi = c * B.xi) (k : ℕ) :
    h.acr0 (A.dxi0 k) = algebraMap B.W B.Acr0 c ^ k * B.dxi0 k :=
  Subtype.ext (by
    have := awayW_dpw f k (A.isUnit_natCast k.factorial_ne_zero) A.xi
    rw [hc, dpw_mul] at this
    exact this)

theorem acrisZero_map_preserves_filtration {A B : PAlg l} {f : A.A →+* B.A} (h : PdOk f) {c : B.W}
    (hc : WittVector.map f A.xi = c * B.xi) (r : ℕ) : ∀ x ∈ A.Fil0 r, h.acr0 x ∈ B.Fil0 r := by
  have h' : A.Fil0 r ≤ (B.Fil0 r).comap h.acr0 := by
    rw [Fil0, Ideal.span_le]
    rintro _ ⟨k, hk, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, acrisZero_map_dividedXi h hc]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, hk, rfl⟩)
  exact fun x hx => h' hx

theorem acr_fil_of {A B : PAlg l} {f : A.A →+* B.A} (h : PdOk f) {c : B.W}
    (hc : WittVector.map f A.xi = c * B.xi) (n r : ℕ) : ∀ x ∈ A.Fil n r, h.acr n x ∈ B.Fil n r := by
  have h' : A.Fil n r ≤ (B.Fil n r).comap (h.acr n) := by
    rw [Fil, Ideal.span_le]
    rintro _ ⟨k, hk, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap]
    change h.acr n (A.mkAcr n (A.dxi0 k)) ∈ _
    rw [PdOk.acr_mk, acrisZero_map_dividedXi h hc, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, hk, rfl⟩)
  exact fun x hx => h' hx

theorem twist_acrisZero_preserves_filtration (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (r : ℕ) :
    ∀ x ∈ (tw σ A).Fil0 r, (pdOk_twId σ A).acr0 x ∈ A.Fil0 r := by
  obtain ⟨c, hc⟩ := exists_twId_xi σ A
  exact acrisZero_map_preserves_filtration (pdOk_twId σ A) hc r

theorem twAcr_fil (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (n r : ℕ) :
    ∀ x ∈ (tw σ A).Fil n r, twAcr σ A n x ∈ A.Fil n r := by
  obtain ⟨c, hc⟩ := exists_twId_xi σ A
  exact acr_fil_of (pdOk_twId σ A) hc n r

theorem acr_eq_self {A : PAlg l} {f : A.A →+* A.A} (h : PdOk f) (hf : f = RingHom.id _) (n : ℕ) (x : A.Acr n) :
    h.acr n x = x := by
  subst hf; exact PdOk.acr_id h n x

theorem pdOk_self (A : PAlg l) : PdOk (RingHom.id A.A) := fun k => by
  rw [wmap_id]; exact A.dpw_xi_mem k

theorem twAcr_bijective (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (n : ℕ) : Function.Bijective (twAcr σ A n) := by
  have e1 : (twBack σ A).comp (twId σ A) = RingHom.id (tw σ A).A := RingHom.ext fun _ => rfl
  have e2 : (twId σ A).comp (twBack σ A) = RingHom.id A.A := RingHom.ext fun _ => rfl
  have h1 : PdOk ((twBack σ A).comp (twId σ A)) := e1 ▸ pdOk_self (tw σ A)
  have h2 : PdOk ((twId σ A).comp (twBack σ A)) := e2 ▸ pdOk_self A
  refine Function.bijective_iff_has_inverse.2 ⟨(pdOk_twBack σ A).acr n, fun x => ?_, fun x => ?_⟩
  · exact (PdOk.acr_comp (pdOk_twId σ A) (pdOk_twBack σ A) h1 n x).symm.trans (acr_eq_self h1 e1 n x)
  · exact (PdOk.acr_comp (pdOk_twBack σ A) (pdOk_twId σ A) h2 n x).symm.trans (acr_eq_self h2 e2 n x)

theorem twAcr_phi (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (n : ℕ) (x : (tw σ A).Acr n) :
    twAcr σ A n ((tw σ A).phi n x) = A.phi n (twAcr σ A n x) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine congrArg (A.mkAcr n) (Subtype.ext ?_)
  change awayW (twId σ A) (awayW (tw σ A).frob y.1) = awayW A.frob (awayW (twId σ A) y.1)
  rw [← RingHom.comp_apply, ← awayW_comp, ← RingHom.comp_apply, ← awayW_comp]
  rfl

theorem exists_phiW (A : PAlg l) (x : A.W) : ∃ y : A.W, A.phiW x = x ^ l + (l : A.W) * y := by
  have h : A.phiW x - x ^ l ∈ Ideal.span {(l : A.W)} := by
    rw [mem_span_l_iff, ← WittVector.constantCoeff_apply, map_sub, map_pow, WittVector.constantCoeff_apply,
      WittVector.constantCoeff_apply, phiW, WittVector.map_coeff, sub_eq_zero]
    rfl
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h
  exact ⟨y, by rw [mul_comm, hy]; ring⟩

theorem factorial_mul_divided_power_xi (A : PAlg l) (k : ℕ) :
    (k.factorial : A.Acr0) * A.dxi0 k = algebraMap A.W A.Acr0 A.xi ^ k := Subtype.ext (by
  change (k.factorial : WL l A.A) * dpw k A.xi = algebraMap _ (WL l A.A) A.xi ^ k
  rw [dpw, ← mul_assoc, Ring.mul_inverse_cancel _ (A.isUnit_natCast k.factorial_ne_zero), one_mul])

theorem natCast_cancel (A : PAlg l) {k : ℕ} (hk : k ≠ 0) {a b : A.Acr0}
    (h : (k : A.Acr0) * a = (k : A.Acr0) * b) : a = b :=
  Subtype.ext ((A.isUnit_natCast hk).mul_left_cancel (congrArg Subtype.val h))

theorem acrisZero_map_algebraMap {A B : PAlg l} {f : A.A →+* B.A} (h : PdOk f) (x : A.W) :
    h.acr0 (algebraMap A.W A.Acr0 x) = algebraMap B.W B.Acr0 (WittVector.map f x) :=
  Subtype.ext (awayW_algebraMap f x)

theorem exists_phi_xi (A : PAlg l) :
    ∃ v : A.Acr0, A.pdOk_frob.acr0 (algebraMap A.W A.Acr0 A.xi) = (l : A.Acr0) * v := by
  obtain ⟨y, hy⟩ := exists_phiW A A.xi
  refine ⟨((l - 1).factorial : A.Acr0) * A.dxi0 l + algebraMap A.W A.Acr0 y, ?_⟩
  rw [acrisZero_map_algebraMap]
  change algebraMap A.W A.Acr0 (A.phiW A.xi) = _
  rw [hy, map_add (f := _), map_pow, ← factorial_mul_divided_power_xi, map_mul, map_natCast, mul_add, ← mul_assoc, ← Nat.cast_mul,
    Nat.mul_factorial_pred (Fact.out : l.Prime).ne_zero]

theorem factorization_factorial_le (k : ℕ) (hk : 1 ≤ k) : (k.factorial).factorization l ≤ k - 1 := by
  have hp : l.Prime := Fact.out
  rw [Nat.factorization_def _ hp]
  have h : (l - 1) * multiplicity l k.factorial < k := sub_one_mul_multiplicity_factorial_lt_of_ne_zero l (n := k) (by omega)
  have h1 : 1 ≤ l - 1 := Nat.le_sub_of_add_le hp.two_le
  have h2 : multiplicity l k.factorial ≤ (l - 1) * multiplicity l k.factorial := Nat.le_mul_of_pos_left _ h1
  omega

theorem exists_factorial_mul (A : PAlg l) (k : ℕ) (hk : 1 ≤ k) :
    ∃ w : A.W, (k.factorial : A.W) * w = (l : A.W) ^ (k - 1) := by
  obtain ⟨c, hc⟩ := ACris.exists_natCast_mul_eq_pow (K := ℂ_[l]) (p := l) (Nat.factorial_ne_zero k)
    (factorization_factorial_le k hk)
  refine ⟨A.sW c, ?_⟩
  rw [← map_natCast A.sW, ← map_mul, hc, map_pow, map_natCast]

theorem frobenius_dividedXi_mem_span_prime (A : PAlg l) (k : ℕ) (hk : 1 ≤ k) :
    A.pdOk_frob.acr0 (A.dxi0 k) ∈ Ideal.span {(l : A.Acr0)} := by
  obtain ⟨v, hv⟩ := exists_phi_xi A
  obtain ⟨w, hw⟩ := exists_factorial_mul A k hk
  refine Ideal.mem_span_singleton'.2 ⟨algebraMap A.W A.Acr0 w * v ^ k, ?_⟩
  apply natCast_cancel A k.factorial_ne_zero
  have h1 : (k.factorial : A.Acr0) * A.pdOk_frob.acr0 (A.dxi0 k) = ((l : A.Acr0) * v) ^ k := by
    rw [← hv, ← map_pow, ← factorial_mul_divided_power_xi, map_mul, map_natCast]
  have h2 : (k.factorial : A.Acr0) * algebraMap A.W A.Acr0 w = (l : A.Acr0) ^ (k - 1) := by
    rw [← map_natCast (algebraMap A.W A.Acr0), ← map_mul, hw, map_pow, map_natCast]
  rw [h1]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h2
  linear_combination (v ^ (m + 1) * (l : A.Acr0)) * h2

theorem frob_pfil0 (A : PAlg l) : ∀ x ∈ A.PFil0, A.pdOk_frob.acr0 x ∈ Ideal.span {(l : A.Acr0)} := by
  have h : A.PFil0 ≤ (Ideal.span {(l : A.Acr0)}).comap A.pdOk_frob.acr0 := by
    refine sup_le ?_ ?_
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
      exact Ideal.mem_span_singleton_self _
    · rw [Fil0, Ideal.span_le]
      rintro _ ⟨k, hk, rfl⟩
      exact frobenius_dividedXi_mem_span_prime A k hk
  exact fun x hx => h hx

theorem tw_fil : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : Gal(PadicAlgCl l/K)), (∀ x ∈ (tw σ A).Fil0 1, (pdOk_twId σ A).acr0 x ∈ A.Fil0 1) ∧
    (∀ x ∈ A.PFil0, A.pdOk_frob.acr0 x ∈ Ideal.span {(l : A.Acr0)}) ∧
    (∀ n r, ∀ x ∈ (tw σ A).Fil n r, twAcr σ A n x ∈ A.Fil n r) ∧
    (∀ n, Function.Bijective (twAcr σ A n)) ∧
    ∀ n x, twAcr σ A n ((tw σ A).phi n x) = A.phi n (twAcr σ A n x) :=
  fun A _ σ => ⟨twist_acrisZero_preserves_filtration σ A 1, frob_pfil0 A, twAcr_fil σ A, twAcr_bijective σ A, twAcr_phi σ A⟩

end GlobalTheory.CompanionTheory.TwFil
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistFrobeniusFiltrationCompatStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_frobenius_filtration_compat : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (σ : Gal(PadicAlgCl l/K)), (∀ x ∈ (tw σ A).Fil0 1, (pdOk_twId σ A).acr0 x ∈ A.Fil0 1) ∧ (∀ x ∈ A.PFil0, A.pdOk_frob.acr0 x ∈ Ideal.span {(l : A.Acr0)}) ∧ (∀ n r, ∀ x ∈ (tw σ A).Fil n r, twAcr σ A n x ∈ A.Fil n r) ∧ (∀ n, Function.Bijective (twAcr σ A n)) ∧ ∀ n x, twAcr σ A n ((tw σ A).phi n x) = A.phi n (twAcr σ A n x) := by
  first | exact @GlobalTheory.CompanionTheory.TwFil.tw_fil | exact GlobalTheory.CompanionTheory.TwFil.tw_fil | (intros; apply GlobalTheory.CompanionTheory.TwFil.tw_fil <;> assumption)
end
end
