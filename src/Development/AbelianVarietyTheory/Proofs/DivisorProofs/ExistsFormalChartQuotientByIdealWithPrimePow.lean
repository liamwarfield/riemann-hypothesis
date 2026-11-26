module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstOfPolConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTransportMumfordBundleIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetSmulDirection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleExtensionGenericFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeFrobeniusKernelIdealLeFrobeniusKernelIde
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalRigidifiedExtensionOfDeRhamClassUnique

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalChartQuotientByIdealWithPrimePow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomEvalCompEqEvAMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomEvalCompEqEvAMap
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem algHom_eval_comp_eq_evA_map :
    ∀ (p m : ℕ) (O A k A' σ : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing k]
      [CommRing A'] [Algebra k A'] [Fintype σ] (x : σ → A) (E : MvPowerSeries σ O →ₐ[O] A),
      IsEval p x E → ∀ (r : O →+* k) (g : A →+* A'),
      (∀ c, g (algebraMap O A c) = algebraMap k A' (r c)) → (p : A') ^ m = 0 →
      ∀ hx : ∀ i, IsNilpotent (g (x i)), ∀ f,
        g (E f) = evA k (fun i => g (x i)) hx (map r f) := by
  intro p m O A k A' σ _ _ _ _ _ _ _ x E hE r g hg _ hx f
  letI : Algebra O A' := ((algebraMap k A').comp r).toAlgebra
  have hs : HasSubst (fun i => (C (g (x i)) : MvPowerSeries Empty A')) :=
    hasSubst_of_constantCoeff_nilpotent fun i => by simpa using hx i
  have hevX : ∀ i, evA k (fun i => g (x i)) hx (X i) = g (x i) := by
    intro i
    simp [evA, coe_substAlgHom, subst_X hs]
  let φ : MvPowerSeries σ O →ₐ[O] A' :=
    { g.comp E.toRingHom with
      commutes' := fun c => by
        show g (E (algebraMap O _ c)) = (algebraMap k A').comp r c
        rw [AlgHom.commutes, hg]; rfl }
  let ψ : MvPowerSeries σ O →ₐ[O] A' :=
    { (evA k (fun i => g (x i)) hx).toRingHom.comp (map r) with
      commutes' := fun c => by
        show evA k (fun i => g (x i)) hx (map r (algebraMap O _ c)) = (algebraMap k A').comp r c
        have hm : map r (algebraMap O (MvPowerSeries σ O) c) =
            algebraMap k (MvPowerSeries σ k) (r c) := by
          simp [MvPowerSeries.algebraMap_apply, map_C]
        rw [hm, AlgHom.commutes]; rfl }
  have hφX : ∀ i, φ (X i) = g (x i) := fun i => by
    show g (E (X i)) = _
    rw [hE.1 i]
  have hψX : ∀ i, ψ (X i) = g (x i) := fun i => by
    show evA k (fun i => g (x i)) hx (map r (X i)) = _
    rw [map_X, hevX]
  have key := GlobalTheory.mvPowerSeries_algHom_ext_of_isNilpotent O σ A' φ ψ
    (fun i => by rw [hφX]; exact hx i) (fun i => by rw [hφX, hψX])
  exact DFunLike.congr_fun key f

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomEvalCompEqEvAMapStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_eval_eq_evA_map_of_isEval_of_pow_eq_zero : ∀ (p m : ℕ) (O A k A' σ : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing k] [CommRing A'] [Algebra k A'] [Fintype σ] (x : σ → A) (E : MvPowerSeries σ O →ₐ[O] A), IsEval p x E → ∀ (r : O →+* k) (g : A →+* A'), (∀ c, g (algebraMap O A c) = algebraMap k A' (r c)) → (p : A') ^ m = 0 → ∀ hx : ∀ i, IsNilpotent (g (x i)), ∀ f, g (E f) = evA k (fun i => g (x i)) hx (map r f) := by
  first | exact @GlobalTheory.algHom_eval_comp_eq_evA_map | exact GlobalTheory.algHom_eval_comp_eq_evA_map | (intros; apply GlobalTheory.algHom_eval_comp_eq_evA_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartPresentsLevelsModIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartPresentsLevelsModIdeal
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.Chart

theorem coeff_mem_of_mem_smul_top {O σ : Type} [CommRing O] (I : Ideal O)
    {h : MvPowerSeries σ O} (hh : h ∈ I • (⊤ : Submodule O (MvPowerSeries σ O))) (α : σ →₀ ℕ) :
    coeff α h ∈ I := by
  refine Submodule.smul_induction_on hh (fun a ha x _ => ?_) (fun x y hx hy => ?_)
  · rw [MvPowerSeries.coeff_smul]
    exact I.mul_mem_right _ ha
  · rw [map_add (f := _)]
    exact I.add_mem hx hy

theorem presents_quotient :
    ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ)
      (c : QLog.Chart G d), ∀ (I : Ideal O) (m : ℕ), (p : O) ^ m ∈ I →
      ∃ hx : ∀ n i, IsNilpotent ((1 : O ⧸ I) ⊗ₜ[O] c.x n i),
        (∀ n f, evA (O ⧸ I) (fun i => (1 : O ⧸ I) ⊗ₜ[O] c.x n i) (hx n)
          (map (Ideal.Quotient.mk I) f) = 1 ⊗ₜ[O] c.ev n f) ∧
        Presents (O ⧸ I) (B := fun n => (O ⧸ I) ⊗[O] G.A n) (fun n i => 1 ⊗ₜ[O] c.x n i) hx := by
  intro p _ O _ G d c I m hm
  have hp : ∀ n, ((p : (O ⧸ I) ⊗[O] G.A n)) ^ m = 0 := fun n => by
    have h0 : ((p : O ⧸ I)) ^ m = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk I), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact hm
    rw [← map_natCast (algebraMap (O ⧸ I) ((O ⧸ I) ⊗[O] G.A n)), ← map_pow, h0, map_zero]
  have hx : ∀ n i, IsNilpotent ((1 : O ⧸ I) ⊗ₜ[O] c.x n i) := fun n i => by
    obtain ⟨N, y, hy⟩ := c.nil n i
    refine ⟨N * m, ?_⟩
    have : (1 : O ⧸ I) ⊗ₜ[O] c.x n i = Algebra.TensorProduct.includeRight (R := O) (A := O ⧸ I)
      (c.x n i) := rfl
    rw [this, ← map_pow, pow_mul, hy, mul_pow, map_mul, map_pow, map_natCast, hp, zero_mul]
  have hev : ∀ n f, evA (O ⧸ I) (fun i => (1 : O ⧸ I) ⊗ₜ[O] c.x n i) (hx n)
      (map (Ideal.Quotient.mk I) f) = 1 ⊗ₜ[O] c.ev n f := fun n f =>
    (GlobalTheory.algHom_eval_comp_eq_evA_map p m O (G.A n) (O ⧸ I) ((O ⧸ I) ⊗[O] G.A n) (Fin d) (c.x n) (c.ev n) (c.isEval n)
      (Ideal.Quotient.mk I)
      (Algebra.TensorProduct.includeRight (R := O) (A := O ⧸ I)).toRingHom
      (fun a => by
        change Algebra.TensorProduct.includeRight (R := O) (A := O ⧸ I) (algebraMap O (G.A n) a) = _
        rw [AlgHom.commutes]
        exact IsScalarTower.algebraMap_apply O (O ⧸ I) ((O ⧸ I) ⊗[O] G.A n) a)
      (hp n) (hx n) f).symm
  refine ⟨hx, hev, fun n y => ?_, fun N => ?_⟩
  · obtain ⟨b, rfl⟩ := (GlobalTheory.PDiv.one_tmul_quot_reduction O (G.A n) I).1 y
    obtain ⟨f, rfl⟩ := c.surj n b
    exact ⟨_, hev n f⟩
  · obtain ⟨n, hn⟩ := c.ker m N
    refine ⟨n, fun g hg α hα => ?_⟩
    obtain ⟨f, rfl, -⟩ := (GlobalTheory.mvPowerSeries_lift_quotient O (Fin d) I).1 g
    rw [hev] at hg
    have h1 : c.ev n f ∈ I • (⊤ : Submodule O (G.A n)) := ((GlobalTheory.PDiv.one_tmul_quot_reduction O (G.A n) I).2.1 _).1 hg
    have h2 : c.ev n f ∈ (I • (⊤ : Submodule O (MvPowerSeries (Fin d) O))).map
        (c.ev n).toLinearMap := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 (c.surj n)]
      exact h1
    obtain ⟨h, hh, he⟩ := h2
    have h3 : c.ev n (f - h) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact he.symm
    have h4 : coeff α (f - h) ∈ I := by
      obtain ⟨z, hz⟩ := hn (f - h) h3 α hα
      rw [hz]
      exact I.mul_mem_right _ hm
    have h5 : coeff α f ∈ I := by
      have := I.add_mem h4 (coeff_mem_of_mem_smul_top I hh α)
      rwa [map_sub, sub_add_cancel] at this
    rw [coeff_map, Ideal.Quotient.eq_zero_iff_mem]
    exact h5

end GlobalTheory.QLog.Chart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartPresentsLevelsModIdealStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalChart_presents_levels_mod_ideal : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (I : Ideal O) (m : ℕ), (p : O) ^ m ∈ I → ∃ hx : ∀ n i, IsNilpotent ((1 : O ⧸ I) ⊗ₜ[O] c.x n i), (∀ n f, evA (O ⧸ I) (fun i => (1 : O ⧸ I) ⊗ₜ[O] c.x n i) (hx n) (map (Ideal.Quotient.mk I) f) = 1 ⊗ₜ[O] c.ev n f) ∧ Presents (O ⧸ I) (B := fun n => (O ⧸ I) ⊗[O] G.A n) (fun n i => 1 ⊗ₜ[O] c.x n i) hx := by
  first | exact @GlobalTheory.QLog.Chart.presents_quotient | exact GlobalTheory.QLog.Chart.presents_quotient | (intros; apply GlobalTheory.QLog.Chart.presents_quotient <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalChartQuotientByIdealWithPrimePow
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog.ChartRed

def twoRing {R R' A A' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} [CommRing A]
    [Bialgebra R A] [CommRing A'] [Bialgebra R' A'] (f : SemiBialgHom σ A A') :
    A ⊗[R] A →+* A' ⊗[R'] A' where
  toFun := f.two
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    simp only [Algebra.TensorProduct.one_def, TensorProduct.map_tmul, SemiBialgHom.lin_apply,
      map_one f.toRingHom]
  map_mul' x y := by
    induction x with
    | add a b ha hb => simp only [add_mul, map_add (f := _), ha, hb]
    | tmul a b =>
      induction y with
      | add u v hu hv => simp only [mul_add, map_add (f := _), hu, hv]
      | tmul u v => simp [SemiBialgHom.lin_apply, map_mul f.toRingHom]

theorem ev₂_map {p m d : ℕ} {O k : Type} [CommRing O] [CommRing k] {r : O →+* k}
    {G : PDivGroup p O} {G' : PDivGroup p k} (s : SemiHom r G' G) (c : QLog.Chart G d)
    (c' : Katz.Chart G' d) (hc : ∀ n i, c'.x n i = s.app n (c.x n i)) (hp : (p : k) ^ m = 0)
    (n : ℕ) (f : MvPowerSeries (Fin d ⊕ Fin d) O) :
    c'.ev₂ n (map r f) = (s.app n).two (c.ev₂ n f) := by
  have e : (fun i => twoRing (s.app n)
      (Sum.elim (fun i => c.x n i ⊗ₜ[O] 1) (fun i => 1 ⊗ₜ[O] c.x n i) i)) = c'.x₂ n := by
    funext i
    cases i with
    | inl i =>
      change (s.app n) (c.x n i) ⊗ₜ[k] (s.app n) 1 = c'.x n i ⊗ₜ[k] 1
      rw [map_one, hc]
    | inr i =>
      change (s.app n) 1 ⊗ₜ[k] (s.app n) (c.x n i) = 1 ⊗ₜ[k] c'.x n i
      rw [map_one, hc]
  have h := T.map_eval_eq_evA_map_of_isEval_of_pow_eq_zero p m O _ k (G'.A n ⊗[k] G'.A n) _ _ _ (c.isEval₂ n) r (twoRing (s.app n))
    (fun a => by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        ← map_one (twoRing (s.app n))]
      exact map_smulₛₗ (s.app n).two a 1)
    (by rw [← map_natCast (algebraMap k _), ← map_pow, hp, map_zero])
    (fun i => (congrFun e i).symm ▸ c'.nil₂ n i) f
  refine Eq.trans ?_ h.symm
  unfold Katz.Chart.ev₂
  congr 2
  exact e.symm

theorem exists_chart : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (I : Ideal O) (m : ℕ), (p : O) ^ m ∈ I → ∃ c' : Katz.Chart (G.baseChange (O ⧸ I)) d, c'.IsLawOf (fun i => map (Ideal.Quotient.mk I) (c.μ i)) ∧ (∀ n f, c'.ev n (map (Ideal.Quotient.mk I) f) = (G.toBase (O ⧸ I)).app n (c.ev n f)) ∧ ∀ n s, c'.ev₂ n (map (Ideal.Quotient.mk I) s) = ((G.toBase (O ⧸ I)).app n).two (c.ev₂ n s) := by
  intro p _ O _ G d c I m hm
  obtain ⟨hx, h1, h2⟩ := T.formalChart_presents_levels_mod_ideal p O G d c I m hm
  have hp : (p : O ⧸ I) ^ m = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), ← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hm
  let c' : Katz.Chart (G.baseChange (O ⧸ I)) d :=
    { x := fun n i => (G.toBase (O ⧸ I)).app n (c.x n i)
      nil := hx
      res := fun n i => ((G.toBase (O ⧸ I)).res_app n _).trans (congrArg _ (c.res n i))
      aug := fun n i => by rw [((G.toBase (O ⧸ I)).app n).counit_map, c.aug, map_zero]
      presents := h2 }
  have h3 := ev₂_map (G.toBase (O ⧸ I)) c c' (fun _ _ => rfl) hp
  refine ⟨c', fun n i => ?_, h1, h3⟩
  exact (h3 n (c.μ i)).trans ((congrArg _ (c.comul n i)).trans
    (((G.toBase (O ⧸ I)).app n).two_comul _))

end GlobalTheory.QLog.ChartRed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalChartQuotientByIdealWithPrimePowStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_formalChart_quotient_by_ideal_with_primePow : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (I : Ideal O) (m : ℕ), (p : O) ^ m ∈ I → ∃ c' : Katz.Chart (G.baseChange (O ⧸ I)) d, c'.IsLawOf (fun i => map (Ideal.Quotient.mk I) (c.μ i)) ∧ (∀ n f, c'.ev n (map (Ideal.Quotient.mk I) f) = (G.toBase (O ⧸ I)).app n (c.ev n f)) ∧ ∀ n s, c'.ev₂ n (map (Ideal.Quotient.mk I) s) = ((G.toBase (O ⧸ I)).app n).two (c.ev₂ n s) := by
  first | exact @GlobalTheory.QLog.ChartRed.exists_chart | exact GlobalTheory.QLog.ChartRed.exists_chart | (intros; apply GlobalTheory.QLog.ChartRed.exists_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsPrimitiveAtUniformisedTrait
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedGenericFibreUniformisedTrait
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedGenericFibreUniformisedTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.UMin.UnifPolFib

theorem polFib_of_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (χ : Sp V ⟶ S) (t' : SAB H (Sp V)), Nonempty (SABMap t' t χ) → Nonempty (PELUnif (IsLocalRing.maximalIdeal V) t') → ∃ g : ℕ, ∀ (R : Type) [CommRing R] (e : FractionRing V →+* R), PolFib t.G t.PP.L g (spMap e ≫ jK V ≫ χ) := by
  intro E _ _ _ H S t V _ _ _ _ χ t' ⟨hm⟩ ⟨P⟩
  refine ⟨P.A.g, fun R _ e => ?_⟩
  have hL : t.PP.L.IsLB := RigLB.isLB _
  have hL' : t'.PP.L.IsLB := RigLB.isLB _
  have hF : LBIso t'.PP.L (t.PP.L.pull hm.cm.F) := by
    obtain ⟨w, hw, -, -⟩ := hm.lin
    exact ⟨w, hw⟩
  have hα : IsGrpPullback P.A.A t'.G (jK V) (P.U.gen.inv.left ≫ pullback.fst t'.G.hom (jK V)) :=
    GlobalTheory.NeutralLevel.isGrpPullback_of_iso_inv (jK V) t'.G P.U.gen P.U.gen_hom
  have hLα : LBIso P.A.L (t'.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t'.G.hom (jK V))) := by
    obtain ⟨w, hw⟩ := P.U.ext
    have hA := P.A.isLB
    have hB : LBIso P.A.L ((P.A.L.pull P.U.gen.hom.left).pull P.U.gen.inv.left) := by
      have e : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
        rw [← Over.comp_left, P.U.gen.inv_hom_id, Over.id_left]
      have h1 := GlobalTheory.UMin.FibMove.lbIso_pull_comp hA P.U.gen.hom.left P.U.gen.inv.left
      rw [e] at h1
      exact LBIso.trans hA (pull_isLB hA _) (pull_isLB (pull_isLB hA _) _)
        (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hA) h1
    have hLG : P.U.LG.L.IsLB := RigLB.isLB _
    have h2 := GlobalTheory.ThetaAffineGlue.lbIso_comp hA (pull_isLB hA _) hLG hB ⟨w, hw⟩
    rw [P.bundle] at h2
    exact h2
  have h0 : PolFib t'.G t'.PP.L P.A.g (jK V) := ⟨P.A, _, rfl, hα, hLα⟩
  have h1 := (GlobalTheory.UMin.FibMove.polFib_move S (Sp V) t.G t.PP.L t'.G t'.PP.L χ hm.cm.F hL hL' hm.cart hF P.A.g
    (FractionRing V) (jK V)).2 R e h0
  have h2 := (GlobalTheory.UMin.FibMove.polFib_move S (Sp V) t.G t.PP.L t'.G t'.PP.L χ hm.cm.F hL hL' hm.cart hF P.A.g
    R (spMap e ≫ jK V)).1.mp h1
  rwa [Category.assoc] at h2

end GlobalTheory.UMin.UnifPolFib
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedGenericFibreUniformisedTraitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principallyPolarised_genericFibre_uniformised_trait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (χ : Sp V ⟶ S) (t' : SAB H (Sp V)), Nonempty (SABMap t' t χ) → Nonempty (PELUnif (IsLocalRing.maximalIdeal V) t') → ∃ g : ℕ, ∀ (R : Type) [CommRing R] (e : FractionRing V →+* R), PolFib t.G t.PP.L g (spMap e ≫ jK V ≫ χ) := by
  first | exact @GlobalTheory.UMin.UnifPolFib.polFib_of_unif | exact GlobalTheory.UMin.UnifPolFib.polFib_of_unif | (intros; apply GlobalTheory.UMin.UnifPolFib.polFib_of_unif <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsPrimitiveAtUniformisedTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.PrimTrait

theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp [spMap, ← Spec.map_comp]

theorem spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 _ := by
  simp [spMap]

section
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left}

theorem heq_pullS {R : Type} [CommRing R] {x₁ x₂ : Sp R ⟶ S} (h : x₁ = x₂) {T : Over S}
    (f₁ : Over.mk x₁ ⟶ T) (f₂ : Over.mk x₂ ⟶ T) (hf : f₁.left = f₂.left)
    (s : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T)) :
    HEq (VVRank.pullS G _ f₁ s) (VVRank.pullS G _ f₂ s) := by
  subst h
  obtain rfl : f₁ = f₂ := Over.OverMorphism.ext hf
  rfl

theorem thList_of_eq (ρ : LB.Gen (L.pull (eSec G))) (m : ℕ) {K : Type} [Field K] {x₁ x₂ : Sp K ⟶ S}
    (h : x₁ = x₂) {θ₁ : SecAt G L x₁} {θ₂ : SecAt G L x₂} (hθ : HEq θ₁ θ₂) {N : ℕ}
    {pt : Fin N → (Over.mk x₁ ⟶ G)} {c : Fin N → K} (H : ThList G L ρ m x₁ θ₁ pt c) :
    ∃ pt₂ : Fin N → (Over.mk x₂ ⟶ G), (∀ a, (pt₂ a).left = (pt a).left) ∧ ThList G L ρ m x₂ θ₂ pt₂ c := by
  subst h
  cases hθ
  exact ⟨pt, fun _ => rfl, H⟩

theorem pt_of_eq {R : Type} [CommRing R] {x₁ x₂ : Sp R ⟶ S} (h : x₁ = x₂) (p : Over.mk x₁ ⟶ G) :
    ∃ p₂ : Over.mk x₂ ⟶ G, p₂.left = p.left ∧ ∀ n : ℕ, p ^ n = 1 → p₂ ^ n = 1 := by
  subst h
  exact ⟨p, rfl, fun _ h => h⟩

theorem thG_unique [IsCommMonObj G] (ρ : LB.Gen (L.pull (eSec G))) (hL : L.IsLB) (hρ : ρ.IsGen) {g m : ℕ}
    {K : Type} [Field K] {x : Sp K ⟶ S} (θ : SecAt G L x) (p : Over.mk x ⟶ G) {c c' : K} (hm : Odd m)
    (hm0 : (m : K) ≠ 0) (hP : PolFib G L g x) (h₁ : ThG G L ρ m θ p (GlobalTheory.ZH.fn c))
    (h₂ : ThG G L ρ m θ p (GlobalTheory.ZH.fn c')) : c' = c := by
  have := (GlobalTheory.T.thetaConstant_unique_and_linear_in_section S G L ρ hL hρ g m K x θ θ p 1 c c' hm hm0 hP (by simp) h₁).1 h₂
  simpa using this
end

theorem isIntegralElem_of_sq {V F K Kb : Type} [CommRing V] [Field F] [Field K] [Field Kb] (φ : V →+* F) (i : V →+* K)
    (i' : K →+* Kb) (j : F →+* Kb) (hsq : i'.comp i = j.comp φ) {z : F} {w : K} (h : j z = i' w)
    (hz : φ.IsIntegralElem z) : i.IsIntegralElem w := by
  obtain ⟨p, hp, hp0⟩ := hz
  refine ⟨p, hp, i'.injective ?_⟩
  rw [Polynomial.hom_eval₂, ← h, hsq, ← Polynomial.hom_eval₂, hp0, map_zero, map_zero]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (χ : Sp V ⟶ S) (t' : SAB H (Sp V)), Nonempty (SABMap t' t χ) → Nonempty (PELUnif (IsLocalRing.maximalIdeal V) t') → ∀ (σ : SecAt t.G t.PP.L χ), NZ t.G t.PP.L χ σ → ∀ (m N : ℕ), Odd m → 3 ≤ m → IsUnit (m : V) → ∀ (K : Type) [Field K] (i : V →+* K) (pt : Fin N → (Over.mk (spMap i ≫ χ) ⟶ t.G)) (c : Fin N → K), Function.Injective i → ThList t.G t.PP.L t.PP.rig m (spMap i ≫ χ) (SecAt.pull t.G t.PP.L σ i) pt c → Prim i c := by
  intro E _ _ _ H S t V _ _ _ hV χ t' ⟨hm⟩ ⟨P⟩ σ hσ m N hodd h3 hmu K _ i pt c hi hL
  haveI : IsDiscreteValuationRing V := hV.1
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let F := AlgebraicClosure (FractionRing V)
  obtain ⟨v, hv⟩ := ReciprocityTheory.ChartRestriction.G.DVR.exists_valOver hϖ F
  obtain ⟨g, hg⟩ := GlobalTheory.T.principallyPolarised_genericFibre_uniformised_trait E H S t V hV χ t' ⟨hm⟩ ⟨P⟩
  set x' : Sp F ⟶ S := (jFK (R := V) F ≫ jK V) ≫ χ with hx'
  set θF : SecAt t.G t.PP.L x' :=
    VVRank.pullS t.G _ (Over.homMk (jFK (R := V) F ≫ jK V) rfl : Over.mk x' ⟶ Over.mk χ) σ with hθF
  obtain ⟨hA, x0, c0, hx0, hv0⟩ := (GlobalTheory.Ex.OneGen.theta_at_trait GlobalTheory.lawsAndExpansions E H S t V hV χ t' hm P σ
    hσ).2 ϖ hϖ F v hv m hodd hmu h3 x' (Over.homMk (jFK (R := V) F ≫ jK V) rfl) rfl
  let φF : V →+* F := (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))
  have hPF : PolFib t.G t.PP.L g x' := by
    have := hg F (algebraMap (FractionRing V) F)
    simpa only [hx', Category.assoc] using this
  have hmF : (m : F) ≠ 0 := by
    have := hmu.map φF
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨ptF, cF, hLF⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed S t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen g m (m ^ (4 * g)) F x' θF hodd
    hmF rfl hPF
  let Kb := AlgebraicClosure K
  let i' : K →+* Kb := algebraMap K Kb
  have hii : Function.Injective (i'.comp i) := i'.injective.comp hi
  let e : FractionRing V →+* Kb := IsFractionRing.lift hii
  letI : Algebra (FractionRing V) Kb := e.toAlgebra
  let j : F →+* Kb := (IsAlgClosed.lift : F →ₐ[FractionRing V] Kb).toRingHom
  have hsq : i'.comp i = j.comp φF := by
    ext r
    change _ = (IsAlgClosed.lift : F →ₐ[FractionRing V] Kb) (algebraMap (FractionRing V) F _)
    rw [AlgHom.commutes]
    exact (IsFractionRing.lift_algebraMap hii r).symm
  have hy : spMap i' ≫ spMap i ≫ χ = spMap j ≫ x' := by
    change _ = spMap j ≫ (spMap (algebraMap (FractionRing V) F) ≫ spMap (algebraMap V (FractionRing V))) ≫ χ
    rw [← Category.assoc, spMap_comp', spMap_comp', ← Category.assoc, spMap_comp', hsq]

  have hPy : PolFib t.G t.PP.L g (spMap j ≫ x') := by
    have := hg Kb (j.comp (algebraMap (FractionRing V) F))
    rw [← spMap_comp'] at this
    simpa only [hx', Category.assoc] using this
  have hmKb : (m : Kb) ≠ 0 := by
    have := hmu.map (i'.comp i)
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨pt1, hpt1, hL1⟩ := GlobalTheory.T.isThetaConstantListOfFibre_pullback_field_extension S t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen m N K Kb i' (spMap i ≫ χ)
    (SecAt.pull t.G t.PP.L σ i) pt c hL
  have hθ : HEq (SecAt.pull t.G t.PP.L (SecAt.pull t.G t.PP.L σ i) i') (SecAt.pull t.G t.PP.L θF j) := by
    simp only [SecAt.pull, hθF, GlobalTheory.ThetaRuleCompare.pullS_comp]
    refine heq_pullS hy _ _ ?_ σ
    simp only [Over.comp_left, Over.homMk_left]
    change spMap i' ≫ spMap i = spMap j ≫ (spMap (algebraMap (FractionRing V) F) ≫ spMap (algebraMap V (FractionRing V)))
    rw [spMap_comp', spMap_comp', spMap_comp', hsq]
  obtain ⟨ptK, hptK, hLK⟩ := thList_of_eq t.PP.rig m hy hθ hL1
  obtain ⟨ptF', hptF', hLF'⟩ := GlobalTheory.T.isThetaConstantListOfFibre_pullback_field_extension S t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen m (m ^ (4 * g)) F Kb j x' θF
    ptF cF hLF
  have hint : ∀ b, φF.IsIntegralElem (cF b) := fun b =>
    GlobalTheory.T.isIntegralElem_of_val_nonneg_over_completeDVR V hV ϖ hϖ F v hv (cF b) (hA (ptF b) (cF b) (hLF.2.1 b))
  refine ⟨fun a => ?_, ?_⟩
  · obtain ⟨b, hb⟩ := hLF.2.2 Kb j (ptK a) (hLK.2.1 a).1
    have heq : ptK a = ptF' b := Over.OverMorphism.ext (hb.trans (hptF' b).symm)
    have h1 := hLK.2.1 a
    rw [heq] at h1
    have hab : j (cF b) = i' (c a) :=
      thG_unique t.PP.rig t.PP.isLB t.PP.rigGen _ (ptF' b) hodd hmKb hPy h1 (hLF'.2.1 b)
    exact isIntegralElem_of_sq φF i i' j hsq hab (hint b)
  · obtain ⟨x0', hx0'l, hx0't⟩ := pt_of_eq (show x' = spMap (RingHom.id F) ≫ x' by rw [spMap_id', Category.id_comp]) x0
    obtain ⟨b0, hb0⟩ := hLF.2.2 F (RingHom.id F) x0' (hx0't _ hx0.1)
    have hx0b : x0 = ptF b0 := Over.OverMorphism.ext (by rw [← hx0'l, hb0, spMap_id', Category.id_comp])
    subst hx0b
    have hc0b : cF b0 = c0 :=
      thG_unique t.PP.rig t.PP.isLB t.PP.rigGen θF (ptF b0) hodd hmF hPF hx0 (hLF.2.1 b0)
    obtain ⟨q, hql, hqt⟩ := pt_of_eq hy.symm (ptF' b0)
    obtain ⟨a0, ha0⟩ := hL.2.2 Kb i' q (hqt _ (hLF'.2.1 b0).1)
    have heq : ptK a0 = ptF' b0 := Over.OverMorphism.ext (by rw [hptK, hpt1, ← ha0, hql])
    have h1 := hLK.2.1 a0
    rw [heq] at h1
    have hab : j c0 = i' (c a0) := by
      rw [← hc0b]
      exact thG_unique t.PP.rig t.PP.isLB t.PP.rigGen _ (ptF' b0) hodd hmKb hPy h1 (hLF'.2.1 b0)
    have hc0 : c0 ≠ 0 := by
      rintro rfl
      simp at hv0
    have hca : c a0 ≠ 0 := by
      intro h
      rw [h, map_zero] at hab
      exact hc0 (j.injective (hab.trans (map_zero j).symm))
    refine ⟨a0, hca, isIntegralElem_of_sq φF i i' j hsq (z := c0⁻¹) (by rw [map_inv₀, map_inv₀, hab]) ?_⟩
    refine GlobalTheory.T.isIntegralElem_of_val_nonneg_over_completeDVR V hV ϖ hϖ F v hv _ ?_
    have h01 : v c0 + v c0⁻¹ = 0 := by
      rw [← AddValuation.map_mul, mul_inv_cancel₀ hc0, AddValuation.map_one]
    rw [hv0, zero_add] at h01
    rw [h01]

end GlobalTheory.UMin.PrimTrait
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsPrimitiveAtUniformisedTraitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstants_primitive_at_uniformisedTrait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (χ : Sp V ⟶ S) (t' : SAB H (Sp V)), Nonempty (SABMap t' t χ) → Nonempty (PELUnif (IsLocalRing.maximalIdeal V) t') → ∀ (σ : SecAt t.G t.PP.L χ), NZ t.G t.PP.L χ σ → ∀ (m N : ℕ), Odd m → 3 ≤ m → IsUnit (m : V) → ∀ (K : Type) [Field K] (i : V →+* K) (pt : Fin N → (Over.mk (spMap i ≫ χ) ⟶ t.G)) (c : Fin N → K), Function.Injective i → ThList t.G t.PP.L t.PP.rig m (spMap i ≫ χ) (SecAt.pull t.G t.PP.L σ i) pt c → Prim i c := by
  first | exact @GlobalTheory.UMin.PrimTrait.main | exact GlobalTheory.UMin.PrimTrait.main | (intros; apply GlobalTheory.UMin.PrimTrait.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearCanonicalMapPrimitiveDeRhamRigExt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyPrimitiveDeRhamTorsionTowerPresentation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyPrimitiveDeRhamTorsionTowerPresentation
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem exists_sub_tower {B : ℕ → Type} [∀ n, AddCommGroup (B n)] (r : ∀ n, B (n + 1) → B n)
    (hr : ∀ n, Function.Surjective (r n)) (a : ∀ n, B n) :
    ∃ h : ∀ n, B n, ∀ n, a n = h n - r n (h (n + 1)) := by
  choose s hs using hr
  refine ⟨fun n ↦ Nat.rec (motive := B) 0 (fun n x ↦ s n (x - a n)) n, fun n ↦ ?_⟩
  simp only [hs, sub_sub_cancel]

theorem nonempty_dat (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) : Nonempty (Dat t c) := by
  obtain ⟨f, hf⟩ := CatCoh.H1.mk_surjective _ c.1
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_additiveStructure_of_primitiveDeRhamClass R A f (by rw [hf]; exact c.2)
  obtain ⟨h, hh⟩ := exists_sub_tower (B := fun n ↦ G.A n) (fun n ↦ G.res n) (fun n ↦ G.res_surjective n)
    (fun n ↦ fv f (G.A (n + 1)) (G.A n) (G.res n : G.A (n + 1) →ₐ[R] G.A n) (t.y (n + 1)))
  exact ⟨⟨f, hf, g, hg, h, hh⟩⟩

end GlobalTheory.PtExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyPrimitiveDeRhamTorsionTowerPresentationStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_primitiveDeRhamTorsionTowerPresentation : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A) (c : primDR A), Nonempty (Dat t c) := by
  first | exact @GlobalTheory.PtExt.nonempty_dat | exact GlobalTheory.PtExt.nonempty_dat | (intros; apply GlobalTheory.PtExt.nonempty_dat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalRigidifiedExtensionDeRhamClassAddSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalRigidifiedExtensionDeRhamClassAddSmul
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

section Basic

variable {X : Over (Sp R)} (f f' : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (r : R)

theorem fv_add_apply (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (x : Pt X D) : fv (f + f') D D' φ x = fv f D D' φ x + fv f' D D' φ x := rfl

theorem fv_smul_apply (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (x : Pt X D) : fv (r • f) D D' φ x = r • fv f D D' φ x := rfl

theorem cotVal_add_apply {D : Type} [CommRing D] [Bialgebra R D] (y : Pt X D) :
    cotVal (f + f') y = cotVal f y + cotVal f' y := by
  unfold cotVal
  simp only [fv_add_apply, map_add (f := _), map_sub]
  abel

theorem cotVal_smul_apply {D : Type} [CommRing D] [Bialgebra R D] (y : Pt X D) :
    cotVal (r • f) y = r • cotVal f y := by
  unfold cotVal
  simp only [fv_smul_apply, map_smul, map_sub, smul_sub]

end Basic

variable {A : Over (Sp R)} [GrpObj A] {p : ℕ} {G : PDivGroup p R} {t : G.TorsionTower A} {c c' : primDR A}

def Dat.sum (d : Dat t c) (d' : Dat t c') : Dat t (c + c') where
  f := d.f + d'.f
  cl := by rw [map_add (f := _), d.cl, d'.cl]; rfl
  g := fun D _ _ x y ↦ d.g D x y + d'.g D x y
  add := fun D _ _ D' _ _ φ x y ↦ by
    have h := d.add D D' φ x y
    have h' := d'.add D D' φ x y
    simp only [fv_add_apply, map_add (f := _)]
    linear_combination h + h'
  h := fun n ↦ d.h n + d'.h n
  res := fun n ↦ by
    have h := d.res n
    have h' := d'.res n
    simp only [fv_add_apply, map_add (f := _)]
    linear_combination h + h'

def Dat.scale (r : R) (d : Dat t c) : Dat t (r • c) where
  f := r • d.f
  cl := by rw [map_smul, d.cl]; rfl
  g := fun D _ _ x y ↦ r • d.g D x y
  add := fun D _ _ D' _ _ φ x y ↦ by
    have h := d.add D D' φ x y
    simp only [fv_smul_apply, map_smul]
    rw [← smul_sub, h, smul_sub, smul_sub]
  h := fun n ↦ r • d.h n
  res := fun n ↦ by
    have h := d.res n
    simp only [fv_smul_apply, map_smul]
    rw [← smul_sub, h]

theorem Dat.coc_sum (d : Dat t c) (d' : Dat t c') (n : ℕ) : (d.sum d').coc n = d.coc n + d'.coc n := by
  simp only [Dat.coc, Dat.sum, fv_add_apply, map_add (f := _)]
  abel

theorem Dat.om_sum (d : Dat t c) (d' : Dat t c') (n : ℕ) : (d.sum d').om n = d.om n + d'.om n := by
  simp only [Dat.om, Dat.sum, cotVal_add_apply, map_add (f := _)]
  abel

theorem Dat.coc_scale (r : R) (d : Dat t c) (n : ℕ) : (d.scale r).coc n = r • d.coc n := by
  simp only [Dat.coc, Dat.scale, fv_smul_apply, map_smul, smul_sub]

theorem Dat.om_scale (r : R) (d : Dat t c) (n : ℕ) : (d.scale r).om n = r • d.om n := by
  simp only [Dat.om, Dat.scale, cotVal_smul_apply, map_smul, smul_sub]

theorem isCan_add_smul (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) :
    (∀ (c c' : primDR A) (x x' : G.RigExt),
      IsCan t c x → IsCan t c' x' → IsCan t (c + c') (x + x')) ∧
    (∀ (r : R) (c : primDR A) (x : G.RigExt), IsCan t c x → IsCan t (r • c) (r • x)) := by
  constructor
  · rintro c c' _ _ ⟨d, z, w, hz, hw, rfl⟩ ⟨d', z', w', hz', hw', rfl⟩
    refine ⟨d.sum d', z + z', w + w', fun n ↦ ?_, fun n ↦ ?_, (map_add G.rigMk _ _).symm⟩
    · rw [Dat.coc_sum, ← hz, ← hz']; rfl
    · rw [Dat.om_sum, ← hw, ← hw']; rfl
  · rintro r c _ ⟨d, z, w, hz, hw, rfl⟩
    refine ⟨d.scale r, r • z, r • w, fun n ↦ ?_, fun n ↦ ?_, (map_smul G.rigMk r (z, w)).symm⟩
    · rw [Dat.coc_scale, ← hz]; rfl
    · rw [Dat.om_scale, ← hw]; rfl

end GlobalTheory.PtExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalRigidifiedExtensionDeRhamClassAddSmulStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalRigidifiedExtension_deRhamClass_add_smul
    (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) :
    (∀ (c c' : primDR A) (x x' : G.RigExt),
      PtExt.IsCan t c x → PtExt.IsCan t c' x' → PtExt.IsCan t (c + c') (x + x')) ∧
    ∀ (r : R) (c : primDR A) (x : G.RigExt), PtExt.IsCan t c x → PtExt.IsCan t (r • c) (r • x) :=
  PtExt.isCan_add_smul R A p G t
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearCanonicalMapPrimitiveDeRhamRigExt
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PtExt.CanMap

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {p : ℕ} {G : PDivGroup p R}

def ext (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (hs : IsSymCoc d.g) : G.RigExt :=
  G.rigMk (⟨d.coc, fun n ↦ ⟨GlobalTheory.T.rigidifiedPresentation_cocycle_mem_bialgebraSymmetricCocycles R A p G t c d hs n, GlobalTheory.T.bialgebraPullbackTwoVariables_res_cocycle_eq R A p G t c d n⟩⟩,
    ⟨d.om, fun n ↦ GlobalTheory.T.torsionTowerPresentation_cotangentPullback_res_rigidification R A p G t c d n⟩)

theorem ext_isCan (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (hs : IsSymCoc d.g) :
    IsCan t c (ext t c d hs) :=
  ⟨d, _, _, fun _ ↦ rfl, fun _ ↦ rfl, rfl⟩

theorem exists_isCan (t : G.TorsionTower A) (hA : IsAbelianScheme A) (c : primDR A) : ∃ x, IsCan t c x := by
  obtain ⟨d⟩ := GlobalTheory.T.nonempty_primitiveDeRhamTorsionTowerPresentation R A p G t c
  exact ⟨_, ext_isCan t c d (GlobalTheory.T.isSymmetricTwoCocycle_of_additiveStructure_torsor R A hA (fv d.f) d.g d.add)⟩

def canFun (t : G.TorsionTower A) (hA : IsAbelianScheme A) (c : primDR A) : G.RigExt :=
  (exists_isCan t hA c).choose

theorem canFun_isCan (t : G.TorsionTower A) (hA : IsAbelianScheme A) (c : primDR A) :
    IsCan t c (canFun t hA c) :=
  (exists_isCan t hA c).choose_spec

theorem isCan_iff (t : G.TorsionTower A) (hA : IsAbelianScheme A) (c : primDR A) (x : G.RigExt) :
    IsCan t c x ↔ canFun t hA c = x :=
  ⟨fun h ↦ GlobalTheory.T.canonicalRigidifiedExtensionOfDeRhamClass_unique R A p G t c hA _ _ (canFun_isCan t hA c) h, fun h ↦ h ▸ canFun_isCan t hA c⟩

def canMap (t : G.TorsionTower A) (hA : IsAbelianScheme A) : primDR A →ₗ[R] G.RigExt where
  toFun := canFun t hA
  map_add' c c' := (isCan_iff t hA _ _).1
    ((GlobalTheory.T.canonicalRigidifiedExtension_deRhamClass_add_smul R A p G t).1 c c' _ _ (canFun_isCan t hA c) (canFun_isCan t hA c'))
  map_smul' r c := (isCan_iff t hA _ _).1
    ((GlobalTheory.T.canonicalRigidifiedExtension_deRhamClass_add_smul R A p G t).2 r c _ (canFun_isCan t hA c))

end GlobalTheory.PtExt.CanMap

theorem GlobalTheory.PtExt.exists_canMap : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A), IsAbelianScheme A →
      ∃ L : primDR A →ₗ[R] G.RigExt, ∀ c x, IsCan t c x ↔ L c = x :=
  fun _ _ _ _ _ _ t hA ↦ ⟨GlobalTheory.PtExt.CanMap.canMap t hA, GlobalTheory.PtExt.CanMap.isCan_iff t hA⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearCanonicalMapPrimitiveDeRhamRigExtStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_canonical_map_primitiveDeRham_rigExt : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A), IsAbelianScheme A → ∃ L : primDR A →ₗ[R] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n)))))), ∀ c x, IsCan t c x ↔ L c = x := by
  first | exact @GlobalTheory.PtExt.exists_canMap | exact GlobalTheory.PtExt.exists_canMap | (intros; apply GlobalTheory.PtExt.exists_canMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedPolarisationKernelKilledSameInteger
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedPolarisationKernelKilledSameInteger
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.DescPolKer

theorem pow_eq_one_of_descent : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left) (e : ℕ), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∀ (T : Over X) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1) → ∀ (T : Over Y) (x : T ⟶ A₀), (∃ t : (P₀.pull (lift (snd A₀ T ≫ x) (fst A₀ T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  intro X Y π Ga _ ρ A _ _ A₀ _ _ φ φ₂ P P₀ e hG hA hA₀ hφ hsq hP hP₀ hw hker T x ⟨t, ht⟩
  rcases Nat.eq_zero_or_pos e with rfl | he
  · exact pow_zero x
  let T₁ : Over X := Over.mk (pullback.snd T.hom π)
  let ε : T₁.left ⟶ T.left := pullback.fst T.hom π
  have hε : Epi ε := GlobalTheory.GaloisCartDesc.epi_pullback_fst hG T.hom
  let x₁ : T₁ ⟶ A := Over.homMk (hφ.1.lift (ε ≫ x.left) (pullback.snd T.hom π)
    (by simp [ε, pullback.condition])) (hφ.1.lift_snd _ _ _)
  have hx₁ : x₁.left ≫ φ = ε ≫ x.left := hφ.1.lift_fst _ _ _

  have p₀ : IsPullback (snd A₀ T).left (fst A₀ T).left T.hom A₀.hom :=
    (IsPullback.of_hasPullback A₀.hom T.hom).flip
  have w₀ : ((snd A T₁).left ≫ ε) ≫ T.hom = ((fst A T₁).left ≫ φ) ≫ A₀.hom := by
    have a₁ := Over.w (snd A T₁)
    have a₂ := Over.w (fst A T₁)
    simp only [T₁, Over.mk_hom] at a₁
    rw [Category.assoc, Category.assoc, hφ.1.w, ← Category.assoc (fst A T₁).left, a₂, ← a₁, Category.assoc]
    simp [ε, pullback.condition]
    rfl
  let hm : (A ⊗ T₁).left ⟶ (A₀ ⊗ T).left := p₀.lift _ _ w₀
  have hc : (lift (snd A T₁ ≫ x₁) (fst A T₁)).left ≫ φ₂ = hm ≫ (lift (snd A₀ T ≫ x) (fst A₀ T)).left := by
    have p₂ : IsPullback (snd A₀ A₀).left (fst A₀ A₀).left A₀.hom A₀.hom :=
      (IsPullback.of_hasPullback A₀.hom A₀.hom).flip
    apply p₂.hom_ext
    · rw [Category.assoc, hsq.2, ← Category.assoc, GlobalTheory.TripleDescent.lift_left_snd, Category.assoc,
        GlobalTheory.TripleDescent.lift_left_snd, p₀.lift_snd]
    · rw [Category.assoc, hsq.1, ← Category.assoc, GlobalTheory.TripleDescent.lift_left_fst, Category.assoc,
        GlobalTheory.TripleDescent.lift_left_fst, Over.comp_left, Over.comp_left, Category.assoc, hx₁,
        ← Category.assoc, ← Category.assoc, p₀.lift_fst]
  obtain ⟨w, hwg⟩ := hw
  obtain ⟨t', ht', -⟩ := GlobalTheory.FamFieldPull.exists_genPull w hwg hP₀ hP (K := PUnit)
    (fun _ => (lift (snd A T₁ ≫ x₁) (fst A T₁)).left) (fun _ => (lift (snd A₀ T ≫ x) (fst A₀ T)).left)
    (fun _ => 1) hm (fun _ => hc) t ht
  have h₁ : x₁ ^ e = 1 := hker T₁ x₁ ⟨t', ht'⟩

  let j : Over.mk (T₁.hom ≫ π) ⟶ T := Over.homMk ε (by simp [T₁, ε, pullback.condition])
  have hj : (j ≫ x).left = x₁.left ≫ φ := by simp [j, hx₁]
  have hpow : ∀ n : ℕ, ((j ≫ x) ^ (n + 1)).left = (x₁ ^ (n + 1)).left ≫ φ := by
    intro n
    induction n with
    | zero => simpa using hj
    | succ n ih =>
      rw [pow_succ, pow_succ x₁]
      exact hφ.2 T₁ (x₁ ^ (n + 1)) x₁ _ _ ih hj
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  have hy : (j ≫ x) ^ (k + 1) * (j ≫ x) ^ (k + 1) = (j ≫ x) ^ (k + 1) := by
    apply Over.OverMorphism.ext
    rw [← pow_add, show k + 1 + (k + 1) = (2 * k + 1) + 1 by ring, hpow, hpow,
      show 2 * k + 1 + 1 = (k + 1) + (k + 1) by ring, pow_add, h₁, _root_.one_mul]
  have hy1 := mul_eq_left.1 hy
  apply Over.OverMorphism.ext
  rw [← cancel_epi ε]
  have e₁ : ε ≫ (x ^ (k + 1)).left = (j ≫ x ^ (k + 1)).left := by rw [Over.comp_left]; rfl
  have e₂ : ε ≫ (1 : T ⟶ A₀).left = (j ≫ (1 : T ⟶ A₀)).left := by rw [Over.comp_left]; rfl
  rw [e₁, e₂, MonObj.comp_pow, hy1, MonObj.comp_one]

end GlobalTheory.DescPolKer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedPolarisationKernelKilledSameIntegerStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descended_polarisation_kernel_killed_same_integer : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left) (e : ℕ), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∀ (T : Over X) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1) → ∀ (T : Over Y) (x : T ⟶ A₀), (∃ t : (P₀.pull (lift (snd A₀ T ≫ x) (fst A₀ T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  first | (exact @GlobalTheory.DescPolKer.pow_eq_one_of_descent) | (exact GlobalTheory.DescPolKer.pow_eq_one_of_descent) | (intros; apply GlobalTheory.DescPolKer.pow_eq_one_of_descent  <;> assumption)
end
end
