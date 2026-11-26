module

public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.JetRdMulInvPow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnFrameA
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsHolFamPullbackLiftOfCommonBase
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TiledBoundaries.NstatementHypsConsistent
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.TraceFormDualOneTraceFormDual

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AbelianHolomorphicFrameReadingConstOfFormsCancel
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AbelianHolomorphicFrameReadingConstOfFormsCancel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AnVal.genRd_const : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε)), t.IsGen → ∀ (N : ℕ) (q : (Fin N → ℂ) → (Sp ℂ ⟶ Z)) (Λ : K → (Fin N → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Ga : AddSubgroup (Fin N → ℂ)), IsHolFam q → (∀ z k, q z ≫ φ k = (Φ.e (Λ k z)).left) → Submodule.span ℝ (Ga : Set (Fin N → ℂ)) = ⊤ → (∀ gm ∈ Ga, (∀ z, q (z + gm) = q z) ∧ ∀ k, Λ k gm ∈ Φ.lat) → (∀ z w, ∑ k, (ε k : ℂ) * hermForm Φ.Hm (Λ k z) (Λ k w) = 0) → (∃ v : ℂ, v ≠ 0 ∧ ∀ z, Φ.GenRd φ ε t (q z) (fun k => Λ k z) v) ∧ ∀ gm ∈ Ga, ∏ k, Φ.χ (Λ k gm) ^ ε k = 1 := by
  intro S A _ _ L x0 g Φ Z K _ φ ε t ht N q Λ Ga hq hqe hspan hper hH
  obtain ⟨v, hv, hv0, hrd, -, hfac⟩ := GlobalTheory.T.exists_holomorphic_generator_reading_automorphy S A L x0 g Φ Z K φ ε t ht N q (fun k z => Λ k z) hq
    (fun k => (LinearMap.toContinuousLinearMap (Λ k)).differentiable) hqe
  have hprod : ∀ gm z, ∏ k, Φ.fac (Λ k gm) (Λ k z) ^ ε k = ∏ k, Φ.χ (Λ k gm) ^ ε k := by
    intro gm z
    simp only [AnFr.fac, mul_zpow, Finset.prod_mul_distrib, ← Complex.exp_int_mul, ← Complex.exp_sum]
    have h : ∑ k, (ε k : ℂ) * (Real.pi * hermForm Φ.Hm (Λ k z) (Λ k gm) +
        Real.pi / 2 * hermForm Φ.Hm (Λ k gm) (Λ k gm)) =
        Real.pi * ∑ k, (ε k : ℂ) * hermForm Φ.Hm (Λ k z) (Λ k gm) +
        Real.pi / 2 * ∑ k, (ε k : ℂ) * hermForm Φ.Hm (Λ k gm) (Λ k gm) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [h, hH, hH]
    simp
  have hstep : ∀ gm ∈ Ga, ∀ z, v (z + gm) = v z * ∏ k, Φ.χ (Λ k gm) ^ ε k := by
    intro gm hgm z
    rw [← hprod gm z]
    exact hfac z (z + gm) (fun k => Λ k gm) ((hper gm hgm).1 z)
      (fun k => ⟨(hper gm hgm).2 k, map_add _ _ _⟩)
  have hnorm : ∀ gm ∈ Ga, ∀ z, ‖v (z + gm)‖ = ‖v z‖ := by
    intro gm hgm z
    rw [hstep gm hgm z, norm_mul, norm_prod]
    have : ∀ k, ‖Φ.χ (Λ k gm) ^ ε k‖ = 1 := fun k => by
      rw [norm_zpow, Φ.χ_norm _ ((hper gm hgm).2 k), one_zpow]
    simp [this]
  have hconst : ∀ z, v z = v 0 := by
    intro z
    refine norm_periodic_const_range Ga.subtype ?_ v hv (fun z a => hnorm a a.2 z) z 0
    simpa using hspan
  refine ⟨⟨v 0, hv0 0, fun z => hconst z ▸ hrd z⟩, fun gm hgm => ?_⟩
  have h := hstep gm hgm 0
  rw [hconst] at h
  exact (mul_eq_left₀ (hv0 0)).1 h.symm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AbelianHolomorphicFrameReadingConstOfFormsCancelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianHolomorphicFrame_reading_const_of_forms_cancel : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε)), t.IsGen → ∀ (N : ℕ) (q : (Fin N → ℂ) → (Sp ℂ ⟶ Z)) (Λ : K → (Fin N → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Ga : AddSubgroup (Fin N → ℂ)), IsHolFam q → (∀ z k, q z ≫ φ k = (Φ.e (Λ k z)).left) → Submodule.span ℝ (Ga : Set (Fin N → ℂ)) = ⊤ → (∀ gm ∈ Ga, (∀ z, q (z + gm) = q z) ∧ ∀ k, Λ k gm ∈ Φ.lat) → (∀ z w, ∑ k, (ε k : ℂ) * hermForm Φ.Hm (Λ k z) (Λ k w) = 0) → (∃ v : ℂ, v ≠ 0 ∧ ∀ z, Φ.GenRd φ ε t (q z) (fun k => Λ k z) v) ∧ ∀ gm ∈ Ga, ∏ k, Φ.χ (Λ k gm) ^ ε k = 1 := by
  first | exact @GlobalTheory.AnVal.genRd_const | exact GlobalTheory.AnVal.genRd_const | (intros; apply GlobalTheory.AnVal.genRd_const <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CmFrameJetPointsAreExponentialJets
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CmFrameJetPointsAreExponentialJets
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal

attribute [local instance] Over.cartesianMonoidalCategory

theorem isHolFam_precomp_clm {Y : Scheme.{0}} {g N : ℕ} (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e)
    (A : (Fin N → ℂ) →L[ℂ] (Fin g → ℂ)) : IsHolFam (fun v => e (A v)) := by
  intro U f
  obtain ⟨h1, h2⟩ := hol U f
  exact ⟨h1.preimage A.continuous, h2.comp A.differentiable.differentiableOn fun _ hv => hv⟩

def colPr (n g : ℕ) (i : Fin n) : (Fin (n * g) → ℂ) →L[ℂ] (Fin g → ℂ) :=
  ContinuousLinearMap.pi fun j =>
    ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n * g) => ℂ) (finProdFinEquiv (i, j))

theorem colPr_apply (n g : ℕ) (i : Fin n) (v : Fin (n * g) → ℂ) (j : Fin g) :
    colPr n g i v j = v (finProdFinEquiv (i, j)) := rfl

theorem anLin_colPr (n g : ℕ) (i : Fin n) (p : Fin 1 × Fin g) :
    anLin (colPr n g i) p = MvPolynomial.X ((0 : Fin 1), finProdFinEquiv (i, p.2)) := by
  rw [anLin, Finset.sum_eq_single (finProdFinEquiv (i, p.2))]
  · rw [colPr_apply, Pi.single_eq_same, map_one, _root_.one_mul]
  · intro k _ hk
    simp [colPr_apply, Ne.symm hk]
  · simp

theorem renN_colPr (n g m : ℕ) (i : Fin n) (a : Jet ℂ (Fin 1 × Fin g) m) :
    renN n g m (jetMap (anLin (colPr n g i)) (anLin_mem _) a) = jetCopy (S := ℂ) g m i a := by
  unfold renN jetCopy
  exact anJetMap_comp _ _ _ _ _ _
    (fun p => by simp only [anLin_colPr, MvPolynomial.aeval_X, Equiv.symm_apply_apply]) a

theorem jetCopy_one_zero (g m : ℕ) (a : Jet ℂ (Fin 1 × Fin g) m) : jetCopy (S := ℂ) g m (0 : Fin 1) a = a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  show Ideal.Quotient.mk _ (MvPolynomial.aeval (fun q : Fin 1 × Fin g =>
    (MvPolynomial.X ((0 : Fin 1), q.2) : MvPolynomial (Fin 1 × Fin g) ℂ)) p) = _
  have h : (fun q : Fin 1 × Fin g => (MvPolynomial.X ((0 : Fin 1), q.2) : MvPolynomial (Fin 1 × Fin g) ℂ)) =
      MvPolynomial.X := by
    funext q
    congr 1
    exact Prod.ext (Subsingleton.elim _ _) rfl
  rw [h, MvPolynomial.aeval_X_left_apply]

theorem spMap_jetCopy_jetPt {Y : Scheme.{0}} {g : ℕ} (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e)
    (n m : ℕ) (i : Fin n) :
    spMap (jetCopy (S := ℂ) g m i : Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin n × Fin g) m) ≫ jetPt e hol m =
      spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫
        jetPt (fun v => e (colPr n g i v)) (isHolFam_precomp_clm e hol _) m := by
  have hring : ((jetCopy (S := ℂ) g m i : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n × Fin g) m) :
      Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin n × Fin g) m) =
      (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m).comp
        ((jetMap (anLin (colPr n g i)) (anLin_mem _) :
          Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin (n * g)) m) :
          Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin (n * g)) m) :=
    RingHom.ext fun a => (renN_colPr n g m i a).symm
  rw [hring, anSpMap_comp, Category.assoc]
  congr 1
  have := isLocalHom_jetMap (K := ℂ) (m := m) (anLin (colPr n g i)) (anLin_mem _)
  refine jetPt_precompD _ _ hol _ (by show e (colPr n g i 0) = e 0; rw [map_zero]) m _ fun U hU f => ?_
  exact (jetOf_comp_anLin m (contDiffAt_val _ hol hU f) (colPr n g i)).symm

section General

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

theorem AnFr.e_zero : Φ.e 0 = 1 := (Φ.e_ker 0).mpr Φ.lat.zero_mem

theorem AnFr.jetMap_copy (n m : ℕ) (i : Fin n) :
    Φ.JetMap m (homAt x0 (jetCopy (S := ℂ) g m i) ≫ anJX x0 Φ.e Φ.hol m).left (LinearMap.proj i) :=
  ⟨isHolFam_precomp_clm _ Φ.hol (colPr n g i), spMap_jetCopy_jetPt _ Φ.hol n m i⟩

theorem AnFr.jetMap_self (m : ℕ) :
    Φ.JetMap (n := 1) m (anJX x0 Φ.e Φ.hol m).left (LinearMap.proj 0) := by
  refine ⟨isHolFam_precomp_clm _ Φ.hol (colPr 1 g 0), ?_⟩
  have h := spMap_jetCopy_jetPt _ Φ.hol 1 m 0
  have hid : (jetCopy (S := ℂ) g m (0 : Fin 1) : Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin g) m) =
      RingHom.id _ := RingHom.ext (jetCopy_one_zero g m)
  rw [hid, spMap, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp] at h
  exact h

theorem AnFr.jetMap_one (n m : ℕ) :
    Φ.JetMap m (1 : overAt x0 (Jet ℂ (Fin n × Fin g) m) ⟶ A).left 0 := by
  have hc : ∀ v : Fin (n * g) → ℂ, (Φ.e ((0 : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (colsOf n g v))).left =
      (1 : Over.mk x0 ⟶ A).left := fun v => by rw [LinearMap.zero_apply, Φ.e_zero]
  have hf := funext hc
  have hol : IsHolFam (fun v : Fin (n * g) → ℂ =>
      (Φ.e ((0 : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (colsOf n g v))).left) := by
    rw [hf]; exact isHolFam_const _
  refine ⟨hol, ?_⟩
  have h1 := jetPt_comp _ (isHolFam_const (g := n * g) (1 : Over.mk x0 ⟶ A).left) (𝟙 _) _ hol
    (fun v => (Category.comp_id _).trans (hc v).symm) m
  rw [← h1, Category.comp_id, ← jetPt_const, ← Category.assoc, spMap_comp_alg]
  let k : overAt x0 (Jet ℂ (Fin n × Fin g) m) ⟶ Over.mk x0 :=
    Over.homMk (spMap (algebraMap ℂ (Jet ℂ (Fin n × Fin g) m))) rfl
  have hk : (1 : overAt x0 (Jet ℂ (Fin n × Fin g) m) ⟶ A) = k ≫ (1 : Over.mk x0 ⟶ A) := (MonObj.comp_one k).symm
  rw [hk]
  rfl

theorem AnFr.jetMap_comp {n m : ℕ} (a : overAt x0 (Jet ℂ (Fin n × Fin g) m) ⟶ A)
    (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (φ : A ⟶ A) (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hT : ∀ z, Φ.e (T z) = Φ.e z ≫ φ) (ha : Φ.JetMap m a.left Λ) : Φ.JetMap m (a ≫ φ).left (T ∘ₗ Λ) := by
  obtain ⟨hol, ha⟩ := ha
  have hc : ∀ v : Fin (n * g) → ℂ, (Φ.e (Λ (colsOf n g v))).left ≫ φ.left =
      (Φ.e ((T ∘ₗ Λ) (colsOf n g v))).left := fun v => by
    rw [LinearMap.comp_apply, hT, Over.comp_left]
  have hol' : IsHolFam (fun v : Fin (n * g) → ℂ => (Φ.e ((T ∘ₗ Λ) (colsOf n g v))).left) := by
    rw [← funext hc]; exact isHolFam_comp _ hol _
  refine ⟨hol', ?_⟩
  rw [Over.comp_left, ha, Category.assoc, jetPt_comp _ hol _ _ hol' hc]

theorem AnFr.jetMap_pair {n m : ℕ} (a b : overAt x0 (Jet ℂ (Fin n × Fin g) m) ⟶ A)
    (Λ Λ' : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (ha : Φ.JetMap m a.left Λ) (hb : Φ.JetMap m b.left Λ') :
    ∃ hq : IsHolFam (fun v : Fin (n * g) → ℂ => (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left),
      (lift a b).left = spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫
        jetPt _ hq m := by
  obtain ⟨hola, ha⟩ := ha
  obtain ⟨holb, hb⟩ := hb
  have hq : IsHolFam (fun v : Fin (n * g) → ℂ =>
      (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left) :=
    GlobalTheory.AnVal.isHolFam_pullback_lift S A.left A.left A.hom A.hom (n * g) _ _ x0 (fun v => Over.w (Φ.e (Λ (colsOf n g v))))
      (fun v => Over.w (Φ.e (Λ' (colsOf n g v)))) hola holb
  refine ⟨hq, ?_⟩
  have hf : ∀ v : Fin (n * g) → ℂ, (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left ≫
      (fst A A).left = (Φ.e (Λ (colsOf n g v))).left := fun v => by rw [← Over.comp_left, lift_fst]
  have hs : ∀ v : Fin (n * g) → ℂ, (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left ≫
      (snd A A).left = (Φ.e (Λ' (colsOf n g v))).left := fun v => by rw [← Over.comp_left, lift_snd]
  apply pullback.hom_ext
  · show (lift a b).left ≫ (fst A A).left = (_ ≫ jetPt _ hq m) ≫ (fst A A).left
    rw [← Over.comp_left, lift_fst, Category.assoc, jetPt_comp _ hq _ _ hola hf, ha]
  · show (lift a b).left ≫ (snd A A).left = (_ ≫ jetPt _ hq m) ≫ (snd A A).left
    rw [← Over.comp_left, lift_snd, Category.assoc, jetPt_comp _ hq _ _ holb hs, hb]

theorem AnFr.jetMap_mul {n m : ℕ} (a b : overAt x0 (Jet ℂ (Fin n × Fin g) m) ⟶ A)
    (Λ Λ' : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (ha : Φ.JetMap m a.left Λ) (hb : Φ.JetMap m b.left Λ') :
    Φ.JetMap m (a * b).left (Λ + Λ') := by
  obtain ⟨hq, hab⟩ := Φ.jetMap_pair a b Λ Λ' ha hb
  have hc : ∀ v : Fin (n * g) → ℂ, (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left ≫
      (MonObj.mul : A ⊗ A ⟶ A).left = (Φ.e ((Λ + Λ') (colsOf n g v))).left := fun v => by
    rw [LinearMap.add_apply, Φ.e_add, CategoryTheory.Hom.mul_def, Over.comp_left]
  have hol' : IsHolFam (fun v : Fin (n * g) → ℂ => (Φ.e ((Λ + Λ') (colsOf n g v))).left) := by
    rw [← funext hc]; exact isHolFam_comp _ hq _
  refine ⟨hol', ?_⟩
  rw [CategoryTheory.Hom.mul_def, Over.comp_left, hab, Category.assoc, jetPt_comp _ hq _ _ hol' hc]

end General

theorem jetPts_jetMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ (n m : ℕ), (∀ i : Fin n, Φ.toAnFr.JetMap m (jpt y g Φ.jx m i).left (LinearMap.proj i)) ∧ Φ.toAnFr.JetMap m (1 : jO y g m n ⟶ Xo.univ.t.G).left 0 ∧ (∀ (a b : jO y g m n ⟶ Xo.univ.t.G) (Λ Λ' : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), Φ.toAnFr.JetMap m a.left Λ → Φ.toAnFr.JetMap m b.left Λ' → Φ.toAnFr.JetMap m (a * b).left (Λ + Λ') ∧ ∃ hq : IsHolFam (fun v : Fin (n * g) → ℂ => (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left), (lift a b).left = spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫ jetPt _ hq m) ∧ (∀ (a : jO y g m n ⟶ Xo.univ.t.G) (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (α : 𝓞 E), Φ.toAnFr.JetMap m a.left Λ → Φ.toAnFr.JetMap m (a ≫ Xo.univ.t.act.act α).left (tyAct ty α ∘ₗ Λ)) ∧ Φ.toAnFr.JetMap (n := 1) m (Φ.jx m).left (LinearMap.proj 0) := by
  intro E _ _ _ H Dw l Xo c _ y g ty el Φ n m
  exact ⟨fun i => Φ.toAnFr.jetMap_copy n m i, Φ.toAnFr.jetMap_one n m,
    fun a b Λ Λ' ha hb => ⟨Φ.toAnFr.jetMap_mul a b Λ Λ' ha hb, Φ.toAnFr.jetMap_pair a b Λ Λ' ha hb⟩,
    fun a Λ α ha => Φ.toAnFr.jetMap_comp a Λ _ _ (Φ.lin α) ha, Φ.toAnFr.jetMap_self m⟩

end GlobalTheory.AnVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CmFrameJetPointsAreExponentialJetsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmFrame_jetPoints_are_exponential_jets : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ (n m : ℕ), (∀ i : Fin n, Φ.toAnFr.JetMap m (jpt y g Φ.jx m i).left (LinearMap.proj i)) ∧ Φ.toAnFr.JetMap m (1 : jO y g m n ⟶ Xo.univ.t.G).left 0 ∧ (∀ (a b : jO y g m n ⟶ Xo.univ.t.G) (Λ Λ' : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), Φ.toAnFr.JetMap m a.left Λ → Φ.toAnFr.JetMap m b.left Λ' → Φ.toAnFr.JetMap m (a * b).left (Λ + Λ') ∧ ∃ hq : IsHolFam (fun v : Fin (n * g) → ℂ => (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left), (lift a b).left = spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫ jetPt _ hq m) ∧ (∀ (a : jO y g m n ⟶ Xo.univ.t.G) (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (α : 𝓞 E), Φ.toAnFr.JetMap m a.left Λ → Φ.toAnFr.JetMap m (a ≫ Xo.univ.t.act.act α).left (tyAct ty α ∘ₗ Λ)) ∧ Φ.toAnFr.JetMap (n := 1) m (Φ.jx m).left (LinearMap.proj 0) := by
  first | exact @GlobalTheory.AnVal.jetPts_jetMap | exact GlobalTheory.AnVal.jetPts_jetMap | (intros; apply GlobalTheory.AnVal.jetPts_jetMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HyperbolicFlagDataBasePoint
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries (E4)

namespace GlobalTheory

namespace HyperbolicCusp

noncomputable section

def ii : E4 := IsCyclotomicExtension.zeta 4 ℚ E4

theorem ii_prim : IsPrimitiveRoot ii 4 := IsCyclotomicExtension.zeta_spec 4 ℚ E4

theorem ii_mul_ii : ii * ii = -1 := by
  have h : IsPrimitiveRoot (ii ^ 2) 2 := ii_prim.pow (by norm_num) (by norm_num : 4 = 2 * 2)
  rw [← sq]
  exact h.eq_neg_one_of_two_right

theorem ii_ne_zero : ii ≠ 0 := ii_prim.ne_zero (by norm_num)

theorem ii_isIntegral : IsIntegral ℤ ii := ii_prim.isIntegral (by norm_num)

theorem emb_ii (τ : E4 →+* ℂ) : τ ii = Complex.I ∨ τ ii = -Complex.I := by
  have h : τ ii * τ ii = Complex.I * Complex.I := by
    rw [← map_mul, ii_mul_ii, Complex.I_mul_I]; simp
  exact mul_self_eq_mul_self_iff.1 h

theorem cc_ii : cc ii = -ii := by
  obtain ⟨τ⟩ : Nonempty (E4 →+* ℂ) := inferInstance
  apply τ.injective
  rw [emb_cc, map_neg]
  rcases emb_ii τ with h | h <;> simp [h]

theorem exists_int_of_isIntegral {x : E4} (hx : IsIntegral ℤ x) :
    ∃ m n : ℤ, x = m + n * ii := by
  have hcl := IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton ii_prim
  obtain ⟨⟨y, hy⟩, rfl⟩ := (hcl.isIntegral_iff).1 hx
  change ∃ m n : ℤ, y = m + n * ii
  clear hx
  induction hy using Algebra.adjoin_induction with
  | mem z hz => exact ⟨0, 1, by simpa using hz⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨m, n, rfl⟩ := ha
    obtain ⟨m', n', rfl⟩ := hb
    exact ⟨m + m', n + n', by push_cast; ring⟩
  | mul a b _ _ ha hb =>
    obtain ⟨m, n, rfl⟩ := ha
    obtain ⟨m', n', rfl⟩ := hb
    exact ⟨m * m' - n * n', m * n' + n * m', by
      push_cast; linear_combination (n * n' : E4) * ii_mul_ii⟩

theorem exists_rat (x : E4) : ∃ p q : ℚ, x = p + q * ii := by
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E4).2 (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨k, hk, hki⟩ := halg.exists_integral_multiple
  obtain ⟨m, n, h⟩ := exists_int_of_isIntegral hki
  have hk' : (k : E4) ≠ 0 := Int.cast_ne_zero.2 hk
  refine ⟨m / k, n / k, ?_⟩
  rw [zsmul_eq_mul] at h
  push_cast
  field_simp
  linear_combination h

theorem trace_ii : Algebra.trace ℚ E4 ii = 0 := by
  have h := trace_cc ii
  rw [cc_ii, map_neg] at h
  linarith

theorem finrank_eq : Module.finrank ℚ E4 = 2 := by
  rw [IsCyclotomicExtension.Rat.finrank 4 E4]
  decide

theorem trace_eq (p q : ℚ) : Algebra.trace ℚ E4 (-(ii / 2) * (p + q * ii)) = q := by
  have e : -(ii / 2) * ((p : E4) + q * ii) = algebraMap ℚ E4 (q / 2) + algebraMap ℚ E4 (-(p / 2)) * ii := by
    simp only [eq_ratCast]
    push_cast
    linear_combination (-(q : E4) / 2) * ii_mul_ii
  rw [e, map_add (f := _), ← Algebra.smul_def, map_smul, trace_ii, Algebra.trace_algebraMap, finrank_eq]
  simp
  ring

def gm : Matrix (Fin 2) (Fin 2) E4 := !![1, 0; 0, -1]

theorem herm_gm (x y : Fin 2 → E4) : herm gm x y = x 0 * cc (y 0) - x 1 * cc (y 1) := by
  simp [herm, gm, Fin.sum_univ_two]
  ring

theorem gm_herm (a b : Fin 2) : cc (gm a b) = gm b a := by
  fin_cases a <;> fin_cases b <;> simp [gm, cc]

theorem gm_det : gm.det ≠ 0 := by
  simp [gm, Matrix.det_fin_two]

def lat : Submodule (𝓞 E4) (Fin 2 → E4) where
  carrier := {x | ∀ a, IsIntegral ℤ (x a)}
  add_mem' hx hy a := (hx a).add (hy a)
  zero_mem' _ := isIntegral_zero
  smul_mem' c _ hx a := c.isIntegral_coe.mul (hx a)

theorem single_mem_lat (a : Fin 2) {c : E4} (hc : IsIntegral ℤ c) : Pi.single a c ∈ lat := by
  intro b
  by_cases h : b = a
  · subst h; simpa using hc
  · simpa [h] using isIntegral_zero

theorem lat_fg : lat.FG := by
  refine Submodule.fg_def.2 ⟨Set.range fun a : Fin 2 => (Pi.single a 1 : Fin 2 → E4),
    Set.finite_range _, le_antisymm ?_ fun x hx => ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact single_mem_lat a isIntegral_one
  · rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun a => ⟨x a, hx a⟩, ?_⟩
    change ∑ a, x a • (Pi.single a 1 : Fin 2 → E4) = x
    funext b
    fin_cases b <;> simp [Fin.sum_univ_two]

theorem lat_span : Submodule.span E4 (lat : Set (Fin 2 → E4)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x = x 0 • (Pi.single 0 1 : Fin 2 → E4) + x 1 • (Pi.single 1 1 : Fin 2 → E4) := by
    funext b
    fin_cases b <;> simp
  rw [hx]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (single_mem_lat 0 isIntegral_one)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (single_mem_lat 1 isIntegral_one)))

theorem lat_int {x y : Fin 2 → E4} (hx : x ∈ lat) (hy : y ∈ lat) : IsIntegral ℤ (herm gm x y) := by
  rw [herm_gm]
  exact ((hx 0).mul (isIntegral_cc (hy 0))).sub ((hx 1).mul (isIntegral_cc (hy 1)))

def cmt : Finset (E4 →+* ℂ) := by
  classical
  exact Finset.univ.filter fun τ => τ ii = Complex.I

theorem mem_cmt {τ : E4 →+* ℂ} : τ ∈ cmt ↔ τ ii = Complex.I := by
  simp [cmt]

theorem cmt_cmType (τ : E4 →+* ℂ) : τ ∈ cmt ↔ ComplexEmbedding.conjugate τ ∉ cmt := by
  have hI : -Complex.I ≠ Complex.I := fun h => by
    have := congrArg Complex.im h
    norm_num at this
  rw [mem_cmt, mem_cmt, ComplexEmbedding.conjugate_coe_eq]
  rcases emb_ii τ with h | h <;> simp [h, hI]

theorem gram_one (τ : E4 →+* ℂ) :
    gram τ gm 1 = Matrix.diagonal fun a : Fin 2 => ((sgn 1 (a : ℕ) : ℝ) : ℂ) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [gram, hermC, col, sgn, gm, Matrix.one_apply]

theorem half_ii_ne_zero : ii / 2 ≠ 0 := div_ne_zero ii_ne_zero two_ne_zero

theorem exists_flagData : ∃ X : Data E4 2, X.Ψ = cmt ∧ X.Gm = gm ∧ X.p0 = 1 ∧ X.Λ = lat ∧
    X.ξ0 = ii / 2 ∧ X.κ0 = -ii ∧ X.m = 3 ∧
    (∀ γ, γ ∈ X.Γ ↔ IsUStab gm lat γ ∧
      (∀ v ∈ lat, ∃ w ∈ lat, Matrix.mulVec (γ : Matrix (Fin 2) (Fin 2) E4) v = v + 3 • w)) ∧
    ∀ la γ, X.χ la γ = 1 := by
  refine FlagData.exists_data latMinkowski E4 2 1 3 3 cmt gm lat (ii / 2) (-ii) cmt_cmType gm_herm
    gm_det (by norm_num) (fun τ _ => ⟨1, by simp, gram_one τ⟩) lat_fg lat_span le_rfl ?_
    half_ii_ne_zero (Or.inr (by ring)) (fun τ hτ => ?_) (by norm_num) fun x hx y hy => ?_
  · have h : IsCMField.complexConj E4 ii = -ii := cc_ii
    simp [cc, h, map_ofNat, neg_div]
  · simp [mem_cmt.1 hτ]
  · rw [div_self (by norm_num), one_mul]
    exact ii_isIntegral.neg.mul (lat_int hx hy)

def flagData : Data E4 2 := exists_flagData.choose

theorem flagData_Ψ : flagData.Ψ = cmt := exists_flagData.choose_spec.1
theorem flagData_Gm : flagData.Gm = gm := exists_flagData.choose_spec.2.1
theorem hyperbolicFlagData_base_point : flagData.p0 = 1 := exists_flagData.choose_spec.2.2.1
theorem flagData_Λ : flagData.Λ = lat := exists_flagData.choose_spec.2.2.2.1
theorem flagData_κ0 : flagData.κ0 = -ii := exists_flagData.choose_spec.2.2.2.2.2.1

theorem emb_ii_eq (τ : flagData.Ψ) : τ.1 ii = Complex.I :=
  mem_cmt.1 (flagData_Ψ ▸ τ.2)

theorem isIso_one : flagData.IsIso ![1, 1] := by
  refine ⟨?_, ?_, fun h => by simpa using congrFun h 0⟩
  · rw [flagData_Λ]
    intro a
    fin_cases a <;> simpa using isIntegral_one
  · rw [flagData_Gm, herm_gm]
    simp

end

end HyperbolicCusp

end GlobalTheory
end
