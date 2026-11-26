module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKerIffMinors
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDivOfExpandsAt
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFinAffineCover
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw GlobalTheory.PrimNorm
noncomputable section
namespace GlobalTheory.PrimVan

variable {X Y Y' : Scheme.{0}}

theorem gm_tw_one (A B : LB Y) (y : Y) (p q : A.ι × B.ι) (hp : y ∈ A.U p.1 ⊓ B.U p.2)
    (hq : y ∈ A.U q.1 ⊓ B.U q.2) :
    gm (𝟙 Y) y (A.U p.1 ⊓ B.U p.2 ⊓ (A.U q.1 ⊓ B.U q.2)) ((tw A B 1).g p q) =
      gm (𝟙 Y) y _ (A.g p.1 q.1) * gm (𝟙 Y) y _ (B.g p.2 q.2) := by
  refine (gm_div (pw B (-1)) A (𝟙 Y) y p q ⟨hp, hq⟩).trans ?_
  congr 1
  change (gm (𝟙 Y) y (B.U p.2 ⊓ B.U q.2) (B.g p.2 q.2 ^ (-1 : ℤ)))⁻¹ = _
  rw [zpow_neg_one, map_inv, inv_inv]

def chartTw (M : LB X) (p q : Y ⟶ X) :
    ChartPull (tw (M.pull p) (M.pull q) 1) (LB.LinComb M (K := Fin 2) ![p, q] ![1, 1]) (𝟙 Y) :=
  have le : ∀ a : (M.pull p).ι × (M.pull q).ι, (M.pull p).U a.1 ⊓ (M.pull q).U a.2 ≤
      LB.wchart M (K := Fin 2) ![p, q] ![a.1 PUnit.unit, a.2 PUnit.unit] := fun a y hy =>
    Set.mem_iInter.2 fun k => by
      fin_cases k
      exacts [mem_pull.1 hy.1, mem_pull.1 hy.2]
  { idx := fun a => ![a.1 PUnit.unit, a.2 PUnit.unit]
    le := le
    g := fun y a b ha hb => by
      refine (gm_tw_one (M.pull p) (M.pull q) y a b ha hb).trans (Eq.trans ?_
        (gm_linComb M _ _ (𝟙 Y) y _ _ (le a ha) (le b hb)).symm)
      rw [gm_pull_g M p (𝟙 Y) y _ _ ha.1 hb.1, gm_pull_g M q (𝟙 Y) y _ _ ha.2 hb.2, Fin.prod_univ_two]
      exact congrArg₂ (· * ·) (zpow_one _).symm (zpow_one _).symm }

def chartTwTriv (N : LB Y) (q : Y ⟶ Y') :
    ChartPull (tw N ((Inh.trivLB Y').pull q) 1) N (𝟙 Y) where
  idx a := a.1
  le _ _ hy := hy.1
  g y a b ha hb := by
    refine (gm_tw_one N ((Inh.trivLB Y').pull q) y a b ha hb).trans ?_
    rw [Inh.linComb_triv_g, map_one, _root_.mul_one]

def chartInv (M : LB X) :
    ChartPull (pw M (-1)) (LB.LinComb M (K := PUnit) (fun _ => 𝟙 X) fun _ => -1) (𝟙 X) :=
  have le : ∀ i : M.ι, M.U i ≤ LB.wchart M (K := PUnit) (fun _ => 𝟙 X) fun _ => i := fun _ _ hy =>
    Set.mem_iInter.2 fun _ => hy
  { idx := fun i _ => i
    le := le
    g := fun y i j hi hj => by
      refine Eq.trans ?_ (gm_linComb M _ _ (𝟙 X) y _ _ (le i hi) (le j hj)).symm
      rw [Fintype.prod_unique, Category.id_comp]
      exact map_zpow _ _ _ }

theorem nontrivial_sec_of_lbIso {L M : LB X} (hL : L.IsLB) (hM : M.IsLB) (h : LBIso L M)
    (hn : Nontrivial (LB.Sec L)) : Nontrivial (LB.Sec M) := by
  obtain ⟨w, hw⟩ := h
  exact (((SecOn.topEquiv L).symm ≪≫ₗ SecOn.congr hL hM w hw ⊤) ≪≫ₗ
    SecOn.topEquiv M).injective.nontrivial

theorem nontrivial_sec_pull [IsIntegral X] (M : LB X) (e : X ⟶ X) [IsIso e]
    (hn : Nontrivial (LB.Sec M)) : Nontrivial (LB.Sec (M.pull e)) := by
  rw [TrivLocus.nontrivial_sec_iff] at hn ⊢
  obtain ⟨σ, i, hi⟩ := hn
  obtain ⟨x, hx⟩ := TrivLocus.nonempty_of_ne_zero hi
  obtain ⟨y, rfl⟩ := e.homeomorph.surjective x
  have hy : y ∈ (M.pull e).U fun _ => i := mem_pull.2 hx
  refine ⟨SecOn.topEquiv _ (SecOn.pullLE M e ⊤ ⊤ le_top (GlobalTheory.LB.ofSec σ ⊤)), fun _ => i, ?_⟩
  refine (SecOn.topEquiv_f _ _).trans_ne ?_
  refine TrivLocus.rs_ne_zero _ ⟨y, hy⟩ ?_
  refine (SecOn.coord_pullLE e le_top (GlobalTheory.LB.ofSec σ ⊤) fun _ => i).trans_ne ?_
  refine TrivLocus.rs_ne_zero (U := e ⁻¹ᵁ (⊤ ⊓ M.U i)) (V := ⊤ ⊓ (M.pull e).U fun _ => i)
    (fun _ hz => ⟨trivial, mem_pull.1 hz.2⟩) ⟨y, trivial, hy⟩ ?_
  refine (map_ne_zero_iff _ (ConcreteCategory.bijective_of_isIso (e.app _)).1).2 ?_
  exact TrivLocus.rs_ne_zero (U := M.U i) (V := ⊤ ⊓ M.U i) inf_le_right ⟨_, trivial, hx⟩ hi

variable {K : Type} [Field K] {B : Over (Spec (CommRingCat.of K))} [GrpObj B] [IsCommMonObj B]
  {M : LB B.left}

theorem ptCls_mul (hM : M.IsLB) (hu : ∃ u : LB.Gen (abelian₂ B M), u.IsGen)
    {T : Over (Spec (CommRingCat.of K))} (x y : T ⟶ B) :
    ptCls M T (x * y) = ptCls M T x * ptCls M T y ∧ ptCls M T 1 = 1 := by
  have h1 : ptCls M T 1 = 1 := by
    obtain ⟨i, hi⟩ := exists_chart hM (η[B].left (IsLocalRing.closedPoint K))
    have := (hasGen_iff hM (K := PUnit) (fun _ => (1 : T ⟶ B).left) fun _ => 1).1
      (AbSquare.exists_gen_of_mem_chart hM _ _ (fun _ => i) fun _ z => by
        change η[B].left ((toUnit T).left z) ∈ _
        have : (toUnit T).left z = IsLocalRing.closedPoint K :=
          Subsingleton.elim (α := PrimeSpectrum K) _ _
        rw [this]; exact hi)
    rwa [Fintype.prod_unique, zpow_one] at this
  refine ⟨?_, h1⟩
  have h := (hasGen_iff hM _ _).1 (MulPull.HasGen.pull hu (lift x y).left)
  have h' := (prod_square (lift x y) (fst B B) (snd B B) (cls M)).symm.trans h
  rw [lift_fst, lift_snd] at h'
  change ptCls M T (x * y) * (ptCls M T x)⁻¹ * (ptCls M T y)⁻¹ * ptCls M T 1 = 1 at h'
  rw [h1, _root_.mul_one, mul_inv_eq_one, mul_inv_eq_iff_eq_mul, _root_.mul_comm (ptCls M T y)] at h'
  exact h'

theorem lbIso_pull_mul (hM : M.IsLB) (hu : ∃ u : LB.Gen (abelian₂ B M), u.IsGen) :
    LBIso (M.pull μ[B].left) (tw (M.pull (fst B B).left) (M.pull (snd B B).left) 1) := by
  refine LBIso.chartPull (chartPullId _) (chartTw M _ _) ((lbIso_iff hM _ _ _ _).2 ?_)
  have h := (ptCls_mul hM hu (fst B B) (snd B B)).1
  have e : fst B B * snd B B = μ[B] := by rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  rw [e] at h
  rw [Fintype.prod_unique, Fin.prod_univ_two]
  exact (zpow_one _).trans (h.trans (congrArg₂ (· * ·) (zpow_one _).symm (zpow_one _).symm))

theorem lbIso_pull_inv (hM : M.IsLB) (hu : ∃ u : LB.Gen (abelian₂ B M), u.IsGen) :
    LBIso (M.pull (𝟙 B : B ⟶ B)⁻¹.left) (pw M (-1)) := by
  refine LBIso.chartPull (chartPullId _) (chartInv M) ((lbIso_iff hM _ _ _ _).2 ?_)
  obtain ⟨h, h1⟩ := ptCls_mul hM hu (𝟙 B : B ⟶ B)⁻¹ (𝟙 B)
  rw [inv_mul_cancel, h1] at h
  rw [Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_neg_one]
  exact eq_inv_of_mul_eq_one_left h.symm


omit [IsCommMonObj B] in
theorem isIntegral_left (hB : IsAbelianScheme B) : IsIntegral B.left :=
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ B.hom hB.smooth
    hB.geomConnected
  GeometricallyIntegral.geometrically_isIntegral (f := B.hom) _ _ _ (IsPullback.of_id_fst (f := B.hom))

theorem subsingleton_sec (hB : IsAbelianScheme B) (hM : M.IsLB) (hu : ∃ u : LB.Gen (abelian₂ B M), u.IsGen)
    (hn : ¬ Triv M) : Subsingleton (LB.Sec M) := by
  have := isIntegral_left hB
  have := hB.proper
  refine not_nontrivial_iff_subsingleton.1 fun h => hn ?_
  have hi : IsIso (𝟙 B : B ⟶ B)⁻¹ := by
    have e : (𝟙 B : B ⟶ B)⁻¹ ≫ (𝟙 B : B ⟶ B)⁻¹ = 𝟙 B := by
      rw [GrpObj.comp_inv, Category.comp_id, inv_inv]
    exact ⟨_, e, e⟩
  have : IsIso (𝟙 B : B ⟶ B)⁻¹.left := inferInstanceAs (IsIso ((Over.forget _).map (𝟙 B : B ⟶ B)⁻¹))
  exact (TrivLocus.triv_iff (isField_of_universallyClosed K B.hom) M hM.cover).2
    ⟨h, nontrivial_sec_of_lbIso (LB.isLB_pull hM _) (isLB_pw hM _) (lbIso_pull_inv hM hu)
      (nontrivial_sec_pull M _ h)⟩

def homologyZeroEquiv {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) (N : LB X) {κ : Type}
    [LinearOrder κ] {D : κ → X.Opens} (hc : ⨆ i, D i = ⊤) :
    (cechLB f N D).homology 0 ≃ₗ[R] SecOnR f N ⊤ :=
  (cechHomologyZeroIso (secCube f N D)).toLinearEquiv.trans
    ((LinearEquiv.ofEq (LinearMap.ker (GlobalTheory.Cube.d (secCube f N D) (0 + 1)))
      (LinearMap.ker ((cechLB f N D).d 0 1).hom) (by rw [cechLB_d f N D 0]; rfl)).trans
      (CechOne.kerEquiv N f (fun _ => le_top) hc.ge).symm)

theorem exists_fin_affine_cover (X : Scheme.{0}) [CompactSpace X] :
    ∃ (n : ℕ) (D : Fin n → X.Opens), (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ := by
  obtain ⟨s, hs, e⟩ := (isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens
    (U := (Set.univ : Set X))).1 ⟨isCompact_univ, isOpen_univ⟩
  obtain ⟨n, ⟨φ⟩⟩ := Finite.exists_equiv_fin (α := s) (h := hs)
  refine ⟨n, fun i => (φ.symm i).1.1, fun i => (φ.symm i).1.2, top_unique fun x _ => ?_⟩
  obtain ⟨U, hU, hx⟩ := Set.mem_iUnion₂.1 (e.le (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨φ ⟨U, hU⟩, show x ∈ (φ.symm (φ ⟨U, hU⟩)).1.1 by
    rw [Equiv.symm_apply_apply]; exact hx⟩

theorem eq_zero_of_conv (h o : ℕ → ℕ) (h0 : h 0 = 0) (o0 : o 0 ≠ 0)
    (e : ∀ n, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, h x.1 * o x.2 = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, h x.1 * h x.2)
    (n : ℕ) : h n = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hr : ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, h x.1 * h x.2 = 0 := Finset.sum_eq_zero fun x hx => by
      have hx := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
      rcases Nat.eq_zero_or_pos x.2 with h2 | h2
      · rw [h2, h0, mul_zero]
      · rw [ih x.1 (by omega), zero_mul]
    have := Finset.sum_eq_zero_iff.1 ((e n).trans hr) (n, 0) (by simp)
    exact (mul_eq_zero.1 this).resolve_right o0


omit [IsCommMonObj B] in
theorem isPullback_mul_snd : IsPullback μ[B].left (snd B B).left B.hom B.hom := by
  have e : fst B B * snd B B = μ[B] := by rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  let α : B ⊗ B ≅ B ⊗ B :=
    { hom := lift (fst B B * snd B B) (snd B B)
      inv := lift (fst B B * (snd B B)⁻¹) (snd B B)
      hom_inv_id := by
        ext1
        · simp [MonObj.comp_mul, GrpObj.comp_inv]
        · simp
      inv_hom_id := by
        ext1
        · simp [MonObj.comp_mul]
        · simp }
  refine (IsPullback.of_hasPullback B.hom B.hom).of_iso ((Over.forget _).mapIso α).symm (Iso.refl _)
    (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · rw [← e]
    exact congrArg (·.left) (show fst B B ≫ 𝟙 B = α.inv ≫ (fst B B * snd B B) by
      simp [α, MonObj.comp_mul])
  · exact congrArg (·.left) (show snd B B ≫ 𝟙 B = α.inv ≫ snd B B by simp [α])

theorem acyclic_of_kuenneth
    (kun : ∀ (K : Type) [Field K] (Y Y' Z : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of K)) (f' : Y' ⟶ Spec (CommRingCat.of K)) (p₁ : Z ⟶ Y) (p₂ : Z ⟶ Y') (M : LB Y) (M' : LB Y'), IsPullback p₁ p₂ f f' → M.IsLB → M'.IsLB → IsSeparated f → IsSeparated f' → ∀ (κ₁ : Type) [LinearOrder κ₁] [Fintype κ₁] (U : κ₁ → Y.Opens) (κ₂ : Type) [LinearOrder κ₂] [Fintype κ₂] (W : κ₂ → Y'.Opens) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Z.Opens), (∀ i, IsAffineOpen (U i)) → ⨆ i, U i = ⊤ → (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = ⊤ → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (∀ n, Module.Finite K ((cechLB f M U).homology n)) → (∀ n, Module.Finite K ((cechLB f' M' W).homology n)) → ∀ n, Module.finrank K ((cechLB (p₁ ≫ f) (tw (M.pull p₁) (M'.pull p₂) 1) D).homology n) = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, Module.finrank K ((cechLB f M U).homology x.1) * Module.finrank K ((cechLB f' M' W).homology x.2))
    (hB : IsAbelianScheme B) (hM : M.IsLB)
    (hadd : LBIso (M.pull μ[B].left) (tw (M.pull (fst B B).left) (M.pull (snd B B).left) 1))
    (hs : Subsingleton (LB.Sec M)) {κ : Type} [LinearOrder κ] [Fintype κ] {D : κ → B.left.Opens}
    (hD : ∀ i, IsAffineOpen (D i)) (hc : ⨆ i, D i = ⊤)
    (hfM : ∀ n, Module.Finite K ((cechLB B.hom M D).homology n))
    (hfO : ∀ n, Module.Finite K ((cechLB B.hom (Inh.trivLB _) D).homology n)) :
    (cechLB B.hom M D).Acyclic := by
  have := isIntegral_left hB
  have := hB.proper
  have hO := Inh.trivLB_isLB B.left
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have : CompactSpace (B ⊗ B).left :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst B.hom B.hom)
  obtain ⟨m, E, hE, hEc⟩ := exists_fin_affine_cover (B ⊗ B).left
  have k₁ := kun K _ _ _ _ _ _ _ M _ isPullback_mul_snd hM hO inferInstance inferInstance
    κ D κ D _ E hD hc hD hc hE hEc hfM hfO
  have k₂ := kun K _ _ (B ⊗ B).left _ _ (fst B B).left (snd B B).left M M
    (IsPullback.of_hasPullback B.hom B.hom) hM hM inferInstance inferInstance
    κ D κ D _ E hD hc hD hc hE hEc hfM hfM
  have l₁ := isLB_tw (LB.isLB_pull hM μ[B].left) (LB.isLB_pull hO (snd B B).left) 1
  have l₂ := isLB_tw (LB.isLB_pull hM (fst B B).left) (LB.isLB_pull hM (snd B B).left) 1
  obtain ⟨w, hw⟩ := LBIso.chartPull (chartTwTriv _ (snd B B).left) (chartPullId _) hadd
  rw [Over.w μ[B], ← Over.w (fst B B)] at k₁
  have key := eq_zero_of_conv (fun n => Module.finrank K ((cechLB B.hom M D).homology n))
    (fun n => Module.finrank K ((cechLB B.hom (Inh.trivLB _) D).homology n)) ?_ ?_ fun n =>
      (k₁ n).symm.trans (Eq.trans (LinearEquiv.finrank_eq (HomologicalComplex.homologyMapIso
        (cechLBCongr _ E l₁ l₂ w hw) n).toLinearEquiv) (k₂ n))
  · intro n
    have := hfM n
    rw [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton]
    exact Module.finrank_zero_iff.1 (key n)
  · have : Subsingleton ((cechLB B.hom M D).homology 0) :=
      ((homologyZeroEquiv B.hom M hc).toEquiv.trans (SecOnR.topEquiv B.hom M).toEquiv).subsingleton
    exact Module.finrank_zero_of_subsingleton
  · have : Nontrivial (LB.Sec (Inh.trivLB B.left)) :=
      ((TrivLocus.triv_iff (isField_of_universallyClosed K B.hom) _ hO.cover).1 (triv_trivLB _)).1
    have : Nontrivial ((cechLB B.hom (Inh.trivLB _) D).homology 0) :=
      ((homologyZeroEquiv B.hom _ hc).toEquiv.trans (SecOnR.topEquiv B.hom _).toEquiv).nontrivial
    have := hfO 0
    exact Module.finrank_pos.ne'

end GlobalTheory.PrimVan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecExpandsAtOfIntegralFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtCancelNonzeroScalar
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtCancelNonzeroScalar
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem expandsAt_cancel_scalar : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GeometricallyConnected G.hom] (U : UnifPre I D A G) (k : ℕ) [QuasiCompact G.hom] (r : R), r ≠ 0 → ∀ (σ₀ σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) (f₀ f : ∀ α, D.toPre.SecB k α), (∀ α, (∀ j, (f₀ α).f j = resTop _ (scal D.toPre.P.A.hom r) * (f α).f j)) → (∀ j, (σ₀).f j = resTop _ (scal G.hom r) * (σ).f j) → (∀ e, U.ExpandsAt e k σ₀ f₀) → ∀ e, U.ExpandsAt e k σ f := by
  intro R _ _ I hR D A G _ _ _ U k _ r hr σ₀ σ f₀ f hf hσ hE
  have := hR.1
  exact expandsAt_cancel_of_ne_zero R I D A G U k r hr σ σ₀ f f₀ hσ hf hE

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtCancelNonzeroScalarStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.expandsAt_cancel_nonzero_scalar : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GeometricallyConnected G.hom] (U : UnifPre I D A G) (k : ℕ) [QuasiCompact G.hom] (r : R), r ≠ 0 → ∀ (σ₀ σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) (f₀ f : ∀ α, D.toPre.SecB k α), (∀ α, (∀ j, (f₀ α).f j = resTop _ (scal D.toPre.P.A.hom r) * (f α).f j)) → (∀ j, (σ₀).f j = resTop _ (scal G.hom r) * (σ).f j) → (∀ e, U.ExpandsAt e k σ₀ f₀) → ∀ e, U.ExpandsAt e k σ f := by
  first | exact @GlobalTheory.expandsAt_cancel_scalar | exact GlobalTheory.expandsAt_cancel_scalar | (intros; apply GlobalTheory.expandsAt_cancel_scalar <;> assumption)
end
end

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_sec_expandsAt_of_integral_family : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GeometricallyConnected G.hom] (U : UnifPre I D A G) (k : ℕ) [QuasiCompact G.hom], (∀ F : Fam D.toPre (FractionRing R) k, ∃ s : U.SecK k, U.Expands k s F) → ∀ (F : Fam D.toPre (FractionRing R) k) (f : ∀ α, D.toPre.SecB k α), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (F.s α) (D.toPre.famφB α) (DegPre.famε k) (f α) (DegPre.prB D.toPre (FractionRing R)).left 1) → ∃ σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))), ∀ e, U.ExpandsAt e k σ f := by
  intro R _ _ I hR D A G _ _ _ U k _ hall F f hf
  obtain ⟨s, r, hr, σ₀, f₀, -, hf₀, hE⟩ := hall F
  have hw : (D.toPre.prB (FractionRing R)).left ≫ D.toPre.P.A.hom = (D.toPre.BF (FractionRing R)).hom := Over.w _
  have hm : ∀ α, DVR.SecIsMul D.toPre.P.A.hom r (f₀ α) (f α) := fun α =>
    GlobalTheory.IntegralExpansion.secIsMul_of_secScal D.toPre.P.isLB D.toPre.P.A.hom
      (fun W => GlobalTheory.IntegralExpansion.prB_app_injective D.toPre W) (hf α) (by rw [hw]; exact hf₀ α)
  have hm' : ∀ α, ∀ j, (f₀ α).f j = resTop _ (scal D.toPre.P.A.hom r) * (f α).f j := fun α j => hm α j
  obtain ⟨σ, hσ⟩ := GlobalTheory.sec_div_of_expandsAt R I hR D A G U k r hr σ₀ f₀ f hm' hE
  exact ⟨σ, GlobalTheory.T.expandsAt_cancel_nonzero_scalar R I hR D A G U k r hr σ₀ σ f₀ f hm' hσ hE⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZero
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExpZero

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem sval_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {s : LB.Sec (LB.LinComb L φ ε)} (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s r z J = 0 := by
  refine (gs_eq r z _ (hJ.mem φ r) _).trans ?_
  exact (congrArg _ ((congrArg _ (h _)).trans (map_zero _))).trans (map_zero _)

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ), AdmBase R I → ∀ (s : U.SecK k) (F : Fam D.toPre (FractionRing R) k), (∀ jj, s.f jj = 0) → U.Expands k s F → F = 0 := by
  intro R _ _ I D A G _ _ U k hR s F hs hE
  obtain ⟨hN, -, -, hC⟩ := hR
  have hI : I ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot I
  obtain ⟨r, hr, σ, f, h₁, hf, hE⟩ := hE
  have := U.smooth
  have : Flat G.hom := inferInstance
  have hσ : ∀ j, σ.f j = 0 := fun j => by
    refine ExpInt.generic_app_injective G _ (Eq.trans (fn_ext fun y hy => ?_) (map_zero _).symm)
    obtain ⟨J, hJ, e⟩ := exists_good U.LG.L U.LG.isLB y
      (fun _ : Unit => (𝟙 _ ≫ pullback.fst G.hom (jK R)) ≫ 𝟙 G.left)
      (fun _ => j 0) (fun _ _ _ => rfl) (fun _ => Set.mem_iInter.1 hy 0)
    have ej : ∀ a : Fin 1, J ((𝟙 _ ≫ pullback.fst G.hom (jK R)) ≫ 𝟙 G.left) = j a := fun a => by
      rw [Subsingleton.elim a 0]; exact e ()
    have e₂ := ExpInt.secScal_sval h₁ (𝟙 _) y hJ
    rw [sval_eq_zero hs _ y hJ, mul_zero, sval_of σ _ y J j ej] at e₂
    refine ((gs_pull (𝟙 _) _ y _ hy _).trans e₂).trans ((gs_eq _ y _ hy _).trans ?_).symm
    exact (congrArg _ (map_zero _)).trans (map_zero _)
  have hf0 : ∀ α j, (f α).f j = 0 := fun α => by
    have := D.toPre.P.isAb.smooth
    have := D.toPre.P.isAb.geomConnected
    refine (sec_eq_zero_and_hom_eq_of_thickenings R I hI D.toPre.P.A).1 _
      (DVR.linComb_isLB _ D.toPre.P.isLB _ _) (f α) fun e j => ?_
    refine (ExtDiv.pG_app_eq_zero_iff (U.gt e) _ _).1
      (WeightPf.weightIndep R I D A G U e k σ f (fun j => ?_) (hE e) α j)
    exact (congrArg _ (hσ j)).trans (map_zero _)
  refine fam_ext fun α j => ?_
  refine sec_ext_val D.toPre.P.isLB (s' := SecOps.secZero) (fun y J hJ => ?_) j
  have e₁ := ExpInt.secScal_sval (hf α) (𝟙 _) y hJ
  rw [sval_eq_zero (hf0 α) _ y hJ, ExpInt.gs_scal] at e₁
  have e₃ : 𝟙 _ ≫ (DegPre.BF D.toPre (FractionRing R)).hom =
      ((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R)) ≫ jK R := by
    rw [Category.id_comp, Category.assoc]
    exact (Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)).symm
  rw [e₃] at e₁
  refine Eq.trans ?_ (sval_eq_zero (fun _ => rfl) _ y hJ).symm
  exact (IsUnit.mul_right_eq_zero (ExpInt.isUnit_cst _ y hr)).1 e₁.symm

end GlobalTheory.ExpZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistThroughIso
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistThroughIso
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.TwistCompare

section Abstract

variable {X N Y V S₀ Z : Scheme.{0}} {L : LB X} {M : LB N} {c₀ : Y ⟶ X} {q : Y ⟶ N}

def wv (w : LB.Iso (L.pull c₀) (M.pull q)) (f : Z ⟶ Y) (z : Z) (JL : (Z ⟶ X) → L.ι) (JM : (Z ⟶ N) → M.ι) :
    (Z.presheaf.stalk z)ˣ := GlobalTheory.FieldBaseChange.isoVal w f z (JM (f ≫ q)) (JL (f ≫ c₀))

theorem val_through_iso (hL : L.IsLB) (hM : M.IsLB) {w : LB.Iso (L.pull c₀) (M.pull q)} (hw : w.IsGen)
    (n : X ⟶ Y) (hn : n ≫ c₀ = 𝟙 X) (s m : V ⟶ X) (a : N ⟶ N) (hc : m ≫ n ≫ q = (s ≫ n ≫ q) ≫ a) (k' k : ℤ)
    (b : LB.Gen (LB.LinComb M (K := Fin 2) ![𝟙 N, a] ![k', -k])) (hb : b.IsGen)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![s, m] ![k', -k])) (hα : α.IsGen)
    (p : V ⟶ S₀) (e : S₀ ⟶ V) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    (h₀ : ∀ y JL JM, Good L y JL → Good M y JM → val b (e ≫ s ≫ n ≫ q) y JM =
      wv w (e ≫ s ≫ n) y JL JM ^ k' * wv w (e ≫ m ≫ n) y JL JM ^ (-k) * val α e y JL)
    (r : Z ⟶ V) (z : Z) (JL) (JM) (hJL : Good L z JL) (hJM : Good M z JM) :
    val b (r ≫ s ≫ n ≫ q) z JM =
      wv w (r ≫ s ≫ n) z JL JM ^ k' * wv w (r ≫ m ≫ n) z JL JM ^ (-k) * val α r z JL := by
  obtain ⟨u, hu, hv⟩ := GlobalTheory.ThetaBaseChange.exists_unpull hw n hn rfl
  have hc' : ∀ κ, (![s, m] : Fin 2 → _) κ ≫ n ≫ q = (s ≫ n ≫ q) ≫ (![𝟙 N, a] : Fin 2 → _) κ := fun κ => by
    fin_cases κ
    exacts [(Category.comp_id _).symm, hc]
  obtain ⟨α', hα', hm⟩ := H1.exists_gen_move hM hL u hu ![𝟙 N, a] ![s, m] ![k', -k] (s ≫ n ≫ q) hc' b hb
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ V) (z : Z) (JL) (JM), Good L z JL → Good M z JM →
      val b (r ≫ s ≫ n ≫ q) z JM =
        wv w (r ≫ s ≫ n) z JL JM ^ k' * wv w (r ≫ m ≫ n) z JL JM ^ (-k) * val α' r z JL := by
    intro Z r z JL JM hJL hJM
    have g : ∀ f : V ⟶ X, gw u (r ≫ f) z (JM (r ≫ f ≫ n ≫ q)) (JL (r ≫ f)) = wv w (r ≫ f ≫ n) z JL JM := fun f => by
      rw [hv Z (r ≫ f) z _ _ (hJM (r ≫ f ≫ n ≫ q)) (hJL (r ≫ f)), wv]
      simp only [Category.assoc, hn, Category.comp_id]
    have := hm Z r z (fun κ => JM (r ≫ (![s, m] : Fin 2 → _) κ ≫ n ≫ q)) (fun κ => JL (r ≫ (![s, m] : Fin 2 → _) κ))
      (fun κ => hJM (r ≫ (![s, m] : Fin 2 → _) κ ≫ n ≫ q)) (fun κ => hJL (r ≫ (![s, m] : Fin 2 → _) κ))
    rw [Fin.prod_univ_two, g, g] at this
    rw [val_of b _ z JM (fun κ => JM (r ≫ (![s, m] : Fin 2 → _) κ ≫ n ≫ q))
      (fun κ => by rw [hc', Category.assoc])]
    exact this
  rw [key Z r z JL JM hJL hJM]
  refine congrArg _ (gen_unique hL p e he hp hα' hα (fun y J hJ => ?_) Z r z JL hJL)
  choose J' hJ' using fun ψ : S₀ ⟶ N => exists_chart hM (ψ y)
  exact mul_left_cancel ((key _ e y J J' hJ hJ').symm.trans (h₀ y J J' hJ hJ'))

end Abstract

section Rig

variable {S Z : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}

abbrev rval (rig : LB.Gen (L.pull (eSec A))) (r : Z ⟶ (𝟙_ (Over S)).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) :
    (Z.presheaf.stalk z)ˣ := val (L := L) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig r z J

theorem val_rigT {T : Over S} (rig : LB.Gen (L.pull (eSec A))) (k : ℤ) (r : Z ⟶ T.left) {y : Z} {J} (hJ : Good L y J) :
    val (rigT A L rig T k) r y J = rval rig (r ≫ T.hom) y J ^ k := by
  have hy := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec A) r
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ((gm_res _ y _ hy _).trans ?_))
  exact gm_pull r T.hom y (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => J (r ≫ T.hom ≫ eSec A)))
    (rigT_le A L _ hy) _

theorem exists_two (hL : L.IsLB) {rig : LB.Gen (L.pull (eSec A))} (hr : rig.IsGen) (a : A.left ⟶ A.left) (k' k : ℤ)
    (β : LB.Gen (LB.LinComb L (K := Fin 3) ![𝟙 _, a, (1 : A ⟶ A).left] ![k', -k, k - k'])) (hβ : β.IsGen) :
    ∃ b : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 _, a] ![k', -k]), b.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ A.left) (z : Z) (J), Good L z J →
        val b r z J = val β r z J * rval rig (r ≫ A.hom) z J ^ (k' - k) := by
  obtain ⟨b, hb, hv⟩ := exists_gen hL (φ' := ![𝟙 _, a]) (ε' := ![k', -k]) (fun U _ h => by
      have e : (1 : A ⟶ A).left = A.hom ≫ eSec A := rfl
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Fin.prod_univ_three, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val, e]
      rw [_root_.mul_assoc, ← zpow_add, sub_add_sub_cancel, sub_self, zpow_zero, _root_.mul_one])
    (LB.mulGen L _ _ _ _ β (rigT A L rig A (k' - k)))
    (mulGen_isGen _ _ _ _ _ _ _ hβ (GlobalTheory.NormTheta.rigT_isGen hr _))
  exact ⟨b, hb, fun Z r z J hJ => (hv Z r z J hJ).trans ((val_mul hJ _ _ _).trans
    (congrArg _ (val_rigT rig _ r hJ)))⟩

end Rig

theorem alg_origin {M : Type} [CommGroup M] {w r g : M} (k' k : ℤ) (h : w * r = g) :
    1 * g ^ (k' - k) = w ^ k' * w ^ (-k) * r ^ (k' - k) := by
  rw [← h, _root_.one_mul, mul_zpow, ← zpow_add, sub_eq_add_neg]

theorem dualNumber_unit_mul_decomposition {M : Type} [CommRing M] {w w' α b : Mˣ} {v v' t t' : M} {k' k : ℕ}
    (h₁ : v' = (w ^ k').val * t') (h₂ : v = (w' ^ k).val * t) (h₃ : t' = α.val * t)
    (h₄ : b = w ^ (k' : ℤ) * w' ^ (-(k : ℤ)) * α) : v' = v * b.val := by
  have e : w ^ k' * α = w' ^ k * b := by
    rw [h₄, zpow_neg, zpow_natCast, zpow_natCast, mul_comm (w ^ k') _⁻¹, _root_.mul_assoc, mul_inv_cancel_left]
  rw [h₁, h₂, h₃, ← _root_.mul_assoc, ← Units.val_mul, e, Units.val_mul, mul_right_comm]

theorem twist_through_iso : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (E : EndU U) (F : Type) [Field F] [Algebra (FractionRing R) F] (k' k : ℕ) (β : LB.Gen (LB.LinComb U.LG.L (K := Fin 3) ![𝟙 _, E.aG.left, (1 : G ⟶ G).left] ![(k' : ℤ), -(k : ℤ), (k : ℤ) - k'])), β.IsGen → LB.Gen.Corr U.LG.L _ _ _ _ (LB.pullGen U.LG.L _ _ β (eSec G)) (LB.oneGen U.LG.L) → ∀ (w₀ : W0 U) (ρ), NormW U w₀ ρ → ∀ (ψ : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)) (m : (TFK (R := R) F ⊗ A.A) ⟶ A.A) (hm : ψ ≫ snd _ _ = m), ψ ≫ fst _ _ = fst _ _ → m = snd _ _ ≫ E.aA → ∀ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, m.left] ![(k' : ℤ), -(k : ℤ)])), α.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := R) F) ((k' : ℤ) - k)) → ∀ (t : SecA A F k) (t' : SecA A F k') (v : U.SecGF F k) (v' : U.SecGF F k'), GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left k (snd (TFK (R := R) F) A.A).left (U.genF F).left t (UnifPre.gFK (G := G) F) (𝟙 _) v → GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left k' (snd (TFK (R := R) F) A.A).left (U.genF F).left t' (UnifPre.gFK (G := G) F) (𝟙 _) v' → IsTwistPull A.A A.L ψ m hm k' k α t t' → ∀ (y : (UnifPre.GF (G := G) F).left) (J), Good U.LG.L y J → sval v' (𝟙 _) y J = sval v (TFK (R := R) F ◁ (Over.pullback (jK R)).map E.aG).left y J * (val β (UnifPre.gFK (G := G) F) y J * val (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rig (UnifPre.gFK (G := G) F ≫ G.hom) y J ^ ((k' : ℤ) - k)).val := by
  intro hG R _ _ I D A G _ _ U E F _ _ k' k β hβ nβ w₀ ρ hw ψ m hm hψ hm' α hα nα t t' v v' H H' HT y J hJ
  have := U.gen_hom
  have := E.homA
  have := E.homG
  obtain ⟨b, hb, vb⟩ := exists_two U.LG.isLB U.LG.rigGen E.aG.left (k' : ℤ) (k : ℤ) β hβ
  have hn : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id]; rfl
  have hn' : U.gen.hom.left ≫ U.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, Iso.hom_inv_id]; rfl
  have f₁ : ((Over.pullback (jK R)).map E.aG).left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G.hom (jK R) ≫ E.aG.left := pullback.lift_fst _ _ _
  have f₂ : E.aA ≫ U.gen.inv = U.gen.inv ≫ (Over.pullback (jK R)).map E.aG := by
    rw [Iso.comp_inv_eq, Category.assoc, E.ext, Iso.inv_hom_id_assoc]
  have f₃ : m.left ≫ U.gen.inv.left =
      ((snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left) ≫ ((Over.pullback (jK R)).map E.aG).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, hm', Category.assoc, f₂, Category.assoc]
  have hc : m.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      ((snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R)) ≫ E.aG.left :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) f₃).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) f₁).trans (by simp only [Category.assoc]))))
  have o₀ : eSec A.A ≫ U.gen.inv.left = eSec ((Over.pullback (jK R)).obj G) := by
    rw [← EvalZero.eK_gen U, Category.assoc, hn', Category.comp_id]
  have o₁ : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left =
      jFK (R := R) F ≫ eSec ((Over.pullback (jK R)).obj G) := by
    rw [← Category.assoc, ← Over.comp_left, ptSecT, lift_snd, ← o₀]; rfl
  have o₂ : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ m.left ≫ U.gen.inv.left =
      jFK (R := R) F ≫ eSec ((Over.pullback (jK R)).obj G) := by
    rw [← Category.assoc, ← Over.comp_left, hm', ptSecT, lift_snd_assoc, MonObj.one_comp, ← o₀]; rfl
  have o₃ : (jFK (R := R) F ≫ eSec ((Over.pullback (jK R)).obj G)) ≫ U.gen.hom.left = jFK (R := R) F ≫ eSec A.A :=
    (Category.assoc _ _ _).trans (congrArg _ (EvalZero.eK_gen U))
  have o₄ : (jFK (R := R) F ≫ eSec ((Over.pullback (jK R)).obj G)) ≫ pullback.fst G.hom (jK R) =
      (jFK (R := R) F ≫ jK R) ≫ eSec G :=
    (Category.assoc _ _ _).trans ((congrArg _ EvalZero.eK_fst).trans (Category.assoc _ _ _).symm)
  have o₅ : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫
      pullback.fst G.hom (jK R) = (jFK (R := R) F ≫ jK R) ≫ eSec G :=
    Eq.trans (Eq.trans (by simp only [Category.assoc]) (congrArg (· ≫ _) o₁)) o₄
  have o₆ : ((jFK (R := R) F ≫ jK R) ≫ eSec G) ≫ G.hom = jFK (R := R) F ≫ jK R :=
    (Category.assoc _ _ _).trans ((congrArg _ (Over.w η[G])).trans (Category.comp_id _))
  obtain ⟨JA, hA⟩ : ∃ JA, Good A.L y JA := by
    choose J' hJ' using fun χ : (UnifPre.GF (G := G) F).left ⟶ A.A.left => exists_chart A.isLB (χ y)
    exact ⟨J', hJ'⟩
  have key := val_through_iso A.isLB U.LG.isLB hw.1 U.gen.inv.left hn (snd (TFK (R := R) F) A.A).left m.left
    E.aG.left hc k' k b hb α hα (fst (TFK (R := R) F) A.A).left (ptSecT A.A 1).left
    (by rw [← Over.comp_left, ptSecT, lift_fst]; rfl) (surj_fst hG A.isAb _) (fun z JL JM hL hM => by
      have a₁ := (val_pull hM β (eSec G) (jFK (R := R) F ≫ jK R)).symm.trans
        ((val_corr hM nβ (jFK (R := R) F ≫ jK R)).trans (val_one _))
      have a₂ := (val_pull hL α _ (𝟙 _)).symm.trans ((val_corr hL nα (𝟙 _)).trans (val_rigT ρ _ _ hL))
      rw [Category.id_comp, Category.id_comp] at a₂
      have a₃ : wv w₀ (jFK (R := R) F ≫ eSec ((Over.pullback (jK R)).obj G)) z JL JM * rval ρ (jFK (R := R) F) z JL =
          rval U.LG.rig (jFK (R := R) F ≫ jK R) z JM := by
        refine Units.ext (Eq.trans ?_ (EvalZero.normW_ext U F hw z hL hM))
        rw [← o₃, ← o₄]
        rfl
      rw [o₅, o₁, o₂, vb _ _ z JM hM]
      refine (congrArg₂ (· * ·) a₁ (congrArg (fun x => rval U.LG.rig x z JM ^ ((k' : ℤ) - k)) o₆)).trans ?_
      exact (alg_origin _ _ a₃).trans (congrArg _ a₂.symm)) (U.genF F).left y JA J hA hJ
  have g₁ : (U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left =
      (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
    rw [← Over.comp_left, ← Over.comp_left, lift_snd_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have g₂ : (U.genF F).left ≫ m.left ≫ U.gen.inv.left = (TFK (R := R) F ◁ (Over.pullback (jK R)).map E.aG).left ≫
      (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, hm', Category.assoc, f₂, lift_snd_assoc, Category.assoc,
      Iso.hom_inv_id_assoc, whiskerLeft_snd]
  have g₃ : (U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      UnifPre.gFK (G := G) F := Eq.trans (by simp only [Category.assoc]) (congrArg (· ≫ _) g₁)
  have g₄ : (U.genF F).left ≫ ψ.left = (TFK (R := R) F ◁ (Over.pullback (jK R)).map E.aG).left ≫ (U.genF F).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [Category.assoc, hψ, Category.assoc, lift_fst, whiskerLeft_fst]
    · rw [Category.assoc, hm, hm', Category.assoc, lift_snd, lift_snd_assoc, whiskerLeft_snd_assoc, E.ext,
        Category.assoc]
  rw [g₃, g₁, g₂, vb _ _ y J hJ] at key
  have b₁ := GlobalTheory.BoxExpansion.isoRel_val H' (𝟙 _) y hA hJ
  have b₂ := GlobalTheory.BoxExpansion.isoRel_val H (TFK (R := R) F ◁ (Over.pullback (jK R)).map E.aG).left y hA hJ
  have b₃ := twist_val HT (U.genF F).left y hA
  rw [Category.comp_id, Category.id_comp, Category.id_comp] at b₁
  rw [Category.comp_id, ← g₄] at b₂
  exact dualNumber_unit_mul_decomposition b₁ b₂ b₃ key

end GlobalTheory.UT.TwistCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistThroughIsoStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.endU_twist_of_iso : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (E : EndU U) (F : Type) [Field F] [Algebra (FractionRing R) F] (k' k : ℕ) (β : LB.Gen (LB.LinComb U.LG.L (K := Fin 3) ![𝟙 _, E.aG.left, (1 : G ⟶ G).left] ![(k' : ℤ), -(k : ℤ), (k : ℤ) - k'])), β.IsGen → LB.Gen.Corr U.LG.L _ _ _ _ (LB.pullGen U.LG.L _ _ β (eSec G)) (LB.oneGen U.LG.L) → ∀ (w₀ : W0 U) (ρ), NormW U w₀ ρ → ∀ (ψ : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)) (m : (TFK (R := R) F ⊗ A.A) ⟶ A.A) (hm : ψ ≫ snd _ _ = m), ψ ≫ fst _ _ = fst _ _ → m = snd _ _ ≫ E.aA → ∀ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, m.left] ![(k' : ℤ), -(k : ℤ)])), α.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := R) F) ((k' : ℤ) - k)) → ∀ (t : SecA A F k) (t' : SecA A F k') (v : U.SecGF F k) (v' : U.SecGF F k'), GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left k (snd (TFK (R := R) F) A.A).left (U.genF F).left t (UnifPre.gFK (G := G) F) (𝟙 _) v → GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left k' (snd (TFK (R := R) F) A.A).left (U.genF F).left t' (UnifPre.gFK (G := G) F) (𝟙 _) v' → IsTwistPull A.A A.L ψ m hm k' k α t t' → ∀ (y : (UnifPre.GF (G := G) F).left) (J), Good U.LG.L y J → sval v' (𝟙 _) y J = sval v (TFK (R := R) F ◁ (Over.pullback (jK R)).map E.aG).left y J * (val β (UnifPre.gFK (G := G) F) y J * val (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rig (UnifPre.gFK (G := G) F ≫ G.hom) y J ^ ((k' : ℤ) - k)).val := by
  first | exact @GlobalTheory.UT.TwistCompare.twist_through_iso | exact GlobalTheory.UT.TwistCompare.twist_through_iso | (intros; apply GlobalTheory.UT.TwistCompare.twist_through_iso <;> assumption)
end
end
