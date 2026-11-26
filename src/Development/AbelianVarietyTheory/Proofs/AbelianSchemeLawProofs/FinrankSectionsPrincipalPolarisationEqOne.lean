module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechCohomologyFinrank
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsOfCubeBundleGenerator

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FinrankPrincipalPolarisationSectionModuleLeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FinrankPrincipalPolarisationSectionModuleLeOne
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.PrincipalSections

theorem le_one_of_convolution (a b : ℕ → ℕ) (g : ℕ)
    (h : ∀ n, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, a x.1 * b x.2 = if n = g then 1 else 0) :
    a 0 ≤ 1 := by
  have hg := h g
  rw [if_pos rfl] at hg
  obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hg.trans_ne one_ne_zero)
  have hb : 1 ≤ b x.2 := Nat.one_le_iff_ne_zero.2 (right_ne_zero_of_mul hx)
  have h₁ : a 0 * b x.2 ≤ ∑ y ∈ Finset.HasAntidiagonal.antidiagonal x.2, a y.1 * b y.2 :=
    Finset.single_le_sum (f := fun y : ℕ × ℕ => a y.1 * b y.2) (a := (0, x.2))
      (fun _ _ => Nat.zero_le _) (by simp)
  have h₂ : (if x.2 = g then 1 else 0) ≤ 1 := by split_ifs <;> omega
  exact (Nat.le_mul_of_pos_right _ hb).trans (h₁.trans ((h x.2).le.trans h₂))

theorem exists_fin_affine_cover (X : Scheme.{0}) [CompactSpace X] :
    ∃ (n : ℕ) (D : Fin n → X.Opens), (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ := by
  obtain ⟨s, hs', hs⟩ := isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
    (⟨isCompact_univ, isOpen_univ⟩ : IsCompact (Set.univ : Set X) ∧ IsOpen (Set.univ : Set X))
  have := hs'.fintype
  let e := (Fintype.equivFin s).symm
  refine ⟨_, fun i => (e i).1.1, fun i => (e i).1.2, ?_⟩
  rw [e.iSup_comp (g := fun i : s => i.1.1)]
  ext1
  simpa using hs.symm

theorem isPullback_mul_snd {S : Scheme.{0}} (A : Over S) [GrpObj A] :
    IsPullback (lift (fst A A ≫ 𝟙 A) (snd A A) ≫ μ[A]).left (snd A A).left A.hom A.hom := by
  let e : A ⊗ A ≅ A ⊗ A :=
    { hom := lift (fst A A * snd A A) (snd A A)
      inv := lift (fst A A * (snd A A)⁻¹) (snd A A)
      hom_inv_id := by
        apply CartesianMonoidalCategory.hom_ext
        · simp [MonObj.comp_mul, GrpObj.comp_inv]
        · simp
      inv_hom_id := by
        apply CartesianMonoidalCategory.hom_ext
        · simp [MonObj.comp_mul]
        · simp }
  have h : IsPullback (fst A A).left (snd A A).left A.hom A.hom := IsPullback.of_hasPullback _ _
  refine h.of_iso ((Over.forget S).mapIso e).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    (by simp) (by simp)
  · change (fst A A).left ≫ 𝟙 _ = (e.inv ≫ lift (fst A A ≫ 𝟙 A) (snd A A) ≫ μ[A]).left
    rw [Category.comp_id, Category.comp_id, ← Hom.mul_def]
    simp [e, MonObj.comp_mul]
  · change (snd A A).left ≫ 𝟙 _ = (e.inv ≫ snd A A).left
    simp [e]

noncomputable def chartTwInv {X Y : Scheme.{0}} (L : LB X) (a b : Y ⟶ X) :
    ChartPull (tw (L.pull a) ((pw L (-1)).pull b) 1)
      (LB.LinComb L (K := Fin 2) ![a, b] ![1, -1]) (𝟙 Y) :=
  have le : ∀ p : (PUnit → L.ι) × (PUnit → L.ι), (tw (L.pull a) ((pw L (-1)).pull b) 1).U p ≤
      LB.wchart L ![a, b] ![p.1 PUnit.unit, p.2 PUnit.unit] := fun p y hy =>
    Set.mem_iInter.2 (Fin.forall_fin_two.2
      ⟨Set.mem_iInter.1 hy.1 PUnit.unit, Set.mem_iInter.1 hy.2 PUnit.unit⟩)
  { idx := fun p => ![p.1 PUnit.unit, p.2 PUnit.unit]
    le := le
    g := fun y p q hp hq => by
      refine Eq.trans ?_ (gm_linComb L _ _ (𝟙 Y) y _ _ (le p hp) (le q hq)).symm
      have e₁ := gm_pull_g L a (𝟙 Y) y p.1 q.1 hp.1 hq.1
      have e₂ := (gm_pull_g (pw L (-1)) b (𝟙 Y) y p.2 q.2 hp.2 hq.2).trans (map_zpow _ _ (-1 : ℤ))
      have e₃ : gm (𝟙 Y) y _ ((pw ((pw L (-1)).pull b) (-1)).g p.2 q.2) =
          (gm (𝟙 Y) y _ (((pw L (-1)).pull b).g p.2 q.2)) ^ (-1 : ℤ) := map_zpow _ _ _
      refine ((gm_div (pw ((pw L (-1)).pull b) (-1)) (L.pull a) (𝟙 Y) y p q ⟨hp, hq⟩).trans
        (congrArg₂ (fun u v => u * v⁻¹) e₁ (e₃.trans (congrArg (· ^ (-1 : ℤ)) e₂)))).trans ?_
      rw [Fin.prod_univ_two]
      refine congrArg₂ (· * ·) (zpow_one _).symm ?_
      rw [zpow_neg_one, inv_inv]
      rfl }

theorem finrank_secOnR_le_one (K : Type) [Field K] [IsAlgClosed K]
    (P : PolAV (Spec (CommRingCat.of K))) : Module.finrank K (SecOnR P.A.hom P.L ⊤) ≤ 1 := by
  obtain ⟨⟨hproj, hsep⟩, -⟩ := GlobalTheory.AbProj.abelian_projective_baseChange K P
  have hpb := isPullback_mul_snd P.A
  have := P.isAb.proper
  have hqc : QuasiCompact P.A.hom := inferInstance
  have hqc₂ : QuasiCompact (snd P.A P.A).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hpb hqc
  have : CompactSpace P.A.left := QuasiCompact.compactSpace_of_compactSpace P.A.hom
  have : CompactSpace (P.A ⊗ P.A).left := QuasiCompact.compactSpace_of_compactSpace (snd P.A P.A).left
  obtain ⟨n, U, hU, hUc⟩ := exists_fin_affine_cover P.A.left
  obtain ⟨m, D, hD, hDc⟩ := exists_fin_affine_cover (P.A ⊗ P.A).left
  have hL' := isLB_pw P.isLB (-1)
  obtain ⟨e⟩ := cechLB_homology_zero_equiv_sections K _ P.A.hom P.L _ U hUc
  rw [← e.finrank_eq]
  refine le_one_of_convolution (fun i => Module.finrank K ((cechLB P.A.hom P.L U).homology i))
    (fun i => Module.finrank K ((cechLB P.A.hom (pw P.L (-1)) U).homology i)) P.g fun k => ?_
  rw [← GlobalTheory.T.finrank_cechLB_homology_extProd_alt K _ _ _ _ _ _ _ P.L (pw P.L (-1)) hpb P.isLB hL' hsep hsep _ U _ U _ D hU hUc hU hUc
    hD hDc (cechLB_homology_finite_of_affine_cover K _ _ _ _ U P.isLB hsep hproj hU hUc)
    (cechLB_homology_finite_of_affine_cover K _ _ _ _ U hL' hsep hproj hU hUc) k, ← GlobalTheory.T.mumford_bundle_cech_cohomology_finrank K P _ D hD hDc k, Over.w]
  have hF : (translDiff P.A P.L (𝟙 P.A)).IsLB := DVR.linComb_isLB _ P.isLB _ _
  obtain ⟨w, hw⟩ := lbIso_of_chartPull (chartTwInv P.L _ _) hF
  exact (HomologicalComplex.homologyMapIso (cechLBCongr _ D
    (isLB_tw (pull_isLB P.isLB _) (pull_isLB hL' _) 1) hF w hw) k).toLinearEquiv.finrank_eq

noncomputable def chartPullOne {X Y : Scheme.{0}} (L : LB X) (a : Y ⟶ X) :
    ChartPull (L.pull a) (LB.LinComb L (K := Fin 1) (fun _ => a) (fun _ => 1)) (𝟙 Y) :=
  have le : ∀ p : PUnit → L.ι, (L.pull a).U p ≤
      LB.wchart L (fun _ : Fin 1 => a) (fun _ => p PUnit.unit) := fun _ _ hy =>
    Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy PUnit.unit
  { idx := fun p _ => p PUnit.unit
    le := le
    g := fun y p q hp hq => by
      refine (gm_pull_g L a (𝟙 Y) y p q hp hq).trans
        (Eq.trans ?_ (gm_linComb L _ _ (𝟙 Y) y _ _ (le p hp) (le q hq)).symm)
      rw [Fin.prod_univ_one, zpow_one] }

theorem finrank_secM_le_one : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))), Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L 1 (baseOver (Spec (CommRingCat.of K)))) ≤ 1 := by
  intro K _ _ P
  let T := baseOver (Spec (CommRingCat.of K))
  let f' : (T ⊗ P.A).left ⟶ Spec (CommRingCat.of K) := (fst T P.A).left
  have : IsIso (snd T P.A).left := inferInstanceAs (IsIso (pullback.snd (𝟙 _) P.A.hom))
  have w : (snd T P.A).left ≫ P.A.hom = f' ≫ Spec.map (CommRingCat.ofHom (RingHom.id K)) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact (pullback.condition (f := 𝟙 _) (g := P.A.hom)).symm
  let e₁ : SecOnR P.A.hom P.L ⊤ ≃ₗ[K] SecOnR f' (P.L.pull (snd T P.A).left) ⊤ :=
    LinearEquiv.ofBijective (SecOnR.pull P.L w ⊤ ⊤ le_top)
      (SecOn.pullLE_bijective_of_le_opensRange P.L (snd T P.A).left
        (Scheme.Hom.opensRange_of_isIso _).ge le_top le_top)
  have hM : (LPow P.A P.L 1 T).IsLB := DVR.linComb_isLB _ P.isLB _ _
  obtain ⟨u, hu⟩ := lbIso_of_chartPull (chartPullOne P.L (snd T P.A).left) hM
  let e₂ : SecOnR f' (P.L.pull (snd T P.A).left) ⊤ ≃ₗ[K] SecOnR f' (LPow P.A P.L 1 T) ⊤ :=
    SecOnR.linEquiv f' (SecOn.congr (pull_isLB P.isLB _) hM u hu ⊤)
  refine le_of_eq_of_le ?_ ((e₁ ≪≫ₗ e₂).finrank_eq.symm.trans_le (finrank_secOnR_le_one K P))
  refine congrArg Cardinal.toNat (rank_eq_of_equiv_equiv (R := K) (R' := Γ(T.left, ⊤))
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    ((SecOnR.of f' _ ⊤).symm.toAddEquiv.trans (GlobalTheory.LB.globalEquivSecM P.A P.L 1 T))
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv)
    fun r s => ?_).symm
  refine Eq.trans ?_ (GlobalTheory.LB.globalEquivSecM_smul P.A P.L 1 T _ ((SecOnR.of f' _ ⊤).symm s))
  exact congrArg (fun c : Γ((T ⊗ P.A).left, ⊤) =>
    GlobalTheory.LB.globalEquivSecM P.A P.L 1 T (c • (SecOnR.of f' _ ⊤).symm s))
    (rs_self le_top _)

end GlobalTheory.PrincipalSections
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FinrankPrincipalPolarisationSectionModuleLeOneStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_principalPolarisation_sectionModule_le_one : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))), Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L 1 (baseOver (Spec (CommRingCat.of K)))) ≤ 1 := by
  first | exact @GlobalTheory.PrincipalSections.finrank_secM_le_one | exact GlobalTheory.PrincipalSections.finrank_secM_le_one | (intros; apply GlobalTheory.PrincipalSections.finrank_secM_le_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.OneLeFinrankSecM
section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.OneLeFinrankSecM
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.PolSection

open GlobalTheory.SecGrowth

variable {X Y : Scheme.{0}} (L : LB X) (π : Y ⟶ X)

theorem wchart_le_tw (N t : ℤ) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => π) j ≤
      (tw (L.pull π) (pw (L.pull π) N) t).U ((fun _ => j 0), (fun _ => j 0)) :=
  le_inf (wchart_le_unit L π j) (wchart_le_unit L π j)

theorem lcg_tw (N t : ℤ) (j j' : Fin 1 → L.ι) :
    LB.lcg L (K := Fin 1) (fun _ => π) (fun _ => 1 + N * t) j j' =
      res (inf_le_inf (wchart_le_tw L π N t j) (wchart_le_tw L π N t j'))
        ((tw (L.pull π) (pw (L.pull π) N) t).g ((fun _ => j 0), (fun _ => j 0))
          ((fun _ => j' 0), (fun _ => j' 0))) := by
  have h := SecOn.res_tw_g (M := L.pull π) (H := pw (L.pull π) N) t (fun _ => j 0) (fun _ => j' 0)
    (fun _ => j 0) (fun _ => j' 0) (inf_le_inf (wchart_le_tw L π N t j) (wchart_le_tw L π N t j'))
    (inf_le_inf (wchart_le_unit L π j) (wchart_le_unit L π j'))
    (inf_le_inf (wchart_le_unit L π j) (wchart_le_unit L π j'))
  refine Eq.trans ?_ h.symm
  change _ = res (inf_le_inf (wchart_le_unit L π j) (wchart_le_unit L π j'))
        (LB.lcg L (K := PUnit) (fun _ => π) (fun _ => 1) (fun _ => j 0) (fun _ => j' 0)) *
      res (inf_le_inf (wchart_le_unit L π j) (wchart_le_unit L π j'))
        (LB.lcg L (K := PUnit) (fun _ => π) (fun _ => 1) (fun _ => j 0) (fun _ => j' 0) ^ N) ^ t
  rw [map_zpow, ← zpow_mul, ← zpow_one_add, LB.lcg_pull, LB.res_res, LB.lcg, Fintype.prod_unique]
  rfl

theorem exists_sec_ne_zero [IsIntegral Y] (hL : L.IsLB) (N t : ℤ)
    (σ : LB.Sec (tw (L.pull π) (pw (L.pull π) N) t)) (i : (tw (L.pull π) (pw (L.pull π) N) t).ι)
    (hi : σ.f i ≠ 0) :
    ∃ τ : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => 1 + N * t)), τ.f ≠ 0 := by
  refine ⟨transSec (M := tw (L.pull π) (pw (L.pull π) N) t)
    (M' := LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => 1 + N * t))
    (fun j => ((fun _ => j 0), (fun _ => j 0))) (wchart_le_tw L π N t) (lcg_tw L π N t) σ, fun h => hi ?_⟩
  obtain ⟨y⟩ : Nonempty Y := inferInstance
  have hc := (LB.isLB_linComb hL (K := Fin 1) (fun _ => π) (fun _ => 1 + N * t)).cover
  have hy : y ∈ ⨆ j, (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => 1 + N * t)).U j := by
    rw [hc]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  haveI : Nonempty (LB.wchart L (fun _ : Fin 1 => π) j) := ⟨⟨y, hj⟩⟩
  exact sec_eq_zero σ (wchart_le_tw L π N t j) (congrFun h j) i

theorem exists_sq_eq (K : Type) [Field K] (N : ℕ) (hN : 1 ≤ N) (t₀ : ℤ) :
    ∃ (n : ℕ) (t : ℤ), (n : K) ≠ 0 ∧ t₀ ≤ t ∧ ((n ^ 2 * 1 : ℕ) : ℤ) = 1 + N * t := by
  have key : ∃ a : ℕ, t₀ ≤ a ∧ ((1 + N * a : ℕ) : K) ≠ 0 := by
    obtain ⟨p, hp⟩ := CharP.exists K
    rcases CharP.char_is_prime_or_zero K p with h | h
    · refine ⟨p * t₀.toNat, ?_, ?_⟩
      · have h1 : t₀.toNat ≤ p * t₀.toNat := Nat.le_mul_of_pos_left _ h.pos
        have h2 := Int.self_le_toNat t₀
        omega
      · push_cast
        rw [CharP.cast_eq_zero K p]
        simp
    · subst h
      haveI := CharP.charP_to_charZero K
      exact ⟨t₀.toNat, Int.self_le_toNat t₀, Nat.cast_ne_zero.2 (by omega)⟩
  obtain ⟨a, ha, hK⟩ := key
  refine ⟨1 + N * a, 2 * a + N * a ^ 2, hK, ?_, ?_⟩
  · have h1 : (0 : ℤ) ≤ a := Int.natCast_nonneg a
    have h2 : (0 : ℤ) ≤ N * a ^ 2 := by positivity
    omega
  · push_cast
    ring

theorem one_le_finrank_secM :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))), 1 ≤ Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L 1 (baseOver (Spec (CommRingCat.of K)))) := by
  intro K _ _ P
  let T : Over (Spec (CommRingCat.of K)) := baseOver (Spec (CommRingCat.of K))
  let π : (T ⊗ P.A).left ⟶ P.A.left := (snd T P.A).left
  let f : (T ⊗ P.A).left ⟶ Spec (CommRingCat.of K) := (fst T P.A).left
  have hpb : IsPullback π f P.A.hom (𝟙 _) := (IsPullback.of_hasPullback T.hom P.A.hom).flip
  obtain ⟨N, hN, m, s, hH, hs⟩ :=
    GlobalTheory.AbLaw.polAV_veryAmpleBy GlobalTheory.laws_without_cohomology.2.2.1 _ P K (𝟙 _) _ π f hpb
  have hgi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ P.A.hom
    P.isAb.smooth P.isAb.geomConnected
  haveI : IsIntegral (T ⊗ P.A).left := GeometricallyIntegral.geometrically_isIntegral _ _ _ hpb
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.exists_high_twist_section_ne_zero K _ f _ m s (P.L.pull π) hH (LB.isLB_pull P.isLB π) hs
  obtain ⟨n, t, hn, ht, hnt⟩ := exists_sq_eq K N hN t₀
  obtain ⟨σ, i, hi⟩ := ht₀ t ht
  obtain ⟨τ, hτ⟩ := exists_sec_ne_zero P.L π P.isLB N t σ i hi
  have hbig : Nontrivial (SecM P.A P.L (1 + N * t) T) :=
    ⟨SecM.ofSec P.A τ, 0, fun h => hτ (congrArg Subtype.val h)⟩
  rw [← hnt] at hbig
  obtain ⟨e⟩ := (GlobalTheory.AbLaw.FromCube.all_of_cubeGen CubeAssembly.cube_gen).2.2.2.2.2.2.2.2.2 K P n 1 hn le_rfl
  have hone : Nontrivial (SecM P.A P.L ((1 : ℕ) : ℤ) T) := by
    by_contra h
    haveI := not_nontrivial_iff_subsingleton.1 h
    exact not_subsingleton _ e.toEquiv.subsingleton
  have hfin := (CubeAssembly.sections_growth K P).1 1
  letI : Field Γ(T.left, ⊤) :=
    (isField_of_isIntegral_of_subsingleton (Spec (CommRingCat.of K))).toField
  exact Module.finrank_pos (R := Γ(T.left, ⊤)) (M := SecM P.A P.L ((1 : ℕ) : ℤ) T)

end GlobalTheory.PolSection
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.OneLeFinrankSecMStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_le_finrank_secM_one_of_isAlgClosed : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))), 1 ≤ Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L 1 (baseOver (Spec (CommRingCat.of K)))) := by
  first | exact @GlobalTheory.PolSection.one_le_finrank_secM | exact GlobalTheory.PolSection.one_le_finrank_secM | (intros; apply GlobalTheory.PolSection.one_le_finrank_secM <;> assumption)
end
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw

theorem finrank_sections_principal_polarisation_eq_one :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))),
      Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)
        (SecM P.A P.L 1 (baseOver (Spec (CommRingCat.of K)))) = 1 :=
  fun K _ _ P => le_antisymm (GlobalTheory.T.finrank_principalPolarisation_sectionModule_le_one K P) (GlobalTheory.T.one_le_finrank_secM_one_of_isAlgClosed K P)

end GlobalTheory.AbLaw
