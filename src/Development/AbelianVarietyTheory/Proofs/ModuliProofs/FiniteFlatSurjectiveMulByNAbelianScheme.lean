module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTripleGlueTwoOpens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeneratorExtendsFromGenericFibreValuationRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalPolarisationVolumeFormSymmetricAmple
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetAbelianLocusOfGoodReduction
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.OActSpreadFromDenseFibresAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SerreVanishingVeryAmple

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteFlatSurjectiveMulByNAbelianScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteFlatSurjectiveMulByNAbelianScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.MulAmple

open GlobalTheory.MulPull GlobalTheory.MulFinite TopologicalSpace

theorem gs_sec_trans {X Z : Scheme.{0}} {H : LB X} (s : LB.Sec H) (p : Z ⟶ X) (z : Z) {k k' : H.ι}
    (hk : p z ∈ H.U k) (hk' : p z ∈ H.U k') :
    gs p z (H.U k) (s.f k) =
      (gm p z (H.U k ⊓ H.U k') (H.g k k')).val * gs p z (H.U k') (s.f k') := by
  have hm : p z ∈ H.U k ⊓ H.U k' := ⟨hk, hk'⟩
  exact (gs_res p z _ hm _).symm.trans ((congrArg (gs p z _) (s.compat k k')).trans
    ((gs_mul p z _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit p z _ hm _) (gs_res p z _ hm _))))

theorem isUnit_gs_sec {X Z : Scheme.{0}} {H : LB X} (s : LB.Sec H) (p : Z ⟶ X) (z : Z) {k : H.ι}
    (hk : p z ∈ H.U k) : IsUnit (gs p z (H.U k) (s.f k)) ↔ p z ∈ Out.nonzeroLocus s := by
  refine ⟨fun h => Opens.mem_iSup.2 ⟨k, (isUnit_gs p z _ hk _).1 h⟩, fun h => ?_⟩
  obtain ⟨k', hk'⟩ := Opens.mem_iSup.1 h
  have h' : p z ∈ H.U k' := X.basicOpen_le _ hk'
  rw [gs_sec_trans s p z hk h']
  exact (Units.isUnit _).mul ((isUnit_gs p z _ h' _).2 hk')

theorem units_mul_pow_mul_inv_cancel {R : Type} [CommRing R] (g h t : Rˣ) (x y : R) (a b : ℕ) :
    (g.val * x) ^ a * (h.val * y) ^ b * ((g ^ a * h ^ b * t)⁻¹).val = x ^ a * y ^ b * (t⁻¹).val := by
  have e : g ^ a * h ^ b * (g ^ a * h ^ b * t)⁻¹ = t⁻¹ := by
    rw [mul_inv, mul_inv_cancel_left]
  have e' : g.val ^ a * h.val ^ b * ((g ^ a * h ^ b * t)⁻¹).val = (t⁻¹).val := congrArg Units.val e
  rw [← e']; ring

theorem exists_fn₂ {X Z : Scheme.{0}} {H : LB X} (hH : H.IsLB) (p q : Z ⟶ X) (a b : ℕ) (ha : a ≠ 0)
    (hb : b ≠ 0) (h : HasGen H (K := Fin 2) ![p, q] ![(a : ℤ), (b : ℤ)]) (s s' : LB.Sec H) :
    ∃ c : Γ(Z, ⊤), Z.basicOpen c = p ⁻¹ᵁ Out.nonzeroLocus s ⊓ q ⁻¹ᵁ Out.nonzeroLocus s' := by
  obtain ⟨α, hα⟩ := h
  let V : (Fin 2 → H.ι) → Z.Opens := fun j => LB.wchart H (K := Fin 2) ![p, q] j
  have l₁ : ∀ j, V j ≤ p ⁻¹ᵁ H.U (j 0) := fun j z hz => Set.mem_iInter.1 hz 0
  have l₂ : ∀ j, V j ≤ q ⁻¹ᵁ H.U (j 1) := fun j z hz => Set.mem_iInter.1 hz 1
  obtain ⟨u, hu⟩ : ∃ u : ∀ j, Γ(Z, V j), ∀ j z, z ∈ V j → gs (𝟙 Z) z (V j) (u j) =
      gs p z (H.U (j 0)) (s.f (j 0)) ^ a * gs q z (H.U (j 1)) (s'.f (j 1)) ^ b *
        ((gm (𝟙 Z) z (V j) (α.s j))⁻¹).val := by
    refine ⟨fun j => (p.appLE _ _ (l₁ j)).hom (s.f (j 0)) ^ a *
      (q.appLE _ _ (l₂ j)).hom (s'.f (j 1)) ^ b * (show Γ(Z, V j) from ((α.s j)⁻¹).val), fun j z hz => ?_⟩
    refine (gs_mul (𝟙 Z) z (V j) hz _ _).trans (congrArg₂ (· * ·)
      ((gs_mul (𝟙 Z) z (V j) hz _ _).trans (congrArg₂ (· * ·) ((gs_pow (𝟙 Z) z (V j) hz _ _).trans ?_)
      ((gs_pow (𝟙 Z) z (V j) hz _ _).trans ?_))) ?_)
    · exact congrArg (· ^ a) (gs_appLE p z _ _ _ hz _)
    · exact congrArg (· ^ b) (gs_appLE q z _ _ _ hz _)
    · exact (gs_unit (𝟙 Z) z _ hz _).trans (congrArg Units.val (map_inv _ _))
  have hex : ∀ z : Z, ∃ j, z ∈ V j := fun z => by
    obtain ⟨k, hk⟩ := exists_chart hH (p z)
    obtain ⟨l, hl⟩ := exists_chart hH (q z)
    refine ⟨![k, l], Set.mem_iInter.2 fun i => ?_⟩
    fin_cases i
    · exact hk
    · exact hl
  have hcov : (⊤ : Z.Opens) ≤ iSup V := fun z _ => Opens.mem_iSup.2 (hex z)
  obtain ⟨c, hc, -⟩ := Z.sheaf.existsUnique_gluing' V ⊤ (fun j => homOfLE le_top) hcov u
    (fun j j' => fn_ext (V := V j ⊓ V j') fun z hz => by
      refine (gs_res (𝟙 Z) z inf_le_left hz _).trans
        (Eq.trans ?_ (gs_res (𝟙 Z) z inf_le_right hz _).symm)
      have e := gen_trans hα (𝟙 Z) z (j := j) (j' := j') hz.1 hz.2
      have t : trF (L := H) (K := Fin 2) ![p, q] ![(a : ℤ), (b : ℤ)] (𝟙 Z) z j j' =
          gm p z (H.U (j 0) ⊓ H.U (j' 0)) (H.g (j 0) (j' 0)) ^ a *
            gm q z (H.U (j 1) ⊓ H.U (j' 1)) (H.g (j 1) (j' 1)) ^ b := by
        rw [trF, Fin.prod_univ_two, ← zpow_natCast, ← zpow_natCast]
        rfl
      rw [t] at e
      rw [hu j z hz.1, hu j' z hz.2, gs_sec_trans s p z (l₁ j hz.1) (l₁ j' hz.2),
        gs_sec_trans s' q z (l₂ j hz.1) (l₂ j' hz.2)]
      exact (congrArg (fun w : (Z.presheaf.stalk z)ˣ => _ * (w⁻¹).val) e).trans
        (units_mul_pow_mul_inv_cancel _ _ _ _ _ a b))
  refine ⟨c, ?_⟩
  ext z
  obtain ⟨j, hj⟩ := hex z
  have k₁ : gs (𝟙 Z) z ⊤ c = gs (𝟙 Z) z (V j) (u j) :=
    (gs_res (𝟙 Z) z le_top hj c).symm.trans (congrArg (gs (𝟙 Z) z (V j)) (hc j))
  refine (isUnit_gs (𝟙 Z) z ⊤ trivial c).symm.trans ?_
  rw [k₁, hu j z hj, Units.isUnit_mul_units, IsUnit.mul_iff, isUnit_pow_iff ha, isUnit_pow_iff hb,
    isUnit_gs_sec s p z (l₁ j hj), isUnit_gs_sec s' q z (l₂ j hj)]
  rfl

theorem hasGen_of_chart {X Z : Scheme.{0}} {H : LB X} (hH : H.IsLB) (p : Z ⟶ X) (j₀ : H.ι)
    (h : ∀ z, p z ∈ H.U j₀) : HasGen H (K := Fin 1) ![p] ![1] := by
  have le : ∀ j : Fin 1 → H.ι, LB.wchart H (K := Fin 1) ![p] j ≤ p ⁻¹ᵁ (H.U (j 0) ⊓ H.U j₀) :=
    fun j z hz => ⟨Set.mem_iInter.1 hz 0, h z⟩
  refine ⟨⟨fun j => res (le j) (pullU p _ (H.g (j 0) j₀))⟩, fun j j' => unit_ext fun z hz => ?_⟩
  have v : ∀ j : Fin 1 → H.ι, z ∈ LB.wchart H (K := Fin 1) ![p] j →
      gm (𝟙 Z) z _ (res (le j) (pullU p _ (H.g (j 0) j₀))) =
        gm (𝟙 Z ≫ p) z (H.U (j 0) ⊓ H.U j₀) (H.g (j 0) j₀) := fun j hj =>
    (gm_res (𝟙 Z) z (le j) hj _).trans (gm_pull (𝟙 Z) p z _ (le j hj) _)
  refine ((gm_res (𝟙 Z) z _ hz _).trans (v j hz.1)).trans (Eq.symm ?_)
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_linComb H ![p] ![1] (𝟙 Z) z j j' hz.1 hz.2)
    ((gm_res (𝟙 Z) z _ hz _).trans (v j' hz.2))).trans ?_)
  rw [Fin.prod_univ_one]
  change gm (𝟙 Z ≫ p) z (H.U (j 0) ⊓ H.U (j' 0)) (H.g (j 0) (j' 0)) ^ (1 : ℤ) * _ = _
  rw [zpow_one]
  exact gm_cocycle hH (𝟙 Z ≫ p) z (le j hz.1).1 (le j' hz.2).1 (h z)

section

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}

theorem hasGen_pow₂ (hL : L.IsLB) (hcube : HasGen L (thφ A (x3 A)) thε) {T : Over S} (x : T ⟶ A)
    (hone : HasGen L (K := Fin 1) ![(1 : T ⟶ A).left] ![1]) (n : ℕ) :
    HasGen L (K := Fin 3) ![x.left, (x⁻¹).left, (x ^ n).left]
      ![(n : ℤ) ^ 2 + n, (n : ℤ) ^ 2 - n, -2] := by
  induction n using Nat.twoStepInduction with
  | zero =>
    exact (hone.inv.mul hone.inv).of_formEq hL (fun U _ h => by
      simp [Fin.prod_univ_succ, Fintype.prod_sum_type, zpow_ofNat, sq])
  | one =>
    exact (hone.mul hone.inv).of_formEq hL (fun U _ h => by
      simp [Fin.prod_univ_succ, Fintype.prod_sum_type, zpow_ofNat])
  | more n ih₀ ih₁ =>
    have hc := hcube.pull (lift (x ^ (n + 1)) (lift x x⁻¹)).left
    refine ((hc.mul hc).mul ((ih₁.mul ih₁).mul (ih₀.inv.mul
      ((hone.mul hone).mul (hone.mul hone))))).of_formEq hL (fun U _ h => ?_)
    refine ((Fintype.prod_sum_type _).trans
      (congrArg₂ (· * ·) ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·)
        (prod_cub (x ^ (n + 1)) x x⁻¹ h) (prod_cub (x ^ (n + 1)) x x⁻¹ h))) rfl)).trans ?_
    have e₁ : x ^ (n + 1) * x * x⁻¹ = x ^ (n + 1) := mul_inv_cancel_right _ _
    have e₂ : x ^ (n + 1) * x = x ^ (n + 2) := (pow_succ x (n + 1)).symm
    have e₃ : x ^ (n + 1) * x⁻¹ = x ^ n := by rw [pow_succ, mul_inv_cancel_right]
    rw [e₁, e₂, e₃, mul_inv_cancel]
    apply Additive.ofMul.injective
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ,
      Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, ofMul_mul, ofMul_inv,
      ofMul_zpow, ofMul_one]
    push_cast
    module

theorem isFinite_pow [IsProper A.hom] [IsAffine S] (hL : L.IsLB) (hcube : HasGen L (thφ A (x3 A)) thε)
    {I : Type} (s : I → LB.Sec L) (hcov : ⨆ i, Out.nonzeroLocus (s i) = ⊤)
    (hs : ∀ i, IsAffineOpen (Out.nonzeroLocus (s i))) (n : ℕ) (hn : 1 ≤ n) :
    IsFinite ((𝟙 A) ^ n : A ⟶ A).left := by
  rcases hn.eq_or_lt with rfl | hn
  · rw [pow_one, Over.id_left]; infer_instance
  generalize hm : ((𝟙 A) ^ n : A ⟶ A) = m
  have hw : m.left ≫ A.hom = A.hom := Over.w m
  have : IsProper (m.left ≫ A.hom) := by rw [hw]; infer_instance
  have : IsProper m.left := .of_comp _ A.hom
  suffices LocallyQuasiFinite m.left from .of_isProper_of_locallyQuasiFinite _
  refine .of_fiberToSpecResidueField _ fun y => ?_
  have hy : ∀ z, m.left (m.left.fiberι y z) = y := fun z =>
    (m.left.range_fiberι y).le ⟨z, rfl⟩
  let T : Over S := Over.mk (m.left.fiberι y ≫ A.hom)
  let x : T ⟶ A := Over.homMk (m.left.fiberι y) rfl
  have hxm : x ^ n = x ≫ m := by rw [← hm, MonObj.comp_pow, Category.comp_id]
  have hxi : x⁻¹ = x ≫ GrpObj.inv := rfl
  obtain ⟨j₀, hj₀⟩ := exists_chart hL y
  obtain ⟨j₁, hj₁⟩ := exists_chart hL ((1 : A ⟶ A).left y)
  have h₀ : HasGen L (K := Fin 1) ![(x ^ n).left] ![1] := hasGen_of_chart hL _ j₀ fun z => by
    rw [hxm]
    exact (congrArg (· ∈ L.U j₀) (hy z)).mpr hj₀
  have h₁ : HasGen L (K := Fin 1) ![(1 : T ⟶ A).left] ![1] := hasGen_of_chart hL _ j₁ fun z => by
    have e : (1 : T ⟶ A) = x ≫ m ≫ (1 : A ⟶ A) := by rw [MonObj.comp_one, MonObj.comp_one]
    rw [e]
    exact (congrArg (fun w => (1 : A ⟶ A).left w ∈ L.U j₁) (hy z)).mpr hj₁
  have hle : n ≤ n ^ 2 := Nat.le_self_pow two_ne_zero n
  have h₂ : HasGen L (K := Fin 2) ![x.left, (x⁻¹).left]
      ![((n ^ 2 + n : ℕ) : ℤ), ((n ^ 2 - n : ℕ) : ℤ)] :=
    ((hasGen_pow₂ hL hcube x h₁ n).mul (h₀.mul h₀)).of_formEq hL fun U _ h => by
      apply Additive.ofMul.injective
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ,
        Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, ofMul_mul,
        ofMul_zpow, ofMul_one]
      push_cast [hle]
      module
  have key := fun i : I × I => exists_fn₂ hL x.left (x⁻¹).left _ _ (by positivity)
    (by have : n < n ^ 2 := by nlinarith
        omega) h₂ (s i.1) (s i.2)
  choose c hc using key
  have := isAffineHom_fromSpecResidueField A.left y
  have hx : IsAffineHom x.left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom.{0})
      (IsPullback.of_hasPullback m.left (A.left.fromSpecResidueField y)).flip this
  have : IsIso (GrpObj.inv : A ⟶ A).left :=
    inferInstanceAs (IsIso ((Over.forget _).map (GrpObj.inv : A ⟶ A)))
  have hx' : IsAffineHom (x⁻¹).left := by
    rw [hxi, Over.comp_left]; infer_instance
  have hp : IsProper (m.left.fiberToSpecResidueField y) :=
    inferInstanceAs (IsProper (pullback.snd m.left (A.left.fromSpecResidueField y)))
  have hsep : T.left.IsSeparated := by
    have : IsSeparated (m.left.fiberToSpecResidueField y ≫ terminal.from _) := inferInstance
    rw [terminal.comp_from] at this
    exact ⟨this⟩
  refine locallyQuasiFinite_of_cover (K := A.left.residueField y)
    (m.left.fiberToSpecResidueField y) c ?_ fun i => ?_
  · refine top_unique fun z _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hcov.ge (Set.mem_univ (x.left z)))
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (hcov.ge (Set.mem_univ ((x⁻¹).left z)))
    exact Opens.mem_iSup.2 ⟨(i, j), (hc (i, j)).ge ⟨hi, hj⟩⟩
  · refine (congrArg IsAffineOpen (hc i)).mpr ?_
    exact ((hs i.1).preimage x.left).inf ((hs i.2).preimage (x⁻¹).left)

end

theorem finite_flat_surjective_pow :
    Out.Laws → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : LB A.left, M.IsLB → Out.RelAmple A M → ∀ n : ℕ, 1 ≤ n → IsFinite ((𝟙 A) ^ n : A ⟶ A).left ∧ Flat ((𝟙 A) ^ n : A ⟶ A).left ∧ Surjective ((𝟙 A) ^ n : A ⟶ A).left := by
  intro hl R _ A _ _ hA M hM hamp n hn
  obtain ⟨d, -, m, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R A M hM).1 hamp
  have hH := isLB_pw hM d
  have := hA.proper
  have := hA.smooth
  have hcube : HasGen (pw M d) (thφ A (x3 A)) thε :=
    GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy hl R A hA ⟨_, hH, m, s, hs⟩ _ hH
  have hf := isFinite_pow hH hcube s hs.1 (fun i => (hs.2 i).1) n hn
  have hm : IsMonHom ((𝟙 A) ^ n : A ⟶ A) := MulN.isMonHom_mulA A n
  have hgeo : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ Sp R),
      Flat ((Over.pullback t).map ((𝟙 A) ^ n : A ⟶ A)).left ∧
        Surjective ((Over.pullback t).map ((𝟙 A) ^ n : A ⟶ A)).left := fun K _ _ t =>
    flat_and_surjective_of_isFinite_abelianEnd
      forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
      (Out.TLinPf.isAb_pullback t A hA) _ inferInstance
      (MorphismProperty.of_isPullback (P := @IsFinite) (MulN.isPullback_baseChange t _) hf)
  exact ⟨hf, flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres _ A A _ inferInstance
    inferInstance inferInstance hf fun K _ _ t => (hgeo K t).1,
    MulN.surjective_of_geomFibres _ fun K _ _ t => (hgeo K t).2⟩

end GlobalTheory.MulAmple
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteFlatSurjectiveMulByNAbelianSchemeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_flat_surjective_mul_by_n_abelianScheme : Out.Laws → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : LB A.left, M.IsLB → Out.RelAmple A M → ∀ n : ℕ, 1 ≤ n → IsFinite ((𝟙 A) ^ n : A ⟶ A).left ∧ Flat ((𝟙 A) ^ n : A ⟶ A).left ∧ Surjective ((𝟙 A) ^ n : A ⟶ A).left := by
  first | exact @GlobalTheory.MulAmple.finite_flat_surjective_pow | exact GlobalTheory.MulAmple.finite_flat_surjective_pow | (intros; apply GlobalTheory.MulAmple.finite_flat_surjective_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianTripleGlueTwoOpenImmersions
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianTripleGlueTwoOpenImmersions
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.TripleGlueMap

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem nonempty_cast {A B : Scheme.{0}} {t : SAB H A} {t' : SAB H B} {f g : A ⟶ B} (h : f = g)
    (m : SABMap t t' f) : Nonempty (SABMap t t' g) := by
  subst h
  exact ⟨m⟩

theorem exists_transport {A B : Scheme.{0}} (e : A ≅ B) (t : SAB H A) :
    ∃ t' : SAB H B, Nonempty (SABMap t' t e.inv) ∧ Nonempty (SABMap t t' e.hom) := by
  have hp := sabPull Out.CubePf.cubePull e.inv t
  have m := hp.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  obtain ⟨i, -⟩ := GlobalTheory.ObjMaps.exists_sab_id t
  obtain ⟨i'⟩ := nonempty_cast (by simp) i (g := e.hom ≫ e.inv)
  obtain ⟨k, -⟩ := GlobalTheory.ObjMaps.exists_sab_cancel m i'
  exact ⟨_, ⟨m⟩, ⟨k⟩⟩

theorem mem_genericPoints_iso {A B : Scheme.{0}} (e : A ≅ B) (x : A) (hx : e.hom x ∈ genericPoints B) :
    x ∈ genericPoints A := by
  have hx' : closure {Scheme.homeoOfIso e x} ∈ irreducibleComponents B := by
    rw [Scheme.coe_homeoOfIso]
    exact hx
  have key := preimage_mem_irreducibleComponents hx' (Scheme.homeoOfIso e).isOpenEmbedding
    ⟨Scheme.homeoOfIso e x, subset_closure rfl, x, rfl⟩
  rw [(Scheme.homeoOfIso e).preimage_closure, ← Set.image_singleton,
    (Scheme.homeoOfIso e).injective.preimage_image] at key
  exact key

theorem generic_transport {A B : Scheme.{0}} (e : A ≅ B) {t : SAB H A} {t' : SAB H B} (m : SABMap t' t e.inv)
    (h : IsReduced A ∧ genericPoints A ⊆ abLocus t.G) : IsReduced B ∧ genericPoints B ⊆ abLocus t'.G := by
  obtain ⟨hr, hg⟩ := h
  refine ⟨@isReduced_of_isOpenImmersion _ _ e.inv _ hr, ?_⟩
  intro y hy
  have hy' : e.inv y ∈ genericPoints A := by
    apply mem_genericPoints_iso e
    have hyy : e.hom (e.inv y) = y := (Scheme.homeoOfIso e).apply_symm_apply y
    rw [hyy]
    exact hy
  have ha := hg hy'
  simp only [abLocus, Set.mem_setOf_eq] at ha ⊢
  intro K _ _ u hu
  have hp : IsProper (pullback.snd t.G.hom (u ≫ e.inv)) := by
    apply ha K (u ≫ e.inv)
    obtain ⟨p, rfl⟩ := hu
    exact ⟨p, rfl⟩
  have sq := (IsPullback.of_hasPullback t'.G.hom u).paste_horiz m.cart.1
  rw [← sq.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback t.G.hom (u ≫ e.inv))]
  exact (MorphismProperty.cancel_left_of_respectsIso @IsProper _ _).mpr hp

theorem exists_sab_glue_of_isPullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X₀ X₁ X₂ : Scheme.{0}) (ψ₁ : X₁ ⟶ X) (ψ₂ : X₂ ⟶ X) (φ₁ : X₀ ⟶ X₁) (φ₂ : X₀ ⟶ X₂) (t₀ : SAB H X₀) (t₁ : SAB H X₁) (t₂ : SAB H X₂) (_ : SABMap t₀ t₁ φ₁) (_ : SABMap t₀ t₂ φ₂), IsOpenImmersion ψ₁ → IsOpenImmersion ψ₂ → IsPullback φ₁ φ₂ ψ₁ ψ₂ → (∀ x : X, x ∈ Set.range ψ₁ ∨ x ∈ Set.range ψ₂) → (IsReduced X₁ ∧ genericPoints X₁ ⊆ abLocus t₁.G) → (IsReduced X₂ ∧ genericPoints X₂ ⊆ abLocus t₂.G) → ∃ t : SAB H X, Nonempty (SABMap t₁ t ψ₁) ∧ Nonempty (SABMap t₂ t ψ₂) := by
  intro E _ _ _ H X X₀ X₁ X₂ ψ₁ ψ₂ φ₁ φ₂ t₀ t₁ t₂ m₁ m₂ h₁ h₂ sq hcov g₁ g₂
  obtain ⟨t₁', ⟨a₁⟩, ⟨b₁⟩⟩ := exists_transport ψ₁.isoOpensRange t₁
  obtain ⟨t₂', ⟨a₂⟩, ⟨b₂⟩⟩ := exists_transport ψ₂.isoOpensRange t₂
  have G₁ := generic_transport ψ₁.isoOpensRange a₁ g₁
  have G₂ := generic_transport ψ₂.isoOpensRange a₂ g₂
  have hr : Set.range (pullback.fst ψ₁ ψ₂ ≫ ψ₁) = Set.range (ψ₁.opensRange ⊓ ψ₂.opensRange).ι := by
    rw [IsOpenImmersion.range_pullback_to_base_of_left, Scheme.Opens.range_ι]
    simp
  let e₀ : X₀ ≅ (ψ₁.opensRange ⊓ ψ₂.opensRange).toScheme :=
    sq.isoPullback ≪≫ IsOpenImmersion.isoOfRangeEq _ _ hr
  have he₀ : e₀.hom ≫ (ψ₁.opensRange ⊓ ψ₂.opensRange).ι = φ₁ ≫ ψ₁ := by
    simp [e₀]
  obtain ⟨t₀', ⟨a₀⟩, -⟩ := exists_transport e₀ t₀
  obtain ⟨c₁, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp m₁ a₀
  obtain ⟨d₁, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp b₁ c₁
  obtain ⟨c₂, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp m₂ a₀
  obtain ⟨d₂, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp b₂ c₂
  have k₁ : (e₀.inv ≫ φ₁) ≫ ψ₁.isoOpensRange.hom =
      X.homOfLE (inf_le_left : ψ₁.opensRange ⊓ ψ₂.opensRange ≤ ψ₁.opensRange) := by
    rw [← cancel_mono ψ₁.opensRange.ι]
    simp only [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, Scheme.homOfLE_ι]
    rw [← he₀, Iso.inv_hom_id_assoc]
  have k₂ : (e₀.inv ≫ φ₂) ≫ ψ₂.isoOpensRange.hom =
      X.homOfLE (inf_le_right : ψ₁.opensRange ⊓ ψ₂.opensRange ≤ ψ₂.opensRange) := by
    rw [← cancel_mono ψ₂.opensRange.ι]
    simp only [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, Scheme.homOfLE_ι]
    rw [← sq.w, ← he₀, Iso.inv_hom_id_assoc]
  obtain ⟨M₁⟩ := nonempty_cast k₁ d₁
  obtain ⟨M₂⟩ := nonempty_cast k₂ d₂
  have hUV : ψ₁.opensRange ⊔ ψ₂.opensRange = ⊤ := by
    ext x
    simp only [TopologicalSpace.Opens.coe_sup, TopologicalSpace.Opens.coe_top, Set.mem_union,
      Scheme.Hom.coe_opensRange, Set.mem_univ, iff_true]
    exact hcov x
  obtain ⟨t, n₁, n₂, -⟩ := GlobalTheory.TripleGlue.exists_sab_glue E H X _ _ t₁' t₂' t₀' M₁ M₂ hUV G₁ G₂
  obtain ⟨p₁, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp n₁ b₁
  obtain ⟨p₂, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp n₂ b₂
  exact ⟨t, nonempty_cast (Scheme.Hom.isoOpensRange_hom_ι ψ₁) p₁,
    nonempty_cast (Scheme.Hom.isoOpensRange_hom_ι ψ₂) p₂⟩

end GlobalTheory.TripleGlueMap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianTripleGlueTwoOpenImmersionsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelianTriple_glue_two_open_immersions : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X₀ X₁ X₂ : Scheme.{0}) (ψ₁ : X₁ ⟶ X) (ψ₂ : X₂ ⟶ X) (φ₁ : X₀ ⟶ X₁) (φ₂ : X₀ ⟶ X₂) (t₀ : SAB H X₀) (t₁ : SAB H X₁) (t₂ : SAB H X₂) (_ : SABMap t₀ t₁ φ₁) (_ : SABMap t₀ t₂ φ₂), IsOpenImmersion ψ₁ → IsOpenImmersion ψ₂ → IsPullback φ₁ φ₂ ψ₁ ψ₂ → (∀ x : X, x ∈ Set.range ψ₁ ∨ x ∈ Set.range ψ₂) → (IsReduced X₁ ∧ genericPoints X₁ ⊆ abLocus t₁.G) → (IsReduced X₂ ∧ genericPoints X₂ ⊆ abLocus t₂.G) → ∃ t : SAB H X, Nonempty (SABMap t₁ t ψ₁) ∧ Nonempty (SABMap t₂ t ψ₂) := by
  first | exact @GlobalTheory.TripleGlueMap.exists_sab_glue_of_isPullback | exact GlobalTheory.TripleGlueMap.exists_sab_glue_of_isPullback | (intros; apply GlobalTheory.TripleGlueMap.exists_sab_glue_of_isPullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFibres
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.FibreAmple

theorem pw_pw_natCast {X : Scheme.{0}} (H : LB X) (a b : ℕ) :
    pw (pw H a) b = pw H ((a * b : ℕ) : ℤ) := by
  rw [Nat.cast_mul]
  exact congrArg (fun g => (⟨H.ι, H.U, g⟩ : LB X))
    (funext fun i => funext fun j => (zpow_mul (H.g i j) a b).symm)

theorem triv_theta_pull {S S' : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (g : S' ⟶ S)
    (H : LB A.left) (h : Triv (Theta ((Over.pullback g).obj A) (H.pull (pullback.fst A.hom g)))) :
    Triv ((Theta A H).pull (pullback.fst (G3 A).hom g)) := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨u, hu⟩ := GlobalTheory.CubeDescent.exists_gen_comp H (pullback.fst A.hom g) _ _ t ht
  let B := (Over.pullback g).obj A
  let T : Over S' := Over.mk (pullback.snd (G3 A).hom g)
  have hG := isGrpPullback_pullback A g
  let y : Fin 3 → (T ⟶ B) := fun i => Over.homMk
    (pullback.lift (pullback.fst (G3 A).hom g ≫ (x3 A i).left) (pullback.snd (G3 A).hom g)
      (by rw [Category.assoc, Over.w, pullback.condition])) (pullback.lift_snd _ _ _)
  let r : T ⟶ G3 B := lift (y 0) (lift (y 1) (y 2))
  have hr : ∀ i, r ≫ x3 B i = y i := fun i => by fin_cases i <;> simp [r, x3]
  let U : Over.mk (T.hom ≫ g) ⟶ G3 A := Over.homMk (pullback.fst (G3 A).hom g) pullback.condition
  have key : ∀ I : Finset (Fin 3), r.left ≫ (psum B (x3 B) I).left ≫ pullback.fst A.hom g =
      pullback.fst (G3 A).hom g ≫ (psum A (x3 A) I).left := fun I => by
    have e₁ : r ≫ psum B (x3 B) I = psum B y I :=
      (psum_hom (preHom r) (x3 B) I).trans (congrArg (fun z => psum B z I) (funext hr))
    have e₂ := psum_push hG y (x3 A) U (fun i => Over.OverMorphism.ext (pullback.lift_fst _ _ _)) I
    rw [← Category.assoc, ← Over.comp_left, e₁]
    exact e₂
  refine (CubeGen.triv_pull_iff H (thφ A (x3 A)) thε _).2 ?_
  have e : (fun k => pullback.fst (G3 A).hom g ≫ thφ A (x3 A) k) =
      fun k => r.left ≫ thφ B (x3 B) k ≫ pullback.fst A.hom g := funext fun k => (key k.down).symm
  unfold CubeGen.TrivAt
  rw [e]
  exact ⟨_, DVR.pullGen_isGen _ _ _ u hu r.left⟩

theorem exists_ne_zero {X : Scheme.{0}} [Nonempty X] {N : LB X} {I : Type} (s : I → LB.Sec N)
    (h : ⨆ i, Out.nonzeroLocus (s i) = ⊤) : ∃ (σ : LB.Sec N) (k : N.ι), σ.f k ≠ 0 := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have hx : x ∈ ⨆ i, Out.nonzeroLocus (s i) := by rw [h]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
  refine ⟨s i, k, fun e => ?_⟩
  rw [e, Scheme.basicOpen_zero] at hk
  exact hk

theorem relAmple_of_fibres : Out.Laws → ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Ring.DimensionLEOne O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (A : Over (Sp O)) [GrpObj A], IsAbelianScheme A → ∀ M : LB A.left, M.IsLB → Out.RelAmple (Over.mk (pullback.snd A.hom (spMap (algebraMap O K)))) (M.pull (pullback.fst A.hom (spMap (algebraMap O K)))) → Out.RelAmple (Over.mk (pullback.snd A.hom (spMap (IsLocalRing.residue O)))) (M.pull (pullback.fst A.hom (spMap (IsLocalRing.residue O)))) → Out.RelAmple A M := by
  intro hL O K _ _ _ _ _ _ _ _ A _ hA M hM hK hk
  have isLB_pw {Y : Scheme.{0}} {H : LB Y} (hH : H.IsLB) (t : ℤ) :
      (pw H t).IsLB := by
    refine ⟨hH.cover, ?_, ?_⟩
    · intro i
      have h := congrArg (· ^ t) (hH.g_self i)
      simp only [one_zpow, ← map_zpow] at h
      exact h
    · intro i j k
      have h := congrArg (· ^ t) (hH.cocycle i j k)
      simp only [mul_zpow, ← map_zpow] at h
      exact h
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have hB := CubeGen.isAb_baseChange hA (spMap (algebraMap O K))
  obtain ⟨d, hd, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy K _ _ (LB.isLB_pull hM _)).1 hK
  have hH := isLB_pw hM d
  have hproj : IsProjBy ((Over.pullback (spMap (algebraMap O K))).obj A).hom :=
    ⟨_, isLB_pw (LB.isLB_pull hM _) _, n, s, hs⟩
  have cK := triv_theta_pull A _ (pw M d)
    (GlobalTheory.T.theorem_of_cube_projective_abelianScheme_affineBase hL K _ hB hproj _ (LB.isLB_pull hH (pullback.fst A.hom (spMap (algebraMap O K)))))
  have s₂ : Smooth (A ⊗ A).hom := by
    change Smooth (pullback.fst A.hom A.hom ≫ A.hom); infer_instance
  have p₂ : IsProper (A ⊗ A).hom := by
    change IsProper (pullback.fst A.hom A.hom ≫ A.hom); infer_instance
  have c₂ : GeometricallyConnected (A ⊗ A).hom := by
    change GeometricallyConnected (pullback.fst A.hom A.hom ≫ A.hom)
    exact GeometricallyConnected.comp _ _
  have s₃ : Smooth (G3 A).hom := by
    change Smooth (pullback.fst A.hom (A ⊗ A).hom ≫ A.hom); infer_instance
  have p₃ : IsProper (G3 A).hom := by
    change IsProper (pullback.fst A.hom (A ⊗ A).hom ≫ A.hom); infer_instance
  have c₃ : GeometricallyConnected (G3 A).hom := by
    change GeometricallyConnected (pullback.fst A.hom (A ⊗ A).hom ≫ A.hom)
    exact GeometricallyConnected.comp _ _
  have gi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
  have cube : Triv (Theta A (pw M d)) :=
    GlobalTheory.T.generator_extends_from_genericFibre_valuationRing O K _ _ (G3 A).hom _ _ (IsPullback.of_hasPullback _ _) s₃ inferInstance (gi _ _ _ s₃ c₃) _
      (LB.isLB_linComb hH _ _) cK
  have ne : Nonempty ((Over.pullback (spMap (algebraMap O K))).obj A).left :=
    ⟨(η[(Over.pullback (spMap (algebraMap O K))).obj A]).left (default : PrimeSpectrum K)⟩
  have hσ : ∃ (σ : LB.Sec ((pw M d).pull (pullback.fst A.hom (spMap (algebraMap O K))))) (k : _), σ.f k ≠ 0 := by
    have := @exists_ne_zero _ ne _ _ s hs.1
    rw [GlobalTheory.TrivLocus.pull_pw]
    exact this
  obtain ⟨σ, hσ⟩ := hσ
  obtain ⟨-, t, -, -, ht⟩ := GlobalTheory.T.exists_sec_nonzero_on_special_fibre_extending_smul O K _ _ A.hom _ _ (IsPullback.of_hasPullback _ _) hA.smooth
    inferInstance (gi _ _ _ hA.smooth hA.geomConnected) _ hH σ hσ
  have hu := GlobalTheory.T.exists_sections_generate_square_bundle O K A hA _ hH cube t ht
  rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, pw_pw_natCast] at hu
  obtain ⟨m, u, hu⟩ := hu
  have aff := GlobalTheory.T.isAffineOpen_nonzeroLocus_of_fibrewise_ample O _ A.hom M (d * 2) m u (by omega) hA.proper hM hu (fun q hq => by
    by_cases h0 : q = ⊥
    · exact ⟨K, inferInstance, algebraMap O K,
        h0 ▸ (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective O K), hK⟩
    · exact ⟨_, inferInstance, IsLocalRing.residue O,
        IsLocalRing.ker_residue.trans (IsLocalRing.eq_maximalIdeal (hq.isMaximal h0)).symm, hk⟩)
  obtain ⟨e, he, hv⟩ := GlobalTheory.AbLaw.veryAmpleBy_pw_of_affine_loci O _ A.hom _ m u (isLB_pw hM _) hu aff
  rw [pw_pw_natCast] at hv
  exact (GlobalTheory.Unif.relAmple_iff_veryAmpleBy O A M hM).2 ⟨d * 2 * e, Nat.mul_pos (by omega) he, hv⟩

end GlobalTheory.FibreAmple
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingOfUnitBall
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.GoodRedUnitBall

theorem finiteType_closure (s : Set ℂ) (hs : s.Finite) :
    (algebraMap ℤ (Subring.closure s)).FiniteType := by
  have h : Algebra.FiniteType ℤ (Algebra.adjoin ℤ s) := Algebra.FiniteType.adjoin_of_finite hs
  rw [RingHom.finiteType_algebraMap]
  have e : (Algebra.adjoin ℤ s).toSubring = Subring.closure s := by
    rw [Algebra.adjoin_int]; rfl
  refine Algebra.FiniteType.of_surjective (R := ℤ) (A := Algebra.adjoin ℤ s)
    (RingEquiv.subringCongr e).toRingHom.toIntAlgHom (RingEquiv.subringCongr e).surjective

theorem valuationRing_of_unitBall {V C : Type} [CommRing V] [NormedField C] [Algebra V C] (h : IsUnitBall V C) :
    ∃ _ : IsDomain V, ValuationRing V ∧ IsFractionRing V C := by
  have hd : IsDomain V := h.1.isDomain _
  refine ⟨hd, ?_⟩
  have key : ∀ x : C, IsLocalization.IsInteger V x ∨ IsLocalization.IsInteger V x⁻¹ := by
    intro x
    rcases le_total ‖x‖ 1 with hx | hx
    · exact Or.inl ((h.2 x).2 hx)
    · exact Or.inr ((h.2 x⁻¹).2 (by rw [norm_inv]; exact inv_le_one_of_one_le₀ hx))
  have : FaithfulSMul V C := (faithfulSMul_iff_algebraMap_injective V C).2 h.1
  have hf : IsFractionRing V C := by
    refine IsFractionRing.of_field V C fun x => ?_
    rcases key x with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨a, 1, by simp [ha]⟩
    · exact ⟨1, a, by simp [ha]⟩
  exact ⟨(ValuationRing.iff_isInteger_or_isInteger V C).2 key, hf⟩

theorem goodRedExt_unitBall : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N) (l₀ : Level H) (B : BaseModel T l₀) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β), Raises B Y → ∀ (V C : Type) [CommRing V] [NontriviallyNormedField C] [IsUltrametricDist C] [Algebra V C], IsUnitBall V C → Y.GoodRedExt V C := by
  intro hext E _ _ _ H D Xo n N T l₀ B l c O _ β Y hR V C _ _ _ _ hV b y hy ⟨𝒜, _, 𝓛, A, _, φ₁, φ₂, hab, _, _, h₁, h₂, _⟩
  obtain ⟨_, _, _⟩ := valuationRing_of_unitBall hV
  obtain ⟨b₀, r, ν, -, -, ⟨ab⟩⟩ := hR
  have hp : IsProper Y.s := projProper _ _ _ Y.proj
  have hp' : IsProper B.C.s := projProper _ _ _ B.C.proj
  have hE : ValuativeCriterion.Existence Y.s :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed Y.s) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) Y.s).1
  obtain ⟨⟨q⟩⟩ := hE
    { R := V
      K := C
      i₁ := y ≫ Y.j
      i₂ := spMap b
      commSq := ⟨by rw [Category.assoc]; exact hy⟩ }
  obtain ⟨y', hs, hl⟩ : ∃ y' : Sp V ⟶ Y.X, y' ≫ Y.s = spMap b ∧ spMap (algebraMap V C) ≫ y' = y ≫ Y.j :=
    ⟨q.l, q.fac_right, q.fac_left⟩
  obtain ⟨π, hπ⟩ : ∃ π : Y.X ⟶ B.C.X, π = ab.π := ⟨_, rfl⟩
  refine ⟨y', hs, hl, ?_⟩
  have hz : LocallyOfFiniteType (spMap (algebraMap ℤ (RZ H (n * l₀.M) 1))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact finiteType_closure _ (Set.toFinite _)
  have hc : IsGrpPullback Y.t.G B.C.t.G π ab.mu.φ := hπ ▸ ab.mu.cart
  have h₃ := (h₂.comp Y.m.cart).comp hc
  have h₄ : IsGrpPullback A B.C.t.G (spMap (algebraMap V C) ≫ (y' ≫ π)) ((φ₂ ≫ Y.m.φ) ≫ ab.mu.φ) := by
    rw [← Category.assoc, hl]
    exact h₃
  have h₅ := GlobalTheory.T.range_subset_abelianLocus_of_goodReduction hext B.C.X (B.C.s ≫ spMap (algebraMap ℤ (RZ H (n * l₀.M) 1))) B.C.t.G V C (y' ≫ π) 𝒜 A φ₁ _
    inferInstance B.C.t.semi hab h₁ h₄
  rintro _ ⟨x, rfl⟩
  exact (abLocus_pullback abLocusOne B.C.t.semi hc.1 _).1 (h₅ ⟨x, rfl⟩)

end GlobalTheory.GoodRedUnitBall
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HilbertFunctionVanishingIdealVeryAmpleSystem
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HilbertFunctionVanishingIdealVeryAmpleSystem
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV

noncomputable section
namespace GlobalTheory.ZV.HilbFn

theorem exists_forms_basis {K σ : Type} [Field K] [Finite σ] (I : Ideal (MvPolynomial σ K)) (e : ℕ) :
    ∃ G : Fin (Module.finrank K (GlobalTheory.quotPiece I e)) → MvPolynomial σ K, (∀ i, (G i).IsHomogeneous e) ∧
      ∀ F : MvPolynomial σ K, F.IsHomogeneous e → ∃! a : Fin (Module.finrank K (GlobalTheory.quotPiece I e)) → K,
        F - ∑ i, a i • G i ∈ I := by
  classical
  have hQ : ∀ x, x ∈ GlobalTheory.quotPiece I e ↔
      ∃ y, y ∈ MvPolynomial.homogeneousSubmodule σ K e ∧ Ideal.Quotient.mkₐ K I y = x := by
    intro x
    rw [GlobalTheory.quotPiece_natCast, Submodule.mem_map]
    rfl
  have : Module.Finite K (GlobalTheory.quotPiece I e) := by
    rw [GlobalTheory.quotPiece_natCast]
    exact Module.Finite.map _ _
  let b := Module.finBasis K (GlobalTheory.quotPiece I e)
  have hlift : ∀ i, ∃ G : MvPolynomial σ K, G.IsHomogeneous e ∧
      Ideal.Quotient.mkₐ K I G = (b i : MvPolynomial σ K ⧸ I) := fun i =>
    (hQ _).1 (b i).2
  choose G hG hGb using hlift
  have hsum : ∀ a : Fin (Module.finrank K (GlobalTheory.quotPiece I e)) → K,
      Ideal.Quotient.mkₐ K I (∑ i, a i • G i) =
        ((∑ i, a i • b i : GlobalTheory.quotPiece I e) : MvPolynomial σ K ⧸ I) := by
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hGb, Submodule.coe_sum, Submodule.coe_smul]
  refine ⟨G, hG, fun F hF => ?_⟩
  have hF' : Ideal.Quotient.mkₐ K I F ∈ GlobalTheory.quotPiece I e := (hQ _).2 ⟨F, hF, rfl⟩
  have hiff : ∀ a : Fin (Module.finrank K (GlobalTheory.quotPiece I e)) → K,
      F - ∑ i, a i • G i ∈ I ↔ (∑ i, a i • b i) = (⟨_, hF'⟩ : GlobalTheory.quotPiece I e) := by
    intro a
    rw [← Ideal.Quotient.eq, ← Ideal.Quotient.mkₐ_eq_mk K, hsum,
      Subtype.ext_iff, eq_comm]
  refine ⟨fun i => b.repr ⟨_, hF'⟩ i, (hiff _).2 (b.sum_repr _), fun a ha => ?_⟩
  funext i
  rw [← (hiff a).1 ha, b.repr_sum_self]

theorem dimDeg_add {K σ : Type} [Field K] [Finite σ] (I : Ideal (MvPolynomial σ K)) (e : ℕ) :
    dimDeg I e + Module.finrank K (GlobalTheory.quotPiece I e) =
      Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e) := by
  classical
  let H := MvPolynomial.homogeneousSubmodule σ K e
  let f : H →ₗ[K] MvPolynomial σ K ⧸ I := (Ideal.Quotient.mkₐ K I).toLinearMap.comp H.subtype
  have hr : LinearMap.range f = GlobalTheory.quotPiece I e := by
    rw [GlobalTheory.quotPiece_natCast, LinearMap.range_comp, Submodule.range_subtype]
  have hk : LinearMap.ker f = (I.restrictScalars K).comap H.subtype := by
    ext x
    simp [f, LinearMap.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  rw [hr, hk] at hrk
  have hm : Module.finrank K ((I.restrictScalars K).comap H.subtype) =
      Module.finrank K ↥(H ⊓ I.restrictScalars K) := by
    rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype]
  unfold dimDeg
  rw [← hm, add_comm]
  exact hrk

variable {K σ : Type} [Field K] {X : Scheme.{0}}

def toPw (M : LB X) (e : ℕ) (t : (lbPow M e).Sec) : (AbLaw.pw M e).Sec where
  f := fun k => resG X (show M.U k ≤ (lbPow M e).U (fun _ => k) from
    fun _ hy => Set.mem_iInter.2 fun _ => hy) (t.f fun _ => k)
  compat := fun (i j : M.ι) => by
    have h := congrArg (resG X (show M.U i ⊓ M.U j ≤ (lbPow M e).U (fun _ => i) ⊓ (lbPow M e).U (fun _ => j) from
      inf_le_inf (fun _ hy => Set.mem_iInter.2 fun _ => hy) (fun _ hy => Set.mem_iInter.2 fun _ => hy)))
      (t.compat (fun _ => i) (fun _ => j))
    rw [map_mul] at h
    refine (AbLaw.rs_rs _ _ _).trans (((AbLaw.rs_rs _ _ _).symm.trans h).trans ?_)
    congr 1
    · have hu : res (show M.U i ⊓ M.U j ≤ (lbPow M e).U (fun _ => i) ⊓ (lbPow M e).U (fun _ => j) from
          inf_le_inf (fun _ hy => Set.mem_iInter.2 fun _ => hy) (fun _ hy => Set.mem_iInter.2 fun _ => hy))
          ((lbPow M e).g (fun _ => i) (fun _ => j)) = M.g i j ^ (e : ℤ) := by
        first
          | (change res _ (∏ _k : PUnit, _) = _
             rw [Fintype.prod_unique, map_zpow])
          | refine (congrArg (res _) (@Fintype.prod_unique PUnit _ _ _ _ _)).trans ((map_zpow _ _ _).trans ?_)
          | refine (congrArg (res _) (Fintype.prod_unique _)).trans ((map_zpow _ _ _).trans ?_)
        congr 1
        ext
        exact (AbLaw.rs_rs _ _ _).trans (AbLaw.rs_self _ _)
      exact congrArg Units.val hu
    · exact (AbLaw.rs_rs _ _ _).trans (AbLaw.rs_rs _ _ _).symm

theorem eventually_surj [Finite σ] [Nonempty σ] (p : X ⟶ Sp K) (M : LB X) (th : σ → M.Sec) (hM : M.IsLB)
    (h : VAmp p M th) : ∀ᶠ e : ℕ in Filter.atTop, ∀ t : (lbPow M e).Sec, ∃ F : MvPolynomial σ K,
      F.IsHomogeneous e ∧ ∀ j, t.f j = MvPolynomial.eval₂ ((resG X le_top).comp (p.appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)) (fun i => resG X
        (LB.wchart_le M (fun _ : PUnit => 𝟙 X) j PUnit.unit) ((th i).f (j PUnit.unit))) F := by
  obtain ⟨m, ε, hε⟩ := h.exists_veryAmpleBy
  obtain ⟨t₀, ht⟩ := (AbLaw.serre_h1Zero_and_sections_polynomial).2 K X p M m (fun i => th (ε i)) hM hε
  refine Filter.eventually_atTop.2 ⟨t₀, fun e he t => ?_⟩
  obtain ⟨F, hF, hFe⟩ := ht e he (toPw M e t)
  refine ⟨MvPolynomial.rename ε F, hF.rename_isHomogeneous, fun j => ?_⟩
  have hj := hFe (j PUnit.unit)
  unfold toPw at hj
  unfold AbLaw.cst at hj
  have hrs : ∀ {U V : X.Opens} (hUV : V ≤ U), resG X hUV = AbLaw.rs X hUV := fun _ => rfl
  have hA : (lbPow M e).U j ≤ M.U (j PUnit.unit) := LB.wchart_le M (fun _ : PUnit => 𝟙 X) j PUnit.unit
  have hj' := congrArg (AbLaw.rs X hA) hj
  simp only [hrs] at hj' ⊢
  erw [AbLaw.rs_rs, AbLaw.rs_self] at hj'
  rw [hj', MvPolynomial.map_eval₂Hom, MvPolynomial.eval₂_rename, MvPolynomial.coe_eval₂Hom]
  congr 1
  ext a
  simp only [RingHom.comp_apply, AbLaw.rs_rs]
  rfl

attribute [local instance] MvPolynomial.gradedAlgebra

theorem hilbertFunction_idealOf : ∀ (K σ : Type) [Field K] [Finite σ] [Nonempty σ] (X : Scheme.{0}) (p : X ⟶ Sp K) (M : LB X) (th : σ → M.Sec), M.IsLB → VAmp p M th → ∃ Q : Polynomial ℚ, ∀ᶠ e : ℕ in Filter.atTop, ∃ r, SectionsHaveFiniteDimension p (lbPow M e) r ∧ (r : ℚ) = Q.eval (e : ℚ) ∧ dimDeg (idealOf p M th (𝟙 X)) e + r = Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e) := by
  intro K σ _ _ _ X p M th hM h
  classical
  obtain ⟨hhom, -, hsec⟩ := GlobalTheory.T.homogeneous_ideal_sections_of_line_bundle_power K σ X p M th hM h
  have hI : (idealOf p M th (𝟙 X)).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K) := by
    intro i r hr
    convert hhom r hr i using 1
    exact MvPolynomial.decomposition.decompose'_apply r i
  refine ⟨GlobalTheory.idealHilbertPoly (idealOf p M th (𝟙 X)), ?_⟩
  filter_upwards [GlobalTheory.eventually_finrank_quotPiece hI, eventually_surj p M th hM h] with e he hsurj
  refine ⟨Module.finrank K (GlobalTheory.quotPiece (idealOf p M th (𝟙 X)) e), ?_, he, dimDeg_add _ e⟩
  obtain ⟨G, hG, hGu⟩ := exists_forms_basis (idealOf p M th (𝟙 X)) e
  choose s hs1 hs2 hs3 using fun i => hsec e (G i) (hG i)
  have lin : ∀ (R : Type) [CommRing R] (φ : K →+* R) (v : σ → R)
      (a : Fin (Module.finrank K (GlobalTheory.quotPiece (idealOf p M th (𝟙 X)) e)) → K),
      MvPolynomial.eval₂ φ v (∑ i, a i • G i) = ∑ i, φ (a i) * MvPolynomial.eval₂ φ v (G i) := by
    intro R _ φ v a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← MvPolynomial.coe_eval₂Hom, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
  have hsumG : ∀ a : Fin (Module.finrank K (GlobalTheory.quotPiece (idealOf p M th (𝟙 X)) e)) → K,
      (∑ i, a i • G i).IsHomogeneous e := by
    intro a
    rw [← MvPolynomial.mem_homogeneousSubmodule]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ ((MvPolynomial.mem_homogeneousSubmodule _ _).2 (hG i))
  have hzero : ∀ D : MvPolynomial σ K, D.IsHomogeneous e →
      ((∀ j : (lbPow M e).ι, MvPolynomial.eval₂ ((resG X le_top).comp (p.appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)) (fun i => resG X
        (LB.wchart_le M (fun _ : PUnit => 𝟙 X) j PUnit.unit) ((th i).f (j PUnit.unit))) D = 0) ↔
        D ∈ idealOf p M th (𝟙 X)) := by
    intro D hD
    obtain ⟨τ, hτ1, hτ2, -⟩ := hsec e D hD
    rw [← hτ2]
    exact forall_congr' fun j => by rw [hτ1 j]; exact Iff.rfl
  refine ⟨s, fun t => ?_⟩
  obtain ⟨F, hF, hFt⟩ := hsurj t
  obtain ⟨a, ha, hau⟩ := hGu F hF
  refine ⟨a, fun j => ?_, fun a' ha' => hau a' ?_⟩
  · have h0 := (hzero _ (hF.sub (hsumG a))).2 ha j
    rw [MvPolynomial.eval₂_sub, sub_eq_zero] at h0
    rw [hFt j, h0, lin]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hs1 i j]
    rfl
  · refine (hzero _ (hF.sub (hsumG a'))).1 fun j => ?_
    rw [MvPolynomial.eval₂_sub, sub_eq_zero, ← hFt j, ha' j, lin]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hs1 i j]
    rfl

end GlobalTheory.ZV.HilbFn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HilbertFunctionVanishingIdealVeryAmpleSystemStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertFunction_vanishingIdeal_veryAmpleSystem : ∀ (K σ : Type) [Field K] [Finite σ] [Nonempty σ] (X : Scheme.{0}) (p : X ⟶ Sp K) (M : LB X) (th : σ → M.Sec), M.IsLB → VAmp p M th → ∃ Q : Polynomial ℚ, ∀ᶠ e : ℕ in Filter.atTop, ∃ r, SectionsHaveFiniteDimension p (lbPow M e) r ∧ (r : ℚ) = Q.eval (e : ℚ) ∧ dimDeg (idealOf p M th (𝟙 X)) e + r = Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e) := by
  first | exact @GlobalTheory.ZV.HilbFn.hilbertFunction_idealOf | exact GlobalTheory.ZV.HilbFn.hilbertFunction_idealOf | (intros; apply GlobalTheory.ZV.HilbFn.hilbertFunction_idealOf <;> assumption)
end
end
